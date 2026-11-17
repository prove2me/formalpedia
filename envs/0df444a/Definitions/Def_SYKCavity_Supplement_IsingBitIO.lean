-- Prove2me | Definitions.Def_SYKCavity_Supplement_IsingBitIO
-- name    : SYKCavity_Supplement_IsingBitIO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:46:54.467036+00:00
-- url     : https://prove2.me/theorems/43160f81-2f0b-4c01-9378-e6e6fc1e78dd
-- title:
--   Finite input (rounded couplings on a box, overflow flag) and decoded output of a bit-cost Ising/SK algorithm
-- statement:
--   This file fixes how a bit-cost algorithm for Theorems 26 and 31 receives its data and reports its answer, on the published log-cost rational RAM.
--
--   1. **Rounding.** $\mathrm{dyad}_b(x)=\lfloor2^bx\rfloor/2^b$ rounds $x$ down to $b$ fractional bits. Write $L_N=\lceil\log_2(N+2)\rceil$.
--   2. **Input.** Given a precision function $b(N)$ and a box constant $C_0$: if $\max_e|J_e|>C_0L_N$, the input is the code of $N$ followed by an overflow flag. Otherwise it is the code of $N$, the flag $0$, and the codes of the $b(N)$-bit roundings of $\beta$, of every $\lambda_p$ (orders increasing), and of every coupling $J_{p,E}$ in a fixed explicit order. This is the paper's "rounded entries on this box, with an overflow flag outside it".
--   3. **Output and failure.** The output must decode as a list of rationals $(\hat m_A)_{|A|\le\ell}$ in a fixed order (by size), followed by $\hat L$. The run **fails** if the output does not decode, or if
--   $$\sum_{|A|\le\ell}|\hat m_A-\langle\sigma_A\rangle_{\beta,J}|^2>N^{-2c}\quad\text{or}\quad|\hat L-\log Z_N(\beta,J)|>N^{-c},$$
--   with both targets at the exact couplings and the exact $\beta$.
--
--   These objects state (7.4) and (8.4) in bit complexity, as Sections L.10 and M.6 prove them.
--
--   **Formalization Note** Codes are the published self-delimiting binary codes `encNat`/`encRats`, and the decoder is `decodeAlloc`. Deterministic programs run on the all-zero coin tape.
-- source:
--   Schmidhuber–Zlokapa, Polynomial-time algorithms for mean-field models up to the glass transition, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), Theorems 26 (p.59) and 31 (p.67); App. L.10, pp.168–169; App. M.6, pp.178–180

import Mathlib
import Definitions.Def_SYKCavity_Supplement_IsingModel
import Definitions.Def_BlottoFPTAS_Main_BitRAM

namespace SYKCavity.Supplement

/-!
# The finite input and the decoded output of a bit-cost Ising/SK algorithm

A. Schmidhuber, A. Zlokapa, *Polynomial-time algorithms for mean-field models up to the glass
transition*, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5): Theorems 26 (p.59) and 31
(p.67); App. L.10, pp.168–169 ("The finite input records rounded coordinates and an overflow
flag"); App. M.6, pp.178–180 (box `max_e |J_e| ≤ C₀⌈log₂(N+2)⌉`, "The finite input consists of
rounded entries on this box, with an overflow flag outside it", certified approximation of `β`).

**Formalization Note.**
* The machine is the published log-cost rational RAM `BlottoFPTAS.Main.BitRAM` (bit cost
  `bitCost`, self-delimiting rational codes `encNat`/`encRats`, output decoder `decodeAlloc`);
  deterministic programs (no `coin`) run on the all-zero tape `zeroTape`.
* `dyad b x = ⌊2^b x⌋/2^b`, the dyadic rounding of `x` to `b` fractional bits.
  `logLen N = ⌈log₂(N+2)⌉ = Nat.clog 2 (N+2)`.
* `bitInput P lam prec C₀ N β J`: if some `|J_e| > C₀·logLen N` (overflow), the code of `N`
  followed by the flag `1`; otherwise the code of `N`, the flag `0`, and the codes of the roundings
  at `prec N` bits of `β`, of `λ_p` for `p ∈ P` in increasing order, and of every coupling
  `J_{p,E}`, ordered by `p` increasing and then by `List.sublistsLen p (List.finRange N)`.
* `targets ℓ N` lists the sets `A ⊆ Fin N` with `|A| ≤ ℓ` (by size, then by `sublistsLen`).
  `Fails` holds when the output does not decode as `#targets + 1` rationals, or when the decoded
  `(m̂_A)_A, L̂` satisfy `Σ_{|A|≤ℓ} |m̂_A − ⟨σ_A⟩_{β,J}|² > N^{−2c}` or
  `|L̂ − log Z_N(β,J)| > N^{−c}`, the targets being taken at the exact `J` and `β`.
-/

open BlottoFPTAS.Main

/-- The dyadic rounding `⌊2^b x⌋/2^b`. -/
noncomputable def dyad (b : ℕ) (x : ℝ) : ℚ :=
  ((⌊(2 : ℝ) ^ b * x⌋ : ℤ) : ℚ) / 2 ^ b

/-- `⌈log₂(N + 2)⌉`. -/
def logLen (N : ℕ) : ℕ := Nat.clog 2 (N + 2)

/-- The coupling `J_{p,E}` read at any order `p` and set `E` (`0` off the index set). -/
noncomputable def extCoupling {P : Finset ℕ} {N : ℕ} (J : CIdx P N → ℝ) (p : ℕ)
    (E : Finset (Fin N)) : ℝ :=
  if h : p ∈ P ∧ E.card = p then J ⟨⟨p, h.1⟩, ⟨E, h.2⟩⟩ else 0

/-- All couplings in the fixed input order: by order `p ∈ P` increasing, then by
`List.sublistsLen p (List.finRange N)`. -/
noncomputable def couplingList (P : Finset ℕ) (N : ℕ) (J : CIdx P N → ℝ) : List ℝ :=
  (P.sort (· ≤ ·)).flatMap fun p =>
    (List.sublistsLen p (List.finRange N)).map fun l => extCoupling J p l.toFinset

/-- The finite input: `N`, an overflow flag, and (on the box) the `prec N`-bit roundings of `β`,
of the `λ_p` and of the couplings. -/
noncomputable def bitInput (P : Finset ℕ) (lam : ℕ → ℝ) (prec : ℕ → ℕ) (C₀ : ℝ) (N : ℕ)
    (β : ℝ) (J : CIdx P N → ℝ) : List Bool := by
  classical
  exact if ∃ e, C₀ * (logLen N : ℝ) < |J e| then BitRAM.encNat N ++ [true]
    else BitRAM.encNat N ++ [false] ++
      BitRAM.encRats (dyad (prec N) β :: ((P.sort (· ≤ ·)).map fun p => dyad (prec N) (lam p)) ++
        (couplingList P N J).map (dyad (prec N)))

/-- The target sets `A ⊆ Fin N` with `|A| ≤ ℓ`, by size and then by `sublistsLen`. -/
def targets (ℓ N : ℕ) : List (Finset (Fin N)) :=
  (List.range (ℓ + 1)).flatMap fun k => (List.sublistsLen k (List.finRange N)).map List.toFinset

/-- The failure event of (7.4)/(8.4) for program `prog` at size `N` and couplings `J`. -/
noncomputable def Fails (P : Finset ℕ) (lam : ℕ → ℝ) (ℓ : ℕ) (c : ℝ) (prog : BitRAM.Program)
    (prec : ℕ → ℕ) (C₀ : ℝ) (N : ℕ) (β : ℝ) (J : CIdx P N → ℝ) : Prop :=
  match BitRAM.decodeAlloc ((targets ℓ N).length + 1)
      (BitRAM.output prog (bitInput P lam prec C₀ N β J) BitRAM.zeroTape) with
  | none => True
  | some x =>
      (N : ℝ) ^ (-2 * c) < ∑ i : Fin (targets ℓ N).length,
          ((x i.castSucc : ℝ) - gibbsAvg P lam N β J ((targets ℓ N).get i)) ^ 2 ∨
        (N : ℝ) ^ (-c) < |(x (Fin.last _) : ℝ) - Real.log (partitionFn P lam N β J)|

end SYKCavity.Supplement


