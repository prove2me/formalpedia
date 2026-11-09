-- Prove2me | Definitions.Def_NoisyOWMPC_construction
-- name    : NoisyOWMPC_construction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:54:02.456095+00:00
-- url     : https://prove2.me/theorems/42b3d3d6-dc65-4afb-b778-37415c65f5bc
-- title:
--   Construction 5.23: one-way MPC
-- statement:
--   **Construction 5.23.** The sender, on $x$:
--   1. samples access states $\Omega_i\leftarrow\mathrm{Gen}_{\mathrm{acc},i}$ (when $k>1$), release states $\Theta_{ijv}\leftarrow\mathrm{Gen}_{\mathrm{rel},i}$ for every $(i,j)\in\mathcal I=\{(i,j):j\in[r_i]\}$ and $v\in[N]$, selector keys $K_{ij}\leftarrow\mathrm{Gen}_{\mathrm{sel}}$ and masks $\pi_i\leftarrow\{0,1\}^{r_i}$, all independently;
--   2. builds the program $P$ of Fig. 6, pads it to the common size, and samples $\tilde P\leftarrow i\mathcal O(1^\lambda,P)$;
--   3. outputs $\tau=\tilde P$ (length-prefixed and padded to the fixed public length given by the obfuscator's public description bound) and the channel word $\hat{\mathbf x}$: the access words $X^{\mathrm{acc}}_i$ and the release words $X_{ijv}$ in a public order.
--
--   Receiver $i$ evaluates $\tau$ on its access and release observations, encoded with index $i$, and returns the decoded output, or $\mathsf{fail}$ if parsing or output validation fails. The module also defines the honest output (5.14) $y^*_i=f_i(x;\pi_i\oplus(b_{K_{ij}}(V_{ij}))_j)$ with $V_{ij}=\{v:Q_{\Theta_{ijv}}(D^{ijv}_i)=1\}$.
--
--   **Formalization Note** The construction is parameterized by the protocol halves, the obfuscator, a Fig. 6 program generator and a pad size $s(\lambda)$; the order of cells is access cells $i=1,\dots,k$, then release cells in lexicographic order of $(i,j,v)$.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Construction 5.23, p.30; Fig. 6, p.31; (5.14), p.31

import Mathlib
import Definitions.Def_NoisyOWMPC_fig6
import Definitions.Def_NoisyOWMPC_IOScheme
import Definitions.Def_NoisyOWMPC_Protocol

namespace NoisyOWMPC

open KarpLiptonOM LaconicBarrier

/-- **Padding a circuit to `s` gates** (Ishai, Lu, Zafar, STOC 2027 submission (manuscript sha256
3a9569fa…), §5 Conventions, p.21: "All circuits that are obfuscated or compared are padded to a
common public polynomial size"): append constant gates, read by no output, until there are `s`
gates (a circuit with `s` or more gates is unchanged). The function computed is unchanged. -/
def padC {n : ℕ} (s : ℕ) (C : MCircuit n) : MCircuit n where
  base :=
    { gates := C.base.gates ++ List.replicate (s - C.base.gates.length) (Gate.const false)
      wf := by
        intro g hg i hi
        by_cases h : g < C.base.gates.length
        · rw [List.getElem_append_left h] at hi
          exact C.base.wf g h i hi
        · rw [List.getElem_append_right (by omega)] at hi
          simp [Gate.refs] at hi }
  outs := C.outs
  outs_wf := by
    intro i hi
    have := C.outs_wf i hi
    simp only [List.length_append, List.length_replicate]
    omega

variable {k : ℕ} {X : Type} {Y : Fin k → Type} [∀ i, Fintype (Y i)]

/-- The sender's coins in Construction 5.23: the sampled constants and the obfuscator's coins for a
circuit with `inLen` inputs and size `s + outLen` (the padded program). -/
abbrev SenderCoins (H : Halves k X Y) (F : Functionality k) (O : IOScheme) (s : ℕ → ℕ)
    (lam : ℕ) : Type :=
  Consts H F lam × (Fin (O.coins lam (inLen H F lam) (s lam + outLen F lam)) → Bool)

/-- The obfuscated program `P̃ ← iO(1^λ, pad(P))` (Construction 5.23, step 4, p.30). -/
def obfProg (H : Halves k X Y) (F : Functionality k) (O : IOScheme) (gen : ProgGen H F)
    (s : ℕ → ℕ) (lam : ℕ) (x : Fin (F.lx lam) → Bool) (r : SenderCoins H F O s lam) :
    MCircuit (inLen H F lam) :=
  O.obf lam (inLen H F lam) (s lam + outLen F lam) (padC (s lam) (gen lam x r.1)) r.2

/-- The public bound on the description length of the obfuscated program: the obfuscator's public
length bound `len(λ, n, s + outLen)` for the padded program (§5 Conventions, p.21: "Obfuscations
are length-prefixed and padded to a fixed public length for transmission"). The generator is not
used; it is a parameter so that the transmission length is a function of the protocol's data. -/
def maxObfLen (H : Halves k X Y) (F : Functionality k) (O : IOScheme)
    (_gen : ProgGen H F) (s : ℕ → ℕ) (lam : ℕ) : ℕ :=
  O.len lam (inLen H F lam) (s lam + outLen F lam)

/-- The fixed public transmission length of `τ`: a length field and the longest description. -/
noncomputable def txLen (H : Halves k X Y) (F : Functionality k) (O : IOScheme)
    (gen : ProgGen H F) (s : ℕ → ℕ) (lam : ℕ) : ℕ :=
  Nat.size (maxObfLen H F O gen s lam) + maxObfLen H F O gen s lam

/-- The transmitted form of a description `d` (§5 Conventions, p.21: "Obfuscations are
length-prefixed and padded to a fixed public length for transmission"): `|d|` in binary, `d`, then
zeros up to `txLen`. -/
noncomputable def txEnc (H : Halves k X Y) (F : Functionality k) (O : IOScheme) (gen : ProgGen H F)
    (s : ℕ → ℕ) (lam : ℕ) (d : List Bool) : Fin (txLen H F O gen s lam) → Bool :=
  fun p => (binW (Nat.size (maxObfLen H F O gen s lam)) d.length ++ d).getD p.val false

/-- The number of channel uses: `k` access cells of length `n_acc` and `qN` release cells of length
`n_rel` (Theorem 5.25, p.31: "`1[k > 1] k n_acc + qN n_rel` noisy channel uses"). -/
def nTot (H : Halves k X Y) (F : Functionality k) (lam : ℕ) : ℕ :=
  k * H.nacc lam + (∑ i, F.r i lam) * H.N lam * H.nrel lam

/-- The **public order of the cells** in `x̂` (Construction 5.23, step 5, p.30: "all access words
`X^acc_i` and all release words `X_{ijv}`, concatenated in a public order"): the access cells
`i = 1, …, k` first, then the release cells in lexicographic order of `(i, j, v)`; inside a cell
the positions in order. -/
def posEquiv (H : Halves k X Y) (F : Functionality k) (lam : ℕ) :
    (Fin k × Fin (H.nacc lam)) ⊕ ((Blocks F lam × Fin (H.N lam)) × Fin (H.nrel lam)) ≃
      Fin (nTot H F lam) :=
  (Equiv.sumCongr finProdFinEquiv
    (((Equiv.prodCongr (Equiv.prodCongr finSigmaFinEquiv (Equiv.refl _)) (Equiv.refl _)).trans
      (Equiv.prodCongr finProdFinEquiv (Equiv.refl _))).trans finProdFinEquiv)).trans finSumFinEquiv

/-- The **channel word `x̂`** (Construction 5.23, steps 1 and 5, p.30): the cells
`X^acc_i = Word_acc,i(Ω_i)` and `X_{ijv} = Word_rel,i(Θ_{ijv})` in the public order. -/
def chanWord (H : Halves k X Y) (F : Functionality k) (lam : ℕ) (c : Consts H F lam) :
    Fin (nTot H F lam) → X :=
  fun p => match (posEquiv H F lam).symm p with
    | .inl a => (H.acc a.1).word lam (c.1 a.1) a.2
    | .inr b => (H.rel b.1.1.1).word lam (c.2.1 b.1.1 b.1.2) b.2

/-- Receiver `i`'s query read off its observation `ŷ_i` of `x̂` (Construction 5.23, `R_i`, p.30:
"evaluates the received program `τ` on its access and release observations, encoded with index
`i`"): its observations of the cells `X^acc_i` and `X_{ijv}`. -/
def recvQuery (H : Halves k X Y) (F : Functionality k) (lam : ℕ) (i : Fin k)
    (yh : Fin (nTot H F lam) → Y i) : Query H F lam i :=
  (fun s => yh (posEquiv H F lam (.inl (i, s))),
    fun j v s => yh (posEquiv H F lam (.inr ((⟨i, j⟩, v), s))))

open Classical in
/-- **Construction 5.23 (One-way MPC)** (STOC 2027 submission (manuscript sha256 3a9569fa…),
pp.30–31), for protocol halves `H`, target functions `F`, an obfuscator `O`, a program generator
`gen` and a pad size `s`.
* `S(1^λ, x)`: sample the access states `Ω_i ← Gen_acc,i`, the release states
  `Θ_{ijv} ← Gen_rel,i`, the selector keys `K_{ij} ← Gen_sel` and the uniform masks, all
  independently; build `P` (Fig. 6) with `gen`, pad it to `s` gates, sample `P̃ ← iO(1^λ, P)`;
  output `τ` (the transmitted form of `P̃`) and the channel word `x̂`.
* `R_i(1^λ, τ, ŷ_i)`: parse `τ` as a circuit, evaluate it on the encoding of receiver `i`'s query,
  and return the decoded output, or `fail` if parsing or output validation fails.

**Formalization Note** The sender's coins are the sampled constants with their exact reference law
and the obfuscator's coins; their encoding in the sender's view is the constants' encoding followed
by the obfuscator's coins. -/
noncomputable def construction (H : Halves k X Y) (F : Functionality k) (O : IOScheme)
    (gen : ProgGen H F) (s : ℕ → ℕ) : Protocol k X Y F where
  RS := SenderCoins H F O s
  wS := fun lam r =>
    (∏ i, (H.acc i).genW lam (r.1.1 i)) * (∏ b, ∏ v, (H.rel b.1).genW lam (r.1.2.1 b v)) *
      (∏ b, H.sel.genW lam (r.1.2.2.1 b)) * (1 / 2 : ℝ) ^ (Fintype.card (Blocks F lam)) *
      (1 / 2 : ℝ) ^ (O.coins lam (inLen H F lam) (s lam + outLen F lam))
  encRS := fun lam r => QAdvFew.PoQOracle.tup [constsEnc H F lam r.1, bits r.2]
  L := txLen H F O gen s
  N := nTot H F
  send := fun lam x r => (txEnc H F O gen s lam (obfProg H F O gen s lam x r).code,
    chanWord H F lam r.1)
  recv := fun lam i τ yh =>
    if h : ∃ Pc : MCircuit (inLen H F lam),
        Pc.code.length ≤ maxObfLen H F O gen s lam ∧ txEnc H F O gen s lam Pc.code = τ then
      if h' : ∃ v, outEnc F lam i v = h.choose.eval (queryEnc H F lam i (recvQuery H F lam i yh))
      then some h'.choose else none
    else none

/-- The **honest output** `y*_i = f_i(x; ρ*_i)` with `ρ*_i = π_i ⊕ (b_{K_{ij}}(V_{ij}))_{j ∈ [r_i]}`
and `V_{ij} = {v : Q_{Θ_{ijv}}(D^{ijv}_i) = 1}` (STOC 2027 submission (manuscript sha256 3a9569fa…),
(5.14), p.31), in the real execution of Construction 5.23. -/
noncomputable def ystar (H : Halves k X Y) (F : Functionality k) (O : IOScheme) (gen : ProgGen H F)
    (s : ℕ → ℕ) (lam : ℕ) (x : Fin (F.lx lam) → Bool)
    (ω : (construction H F O gen s).RS lam × (Fin ((construction H F O gen s).N lam) → ∀ i, Y i))
    (i : Fin k) : Fin (F.lo i lam) → Bool :=
  F.f lam i x (fun j => xor (ω.1.1.2.2.2 ⟨i, j⟩) (H.sel.coin lam (ω.1.1.2.2.1 ⟨i, j⟩)
    (acceptSet H F lam ω.1.1 i (recvQuery H F lam i (fun p => ω.2 p i)).2 j)))

end NoisyOWMPC


