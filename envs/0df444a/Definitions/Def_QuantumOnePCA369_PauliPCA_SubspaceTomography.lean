-- Prove2me | Definitions.Def_QuantumOnePCA369_PauliPCA_SubspaceTomography
-- name    : QuantumOnePCA369_PauliPCA_SubspaceTomography
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:55.203738+00:00
-- url     : https://prove2.me/theorems/200ba875-317f-4184-88c9-9b5fabb6d7a4
-- title:
--   Algorithm 3: layer-$\ell$ subspace tomography
-- statement:
--   Algorithm 3 of the paper as a non-adaptive Pauli protocol. Inputs: prefix length $\ell$, suffix length $m$ ($n=\ell+m$), width $k_0$, parameter $k$, block size $M$, mass threshold $p_\ell$, confidence $\delta$, and $2^m\times k_0$ matrices $\tilde U_s$, $s\in\{0,1\}^\ell$.
--
--   1. $\beta^2_{\min}=3k(p_\ell^2+p_\ell/2^\ell)$, $\beta^2_{\max}=24k$, $R=2M\lceil\log_2(\beta^2_{\max}/\beta^2_{\min})\rceil$; $2^nR$ copies are allocated.
--   2. $A_r$ uniform in $\mathrm{Sym}_m(\mathbb F_2)$ and $c_r$ uniform in $\mathbb F_2^m$, independently for $r<R$ (the protocol's randomness).
--   3. Algorithm 2 computes $\pi_s^{(r)}(x)=\tilde U_s^\dagger\sigma_{x,A_rx+c_r}\tilde U_s$.
--   4. For each $r$, $x\in\mathbb F_2^m$ and $j=1,\dots,2^\ell$, a fresh copy is measured with $Z$ on the first $\ell$ qubits, giving $s^{(r,x,j)}$, and in the basis of $\sigma_{x,A_rx+c_r}$ on the last $m$, giving $O^{(r,x,j)}\in\{\pm1\}$.
--   5. $$\hat\rho_s^{(r)}=\sum_x\hat\rho_s^{(r,x)},\qquad\hat\rho_s^{(r,x)}=\frac1{2^\ell}\sum_j\mathbb 1\{s^{(r,x,j)}=s\}\,O^{(r,x,j)}\,\pi_s^{(r)}(x),$$
--   accumulated on the fly into $2^\ell$ matrices.
--   6. For each $s$, Algorithm 1 is run on $\hat\rho_s^{(0)},\hat\rho_s^{(1)},\dots$ with block size $M$, thresholds $\beta^2_{\min},\beta^2_{\max}$ and confidence $\delta/2^\ell$; the outputs are the estimates $\hat\rho_s$.
--
--   Algorithm 1 reads the first $(I+1)M\le R$ rounds; the remaining rounds are discarded.
--
--   **Formalization Note** $\delta$ is an explicit input (the paper uses it without listing it) and is split as $\delta/2^\ell$ over the $2^\ell$ prefixes, as in the proof of Lemma 3.7. The copies are indexed by $(r,x,j)$ with $j\in\mathbb F_2^\ell$.
-- source:
--   Dutch Hansen, Jerry Li, Quantum 1-PCA with Pauli Measurements in Nearly Linear Time, STOC 2027 submission #369 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/369.pdf, p. 10, Algorithm 3 (Layer-ℓ Subspace Tomography); p. 11 (union bound over prefixes in the proof of Lemma 3.7)

import Mathlib
import Definitions.Def_MITMSynthesis_Timed
import Definitions.Def_QuantumOnePCA369_PauliPCA_Basic
import Definitions.Def_QuantumOnePCA369_PauliPCA_Cost
import Definitions.Def_QuantumOnePCA369_PauliPCA_Lepskii
import Definitions.Def_QuantumOnePCA369_PauliPCA_ProjectedPauli
import Definitions.Def_QuantumOnePCA369_PauliPCA_Protocol

namespace QuantumOnePCA369.PauliPCA

open MITMSynthesis

/-! Algorithm 3 (layer-ℓ subspace tomography), p. 10, as a non-adaptive Pauli protocol. -/

/-- Line 1: `β²_min = 3k(p_ℓ² + p_ℓ/2^ℓ)`. -/
noncomputable def alg3BetaMin (ℓ k : ℕ) (p : ℝ) : ℝ := 3 * k * (p ^ 2 + p / 2 ^ ℓ)

/-- Line 1: `β²_max = 24k`. -/
def alg3BetaMax (k : ℕ) : ℝ := 24 * k

/-- Line 2: the number of rounds `R = 2M ⌈log₂(β²_max/β²_min)⌉`. -/
noncomputable def alg3R (ℓ k M : ℕ) (p : ℝ) : ℕ :=
  2 * M * ⌈Real.logb 2 (alg3BetaMax k / alg3BetaMin ℓ k p)⌉₊

/-- Lines 6–14 of Algorithm 3 for given rounds: the projected Paulis
`π_s^{(r)}(x) = Ũ_s† σ_{x, A_r x + c_r} Ũ_s` from Algorithm 2 (line 6), then for each round `r` the
estimates `ρ̂_s^{(r)} = ∑_x ρ̂_s^{(r,x)}` with
`ρ̂_s^{(r,x)} = 2^{-ℓ} ∑_j 1{s^{(r,x,j)} = s} O^{(r,x,j)} π_s^{(r)}(x)` (lines 13–14). Here
`rnd r = (A_r, c_r)` and `out r x j ∈ 𝔽₂ⁿ` is the outcome of copy `(r, x, j)`, `j ∈ 𝔽₂^ℓ` indexing
the `2^ℓ` copies; `s^{(r,x,j)}` is its first `ℓ` bits and `O^{(r,x,j)}` the `±1` value of
`σ_{x, A_r x + c_r}` on the last `m` qubits. The per-copy contributions are added on the fly into
an array of `2^ℓ` accumulators (p. 12). -/
noncomputable def alg3Rounds (n ℓ m k₀ R : ℕ) (U : Bits ℓ → Matrix (Bits m) (Fin k₀) ℂ)
    (rnd : Fin R → SymF2 m × Bits m) (out : Fin R → Bits m → Bits ℓ → Bits n) :
    Timed (Fin R → Bits ℓ → Matrix (Fin k₀) (Fin k₀) ℂ) := do
  let π ← alg2 ℓ m k₀ R (fun r => (rnd r).1) (fun r => (rnd r).2) U
  tab fun r : Fin R => do
    let z ← tab fun x : Bits m => tab fun i : Fin m => do
      let t ← sumC fun j : Fin m => op ((rnd r).1.1 i j * x j)
      op (t + (rnd r).2 i)
    let w ← op (((2 : ℂ) ^ ℓ)⁻¹)
    let acc0 ← tab fun _ : Bits ℓ => tab fun _ : Fin k₀ => tab fun _ : Fin k₀ => op (0 : ℂ)
    foldC (fun (acc : Bits ℓ → Matrix (Fin k₀) (Fin k₀) ℂ) (xj : Bits m × Bits ℓ) => do
        let y := out r xj.1 xj.2
        let s ← tab fun i : Fin ℓ => op (prefixBits ℓ y i)
        let par ← sumC fun t : Fin m =>
          op (if xj.1 t = 0 ∧ z xj.1 t = 0 then (0 : ZMod 2) else suffixBits ℓ m y t)
        let o ← op (sgn par * w)
        let term ← smulMatC o (π r s xj.1)
        let upd ← matAddC (acc s) term
        op (Function.update acc s upd))
      (Finset.univ : Finset (Bits m × Bits ℓ)).toList acc0

/-- **Algorithm 3 (layer-ℓ subspace tomography)**, classical part, for `R` rounds. Inputs: the
prefix length `ℓ`, suffix length `m` (`n = ℓ + m`), width `k₀`, dimension parameter `k`, block size
`M`, mass threshold `p = p_ℓ`, confidence `δ`, the `2^m × k₀` matrices `Ũ_s`, the randomness and the
outcomes. Lines 1–2 compute `β²_min, β²_max` and `R`; lines 6–14 are `alg3Rounds`; line 15 runs
Algorithm 1 for each `s ∈ 𝔽₂^ℓ` on the samples `ρ̂_s^{(0)}, ρ̂_s^{(1)}, …` (rounds beyond `R`
read as `0`) with block size `M`, thresholds `β²_min, β²_max`, and confidence `δ / 2^ℓ`. -/
noncomputable def alg3Decode (ch : SpectralChooser) (n ℓ m k₀ k M : ℕ) (p δ : ℝ) (R : ℕ)
    (U : Bits ℓ → Matrix (Bits m) (Fin k₀) ℂ) (rnd : Fin R → SymF2 m × Bits m)
    (out : Fin R → Bits m → Bits ℓ → Bits n) :
    Timed (Bits ℓ → Matrix (Fin k₀) (Fin k₀) ℂ) := do
  let bmin ← op (alg3BetaMin ℓ k p)
  let bmax ← op (alg3BetaMax k)
  let _ ← op (alg3R ℓ k M p)
  let δs ← op (δ / 2 ^ ℓ)
  let rounds ← alg3Rounds n ℓ m k₀ R U rnd out
  tab fun s : Bits ℓ =>
    lepskii ch k₀ M bmin bmax δs (fun r => if h : r < R then rounds ⟨r, h⟩ s else 0)

/-- **Algorithm 3** as a non-adaptive Pauli protocol on `n` qubits: `R = alg3R ℓ k M p` rounds;
the randomness is `(A_r, c_r)_{r < R}` with `A_r` uniform in `Sym_m(𝔽₂)` and `c_r` uniform in
`𝔽₂^m`, independently (lines 4–5); the `2^n R` copies are indexed by `(r, x, j)` with
`x ∈ 𝔽₂^m`, `j ∈ 𝔽₂^ℓ`, and copy `(r, x, j)` is measured with `Z` on the first `ℓ` qubits and in
the basis of `σ_{x, A_r x + c_r}` on the last `m` qubits (lines 10–12). The output is the family of
Lepskii estimates `ρ̂_s`, `s ∈ 𝔽₂^ℓ`. -/
noncomputable def alg3Protocol (ch : SpectralChooser) (n ℓ m k₀ k M : ℕ) (p δ : ℝ)
    (U : Bits ℓ → Matrix (Bits m) (Fin k₀) ℂ) :
    PauliProtocol n (Bits ℓ → Matrix (Fin k₀) (Fin k₀) ℂ) where
  Rand := Fin (alg3R ℓ k M p) → SymF2 m × Bits m
  Copy := Fin (alg3R ℓ k M p) × Bits m × Bits ℓ
  setting rnd c := alg3Setting n ℓ m c.2.1 ((rnd c.1).1.1.mulVec c.2.1 + (rnd c.1).2)
  decode rnd out := alg3Decode ch n ℓ m k₀ k M p δ (alg3R ℓ k M p) U rnd
    (fun r x j => out (r, x, j))

end QuantumOnePCA369.PauliPCA


