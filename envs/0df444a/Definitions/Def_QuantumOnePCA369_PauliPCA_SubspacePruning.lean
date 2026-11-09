-- Prove2me | Definitions.Def_QuantumOnePCA369_PauliPCA_SubspacePruning
-- name    : QuantumOnePCA369_PauliPCA_SubspacePruning
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:39:04.86859+00:00
-- url     : https://prove2.me/theorems/9f73cca6-02f7-4508-978c-1e86ea537332
-- title:
--   Algorithm 4: subspace pruning, the algorithm of Theorem 1.1
-- statement:
--   Algorithm 4 of the paper as a non-adaptive Pauli protocol, with inputs $n,\Delta,\eta,\varepsilon,\delta$, the algorithm's universal constant $C_M$, and a spectral chooser.
--
--   1. $k=\lceil n\eta/(\Delta\varepsilon)\rceil$, $p=\varepsilon\Delta/n$, and
--   $$M=\Big\lceil C_M\cdot\frac{n^5\eta^2}{\Delta^3\varepsilon^3}\log\frac{n^3\eta}{\Delta^2\varepsilon^2\delta}\Big\rceil .$$
--   2. $U_x=1$ ($1\times1$) for $x\in\{0,1\}^n$.
--   3. For $\ell=n-1,\dots,1$: $\tilde U_s=|0\rangle\langle0|\otimes U_{s0}+|1\rangle\langle1|\otimes U_{s1}$ for $s\in\{0,1\}^\ell$. If $2^{n-\ell}\le k$ then $U_s=\tilde U_s$; otherwise Algorithm 3 runs at layer $\ell$ on fresh copies with mass threshold $p/2^\ell$ and the $\tilde U_s$, $V_s$ is the matrix of top-$k$ eigenvectors of $\hat\rho_s$ (the first $k$ columns returned by the chooser), and $U_s=\tilde U_sV_s$.
--   4. $\tilde U_\emptyset=|0\rangle\langle0|\otimes U_0+|1\rangle\langle1|\otimes U_1$; Algorithm 3 runs at layer $0$ with threshold $p$, giving $\hat\rho_\emptyset$; $|v_\emptyset\rangle$ is its top unit eigenvector, and the output is a dense description of $|\hat\psi\rangle=\tilde U_\emptyset|v_\emptyset\rangle$.
--
--   Every Algorithm 3 call receives confidence $\delta/n$. The randomness of the protocol is the family of pairs $(A_r,c_r)$ of all layers that run Algorithm 3, and its copies are the copies of those calls; which layers run is decided by $n$ and $k$ alone, so the settings never depend on outcomes. Only the classical post-processing ($\tilde U_s$, $V_s$) adapts. If $\varepsilon\ge1$ or $\delta\ge1$ the protocol measures no copy and returns $|0\cdots0\rangle$ after a constant number of charged steps.
--
--   The file also fixes the quantities standing for the factors hidden by $\tilde O$: $L=n+\log(2+1/\varepsilon)+\log(2+1/\Delta)+\log(2+\eta)$ and $D=\log(2+1/\delta)$.
--
--   **Formalization Note** The constant of line 3 is the parameter $C_M$; theorems quantify it before every instance. The layer-zero threshold, absent from line 14, is $p$, as in the proof on p. 17. Widths are tracked exactly ($2^{n-\ell}$ before the first pruned layer, $k$ after it), so no column is padded.
-- source:
--   Dutch Hansen, Jerry Li, Quantum 1-PCA with Pauli Measurements in Nearly Linear Time, STOC 2027 submission #369 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/369.pdf, p. 15, Algorithm 4 (Subspace Pruning); pp. 15–17 (proof of Lemma 4.3: layer conditioning, δ split, layer zero)

import Mathlib
import Definitions.Def_MITMSynthesis_Timed
import Definitions.Def_QuantumOnePCA369_PauliPCA_Basic
import Definitions.Def_QuantumOnePCA369_PauliPCA_Cost
import Definitions.Def_QuantumOnePCA369_PauliPCA_Protocol
import Definitions.Def_QuantumOnePCA369_PauliPCA_SubspaceTomography

namespace QuantumOnePCA369.PauliPCA

open MITMSynthesis

/-! Algorithm 4 (subspace pruning), p. 15, as a non-adaptive Pauli protocol. -/

/-- Line 1: `k = ⌈nη/(Δε)⌉`. -/
noncomputable def alg4k (n : ℕ) (Δ η ε : ℝ) : ℕ := ⌈(n : ℝ) * η / (Δ * ε)⌉₊

/-- Line 2: `p = εΔ/n`. -/
noncomputable def alg4p (n : ℕ) (Δ ε : ℝ) : ℝ := ε * Δ / n

/-- Line 3: `M = ⌈C_M · (n⁵η²/(Δ³ε³)) · log(n³η/(Δ²ε²δ))⌉` for the algorithm's constant `C_M`. -/
noncomputable def alg4M (CM : ℝ) (n : ℕ) (Δ η ε δ : ℝ) : ℕ :=
  ⌈CM * ((n : ℝ) ^ 5 * η ^ 2 / (Δ ^ 3 * ε ^ 3)) *
    Real.log ((n : ℝ) ^ 3 * η / (Δ ^ 2 * ε ^ 2 * δ))⌉₊

/-- Number of Algorithm-3 rounds at stage `t` (suffix length `t + 1`, layer `ℓ = n − (t+1)`):
`R = 2M⌈log₂(β²_max/β²_min)⌉` with threshold `p/2^ℓ` if the layer runs Algorithm 3 (the last
layer `ℓ = 0`, line 14, or a layer with `2^{n−ℓ} > k`, line 10), and `0` otherwise. -/
noncomputable def alg4Rounds (n k M : ℕ) (p : ℝ) (t : ℕ) : ℕ :=
  if t + 1 = n ∨ k < 2 ^ (t + 1) then alg3R (n - (t + 1)) k M (p / 2 ^ (n - (t + 1))) else 0

/-- Randomness of Algorithm 4: the pairs `(A_r, c_r)` of every layer that runs Algorithm 3. -/
abbrev Alg4Rand (n k M : ℕ) (p : ℝ) :=
  (t : Fin n) → Fin (alg4Rounds n k M p t) → SymF2 (t.val + 1) × Bits (t.val + 1)

/-- Copies of Algorithm 4: copy `(r, x, j)` of the Algorithm-3 call at stage `t`. -/
abbrev Alg4Copy (n k M : ℕ) (p : ℝ) :=
  Σ t : Fin n, Fin (alg4Rounds n k M p t) × Bits (t.val + 1) × Bits (n - (t.val + 1))

/-- `|0⟩⟨0| ⊗ U₀ + |1⟩⟨1| ⊗ U₁` (lines 6 and 13): the first suffix qubit selects the block; column
`b·w + c` is column `c` of `U_b`. -/
def mergeU {J J' w : ℕ} (U0 U1 : Matrix (Bits J') (Fin w) ℂ) : Matrix (Bits J) (Fin (2 * w)) ℂ :=
  fun y col =>
    if h : col.val < w then (if headBit y = 0 then U0 (tailBits J' y) ⟨col.val, h⟩ else 0)
    else (if headBit y = 1 then U1 (tailBits J' y) ⟨col.val - w, by omega⟩ else 0)

/-- Lines 4–12 of Algorithm 4. Stage `j` holds, for every prefix `s` of length `n − j`, a
`2^j × w` matrix `U_s`; stage `0` is `U_x = 1` (`1 × 1`). Stage `j + 1` (layer `ℓ = n − (j+1)`)
forms `Ũ_s = |0⟩⟨0| ⊗ U_{s0} + |1⟩⟨1| ⊗ U_{s1}`; if `2^{j+1} ≤ k` it keeps `U_s = Ũ_s`, otherwise
it runs Algorithm 3 at layer `ℓ` with mass threshold `p/2^ℓ`, confidence `δL`, and the stage's fresh
copies and randomness, takes `V_s` = the top-`k` eigenvectors of `ρ̂_s` (the first `k` columns
returned by the spectral primitive), and sets `U_s = Ũ_s V_s`. -/
noncomputable def alg4Stages (ch : SpectralChooser) (n k M : ℕ) (p δL : ℝ)
    (rnd : Alg4Rand n k M p) (out : Alg4Copy n k M p → Bits n) :
    (j : ℕ) → Timed (Σ w : ℕ, Bits (n - j) → Matrix (Bits j) (Fin w) ℂ)
  | 0 => pure ⟨1, fun _ _ _ => 1⟩
  | j + 1 => do
    let st ← alg4Stages ch n k M p δL rnd out j
    let Ut ← tab fun s : Bits (n - (j + 1)) => tab fun y : Bits (j + 1) =>
      tab fun col : Fin (2 * st.1) =>
        op (mergeU (st.2 (childBits (n - j) s 0)) (st.2 (childBits (n - j) s 1)) y col)
    if h : j < n ∧ k < 2 ^ (j + 1) then do
      let ρh ← alg3Decode ch n (n - (j + 1)) (j + 1) (2 * st.1) k M (p / 2 ^ (n - (j + 1))) δL
        (alg4Rounds n k M p j) Ut (rnd ⟨j, h.1⟩) (fun r x jj => out ⟨⟨j, h.1⟩, (r, x, jj)⟩)
      let Unew ← tab fun s : Bits (n - (j + 1)) => do
        let e ← eighC ch (ρh s)
        matMulC (Ut s) (fun (a : Fin (2 * st.1)) (b : Fin (min k (2 * st.1))) =>
          e.2 a ⟨b.val, lt_of_lt_of_le b.isLt (min_le_right _ _)⟩)
      pure ⟨min k (2 * st.1), Unew⟩
    else pure ⟨2 * st.1, Ut⟩

/-- Lines 13–15 of Algorithm 4: `Ũ_∅ = |0⟩⟨0| ⊗ U₀ + |1⟩⟨1| ⊗ U₁`, Algorithm 3 at layer zero
(threshold `p`, confidence `δL`), `|v_∅⟩` = the top unit eigenvector of `ρ̂_∅` (first column
returned by the spectral primitive), and the dense description of `|ψ̂⟩ = Ũ_∅ |v_∅⟩`. -/
noncomputable def alg4Final (ch : SpectralChooser) (n k M : ℕ) (p δL : ℝ)
    (rnd : Alg4Rand n k M p) (out : Alg4Copy n k M p → Bits n) : Timed (VecDesc n) := do
  let st ← alg4Stages ch n k M p δL rnd out (n - 1)
  if h : 0 < n then do
    let t : Fin n := ⟨n - 1, by omega⟩
    let Ut ← tab fun s : Bits (n - (n - 1 + 1)) => tab fun y : Bits (n - 1 + 1) =>
      tab fun col : Fin (2 * st.1) =>
        op (mergeU (st.2 (childBits (n - (n - 1)) s 0)) (st.2 (childBits (n - (n - 1)) s 1)) y col)
    let ρh ← alg3Decode ch n (n - (n - 1 + 1)) (n - 1 + 1) (2 * st.1) k M
      (p / 2 ^ (n - (n - 1 + 1))) δL (alg4Rounds n k M p (n - 1)) Ut (rnd t)
      (fun r x jj => out ⟨t, (r, x, jj)⟩)
    let e ← eighC ch (ρh (fun _ => 0))
    let v : Fin (2 * st.1) → ℂ := fun b => if hw : 0 < 2 * st.1 then e.2 b ⟨0, hw⟩ else 0
    let ψ ← mulVecC (Ut (fun _ => 0)) v
    let ψn ← tab fun x : Bits n => op (ψ (fun i => if hi : i.val < n then x ⟨i.val, hi⟩ else 0))
    op (VecDesc.dense ψn)
  else op (VecDesc.basis 0)

/-- **Algorithm 4 (subspace pruning)**, the algorithm of Theorem 1.1, as a non-adaptive Pauli
protocol on `n` qubits with inputs `Δ, η, ε, δ` and the algorithm's universal constant `C_M`
(line 3); the spectral primitive is the chooser `ch`. If `ε ≥ 1` or `δ ≥ 1` the success requirement
is met by every unit vector or is vacuous, and the protocol measures no copy and returns `|0…0⟩`.
Otherwise it runs Algorithm 4 with `k = ⌈nη/(Δε)⌉`, `p = εΔ/n`, `M` as in line 3, layer failure
probability `δ/n`, and the Algorithm-3 calls of every layer on fresh copies. The state is not an
input: it enters only through the outcome law. -/
noncomputable def alg4 (ch : SpectralChooser) (CM : ℝ) (n : ℕ) (Δ η ε δ : ℝ) :
    PauliProtocol n (VecDesc n) :=
  if 1 ≤ ε ∨ 1 ≤ δ then
    { Rand := Unit
      Copy := Empty
      setting := fun _ c => c.elim
      decode := fun _ _ => do
        let _ ← op (decide (1 ≤ ε))
        let _ ← op (decide (1 ≤ δ))
        op (VecDesc.basis 0) }
  else
    { Rand := Alg4Rand n (alg4k n Δ η ε) (alg4M CM n Δ η ε δ) (alg4p n Δ ε)
      randDecEq := Classical.decEq _
      Copy := Alg4Copy n (alg4k n Δ η ε) (alg4M CM n Δ η ε δ) (alg4p n Δ ε)
      setting := fun rnd c =>
        alg3Setting n (n - (c.1.val + 1)) (c.1.val + 1) c.2.2.1
          ((rnd c.1 c.2.1).1.1.mulVec c.2.2.1 + (rnd c.1 c.2.1).2)
      decode := fun rnd out => do
        let _ ← op (decide (1 ≤ ε))
        let _ ← op (decide (1 ≤ δ))
        let _ ← op (alg4k n Δ η ε)
        let _ ← op (alg4p n Δ ε)
        let _ ← op (alg4M CM n Δ η ε δ)
        let δL ← op (δ / n)
        alg4Final ch n (alg4k n Δ η ε) (alg4M CM n Δ η ε δ) (alg4p n Δ ε) δL rnd out }

/-- The quantity whose powers stand for the polylogarithmic factors suppressed by `Õ` (Lemma 4.3:
"polylogarithmic factors in `1/ε, 1/Δ, η, 2ⁿ`"): `L = n + log(2 + 1/ε) + log(2 + 1/Δ) + log(2 + η)`. -/
noncomputable def polylogL (n : ℕ) (Δ η ε : ℝ) : ℝ :=
  n + Real.log (2 + 1 / ε) + Real.log (2 + 1 / Δ) + Real.log (2 + η)

/-- The confidence factor `D = log(2 + 1/δ)`, used for the printed `log(1/δ)`; it agrees with
`log(1/δ)` up to a factor `2` for `δ ≤ 1/2` and stays positive as `δ → 1`. -/
noncomputable def confD (δ : ℝ) : ℝ := Real.log (2 + 1 / δ)

end QuantumOnePCA369.PauliPCA


