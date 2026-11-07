-- Prove2me | Definitions.Def_CliffordHierTest_PNormBias
-- name    : CliffordHierTest_PNormBias
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:59.279304+00:00
-- url     : https://prove2.me/theorems/51e033d1-651c-44e1-a154-0e6a5b38c79a
-- title:
--   Algorithm 1 ($\mathrm{PNormBias}$): swap test on $|\Phi\rangle$ and $(V\otimes I)|\Phi\rangle$, output probability
-- statement:
--   Let $|\Phi\rangle=\frac1{\sqrt{d^n}}\sum_{i\in\mathbb F_d^n}|i,i\rangle$ be the maximally entangled state on two $n$-qudit registers. The **swap test** on two vectors $\psi_1,\psi_2$ prepares a control qubit in $|0\rangle$, applies a Hadamard gate to it, swaps the two registers controlled on the control qubit being $|1\rangle$, applies a second Hadamard gate and measures the control qubit; its result is $1$ when the control qubit reads $|0\rangle$.
--
--   **Algorithm 1** ($\mathrm{PNormBias}(n,d,k,U,U^*)$, $k\ge1$): if $k=1$, perform a swap test on $|\Phi\rangle$ and $(U\otimes I)|\Phi\rangle$ and return the result; otherwise sample $h\in\mathbb F_d^{2n}$ uniformly at random and return $\mathrm{PNormBias}(n,d,k-1,\partial_hU,(\partial_hU)^*)$. Its probability of outputting $1$ is therefore
--   $$\mathop{\mathbb E}_{h_1,\dots,h_{k-1}\in\mathbb F_d^{2n}}\Pr\big[\text{swap test on }|\Phi\rangle,\ (\partial_{h_{k-1}}\cdots\partial_{h_1}U\otimes I)|\Phi\rangle\ \text{returns }1\big].$$
--
--   This acceptance probability is the quantity the tester estimates to learn $\|U\|_{P^4}$.
--
--   **Formalization Note** `pnormBiasProb k U` is the average above, written out over `Fin (k-1) → DiscretePhaseSpace d n`; the swap test is given by its explicit amplitudes (Hadamard on `Fin 2`, controlled swap of the two copies of the pair register). The definition is meant for $k\ge1$.
-- source:
--   Bao, Briët, Castro-Silva, van Dordrecht, Helsen, On Clifford hierarchy testing and near-extremizers of noncommutative uniformity norms, arXiv:2605.26983 (held version, sha256 610d53a6…), §5 Algorithm 1, p.12

import Mathlib
import Definitions.Def_CliffordHierTest_PauliNorm

open scoped Matrix

namespace CliffordHierTest

/-!
# Algorithm 1 (`PNormBias`): output probability

Z. Bao, J. Briët, D. Castro-Silva, P. van Dordrecht, J. Helsen, *On Clifford hierarchy testing and
near-extremizers of noncommutative uniformity norms*, arXiv:2605.26983 (held version, sha256
610d53a6…), §5, Algorithm 1, p.12.

**Formalization Note.** Algorithm 1 on input `k ≥ 1` samples `h₁, …, h_{k-1}` uniformly and
independently from `𝔽_d^{2n}` (step 2, once per recursion level, `h₁` first), so that the oracle
of the last level is `V = ∂_{h_{k-1}} ⋯ ∂_{h₁} U` (built from `U`, `U*` and Weyl gates), and then
performs step 1 on `V`: a swap test on `|Φ⟩` and `(V ⊗ I)|Φ⟩`, with
`|Φ⟩ = d^{-n/2} Σ_{i ∈ 𝔽_d^n} |i, i⟩`. Its output probability is therefore the average over the
directions of the swap-test acceptance probability, which is how `pnormBiasProb` is written.

The swap test of two vectors `ψ₁, ψ₂` is the standard circuit: a control qubit in `|0⟩`, a Hadamard
on it, a swap of the two registers controlled on it being `|1⟩`, a second Hadamard, and a
measurement of the control qubit. Its "result" is `1` when the control qubit reads `|0⟩` (the
symmetric outcome); this is the convention under which Algorithm 1 "returns the result".
The definitions take the input `k ≥ 1`; at `k = 0` the algorithm is undefined and `pnormBiasProb 0`
has no meaning.
-/

open QAlgorithms.Papers.Independent.Extend50.P30

/-- The maximally entangled vector `|Φ⟩ = d^{-n/2} Σ_{i ∈ 𝔽_d^n} |i, i⟩` on two `n`-qudit registers. -/
noncomputable def maxEntangled (d n : ℕ) [NeZero d] : ResidueRegister d n × ResidueRegister d n → ℂ :=
  fun x => if x.1 = x.2 then ((Real.sqrt ((d : ℝ) ^ n))⁻¹ : ℂ) else 0

/-- The Hadamard gate on the control qubit (basis `|0⟩, |1⟩` = `0, 1 : Fin 2`). -/
noncomputable def hadamard2 : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => ((Real.sqrt 2)⁻¹ : ℂ) * (if i = 1 ∧ j = 1 then -1 else 1)

/-- The state after the swap test circuit on `|0⟩ ⊗ ψ₁ ⊗ ψ₂`: Hadamard on the control, swap of the
two registers controlled on `|1⟩`, Hadamard on the control. -/
noncomputable def swapTestState {S : Type*} [Fintype S] (ψ₁ ψ₂ : S → ℂ) : Fin 2 × S × S → ℂ :=
  let init : Fin 2 × S × S → ℂ := fun z => if z.1 = 0 then ψ₁ z.2.1 * ψ₂ z.2.2 else 0
  let s₁ : Fin 2 × S × S → ℂ := fun z => ∑ c : Fin 2, hadamard2 z.1 c * init (c, z.2)
  let s₂ : Fin 2 × S × S → ℂ := fun z => if z.1 = 0 then s₁ z else s₁ (z.1, z.2.2, z.2.1)
  fun z => ∑ c : Fin 2, hadamard2 z.1 c * s₂ (c, z.2)

/-- The probability that the swap test of `ψ₁` and `ψ₂` returns `1` (control qubit reads `|0⟩`). -/
noncomputable def swapTestAccept {S : Type*} [Fintype S] (ψ₁ ψ₂ : S → ℂ) : ℝ :=
  ∑ x : S × S, Complex.normSq (swapTestState ψ₁ ψ₂ (0, x))

/-- Algorithm 1, p.12: the probability that `PNormBias(n, d, k, U, U*)` outputs `1`, for `k ≥ 1`:
the average over `h₁, …, h_{k-1} ∈ 𝔽_d^{2n}` of the probability that the swap test on `|Φ⟩` and
`(V ⊗ I)|Φ⟩` returns `1`, where `V = ∂_{h_{k-1}} ⋯ ∂_{h₁} U`. -/
noncomputable def pnormBiasProb {d n : ℕ} [NeZero d] (k : ℕ) (U : QuditOperator d n) : ℝ :=
  ((Fintype.card (Fin (k - 1) → DiscretePhaseSpace d n) : ℝ))⁻¹ *
    ∑ hs : Fin (k - 1) → DiscretePhaseSpace d n,
      swapTestAccept (maxEntangled d n)
        ((Matrix.kroneckerMap (· * ·) (iterDeriv (k - 1) hs U) (1 : QuditOperator d n)).mulVec
          (maxEntangled d n))

end CliffordHierTest


