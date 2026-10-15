-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection__RegularParity
-- name    : OAI_InformationTheory_QuantumCircuit_ProductProjection__RegularParity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:09:11.031035+00:00
-- url     : https://prove2.me/theorems/80cfe2be-9b51-4656-b688-e3c63b7fe8b0
-- title:
--   Tensor-product identities and the resolution of the identity by mismatch patterns
-- statement:
--   This file contains no new objects; it records the basic algebraic identities for tensor products of one-qubit matrices and for the mismatch-pattern projections $P_M^F$ of a count $M=(S,v)$ (with $\Pi_i=|v_i\rangle\langle v_i|$). Tensor products are taken in the computational basis, $\bigl(\bigotimes_i a_i\bigr)_{x,y}=\prod_i (a_i)_{x_i,y_i}$.
--
--   1. **Identity and adjoint.** $\bigotimes_i I=I$ and $\bigl(\bigotimes_i a_i\bigr)^{\ast}=\bigotimes_i a_i^{\ast}$.
--   2. **Rank-one projectors are self-adjoint.** $\bigl(|v\rangle\langle v|\bigr)^{\ast}=|v\rangle\langle v|$ for every $v\in\mathbb C^2$.
--   3. **Normalization over $\mathbb C$.** If $\sum_b |v_b|^2=1$ then $\sum_b\overline{v_b}\,v_b=1$ as a complex number.
--   4. **Empty pattern.** $P_M^{\varnothing}=P_M^0$.
--   5. **Subset expansion.** In a commutative semiring, for a finite set $S$ and families $a,b$,
--   $$
--   \sum_{F\subseteq S}\ \prod_{i\in S}\begin{cases}a_i & i\in F\\ b_i & i\notin F\end{cases}\;=\;\prod_{i\in S}(a_i+b_i),
--   $$
--   and in a commutative monoid, a product over all indices splits as $\prod_i (a_i \text{ if } i\in S,\ b_i \text{ otherwise})=\prod_{i\in S}a_i\cdot\prod_{i\notin S}b_i$.
--   6. **Tensor subset expansion.** For one-qubit matrices $a_i,b_i,c_i$ and a set $S$ of qubits,
--   $$
--   \sum_{F\subseteq S}\ \bigotimes_i\begin{cases}a_i & i\in S\cap F\\ b_i & i\in S\setminus F\\ c_i & i\notin S\end{cases}\;=\;\bigotimes_i\begin{cases}a_i+b_i & i\in S\\ c_i & i\notin S.\end{cases}
--   $$
--   7. **Resolution of the identity.** $\displaystyle\sum_{F\subseteq S}P_M^F=I$.
--
--   Item 7 says that the pattern projections of a count partition the Hilbert space according to the exact set of mismatched qubits; together with their mutual orthogonality (proved later) it yields the spectral decomposition of the mismatch operator $\mathcal N_M$ used throughout the localization argument.
--
--   **Formalization Note** The items are the lemmas `tensorMatrix_one`, `tensorMatrix_star`, `rankOne_star`, `normalized_complex`, `Count.pattern_empty`, `sum_powerset_prod_ite`, `prod_ite_mem`, `tensorMatrix_sum_patterns` and `Count.sum_pattern`. The file also contains a private copy of the core lemma `ite_eq_right` (a compatibility alias) and an empty section.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/ProductProjection.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/ProductProjection.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RegularParity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Model
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic__RegularParity

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

@[simp] lemma tensorMatrix_one {N : ℕ} : tensorMatrix (fun _ : Fin N => (1 : QubitOperator)) = 1 := by
  classical
  ext x y
  simp only [tensorMatrix, Matrix.one_apply]
  by_cases h : x = y
  · subst y
    simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

@[simp] lemma tensorMatrix_star {N : ℕ} (a : Fin N → QubitOperator) :
    star (tensorMatrix a) = tensorMatrix (fun i => star (a i)) := by
  classical
  ext x y
  simp [tensorMatrix, Matrix.star_apply]

@[simp] lemma rankOne_star (v : Bit → ℂ) : star (rankOne v) = rankOne v := by
  ext x y
  simp [rankOne, Matrix.star_apply, mul_comm]

lemma normalized_complex {v : Bit → ℂ} (hv : ∑ b, Complex.normSq (v b) = 1) :
    ∑ b, star (v b) * v b = 1 := by
  have h := congrArg (fun x : ℝ => (x : ℂ)) hv
  simp only [Complex.ofReal_sum, Complex.ofReal_one] at h
  simpa only [mul_comm, Complex.star_def, Complex.mul_conj] using h

@[simp] lemma Count.pattern_empty {N : ℕ} (M : Count N) : M.pattern ∅ = M.zero := by
  simp [Count.pattern, Count.zero]

lemma sum_powerset_prod_ite {ι R : Type*} [DecidableEq ι] [CommSemiring R]
    (S : Finset ι) (a b : ι → R) :
    ∑ F ∈ S.powerset, ∏ i ∈ S, (if i ∈ F then a i else b i) = ∏ i ∈ S, (a i + b i) := by
  classical
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro F hF
  have hFS : F ⊆ S := Finset.mem_powerset.mp hF
  rw [Finset.prod_ite]
  congr 1
  · congr 1
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hFS h, h⟩⟩
  · congr 1
    ext i
    simp

lemma prod_ite_mem {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid R]
    (S : Finset ι) (a b : ι → R) :
    ∏ i, (if i ∈ S then a i else b i) = (∏ i ∈ S, a i) * ∏ i ∈ Finset.univ \ S, b i := by
  classical
  rw [Finset.prod_ite]
  congr 1
  · simp
  · congr 1
    ext i
    simp

lemma tensorMatrix_sum_patterns {N : ℕ} (S : Finset (Fin N))
    (a b c : Fin N → QubitOperator) :
    (∑ F ∈ S.powerset, tensorMatrix (fun i =>
      if i ∈ S then (if i ∈ F then a i else b i) else c i)) =
      tensorMatrix (fun i => if i ∈ S then a i + b i else c i) := by
  classical
  ext x y
  simp only [Matrix.sum_apply]
  change (∑ F ∈ S.powerset, ∏ i, (if i ∈ S then (if i ∈ F then a i else b i) else c i) (x i) (y i)) =
    ∏ i, (if i ∈ S then a i + b i else c i) (x i) (y i)
  simp only [Matrix.ite_apply, Matrix.add_apply]
  simp_rw [prod_ite_mem S]
  rw [← Finset.sum_mul, sum_powerset_prod_ite]

@[simp] lemma Count.sum_pattern {N : ℕ} (M : Count N) :
    ∑ F ∈ M.support.powerset, M.pattern F = 1 := by
  classical
  unfold Count.pattern
  rw [tensorMatrix_sum_patterns]
  simp

section SpectralAlgebra

variable {A ι : Type*} [CStarAlgebra A]

variable [PartialOrder A] [StarOrderedRing A]

end SpectralAlgebra

end QAC

end

end OAI


