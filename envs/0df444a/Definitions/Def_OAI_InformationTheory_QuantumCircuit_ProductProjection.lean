-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
-- name    : OAI_InformationTheory_QuantumCircuit_ProductProjection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:10:52.446644+00:00
-- url     : https://prove2.me/theorems/fa631cdb-0ca0-4606-bd27-c3c1e8dfbdf4
-- title:
--   Tensor-product identities and the pattern resolution of the identity
-- statement:
--   This file collects elementary algebraic facts about tensor products of $2\times2$ matrices and about the pattern projections of a count $M$ on $N$ qubits (support $S\subseteq[N]$, vectors $v_i$ that are unit for $i\in S$, $P_i=|v_i\rangle\langle v_i|$, pattern projections $\Pi^M_F$ and zero projection $\Pi^M_0$, as in the basic definitions). It introduces no new objects; its results are:
--
--   1. $\bigotimes_{i}I=I$, and $\bigl(\bigotimes_i a_i\bigr)^*=\bigotimes_i a_i^*$ for $2\times2$ complex matrices $a_i$.
--
--   2. $|v\rangle\langle v|$ is self-adjoint for every $v\in\mathbb{C}^2$.
--
--   3. If $\sum_b|v_b|^2=1$ then $\sum_b\overline{v_b}\,v_b=1$ in $\mathbb{C}$.
--
--   4. $\Pi^M_\varnothing=\Pi^M_0$.
--
--   5. For a finite set $S$ and elements $a_i,b_i$ of a commutative semiring, $\sum_{F\subseteq S}\prod_{i\in S}c^F_i=\prod_{i\in S}(a_i+b_i)$, where $c^F_i=a_i$ for $i\in F$ and $c^F_i=b_i$ otherwise; and, over a finite index type, $\prod_i e_i=\prod_{i\in S}a_i\cdot\prod_{i\notin S}b_i$ when $e_i=a_i$ for $i\in S$ and $e_i=b_i$ otherwise.
--
--   6. For $2\times2$ matrices $a_i,b_i,c_i$ and $S\subseteq[N]$,
--   $$
--   \sum_{F\subseteq S}\ \bigotimes_i\begin{cases}a_i & i\in S\cap F\\ b_i & i\in S\setminus F\\ c_i& i\notin S\end{cases}\;=\;\bigotimes_i\begin{cases}a_i+b_i & i\in S\\ c_i & i\notin S.\end{cases}
--   $$
--
--   7. The pattern projections resolve the identity:
--   $$
--   \sum_{F\subseteq S}\Pi^M_F=I .
--   $$
--
--   Item 7 is item 6 with $a_i=I-P_i$, $b_i=P_i$ and $c_i=I$. It is the completeness half of the spectral decomposition of the mismatch count; together with the mutual orthogonality of the $\Pi^M_F$ it makes $\{\Pi^M_F\}_{F\subseteq S}$ an orthogonal resolution of the identity, on which the high and low projections and the functional calculus of the count are built.
--
--   **Formalization Note** The Lean names are `tensorMatrix_one`, `tensorMatrix_star`, `rankOne_star`, `normalized_complex`, `Count.pattern_empty`, `sum_powerset_prod_ite`, `prod_ite_mem`, `tensorMatrix_sum_patterns` and `Count.sum_pattern`. The private lemma `ite_eq_right` is a compatibility alias for `if_neg`, and the section `SpectralAlgebra` only declares variables.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/ProductProjection.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/ProductProjection.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the QACParity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic

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


