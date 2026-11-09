-- Prove2me | Definitions.Def_BosonicLearn_Herm0
-- name    : BosonicLearn_Herm0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:15:23.414771+00:00
-- url     : https://prove2.me/theorems/7b5dfd49-5ed3-4acb-8ac5-278b1fe00903
-- title:
--   $\mathrm{Herm}_0(n)$: traceless Hermitian matrices with Lebesgue measure
-- statement:
--   $\mathrm{Herm}_0(n)=\{X\in\mathbb C^{n\times n}: X^\dagger=X,\ \operatorname{Tr}X=0\}$ is a real vector space of dimension $n^2-1$. It carries its Euclidean topology, the Borel σ-algebra and Lebesgue (additive Haar) measure. The prior of the lower bound and the uniform laws on its balls are taken with respect to this measure.
--
--   **Formalization Note** It is a real subspace of $\mathbb C^{n\times n}$; the instances in the module (closedness, local compactness, Borel σ-algebra) make Haar measures and Fréchet derivatives available. Every use of Lebesgue measure is a normalized law, so the normalization of the Haar measure is immaterial.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §5.1, p. 30

import Mathlib

open MeasureTheory

namespace BosonicLearn

/-- **`Herm₀(n)`: traceless Hermitian `n × n` matrices.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §5.1, p. 30: "Herm_0(n) denotes the space of n-by-n traceless Hermitian matrices"; the prior has a
density "with respect to the Lebesgue measure on Herm_0(n)" (Eq. (32)).

`Herm0 n` is the real subspace `{X ∈ ℂ^{n×n} | X^† = X, Tr X = 0}`, of real dimension `n² − 1` (for `n ≥ 1`). It
carries the subspace topology of `ℂ^{n×n}`, its Borel σ-algebra, and hence additive Haar (Lebesgue) measures.

**Formalization Note.** The instances below (closedness, local compactness, Borel σ-algebra) are structural;
they make `Measure.addHaar` and `fderiv` available on `Herm0 n`. Every use of Lebesgue measure in the paper is a
ratio or a normalized law, so the choice of Haar normalization is immaterial. -/
def Herm0 (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | X.IsHermitian ∧ X.trace = 0}
  add_mem' := fun ha hb => ⟨ha.1.add hb.1, by simp [Matrix.trace_add, ha.2, hb.2]⟩
  zero_mem' := ⟨Matrix.isHermitian_zero, by simp⟩
  smul_mem' := by
    intro c X hX
    refine ⟨?_, by simp [Matrix.trace_smul, hX.2]⟩
    ext i j
    have := congrFun (congrFun hX.1 i) j
    simp [Matrix.conjTranspose_apply] at this ⊢
    rw [← this]; simp

/-- `Herm₀(n)` is closed in `ℂ^{n×n}`. -/
theorem Herm0_isClosed (n : ℕ) : IsClosed ((Herm0 n : Set (Matrix (Fin n) (Fin n) ℂ))) := by
  have h1 : IsClosed {X : Matrix (Fin n) (Fin n) ℂ | X.conjTranspose = X} :=
    isClosed_eq (continuous_id.matrix_conjTranspose) continuous_id
  have h2 : IsClosed {X : Matrix (Fin n) (Fin n) ℂ | X.trace = 0} :=
    isClosed_eq (continuous_id.matrix_trace) continuous_const
  exact h1.inter h2

noncomputable instance (n : ℕ) : LocallyCompactSpace (Herm0 n) :=
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  (Herm0_isClosed n).isClosedEmbedding_subtypeVal.locallyCompactSpace

noncomputable instance (n : ℕ) : MeasurableSpace (Herm0 n) := borel _

instance (n : ℕ) : BorelSpace (Herm0 n) := ⟨rfl⟩

end BosonicLearn


