-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P43
-- name    : QAlgorithms_Papers_Independent_Intake100_P43
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T12:24:07.398184+00:00
-- url     : https://prove2.me/theorems/6702ff17-dc19-4a1f-8121-c297372a0ce9
-- title:
--   Definitions for On the dimension of subspaces with bounded Schmidt rank
-- statement:
--   The objects the formalized statements of *On the dimension of subspaces with bounded Schmidt rank* (arXiv:0706.0705) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `coefficientEquiv`: PDF pp.1–2: the full complex-linear coefficient identification in the fixed ordered local computational bases; no normalization or conjugation.
--   - `HasLowerSchmidtRank`: PDF p.1, notation: every nonzero vector of S has Schmidt rank at least r.
--   - `HasUpperSchmidtRank`: PDF p.1, notation: every nonzero vector of S has Schmidt rank at most r.
--   - `HasConstantSchmidtRank`: PDF pp.1,3: constant Schmidt rank means equality for all nonzero vectors.
--   - `TotallyNonsingular`: PDF p.2, Definition 7: every square minor is nonzero. Embeddings select distinct rows and columns. The order-zero minor is included and equals one.
--   - `antisymmetricSubspace`: PDF p.3: the completely antisymmetric subspace. The coefficient condition is transpose = minus itself, without complex conjugation.
--   - `normalizedProjector`: PDF p.4: the canonical normalized orthogonal projector onto S, computed from S itself. Its total-function value for the zero subspace is zero; all physical applications below have strictly positive dimension.
--   - `schmidtMeasure`: PDF p.1: the mixed-state Schmidt measure is the least achievable bound on ranks of positive-weight components, without taking a logarithm. Countable decompositions are written directly using weights and vectors; the imported PureEnsemble is the distinct finite interface used for witnesses. For physical density matrices the candidate set is nonempty (spectral ensemble) and bounded below in N. On an invalid rho with no ensemble this definition has Mathlib's Nat.sInf empty default zero; no theorem uses that default.
-- source:
--   On the dimension of subspaces with bounded Schmidt rank, arXiv:0706.0705v1, https://arxiv.org/abs/0706.0705v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P50
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03

/-!
Cubitt, Montanaro and Winter, arXiv:0706.0705v1, PDF pp.1–4.
Finite complex bipartite spaces use the accepted product computational basis.
A source state is NONZERO, without a normalization requirement (PDF p.1).
Only the vectors in mixed-state decompositions are required to have unit norm.
The accepted Dependency50.P50 module supplies Bipartite and schmidtNumber;
its coefficient rank extends Schmidt rank to zero by zero.
All additions in this module are local to this paper. Compilation is pending.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intake100.P43

open QAlgorithms.Papers.Independent.Dependency50.P50 (Bipartite schmidtNumber)
open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

/-- PDF pp.1–2: the full complex-linear coefficient identification in the
fixed ordered local computational bases; no normalization or conjugation. -/
def coefficientEquiv {dA dB : ℕ} :
    Bipartite dA dB ≃ₗ[ℂ] Matrix (Fin dA) (Fin dB) ℂ where
  toFun v := fun i j => v (i, j)
  invFun M := WithLp.toLp 2 (fun p => M p.1 p.2)
  left_inv v := by ext p; rfl
  right_inv M := by ext i j; rfl
  map_add' v w := by ext i j; rfl
  map_smul' c v := by ext i j; rfl

/-- PDF p.1, notation: every nonzero vector of S has Schmidt rank at least r. -/
def HasLowerSchmidtRank {dA dB : ℕ}
    (S : Submodule ℂ (Bipartite dA dB)) (r : ℕ) : Prop :=
  ∀ v ∈ S, v ≠ 0 → r ≤ schmidtNumber v

/-- PDF p.1, notation: every nonzero vector of S has Schmidt rank at most r. -/
def HasUpperSchmidtRank {dA dB : ℕ}
    (S : Submodule ℂ (Bipartite dA dB)) (r : ℕ) : Prop :=
  ∀ v ∈ S, v ≠ 0 → schmidtNumber v ≤ r

/-- PDF pp.1,3: constant Schmidt rank means equality for all nonzero vectors. -/
def HasConstantSchmidtRank {dA dB : ℕ}
    (S : Submodule ℂ (Bipartite dA dB)) (r : ℕ) : Prop :=
  ∀ v ∈ S, v ≠ 0 → schmidtNumber v = r

/-- PDF p.2, Definition 7: every square minor is nonzero. Embeddings select
 distinct rows and columns. The order-zero minor is included and equals one. -/
def TotallyNonsingular {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ (k : ℕ) (rows cols : Fin k ↪ Fin n),
    (M.submatrix rows cols).det ≠ 0

/-- PDF p.3: the completely antisymmetric subspace. The coefficient condition
is transpose = minus itself, without complex conjugation. -/
def antisymmetricSubspace : Submodule ℂ (Bipartite 3 3) where
  carrier := {v | ∀ i j, v (i, j) = -v (j, i)}
  zero_mem' := by intro i j; simp
  add_mem' := by
    intro v w hv hw i j
    change v (i, j) + w (i, j) = -(v (j, i) + w (j, i))
    rw [hv i j, hw i j, neg_add]
  smul_mem' := by
    intro c v hv i j
    change c * v (i, j) = -(c * v (j, i))
    rw [hv i j, mul_neg]

/-- PDF p.4: the canonical normalized orthogonal projector onto S, computed
from S itself. Its total-function value for the zero subspace is zero;
all physical applications below have strictly positive dimension. -/
def normalizedProjector {dA dB : ℕ} (S : Submodule ℂ (Bipartite dA dB)) :
    Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ :=
  (Module.finrank ℂ S : ℂ)⁻¹ •
    (fun i j => (S.starProjection (QAlgorithms.ket j)) i)

/-- PDF p.1: the mixed-state Schmidt measure is the least achievable bound
on ranks of positive-weight components, without taking a logarithm.
Countable decompositions are written directly using weights and vectors; the
imported PureEnsemble is the distinct finite interface used for witnesses.
For physical density matrices the candidate set is nonempty (spectral ensemble)
and bounded below in N. On an invalid rho with no ensemble this definition has
Mathlib's Nat.sInf empty default zero; no theorem uses that default. -/
def schmidtMeasure {dA dB : ℕ}
    (rho : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) : ℕ :=
  sInf {k : ℕ | ∃ (weight : ℕ → ℝ) (vector : ℕ → Bipartite dA dB),
    (∀ i, 0 ≤ weight i) ∧ HasSum weight 1 ∧
    (∀ i, ‖vector i‖ = 1) ∧
    (∀ a b, HasSum
      (fun i => (weight i : ℂ) * QAlgorithms.pureDensity (vector i) a b) (rho a b)) ∧
    ∀ i, 0 < weight i → schmidtNumber (vector i) ≤ k}

/-- Sanity: one coefficient is read in the ordered product basis. -/
example (v : Bipartite 2 3) : coefficientEquiv v (0 : Fin 2) (1 : Fin 3) =
    v ((0 : Fin 2), (1 : Fin 3)) := rfl

/-- Sanity: the zero subspace has no nonzero vectors to constrain. -/
example (r : ℕ) : HasLowerSchmidtRank (⊥ : Submodule ℂ (Bipartite 1 1)) r := by
  intro v hv hne
  exact (hne (by simpa using hv)).elim

/-- Sanity: the upper/constant predicates also exclude the zero vector. -/
example (r : ℕ) : HasUpperSchmidtRank (⊥ : Submodule ℂ (Bipartite 1 1)) r ∧
    HasConstantSchmidtRank (⊥ : Submodule ℂ (Bipartite 1 1)) r := by
  constructor <;> intro v hv hne <;> exact (hne (by simpa using hv)).elim

/-- Sanity: the order-zero determinant in the minor predicate equals one. -/
example {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (rows cols : Fin 0 ↪ Fin n) : (M.submatrix rows cols).det = 1 := by
  simp

/-- Sanity: antisymmetry permits zero, as a linear subspace must. -/
example : (0 : Bipartite 3 3) ∈ antisymmetricSubspace := by
  intro i j
  simp

/-- Sanity: normalization on the zero subspace returns zero, never a density. -/
example : normalizedProjector (⊥ : Submodule ℂ (Bipartite 1 1)) = 0 := by
  simp [normalizedProjector] <;> rfl

/-- Sanity: the imported finite ensemble has total weight one. -/
example {dA dB : ℕ} (E : PureEnsemble (Fin dA × Fin dB)) :
    ∑ i, E.weight i = 1 := E.total

/-- Sanity: a convergent decomposition with all positive-weight ranks at most
one supplies a candidate in the countable Schmidt-measure definition. -/
example {rho : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ}
    (weight : ℕ → ℝ) (vector : ℕ → Bipartite 1 1)
    (hw : ∀ i, 0 ≤ weight i) (hs : HasSum weight 1)
    (hv : ∀ i, ‖vector i‖ = 1)
    (he : ∀ a b, HasSum
      (fun i => (weight i : ℂ) * QAlgorithms.pureDensity (vector i) a b) (rho a b))
    (hr : ∀ i, 0 < weight i → schmidtNumber (vector i) ≤ 1) :
    1 ∈ {k : ℕ | ∃ (w : ℕ → ℝ) (v : ℕ → Bipartite 1 1),
      (∀ i, 0 ≤ w i) ∧ HasSum w 1 ∧ (∀ i, ‖v i‖ = 1) ∧
      (∀ a b, HasSum
        (fun i => (w i : ℂ) * QAlgorithms.pureDensity (v i) a b) (rho a b)) ∧
      ∀ i, 0 < w i → schmidtNumber (v i) ≤ k} :=
  ⟨weight, vector, hw, hs, hv, he, hr⟩

end QAlgorithms.Papers.Independent.Intake100.P43


