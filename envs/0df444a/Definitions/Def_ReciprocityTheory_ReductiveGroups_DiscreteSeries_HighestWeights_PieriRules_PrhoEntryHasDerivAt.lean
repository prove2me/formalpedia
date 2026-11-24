-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_PrhoEntryHasDerivAt
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_PrhoEntryHasDerivAt
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T15:13:32.77647+00:00
-- url     : https://prove2.me/theorems/b55c3a2b-e486-490d-b764-8ab4eb157372
-- title:
--   Prho Entry Has Deriv At
-- statement:
--   Definitions and structural lemmas for Prho Entry Has Deriv At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/PrhoEntryHasDerivAt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Unique
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_uq_offdiag_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open scoped Kronecker
namespace ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
lemma prho_submatrix_mul {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P]
    (A B : Matrix ι ι ℂ) (hA : ∀ i k, P i → ¬ P k → A i k = 0) :
    ((A * B).submatrix Subtype.val Subtype.val : Matrix {i // P i} {i // P i} ℂ) =
      (A.submatrix Subtype.val Subtype.val : Matrix {i // P i} {i // P i} ℂ) *
        (B.submatrix Subtype.val Subtype.val : Matrix {i // P i} {i // P i} ℂ) := by
  ext p r
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← Finset.sum_filter_of_ne (p := P) (fun k _ hk => by_contra fun h => hk (by rw [hA _ _ p.2 h, zero_mul]))]
  exact Finset.sum_subtype _ (fun k => by simp) _
def adFull (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  g ⊗ₖ g.map (starRingEnd ℂ)
def adDFull (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  X ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) - (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ Xᵀ
lemma adFull_mul (g h : Matrix (Fin n) (Fin n) ℂ) : adFull (g * h) = adFull g * adFull h := by
  unfold adFull
  rw [Matrix.map_mul, mul_kronecker_mul]
lemma adFull_one : adFull (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  unfold adFull
  rw [Matrix.map_one (starRingEnd ℂ) (map_zero _) (map_one _), one_kronecker_one]
lemma adFull_star (g : Matrix (Fin n) (Fin n) ℂ) : star (adFull g) = adFull (star g) := by
  ext p q
  simp only [adFull, Matrix.star_apply, Matrix.kroneckerMap_apply, Matrix.map_apply, star_mul',
    RCLike.star_def, RCLike.conj_conj]
variable {ε : Fin n → Bool} {β : Bool}
lemma adFull_zero_out {g : Matrix (Fin n) (Fin n) ℂ} (hg : g * Jm ε = Jm ε * g) (p k : Fin n × Fin n)
    (hp : ε p.1 = β ∧ ε p.2 = !β) (hk : ¬ (ε k.1 = β ∧ ε k.2 = !β)) : adFull g p k = 0 := by
  simp only [adFull, Matrix.kroneckerMap_apply, Matrix.map_apply]
  by_cases h1 : ε k.1 = β
  · have h2 : ε p.2 ≠ ε k.2 := fun h => hk ⟨h1, by rw [← h]; exact hp.2⟩
    rw [uq_offdiag_zero hg h2, map_zero, mul_zero]
  · have h2 : ε p.1 ≠ ε k.1 := fun h => h1 (by rw [← h]; exact hp.1)
    rw [uq_offdiag_zero hg h2, zero_mul]
variable (ε β)
def pRhoM (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (pIdx ε β) (pIdx ε β) ℂ :=
  (adFull g).submatrix Subtype.val Subtype.val
lemma pRhoM_mul {g : Matrix (Fin n) (Fin n) ℂ} (hg : g * Jm ε = Jm ε * g) (h : Matrix (Fin n) (Fin n) ℂ) :
    pRhoM ε β (g * h) = pRhoM ε β g * pRhoM ε β h := by
  unfold pRhoM
  rw [adFull_mul]
  exact prho_submatrix_mul (fun p : Fin n × Fin n => ε p.1 = β ∧ ε p.2 = !β) _ _
    (fun i k hi hk => adFull_zero_out hg i k hi hk)
lemma pRhoM_one : pRhoM ε β (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  unfold pRhoM
  rw [adFull_one]
  exact Matrix.submatrix_one _ Subtype.val_injective
lemma pRhoM_star (g : Matrix (Fin n) (Fin n) ℂ) : star (pRhoM ε β g) = pRhoM ε β (star g) := by
  unfold pRhoM
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, ← Matrix.star_eq_conjTranspose,
    adFull_star]
lemma pRhoM_mem (k : KG ε) : pRhoM ε β (toMK k) ∈ unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ) := by
  have hk : toMK k ∈ Kset ε := k.2
  have hs : star (toMK k) ∈ Kset ε := Kset_star ε hk
  rw [Unitary.mem_iff, pRhoM_star, ← pRhoM_mul ε β hs.2, ← pRhoM_mul ε β hk.2,
    Unitary.star_mul_self_of_mem hk.1, Unitary.mul_star_self_of_mem hk.1, pRhoM_one]
  exact ⟨rfl, rfl⟩
def pRho : KG ε →* unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ) where
  toFun k := ⟨pRhoM ε β (toMK k), pRhoM_mem ε β k⟩
  map_one' := Subtype.ext (pRhoM_one ε β)
  map_mul' k l := Subtype.ext (pRhoM_mul ε β (k.2 : toMK k ∈ Kset ε).2 (toMK l))
def pDRho : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (pIdx ε β) (pIdx ε β) ℂ where
  toFun X := (adDFull X).submatrix Subtype.val Subtype.val
  map_add' X Y := by
    ext p q
    simp only [adDFull, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply]
    ring
  map_smul' c X := by
    ext p q
    simp only [adDFull, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply, smul_eq_mul, RingHom.id_apply]
    ring
section Deriv
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end Deriv
end ReciprocityTheory.ChartRestriction.DS.HW


