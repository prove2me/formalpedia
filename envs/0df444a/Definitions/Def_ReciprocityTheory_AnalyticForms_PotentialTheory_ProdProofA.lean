-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ProdProofA
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_ProdProofA
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T12:35:22.447164+00:00
-- url     : https://prove2.me/theorems/68a9de33-26ff-4063-9adb-95cd8ad242e6
-- title:
--   Prod Proof A
-- statement:
--   Definitions and structural lemmas for Prod Proof A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ProdProofA.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_FubiniStudyPotentialProductIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply


set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M
open MeasureTheory Matrix Filter Topology
open scoped ContDiff
noncomputable section
variable {e e' : ℕ}
@[simp] theorem appendCLE_apply_castAdd (u : Fin e → ℂ) (v : Fin e' → ℂ) (i : Fin e) :
    appendCLE e e' (u, v) (Fin.castAdd e' i) = u i := by
  simp [appendCLE]
@[simp] theorem appendCLE_apply_natAdd (u : Fin e → ℂ) (v : Fin e' → ℂ) (i : Fin e') :
    appendCLE e e' (u, v) (Fin.natAdd e i) = v i := by
  simp [appendCLE]
theorem appendCLE_symm_apply (y : Fin (e + e') → ℂ) :
    (appendCLE e e').symm y = (fun i => y (Fin.castAdd e' i), fun i => y (Fin.natAdd e i)) := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp
def pr1L : (Fin (e + e') → ℂ) →L[ℂ] (Fin e → ℂ) :=
  (ContinuousLinearMap.fst ℂ (Fin e → ℂ) (Fin e' → ℂ)).comp
    ((appendCLE e e').symm : (Fin (e + e') → ℂ) →L[ℂ] _)
def pr2L : (Fin (e + e') → ℂ) →L[ℂ] (Fin e' → ℂ) :=
  (ContinuousLinearMap.snd ℂ (Fin e → ℂ) (Fin e' → ℂ)).comp
    ((appendCLE e e').symm : (Fin (e + e') → ℂ) →L[ℂ] _)
theorem firstProjection_apply (y : Fin (e + e') → ℂ) : (pr1L y : Fin e → ℂ) = ((appendCLE e e').symm y).1 := rfl
theorem secondProjection_apply (y : Fin (e + e') → ℂ) : (pr2L y : Fin e' → ℂ) = ((appendCLE e e').symm y).2 := rfl
@[simp] theorem firstProjection_apply_apply (y : Fin (e + e') → ℂ) (i : Fin e) :
    (pr1L y : Fin e → ℂ) i = y (Fin.castAdd e' i) := by
  rw [firstProjection_apply, appendCLE_symm_apply]
@[simp] theorem secondProjection_apply_apply (y : Fin (e + e') → ℂ) (i : Fin e') :
    (pr2L y : Fin e' → ℂ) i = y (Fin.natAdd e i) := by
  rw [secondProjection_apply, appendCLE_symm_apply]
def J1 (e e' : ℕ) : Matrix (Fin e) (Fin (e + e')) ℂ := Matrix.of fun a k => if k = Fin.castAdd e' a then 1 else 0
def J2 (e e' : ℕ) : Matrix (Fin e') (Fin (e + e')) ℂ := Matrix.of fun a k => if k = Fin.natAdd e a then 1 else 0
theorem natAdd_ne_castAdd' (a : Fin e) (b : Fin e') : (Fin.natAdd e b : Fin (e + e')) ≠ Fin.castAdd e' a := by
  intro h; have := congrArg Fin.val h; simp at this; omega
theorem castAdd_ne_natAdd' (a : Fin e) (b : Fin e') : (Fin.castAdd e' a : Fin (e + e')) ≠ Fin.natAdd e b :=
  fun h => natAdd_ne_castAdd' a b h.symm
def finsetAppendEquiv (e e' : ℕ) : Finset (Fin e) × Finset (Fin e') ≃ Finset (Fin (e + e')) where
  toFun p := p.1.map (Fin.castAddEmb e') ∪ p.2.map (Fin.natAddEmb e)
  invFun S := (Finset.univ.filter (fun a => Fin.castAdd e' a ∈ S),
    Finset.univ.filter (fun b => Fin.natAdd e b ∈ S))
  left_inv p := by
    refine Prod.ext ?_ ?_ <;> ext a <;> simp [natAdd_ne_castAdd', castAdd_ne_natAdd']
  right_inv S := by
    ext k
    refine Fin.addCases (fun a => ?_) (fun b => ?_) k <;>
      simp [natAdd_ne_castAdd', castAdd_ne_natAdd']
end
end ReciprocityTheory.AnForm.M


