-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LocTransfer
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_LocTransfer
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T13:44:15.294848+00:00
-- url     : https://prove2.me/theorems/d02b9eca-0e1b-4ed8-a48e-8e93fbd7be7b
-- title:
--   Loc Transfer
-- statement:
--   Definitions and structural lemmas for Loc Transfer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/LocTransfer.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open MvPolynomial IsLocalRing
noncomputable section
variable {σ : Type} [Fintype σ]
abbrev renC (σ : Type) [Fintype σ] : MvPolynomial σ ℂ ≃ₐ[ℂ] MvPolynomial (Fin (Fintype.card σ)) ℂ :=
  renameEquiv ℂ (Fintype.equivFin σ)
abbrev renR (σ : Type) [Fintype σ] : MvPolynomial σ ℂ ≃+* MvPolynomial (Fin (Fintype.card σ)) ℂ :=
  (renC σ).toRingEquiv
abbrev renPt (z : σ → ℂ) : Fin (Fintype.card σ) → ℂ := z ∘ (Fintype.equivFin σ).symm
theorem eval_renC (z : σ → ℂ) (h : MvPolynomial σ ℂ) : eval (renPt z) (renC σ h) = eval z h := by
  simp only [renC, renPt, renameEquiv_apply, eval_rename]
  rw [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
theorem map_primeCompl_renC (z : σ → ℂ) :
    Submonoid.map (renR σ).toMonoidHom (ptIdealOf z).primeCompl = (ptIdeal (renPt z)).primeCompl := by
  have key : ∀ x : MvPolynomial σ ℂ, eval (renPt z) ((renR σ).toMonoidHom x) = eval z x :=
    fun x => eval_renC z x
  have key' : ∀ y, (renR σ).toMonoidHom ((renR σ).symm y) = y := fun y => (renR σ).apply_symm_apply y
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    intro hy
    apply hx
    change x ∈ RingHom.ker _
    change _ ∈ RingHom.ker _ at hy
    rw [RingHom.mem_ker] at hy ⊢
    rw [← key x]
    exact hy
  · intro hy
    refine ⟨(renR σ).symm y, ?_, key' y⟩
    intro hx
    apply hy
    change y ∈ RingHom.ker _
    change _ ∈ RingHom.ker _ at hx
    rw [RingHom.mem_ker] at hx ⊢
    rw [← key' y, key]
    exact hx
def locPtEquiv (z : σ → ℂ) : Localization.AtPrime (ptIdealOf z) ≃+* locPt (renPt z) :=
  IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime (ptIdealOf z)) (locPt (renPt z))
    (renR σ) (map_primeCompl_renC z)
theorem locPtEquiv_algebraMap (z : σ → ℂ) (x : MvPolynomial σ ℂ) :
    locPtEquiv z (algebraMap _ _ x) = algebraMap _ (locPt (renPt z)) (renC σ x) := by
  unfold locPtEquiv
  exact IsLocalization.ringEquivOfRingEquiv_eq _ x
def locAtEquiv (I : Ideal (MvPolynomial σ ℂ)) (z : σ → ℂ) :
    locAt I z ≃+* locRing (I.map (renR σ : MvPolynomial σ ℂ →+* _)) (renPt z) :=
  Ideal.quotientEquiv _ _ (locPtEquiv z) (by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    refine RingHom.ext fun x => ?_
    exact (locPtEquiv_algebraMap z x).symm)
end
end ReciprocityTheory.AnForm.R


