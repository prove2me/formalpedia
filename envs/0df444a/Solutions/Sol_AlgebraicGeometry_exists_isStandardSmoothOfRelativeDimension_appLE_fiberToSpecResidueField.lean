-- Prove2me | solution 1 for AlgebraicGeometry.exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/cd73634a-960a-585e-8612-2a5a757fcf7f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (m : ℕ)
    (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (hxV : x ∈ V) (e : V ≤ f ⁻¹ᵁ U)
    (h : (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension m) :
    ∃ (U' : (Spec (Y.residueField (f.base x))).Opens) (V' : (f.fiber (f.base x)).Opens) (_ : IsAffineOpen V')
      (_ : f.asFiber x ∈ V') (e' : V' ≤ (f.fiberToSpecResidueField (f.base x)) ⁻¹ᵁ U'),
      ((f.fiberToSpecResidueField (f.base x)).appLE U' V' e').hom.IsStandardSmoothOfRelativeDimension m := by
  classical

  let P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop :=
    fun g => g.IsStandardSmoothOfRelativeDimension m
  have hPi : RingHom.RespectsIso P := RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  have hPb : RingHom.IsStableUnderBaseChange P := RingHom.isStandardSmoothOfRelativeDimension_isStableUnderBaseChange m

  set y : Y := f.base x with hy
  let ι : Spec (Y.residueField y) ⟶ Y := Y.fromSpecResidueField y
  have hyU : y ∈ U := e hxV
  have hιU : (⊤ : (Spec (Y.residueField y)).Opens) ≤ ι ⁻¹ᵁ U := by
    intro p _
    show ι.base p ∈ U
    rw [Scheme.fromSpecResidueField_apply]
    exact hyU

  have H : IsPullback (f.fiberι y) (f.fiberToSpecResidueField y) f ι := IsPullback.of_hasPullback f ι
  let V' : (f.fiber y).Opens := (f.fiberι y) ⁻¹ᵁ V ⊓ (f.fiberToSpecResidueField y) ⁻¹ᵁ ⊤
  have H' := Scheme.Hom.isPullback_resLE H hιU e (UY := V') rfl

  haveI : IsAffine U := hU
  haveI : IsAffine V := hV
  haveI : IsAffine (⊤ : (Spec (Y.residueField y)).Opens) := isAffineOpen_top (Spec (Y.residueField y))

  have h1 : P (f.resLE U V e).appTop.hom := (hPi.arrow_mk_iso_iff (arrowResLEAppIso f U V e)).mpr h

  have h2 : P (pullback.fst (ι.resLE U ⊤ hιU) (f.resLE U V e)).appTop.hom :=
    RingHom.IsStableUnderBaseChange.pullback_fst_appTop P hPb hPi _ _ h1

  let c := H'.flip.isoPullback
  have hc : c.hom ≫ pullback.fst _ _ = (f.fiberToSpecResidueField y).resLE ⊤ V' (by simp [V']) :=
    H'.flip.isoPullback_hom_fst
  haveI : IsAffine V' := IsAffine.of_isIso c.hom
  haveI : IsIso c.hom.appTop := by show IsIso (c.hom.app ⊤); infer_instance
  have h3 : P ((f.fiberToSpecResidueField y).resLE ⊤ V' (by simp [V'])).appTop.hom := by
    rw [← hc, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, hPi.cancel_right_isIso]
    exact h2
  have h4 : P ((f.fiberToSpecResidueField y).appLE ⊤ V' (by simp [V'])).hom :=
    (hPi.arrow_mk_iso_iff (arrowResLEAppIso _ ⊤ V' _)).mp h3
  refine ⟨⊤, V', ‹IsAffine V'›, ?_, by simp [V'], h4⟩

  show f.asFiber x ∈ (f.fiberι y) ⁻¹ᵁ V ⊓ (f.fiberToSpecResidueField y) ⁻¹ᵁ ⊤
  refine ⟨?_, trivial⟩
  show (f.fiberι y).base (f.asFiber x) ∈ V
  rw [Scheme.Hom.fiberι_asFiber]
  exact hxV

end S_AlgebraicGeometry_exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField (solution)
