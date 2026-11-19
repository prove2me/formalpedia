-- Prove2me | Definitions.Def_AlgebraicGeometry_SmallEtaleUnits
-- name    : AlgebraicGeometry_SmallEtaleUnits
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-18T18:48:58.856871+00:00
-- url     : https://prove2.me/theorems/5fe33e6a-5608-4098-9bd3-121d9c89a43b
-- title:
--   The small étale sheaf of units and roots of unity
-- statement:
--   For a scheme $X$, the sheaf of units on the small étale site assigns to an étale $X$-scheme $U$ the group of units in its ring of global sections. The sheaf $\mu_n$ is the kernel of the $n$-th power map on this sheaf. The group law is written additively in the category of abelian sheaves.
-- source:
--   Stacks Project, Sections 59.24 and 59.28, https://stacks.math.columbia.edu/tag/03PK.

import Mathlib

universe u

/- Global units -/
section

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Polynomial
open scoped LaurentPolynomial

namespace PhilipponEtaleUnits

/-- The group of global units, in additive notation, on each scheme. -/
def presheaf : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (Additive ((Scheme.Γ.obj U)ˣ))
  map f := AddCommGrpCat.ofHom (Units.map (Scheme.Γ.map f).hom.toMonoidHom).toAdditive
  map_id U := by
    rw [Scheme.Γ.map_id]
    rfl
  map_comp f g := by
    rw [Scheme.Γ.map_comp]
    rfl

private def laurent : CommRingCat.{u} := CommRingCat.of (ULift.{u} ℤ[T;T⁻¹])

private def coordinate : (ULift.{u} ℤ[T;T⁻¹])ˣ :=
  ((LaurentPolynomial.isUnit_T (R := ℤ) 1).map ULift.ringEquiv.symm.toRingHom).unit

private theorem coordinate_val : (coordinate : ULift.{u} ℤ[T;T⁻¹]) =
    ULift.up (LaurentPolynomial.T 1) := IsUnit.unit_spec _

private theorem laurent_ext {R : CommRingCat.{u}} {f g : laurent.{u} ⟶ R}
    (h : Units.map f.hom.toMonoidHom coordinate = Units.map g.hom.toMonoidHom coordinate) :
    f = g := by
  apply CommRingCat.hom_ext
  let up : ℤ[T;T⁻¹] →+* ULift.{u} ℤ[T;T⁻¹] := ULift.ringEquiv.symm.toRingHom
  have he : f.hom.comp up = g.hom.comp up := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : ℤ[X]))
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent,
        Polynomial.toLaurent_C]
      have hc : LaurentPolynomial.C a = (a : ℤ[T;T⁻¹]) := map_intCast _ _
      rw [hc, map_intCast, map_intCast, map_intCast]
    · simp only [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_X]
      change f.hom (ULift.up (LaurentPolynomial.T 1)) = g.hom (ULift.up (LaurentPolynomial.T 1))
      have h' := congrArg (fun z : Rˣ => (z : R)) h
      simp only [Units.coe_map, coordinate_val] at h'
      exact h'
  ext x
  exact RingHom.congr_fun he x.down

/-- Evaluation at the Laurent coordinate classifies ring maps from the
Laurent polynomial ring by units. -/
private def laurentEquiv (R : CommRingCat.{u}) : (laurent.{u} ⟶ R) ≃ Rˣ where
  toFun f := Units.map f.hom.toMonoidHom coordinate
  invFun a := CommRingCat.ofHom ((LaurentPolynomial.eval₂ (Int.castRingHom R) a).comp
    ULift.ringEquiv.toRingHom)
  left_inv f := by
    apply laurent_ext
    apply Units.ext
    simp only [Units.coe_map, coordinate_val]
    change LaurentPolynomial.eval₂ (Int.castRingHom R)
      (Units.map f.hom.toMonoidHom coordinate) (LaurentPolynomial.T 1) = _
    rw [LaurentPolynomial.eval₂_T, zpow_one, Units.coe_map, coordinate_val]
  right_inv a := by
    apply Units.ext
    simp only [Units.coe_map, coordinate_val]
    change LaurentPolynomial.eval₂ (Int.castRingHom R) a (LaurentPolynomial.T 1) = _
    rw [LaurentPolynomial.eval₂_T, zpow_one]

/-- The underlying set-valued presheaf is represented by the spectrum of
the Laurent polynomial ring. -/
def represented : (presheaf.{u} ⋙ forget AddCommGrpCat) ≅ yoneda.obj (Spec laurent.{u}) :=
  NatIso.ofComponents (fun U => Equiv.toIso <|
    (laurentEquiv (Scheme.Γ.obj U)).symm.trans <|
      (Equiv.trans ⟨fun f => f.op, fun f => f.unop, fun _ => rfl, fun _ => rfl⟩
        (ΓSpec.adjunction.homEquiv U.unop (op laurent.{u})))) (by
    intro U V f
    apply ConcreteCategory.hom_ext
    intro a
    change (Scheme.Γ.obj U)ˣ at a
    change ΓSpec.adjunction.homEquiv V.unop (op laurent.{u})
        ((laurentEquiv (Scheme.Γ.obj V)).symm (Units.map (Scheme.Γ.map f).hom.toMonoidHom a)).op =
      f.unop ≫ ΓSpec.adjunction.homEquiv U.unop (op laurent.{u})
        ((laurentEquiv (Scheme.Γ.obj U)).symm a).op
    rw [← ΓSpec.adjunction.homEquiv_naturality_left]
    congr 1
    apply Quiver.Hom.unop_inj
    change (laurentEquiv (Scheme.Γ.obj V)).symm (Units.map (Scheme.Γ.map f).hom.toMonoidHom a) =
      (laurentEquiv (Scheme.Γ.obj U)).symm a ≫ Scheme.Γ.map f
    apply (laurentEquiv (Scheme.Γ.obj V)).injective
    rw [Equiv.apply_symm_apply]
    change _ = Units.map (((laurentEquiv (Scheme.Γ.obj U)).symm a ≫
      Scheme.Γ.map f).hom.toMonoidHom) coordinate
    change _ = Units.map (Scheme.Γ.map f).hom.toMonoidHom
      ((laurentEquiv (Scheme.Γ.obj U)) ((laurentEquiv (Scheme.Γ.obj U)).symm a))
    rw [Equiv.apply_symm_apply])

theorem isSheaf_big : Presheaf.IsSheaf Scheme.etaleTopology presheaf.{u} := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat)
  apply (Presheaf.isSheaf_of_iso_iff represented).mpr
  apply Presheaf.IsSheaf.of_le
    (Scheme.etaleTopology_le_proetaleTopology.trans Scheme.proetaleTopology_le_fpqcTopology)
  rw [isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

end PhilipponEtaleUnits

end
end

/- Small étale units and roots of unity -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace PhilipponKummerSequence

def underlying (X : Scheme.{u}) : X.Etale ⥤ Scheme.{u} :=
  Scheme.Etale.forget X ⋙ Over.forget X

instance continuous_underlying (X : Scheme.{u}) :
    (underlying X).IsContinuous X.smallEtaleTopology Scheme.etaleTopology := by
  have hle : Scheme.precoverage (@Etale.{u}) ≤ (MorphismProperty.precoverage (@Etale.{u})) :=
    inf_le_right
  have hc := MorphismProperty.isContinuous_comap_forget (S := X) (P := @Etale)
    (Scheme.precoverage @Etale) hle
  rw [MorphismProperty.toGrothendieck_comap_forget_eq_restrictedTopology _ hle] at hc
  letI : (Scheme.Etale.forget X).IsContinuous X.smallEtaleTopology (Scheme.etaleTopology.over X) := hc
  exact Functor.isContinuous_comp _ _ _ (Scheme.etaleTopology.over X) _

/-- The étale sheaf of units is the restriction of the big representable
sheaf, with its pointwise abelian group structure. -/
def units (X : Scheme.{u}) : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  ((underlying X).sheafPushforwardContinuous AddCommGrpCat X.smallEtaleTopology
    Scheme.etaleTopology).obj ⟨PhilipponEtaleUnits.presheaf, PhilipponEtaleUnits.isSheaf_big⟩

def power (X : Scheme.{u}) (n : ℕ) : units X ⟶ units X := n • 𝟙 (units X)

/-- The kernel of the power map is the sheaf of roots of unity. -/
abbrev roots (X : Scheme.{u}) (n : ℕ) : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  kernel (power X n)

def sequence (X : Scheme.{u}) (n : ℕ) : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  ShortComplex.mk (kernel.ι (power X n)) (power X n) (kernel.condition _)


end PhilipponKummerSequence
end
end


