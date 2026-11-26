-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleAdditiveStructureSheaf
-- name    : AlgebraicGeometry_EtaleAdditiveStructureSheaf
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-26T09:40:14.43934+00:00
-- url     : https://prove2.me/theorems/ca547111-b5e6-5b92-bc2f-f5872c4bdc5e
-- title:
--   The additive structure sheaf on the small étale site
-- statement:
--   The additive group of sections on each étale chart defines a sheaf. Scalars act on its cohomology through multiplication on sections.
-- source:
--   Stacks Project, Lemma 59.63.6, https://stacks.math.columbia.edu/tag/0A3P.

import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Module.MinimalAxioms
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.AlgebraicGeometry.AffineSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Opposite

universe u

noncomputable section

namespace PhilipponEtaleAdditiveStructureSheaf

private def underlying (X : Scheme.{u}) : X.Etale ⥤ Scheme.{u} :=
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

private def bigPresheaf : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (Scheme.Γ.obj U)
  map f := AddCommGrpCat.ofHom (Scheme.Γ.map f).hom.toAddMonoidHom
  map_id U := by rw [Scheme.Γ.map_id]; rfl
  map_comp f g := by rw [Scheme.Γ.map_comp]; rfl

private def globalEquiv (U : Scheme.{u}) :
    Γ(U, ⊤) ≃ (U ⟶ Spec (.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ)))) where
  toFun x := (AffineSpace.toSpecMvPolyIntEquiv PUnit).symm (fun _ => x)
  invFun f := AffineSpace.toSpecMvPolyIntEquiv PUnit f PUnit.unit
  left_inv x := by simp
  right_inv f := by
    apply (AffineSpace.toSpecMvPolyIntEquiv PUnit).injective
    rw [Equiv.apply_symm_apply]

private def represented :
    (bigPresheaf.{u} ⋙ forget AddCommGrpCat) ≅
      yoneda.obj (Spec (.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ)))) :=
  NatIso.ofComponents (fun U => Equiv.toIso (globalEquiv U.unop)) (by
    intro U V f
    apply ConcreteCategory.hom_ext
    intro a
    change Γ(U.unop, ⊤) at a
    change globalEquiv V.unop (f.unop.appTop a) = f.unop ≫ globalEquiv U.unop a
    apply (AffineSpace.toSpecMvPolyIntEquiv PUnit).injective
    funext i
    rw [AffineSpace.toSpecMvPolyIntEquiv_comp]
    simp only [globalEquiv, Equiv.coe_fn_mk, Equiv.apply_symm_apply])

private theorem isSheaf_big : Presheaf.IsSheaf Scheme.etaleTopology bigPresheaf.{u} := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat)
  apply (Presheaf.isSheaf_of_iso_iff represented).mpr
  apply Presheaf.IsSheaf.of_le
    (Scheme.etaleTopology_le_proetaleTopology.trans Scheme.proetaleTopology_le_fpqcTopology)
  rw [isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

/-- The additive sheaf on the small étale site, obtained from the global sections
of its objects with their ordinary pullback maps. -/
def sheaf (X : Scheme.{u}) : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  ((underlying X).sheafPushforwardContinuous AddCommGrpCat
    X.smallEtaleTopology Scheme.etaleTopology).obj ⟨bigPresheaf, isSheaf_big⟩

variable {K : Type u} [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (.of K))

/-- Pullback of a base scalar to an object in the small étale site. -/
def scalar (U : X.Etale) : CommRingCat.of K ⟶ Γ(U.left, ⊤) :=
  (Scheme.ΓSpecIso (.of K)).inv ≫ (U.hom ≫ π).appTop

private theorem scalar_natural {U V : X.Etale} (f : U ⟶ V) :
    scalar π V ≫ f.left.appTop = scalar π U := by
  rw [scalar, scalar, Category.assoc, ← Scheme.Hom.comp_appTop,
    ← Category.assoc, MorphismProperty.Over.w f]

/-- Multiplication by a scalar is an endomorphism of the additive sheaf. -/
def mulScalar (a : K) : sheaf X ⟶ sheaf X where
  hom :=
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun x : Γ(U.unop.left, ⊤) => scalar π U.unop a * x
          map_zero' := mul_zero _
          map_add' := mul_add _ }
      naturality := by
        intro U V f
        apply AddCommGrpCat.ext
        intro x
        change Γ(U.unop.left, ⊤) at x
        have h := ConcreteCategory.congr_hom (scalar_natural π f.unop) a
        change scalar π V.unop a * f.unop.left.appTop x =
          f.unop.left.appTop (scalar π U.unop a * x)
        rw [map_mul, ← h]
        rfl }

variable {p : ℕ} (hp : p.Prime) (hK : (p : K) = 0)

include π hK in
theorem cast_eq_zero (U : X.Etale) : (p : Γ(U.left, ⊤)) = 0 := by
  simpa using congrArg (fun a : K => scalar π U a) hK

include π hp hK in
private theorem add_pow_eq (U : X.Etale) (x y : Γ(U.left, ⊤)) :
    (x + y) ^ p = x ^ p + y ^ p := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp x y
  simpa [cast_eq_zero π hK U] using hr

/-- The Frobenius endomorphism raises every section on the étale site to the p-th power. -/
def frobenius : sheaf X ⟶ sheaf X where
  hom :=
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun x : Γ(U.unop.left, ⊤) => x ^ p
          map_zero' := zero_pow hp.ne_zero
          map_add' := add_pow_eq π hp hK U.unop }
      naturality := by
        intro U V f
        apply AddCommGrpCat.ext
        intro x
        change Γ(U.unop.left, ⊤) at x
        change f.unop.left.appTop x ^ p = f.unop.left.appTop (x ^ p)
        rw [map_pow] }

@[simp] theorem frobenius_app (U : X.Etale) (x : Γ(U.left, ⊤)) :
    (frobenius π hp hK).hom.app (op U) x = x ^ p := rfl

@[simp] theorem mulScalar_app (a : K) (U : X.Etale) (x : Γ(U.left, ⊤)) :
    (mulScalar π a).hom.app (op U) x = scalar π U a * x := rfl

private theorem mulScalar_add (a b : K) :
    mulScalar π (a + b) = mulScalar π a + mulScalar π b := by
  ext U x
  change Γ(U.unop.left, ⊤) at x
  change scalar π U.unop (a + b) * x = scalar π U.unop a * x + scalar π U.unop b * x
  rw [map_add, add_mul]

private theorem mulScalar_mul (a b : K) :
    mulScalar π (a * b) = mulScalar π b ≫ mulScalar π a := by
  ext U x
  change Γ(U.unop.left, ⊤) at x
  change scalar π U.unop (a * b) * x = scalar π U.unop a * (scalar π U.unop b * x)
  rw [map_mul, mul_assoc]

private theorem mulScalar_one : mulScalar π 1 = 𝟙 (sheaf X) := by
  ext U x
  change Γ(U.unop.left, ⊤) at x
  change scalar π U.unop 1 * x = x
  rw [map_one, one_mul]

/-- The scalar action induced on cohomology by multiplication on sections. -/
@[instance_reducible] def cohomologyModule (q : ℕ) : Module K ((sheaf X).H q) := by
  letI : SMul K ((sheaf X).H q) := ⟨fun a x => Sheaf.H.map (mulScalar π a) q x⟩
  refine Module.ofMinimalAxioms (fun a x y => map_add (Sheaf.H.map (mulScalar π a) q) x y)
    (fun a b x => ?_) (fun a b x => ?_) (fun x => ?_)
  · change Sheaf.H.map (mulScalar π (a + b)) q x =
      Sheaf.H.map (mulScalar π a) q x + Sheaf.H.map (mulScalar π b) q x
    rw [mulScalar_add, Sheaf.H.map_add_apply]
  · change Sheaf.H.map (mulScalar π (a * b)) q x =
      Sheaf.H.map (mulScalar π a) q (Sheaf.H.map (mulScalar π b) q x)
    rw [mulScalar_mul, Sheaf.H.map_comp_apply]
  · change Sheaf.H.map (mulScalar π 1) q x = x
    rw [mulScalar_one, Sheaf.H.map_id_apply]

end PhilipponEtaleAdditiveStructureSheaf


