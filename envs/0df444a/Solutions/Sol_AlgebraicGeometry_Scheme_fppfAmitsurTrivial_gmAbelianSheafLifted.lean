-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.fppfAmitsurTrivial_gmAbelianSheafLifted
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/0b2f9e57-433d-5712-a478-9f6d83483152

import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import Definitions.Def_AlgebraicGeometry_FppfAmitsurTrivial
import Theorems.Thm_Module_FaithfullyFlat_exists_eq_inv_tmul_of_amitsur_cocycle
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_fppfAmitsurTrivial_gmAbelianSheafLifted

set_option autoImplicit false

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec Spec.map Scheme Scheme.ΓSpecIso_naturality Scheme.ΓSpecIso Scheme.FppfAmitsurTrivial"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Γ ΓSpecIso_naturality ΓSpecIso FppfAmitsurTrivial"
namespace GmCob
p2m_open "AlgebraicGeometry.Scheme AlgebraicGeometry"
p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_fppfAmitsurTrivial_gmAbelianSheafLifted.AlgebraicGeometry Opposite Algebra.DescentCofaces FppfKummerSES TensorProduct"

noncomputable abbrev G := GmAbelianSheafLifted.{0}.obj

noncomputable def toUnit (R : CommRingCat.{0}) (s : ToType (G.obj (op (Spec R)))) : (R : Type)ˣ :=
  Units.map (Scheme.ΓSpecIso R).hom.hom.toMonoidHom (gmLiftedSectionUnit s)

noncomputable def ofUnit (R : CommRingCat.{0}) (v : (R : Type)ˣ) : ToType (G.obj (op (Spec R))) :=
  ULift.up (Additive.ofMul (Units.map (Scheme.ΓSpecIso R).inv.hom.toMonoidHom v))

theorem toUnit_ofUnit (R : CommRingCat.{0}) (v : (R : Type)ˣ) : toUnit R (ofUnit R v) = v := by
  apply Units.ext
  simp only [toUnit, ofUnit, gmLiftedSectionUnit, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, toMul_ofMul]
  exact congrArg (fun f : R ⟶ R => f.hom (v : R)) (Scheme.ΓSpecIso R).inv_hom_id

theorem ofUnit_toUnit (R : CommRingCat.{0}) (s : ToType (G.obj (op (Spec R)))) : ofUnit R (toUnit R s) = s := by
  have : Units.map (Scheme.ΓSpecIso R).inv.hom.toMonoidHom
      (Units.map (Scheme.ΓSpecIso R).hom.hom.toMonoidHom (gmLiftedSectionUnit s)) = gmLiftedSectionUnit s := by
    apply Units.ext
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    exact congrArg (fun f : Γ(Spec R, ⊤) ⟶ Γ(Spec R, ⊤) => f.hom _) (Scheme.ΓSpecIso R).hom_inv_id
  simp only [ofUnit, toUnit, this]
  rfl

theorem toUnit_injective (R : CommRingCat.{0}) : Function.Injective (toUnit R) := by
  intro s t h
  rw [← ofUnit_toUnit R s, ← ofUnit_toUnit R t, h]

theorem toUnit_add (R : CommRingCat.{0}) (s t : ToType (G.obj (op (Spec R)))) :
    toUnit R (s + t) = toUnit R s * toUnit R t := by
  simp only [toUnit]
  rw [← map_mul]
  rfl

theorem toUnit_neg (R : CommRingCat.{0}) (s : ToType (G.obj (op (Spec R)))) :
    toUnit R (-s) = (toUnit R s)⁻¹ := by
  simp only [toUnit]
  rw [← map_inv]
  rfl

theorem toUnit_sub (R : CommRingCat.{0}) (s t : ToType (G.obj (op (Spec R)))) :
    toUnit R (s - t) = toUnit R s * (toUnit R t)⁻¹ := by
  rw [sub_eq_add_neg, toUnit_add, toUnit_neg]

theorem toUnit_map {R S : CommRingCat.{0}} (φ : R ⟶ S) (s : ToType (G.obj (op (Spec R)))) :
    toUnit S (G.map (Spec.map φ).op s) = Units.map φ.hom.toMonoidHom (toUnit R s) := by
  apply Units.ext
  simp only [toUnit, gmLiftedSectionUnit, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  rw [gmLifted_map_apply]
  simp only [RingHom.toMonoidHom_eq_coe]
  exact congrArg (fun f : Γ(Spec R, ⊤) ⟶ S => f.hom _) (Scheme.ΓSpecIso_naturality φ)

theorem coe_toUnit_map {R S : CommRingCat.{0}} (φ : R ⟶ S) (s : ToType (G.obj (op (Spec R)))) :
    (toUnit S (G.map (Spec.map φ).op s) : (S : Type)) = φ.hom (toUnit R s : (R : Type)) := by
  rw [toUnit_map]; rfl

theorem main (A : Type) [CommRing A] [Module.FaithfullyFlat ℤ A] :
    Scheme.FppfAmitsurTrivial GmAbelianSheafLifted.{0} A := by
  intro c hc

  have h3 : (c₁₂ ℤ A).hom (toUnit (R₂ ℤ A) c : (R₂ ℤ A : Type)) * (c₂₃ ℤ A).hom (toUnit (R₂ ℤ A) c) =
      (c₁₃ ℤ A).hom (toUnit (R₂ ℤ A) c) := by
    have := congrArg (fun s => ((toUnit (R₃ ℤ A) s : (R₃ ℤ A : Type)))) hc
    simpa only [toUnit_add, Units.val_mul, coe_toUnit_map] using this
  obtain ⟨a, ha⟩ :=
    Module.FaithfullyFlat.exists_eq_inv_tmul_of_amitsur_cocycle (R := ℤ) (A := A) (toUnit (R₂ ℤ A) c) h3
  refine ⟨ofUnit (CommRingCat.of A) a⁻¹, ?_⟩
  apply toUnit_injective
  rw [toUnit_sub, toUnit_map, toUnit_map, toUnit_ofUnit, ← map_inv, inv_inv]
  apply Units.ext
  rw [ha, Units.val_mul, Units.coe_map, Units.coe_map]
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  change _ = (i₁ ℤ A).hom (↑a⁻¹ : A) * (i₂ ℤ A).hom (a : A)
  rw [i₁_apply, i₂_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

end AlgebraicGeometry.Scheme.GmCob

open CategoryTheory _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_fppfAmitsurTrivial_gmAbelianSheafLifted.AlgebraicGeometry in
theorem solution (A : Type) [CommRing A] [Module.FaithfullyFlat ℤ A] :
    Scheme.FppfAmitsurTrivial FppfKummerSES.GmAbelianSheafLifted.{0} A :=
  AlgebraicGeometry.Scheme.GmCob.main A

end S_AlgebraicGeometry_Scheme_fppfAmitsurTrivial_gmAbelianSheafLifted
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_fppfAmitsurTrivial_gmAbelianSheafLifted (solution)
