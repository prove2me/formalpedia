-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TorsionGalois
-- name    : GroundTheory_ArithmeticGeometry_AbelianVarieties_TorsionGalois
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:28:19.543411+00:00
-- url     : https://prove2.me/theorems/e24102b9-ffb2-43cc-9f0f-befa546d3fa2
-- title:
--   Torsion Galois
-- statement:
--   Definitions and structural lemmas for Torsion Galois, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TorsionGalois.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Torsion
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
import Theorems.Thm_GroundTheory_ProfCoh_coe_galRootsOfUnityHom_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_openNormalSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
import Theorems.Thm_GroundTheory_ProfCoh_openNormalSubgroupEquiv_apply
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some
attribute [local simp] GroundTheory.ProfCoh.coe_galRootsOfUnityHom_apply
attribute [local simp] GroundTheory.ProfCoh.coe_openNormalSubgroupEquiv_symm_apply
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer
attribute [local simp] GroundTheory.ProfCoh.openNormalSubgroupEquiv_apply
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
attribute [local simp] P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21


set_option autoImplicit false
namespace GroundTheory.Arith.Abelian
open GroundTheory.ProfCoh IntermediateField AddSubgroup WeierstrassCurve
universe w u
section Action
variable (K L : Type u) [Field K] [Field L] [Algebra K L] [DecidableEq L] (W : WeierstrassCurve K)
noncomputable def galPointsHom : Gal(L/K) →* AddMonoid.End (W.baseChange L).toAffine.Point where
  toFun σ := Affine.Point.map (W' := W.toAffine) (σ : L →ₐ[K] L)
  map_one' := by
    refine AddMonoidHom.ext fun P => ?_
    cases P <;> rfl
  map_mul' σ τ := by
    refine AddMonoidHom.ext fun P => ?_
    cases P <;> rfl
@[simp]
theorem galPointsHom_zero (σ : Gal(L/K)) : galPointsHom K L W σ 0 = 0 :=
  rfl
theorem galPointsHom_some (σ : Gal(L/K)) {x y : L}
    (h : (W.baseChange L).toAffine.Nonsingular x y) :
    ∃ h' : (W.baseChange L).toAffine.Nonsingular (σ x) (σ y),
      galPointsHom K L W σ (.some x y h) = .some (σ x) (σ y) h' :=
  ⟨_, rfl⟩
theorem galPointsHom_some_eq_self {σ : Gal(L/K)} {x y : L}
    (h : (W.baseChange L).toAffine.Nonsingular x y) (hx : σ x = x) (hy : σ y = y) :
    galPointsHom K L W σ (.some x y h) = .some x y h := by
  obtain ⟨h', e⟩ := galPointsHom_some K L W σ h
  rw [e]
  simp only [Affine.Point.some.injEq]
  exact ⟨hx, hy⟩
noncomputable def galTorsionHom (n : ℕ) :
    Gal(L/K) →* AddMonoid.End (torsionBy (W.baseChange L).toAffine.Point n) where
  toFun σ :=
    { toFun := fun P => ⟨galPointsHom K L W σ P, by
        rw [torsionBy.nsmul_iff, ← map_nsmul, torsionBy.nsmul_iff.mp P.2, map_zero]⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun P Q => Subtype.ext (map_add _ _ _) }
  map_one' := by
    refine AddMonoidHom.ext fun P => Subtype.ext ?_
    show galPointsHom K L W 1 P = P
    rw [map_one]
    rfl
  map_mul' σ τ := by
    refine AddMonoidHom.ext fun P => Subtype.ext ?_
    show galPointsHom K L W (σ * τ) P = galPointsHom K L W σ (galPointsHom K L W τ P)
    rw [map_mul]
    rfl
@[simp]
theorem coe_galTorsionHom_apply (n : ℕ) (σ : Gal(L/K))
    (P : torsionBy (W.baseChange L).toAffine.Point n) :
    ((galTorsionHom K L W n σ P : torsionBy (W.baseChange L).toAffine.Point n) :
      (W.baseChange L).toAffine.Point) = galPointsHom K L W σ P :=
  rfl
noncomputable abbrev galPoints : Rep.{u} (ULift.{w} ℤ) Gal(L/K) :=
  Rep.of (intRep.{w} (galPointsHom K L W))
noncomputable abbrev galPointsZ : Rep.{u} ℤ Gal(L/K) :=
  Rep.of ((addMonoidEndRingEquivInt (W.baseChange L).toAffine.Point).toRingHom.toMonoidHom.comp
    (galPointsHom K L W))
noncomputable abbrev galTorsion (n : ℕ) : Rep.{u} (ULift.{w} ℤ) Gal(L/K) :=
  Rep.of (intRep.{w} (galTorsionHom K L W n))
noncomputable abbrev galTorsionZ (n : ℕ) : Rep.{u} ℤ Gal(L/K) :=
  Rep.of ((addMonoidEndRingEquivInt
    (torsionBy (W.baseChange L).toAffine.Point n)).toRingHom.toMonoidHom.comp
    (galTorsionHom K L W n))
end Action
section Discrete
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [DecidableEq L] (W : WeierstrassCurve K)
theorem isOpen_of_forall_apply_eq_apply_eq_mem [Algebra.IsIntegral K L] (H : Subgroup Gal(L/K))
    (x y : L) (h : ∀ σ : Gal(L/K), σ x = x → σ y = y → σ ∈ H) : IsOpen (H : Set Gal(L/K)) := by
  have : FiniteDimensional K K⟮x⟯ := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have : FiniteDimensional K K⟮y⟯ := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)
  refine Subgroup.isOpen_mono (H₁ := (K⟮x⟯).fixingSubgroup ⊓ (K⟮y⟯).fixingSubgroup)
    (fun σ hσ => h σ (apply_eq_of_mem_fixingSubgroup_adjoin hσ.1)
      (apply_eq_of_mem_fixingSubgroup_adjoin hσ.2)) ?_
  rw [Subgroup.coe_inf]
  exact (fixingSubgroup_isOpen _).inter (fixingSubgroup_isOpen _)
theorem isOpen_stabilizer_point [Algebra.IsIntegral K L] (H : Subgroup Gal(L/K))
    (P : (W.baseChange L).toAffine.Point) (h : ∀ σ, galPointsHom K L W σ P = P → σ ∈ H) :
    IsOpen (H : Set Gal(L/K)) := by
  rcases P with _ | ⟨x, y, hP⟩
  · have : H = ⊤ := eq_top_iff.mpr fun σ _ => h σ rfl
    rw [this]
    exact isOpen_univ
  · exact isOpen_of_forall_apply_eq_apply_eq_mem H x y fun σ hx hy =>
      h σ (galPointsHom_some_eq_self K L W hP hx hy)
variable [Algebra.IsIntegral K L]
instance isDiscreteRep_galPoints : IsDiscreteRep (galPoints.{w} K L W) :=
  ⟨fun P => isOpen_stabilizer_point W _ P fun _ h => h⟩
instance isDiscreteRep_galPointsZ : IsDiscreteRep (galPointsZ K L W) :=
  ⟨fun P => isOpen_stabilizer_point W _ P fun _ h => h⟩
instance isDiscreteRep_galTorsion (n : ℕ) : IsDiscreteRep (galTorsion.{w} K L W n) :=
  ⟨fun P => isOpen_stabilizer_point W _ (P : (W.baseChange L).toAffine.Point) fun _ h =>
    Subtype.ext h⟩
instance isDiscreteRep_galTorsionZ (n : ℕ) : IsDiscreteRep (galTorsionZ K L W n) :=
  ⟨fun P => isOpen_stabilizer_point W _ (P : (W.baseChange L).toAffine.Point) fun _ h =>
    Subtype.ext h⟩
end Discrete
section SepClosed
instance isElliptic_baseChange {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (W : WeierstrassCurve R) [W.IsElliptic] : (W.baseChange A).IsElliptic :=
  inferInstanceAs (W.map (algebraMap R A)).IsElliptic
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [DecidableEq L] [IsSepClosed L]
  (W : WeierstrassCurve K) [W.IsElliptic]
end SepClosed
end GroundTheory.Arith.Abelian


