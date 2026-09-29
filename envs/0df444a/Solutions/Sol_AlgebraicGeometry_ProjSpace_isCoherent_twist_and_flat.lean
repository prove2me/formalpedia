-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.isCoherent_twist_and_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/8ceaa9f0-bf00-587f-90dd-5331c004ed1b

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Definitions.Def_AlgebraicGeometry_OModulePresheafSectionsLinearRes
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isLocalizedModule_res_of_isQuasicoherent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_isCoherent_twist_and_flat
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace P2mTwistCohFlat

open AlgebraicGeometry.ProjSpace AlgebraicGeometry.OModulePresheaf

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (m : ℕ)
  (U : X.affineOpens)

def smallFuns : Set Γ(X, U.1) := {f | ∃ j : Fin (N + 1), X.basicOpen f ≤ pullbackChart φ j}

theorem span_smallFuns [IsAffineHom φ] : Ideal.span (smallFuns φ U) = ⊤ := by
  rw [← U.2.self_le_iSup_basicOpen_iff]
  intro x hx

  have hcov : (⨆ j : ULift.{u} (Fin (N + 1)), (ProjSpace.stdCoverPullback φ).U j) = ⊤ :=
    (ProjSpace.stdCoverPullback φ).iSup_eq_top
  have hx' : x ∈ (⨆ j : ULift.{u} (Fin (N + 1)), (ProjSpace.stdCoverPullback φ).U j) := by
    rw [hcov]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
  obtain ⟨f, hfle, hxf⟩ := U.2.exists_basicOpen_le ⟨x, hj⟩ hx
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, ⟨j.down, ?_⟩⟩, hxf⟩
  exact hfle

section Local

variable (f : Γ(X, U.1))

noncomputable scoped instance moduleU : Module Γ(X, U.1) ((twist π φ m).obj (X.basicOpen f)) :=
  (twist π φ m).moduleRestrict (X.basicOpen_le f)

scoped instance isScalarTower_U : IsScalarTower Γ(X, U.1) Γ(X, X.basicOpen f) ((twist π φ m).obj (X.basicOpen f)) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

scoped instance isLocalization_U : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_basicOpen f

theorem isLocalizedModule_res [IsSeparated π] [IsAffineHom φ] :
    IsLocalizedModule.Away f ((twist π φ m).resₗ (X.basicOpen_le f) :
      (twist π φ m).obj U.1 →ₗ[Γ(X, U.1)] (twist π φ m).obj (X.basicOpen f)) :=
  isLocalizedModule_res_of_isQuasicoherent (twist π φ m) (ProjSpace.isQuasicoherent_twist π φ m) U f

variable {f}

theorem finite_local {j : Fin (N + 1)} (hf : X.basicOpen f ≤ pullbackChart φ j) :
    Module.Finite Γ(X, X.basicOpen f) ((twist π φ m).obj (X.basicOpen f)) := by
  obtain ⟨e, -, -⟩ := ProjSpace.exists_linearEquiv_twistObj_of_le_pullbackChart π φ m hf
  exact Module.Finite.equiv (e.symm : Γ(X, X.basicOpen f) ≃ₗ[Γ(X, X.basicOpen f)] twistObj π φ m (X.basicOpen f))

theorem flat_local {j : Fin (N + 1)} (hf : X.basicOpen f ≤ pullbackChart φ j) :
    Module.Flat Γ(X, U.1) ((twist π φ m).obj (X.basicOpen f)) := by
  obtain ⟨e, -, -⟩ := ProjSpace.exists_linearEquiv_twistObj_of_le_pullbackChart π φ m hf
  haveI : Module.Flat Γ(X, U.1) Γ(X, X.basicOpen f) := IsLocalization.flat _ (Submonoid.powers f)
  haveI : Module.Flat Γ(X, X.basicOpen f) ((twist π φ m).obj (X.basicOpen f)) :=
    Module.Flat.of_linearEquiv (e : twistObj π φ m (X.basicOpen f) ≃ₗ[Γ(X, X.basicOpen f)] Γ(X, X.basicOpen f))
  exact Module.Flat.trans Γ(X, U.1) Γ(X, X.basicOpen f) _

end Local

theorem finite [IsSeparated π] [IsAffineHom φ] : Module.Finite Γ(X, U.1) ((twist π φ m).obj U.1) := by
  haveI := fun g : smallFuns φ U => isLocalizedModule_res π φ m U g.1
  refine Module.Finite.of_localizationSpan' (smallFuns φ U) (span_smallFuns φ U)
    (Mₚ := fun g : smallFuns φ U => (twist π φ m).obj (X.basicOpen g.1))
    (Rₚ := fun g : smallFuns φ U => Γ(X, X.basicOpen g.1))
    (fun g => (twist π φ m).resₗ (X.basicOpen_le g.1)) fun g => ?_
  obtain ⟨j, hj⟩ := g.2
  exact finite_local π φ m U hj

private theorem _root_.P2mTwistCohFlat.flat [IsSeparated π] [IsAffineHom φ] : Module.Flat Γ(X, U.1) ((twist π φ m).obj U.1) := by
  haveI := fun g : smallFuns φ U => isLocalizedModule_res π φ m U g.1
  refine Module.flat_of_isLocalized_span Γ(X, U.1) ((twist π φ m).obj U.1) (smallFuns φ U) (span_smallFuns φ U)
    (fun g : smallFuns φ U => (twist π φ m).obj (X.basicOpen g.1))
    (fun g => (twist π φ m).resₗ (X.basicOpen_le g.1)) fun g => ?_
  obtain ⟨j, hj⟩ := g.2
  exact flat_local π φ m U hj

p2m_export "P2mTwistCohFlat" "flat"
theorem main [IsSeparated π] [IsAffineHom φ] : (twist π φ m).IsCoherent ∧ ∀ U : X.affineOpens, Module.Flat Γ(X, U.1) ((twist π φ m).obj U.1) :=
  ⟨fun U => finite π φ m U, fun U => flat π φ m U⟩

end P2mTwistCohFlat
p2m_reactivate "P2MW.S_AlgebraicGeometry_ProjSpace_isCoherent_twist_and_flat.P2mTwistCohFlat"

theorem solution
    {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
    (π : X ⟶ Spec (.of A)) [IsSeparated π]
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) [IsAffineHom φ] (m : ℕ) :
    (ProjSpace.twist π φ m).IsCoherent ∧
      ∀ U : X.affineOpens, Module.Flat Γ(X, U.1) ((ProjSpace.twist π φ m).obj U.1) :=
  P2mTwistCohFlat.main π φ m

end S_AlgebraicGeometry_ProjSpace_isCoherent_twist_and_flat
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_isCoherent_twist_and_flat (solution)
