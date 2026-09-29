-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.exists_projPresentation_toProj_eq_and_locallyTrivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/cd3c8c61-eb1f-5f4f-b19f-881fe1db03b2

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial.AlgebraicGeometry MvPolynomial HomogeneousLocalization"

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme Proj Proj.basicOpen Scheme.Modules Proj.iSup_basicOpen_eq_top ProjSpace.π ProjSpace.irrelevant_le_span_X Scheme.Modules.glueOfCocycle Scheme.Modules.isFrameOn_glueFrame Scheme.Modules.IsFrameOn ProjSpace.pullbackChart ProjSpace.frameUnit ProjSpace.restrictFun ProjSpace.restrictFun_restrictFun ProjSpace.pullbackOverlap ProjSpace.pullbackOverlap_eq_inf ProjSpace.frameUnit_cocycle ProjSpace.frameUnit_self Scheme.Modules.IsFrameOn.nonempty_pullback_iso_unit"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π irrelevant_le_span_X ratio map pullbackChart frameUnit restrictFun restrictFun_restrictFun pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self"
namespace PRES
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlueOfCocycle

variable {A : Type u} [CommRing A] {n : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

def U (i : ULift.{u} (Fin (n + 1))) : X.Opens := ProjSpace.pullbackChart φ i.down

def fu (i j : ULift.{u} (Fin (n + 1))) : Γ(X, U φ i) := ProjSpace.frameUnit φ i.down j.down

theorem fu_self (i : ULift.{u} (Fin (n + 1))) : fu φ i i = 1 := ProjSpace.frameUnit_self φ i.down

theorem fu_cocycle (i j k : ULift.{u} (Fin (n + 1))) {W : X.Opens} (hi : W ≤ U φ i) (hj : W ≤ U φ j) :
    rO hi (fu φ i j) * rO hj (fu φ j k) = rO hi (fu φ i k) := by
  have hW : W ≤ ProjSpace.pullbackOverlap φ i.down j.down := by
    rw [ProjSpace.pullbackOverlap_eq_inf]; exact le_inf hi hj
  have key := congrArg (ProjSpace.restrictFun hW) (ProjSpace.frameUnit_cocycle φ i.down j.down k.down)
  rw [map_mul, ProjSpace.restrictFun_restrictFun, ProjSpace.restrictFun_restrictFun,
    ProjSpace.restrictFun_restrictFun] at key
  exact key

def cocycle : UnitCocycle (U φ) where
  u i j := rO inf_le_left (fu φ i j)
  refl i := by rw [fu_self, map_one]
  cocycle i j k := by
    rw [rO_rO, rO_rO, rO_rO]
    exact fu_cocycle φ i j k _ _

def σ (i : ULift.{u} (Fin (n + 1))) : Γ(glueOfCocycle (cocycle φ), ⊤) :=
  glueMk (cocycle φ) ⊤ (fun k => rO inf_le_right (fu φ k i)) fun k l => by
    show rO _ (rO _ (fu φ k i)) = rO _ (rO _ (fu φ k l)) * rO _ (rO _ (fu φ l i))
    rw [rO_rO, rO_rO, rO_rO]
    exact (fu_cocycle φ k l i _ _).symm

theorem map_σ (i : ULift.{u} (Fin (n + 1))) :
    (glueOfCocycle (cocycle φ)).presheaf.map (homOfLE (le_top : U φ i ≤ ⊤)).op (σ φ i) = glueFrame (cocycle φ) i := by
  apply glue_ext
  intro k
  rw [glueComponent_map, glueComponent_glueFrame]
  show rO _ (rO _ (fu φ k i)) = rO _ (rO _ (fu φ k i))
  rw [rO_rO, rO_rO]

theorem map_σ_of_le (i : ULift.{u} (Fin (n + 1))) {V : X.Opens} (hV : V ≤ U φ i) :
    (glueOfCocycle (cocycle φ)).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ φ i) =
      (glueOfCocycle (cocycle φ)).presheaf.map (homOfLE hV).op (glueFrame (cocycle φ) i) := by
  rw [← map_σ φ i, ← CategoryTheory.comp_apply, ← (glueOfCocycle (cocycle φ)).presheaf.map_comp]
  rfl

theorem fu_smul_map_σ (i j : ULift.{u} (Fin (n + 1))) :
    fu φ i j • (glueOfCocycle (cocycle φ)).presheaf.map (homOfLE (le_top : U φ i ≤ ⊤)).op (σ φ i) =
      (glueOfCocycle (cocycle φ)).presheaf.map (homOfLE (le_top : U φ i ≤ ⊤)).op (σ φ j) := by
  rw [map_σ]
  apply glue_ext
  intro k
  rw [glueComponent_smul, glueComponent_glueFrame, glueComponent_map]
  show rO _ (fu φ i j) * rO _ (rO _ (fu φ k i)) = rO _ (rO _ (fu φ k j))
  rw [rO_rO, rO_rO, mul_comm]
  exact fu_cocycle φ k i j _ _

theorem exists_mem_U (x : X) : ∃ i, x ∈ U φ i := by
  have h := Proj.iSup_basicOpen_eq_top 𝒜 (fun j : Fin (n + 1) => MvPolynomial.X j) (ProjSpace.irrelevant_le_span_X A n)
  have hx : φ.base x ∈ (⨆ j : Fin (n + 1), Proj.basicOpen 𝒜 (MvPolynomial.X j)) := by rw [h]; trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
  exact ⟨⟨j⟩, hj⟩

def pres : (glueOfCocycle (cocycle φ)).ProjPresentation (φ ≫ ProjSpace.π A n) n where
  σ i := σ φ ⟨i⟩
  toProj := φ
  toProj_π := rfl
  frame i V hV := by
    rw [map_σ_of_le φ ⟨i⟩ hV]
    exact isFrameOn_glueFrame (cocycle φ) ⟨i⟩ hV hV
  app_ratio_smul i j := fu_smul_map_σ φ ⟨i⟩ ⟨j⟩

end AlgebraicGeometry.ProjSpace.PRES

end

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial.AlgebraicGeometry MvPolynomial"
attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {A : Type u} [CommRing A] {n : ℕ} {X : Scheme.{u}}
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) :
    ∃ (L : X.Modules) (𝔓 : L.ProjPresentation (φ ≫ ProjSpace.π A n) n), 𝔓.toProj = φ ∧
      ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) := by
  refine ⟨AlgebraicGeometry.Scheme.Modules.glueOfCocycle (AlgebraicGeometry.ProjSpace.PRES.cocycle φ),
    AlgebraicGeometry.ProjSpace.PRES.pres φ, rfl, fun x => ?_⟩
  obtain ⟨i, hi⟩ := AlgebraicGeometry.ProjSpace.PRES.exists_mem_U φ x
  exact ⟨AlgebraicGeometry.ProjSpace.PRES.U φ i, hi,
    AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_pullback_iso_unit
      (AlgebraicGeometry.Scheme.Modules.isFrameOn_glueFrame (AlgebraicGeometry.ProjSpace.PRES.cocycle φ) i)
      (AlgebraicGeometry.ProjSpace.PRES.U φ i) le_rfl le_rfl⟩

end S_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial (solution)
