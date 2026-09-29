-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_unitCocycle_map_eq_smul_of_isFrameOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/87e35bef-173a-541e-a4d2-b4b631fdc84c

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_unitCocycle_map_eq_smul_of_isFrameOn

set_option autoImplicit false

p2m_open "CategoryTheory Opposite TopologicalSpace CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_unitCocycle_map_eq_smul_of_isFrameOn.AlgebraicGeometry"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme Scheme.Modules Scheme.Modules.map_smul Scheme.Modules.IsFrameOn Scheme.Modules.UnitCocycle"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Γ Modules Opens Modules.map_smul restrict Modules.IsFrameOn Modules.UnitCocycle"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "presheaf restrict map_smul IsFrameOn UnitCocycle"
namespace RatioCocycle
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.Modules.GlueOfCocycle"

variable {X : Scheme.{u}} {M : X.Modules}

theorem map_smul' {A B : X.Opens} (h : B ≤ A) (r : Γ(X, A)) (m : Γ(M, A)) :
    M.presheaf.map (homOfLE h).op (r • m) = X.presheaf.map (homOfLE h).op r • M.presheaf.map (homOfLE h).op m :=
  Scheme.Modules.map_smul M _ r m

theorem map_map {A B C : X.Opens} (hBA : B ≤ A) (hCB : C ≤ B) (m : Γ(M, A)) :
    M.presheaf.map (homOfLE hCB).op (M.presheaf.map (homOfLE hBA).op m) = M.presheaf.map (homOfLE (hCB.trans hBA)).op m := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]; rfl

end AlgebraicGeometry.Scheme.Modules.RatioCocycle

open AlgebraicGeometry.Scheme.Modules.RatioCocycle AlgebraicGeometry.Scheme.Modules.GlueOfCocycle in
theorem solution
    {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens}
    {M : X.Modules} (e : ∀ i, Γ(M, U i)) (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (U i)) :
    ∃ c : Scheme.Modules.UnitCocycle U, ∀ i j,
      M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (e j) =
        c.u i j • M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (e i) := by
  classical

  have hcoef : ∀ i j, ∃! u : Γ(X, U i ⊓ U j),
      u • M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (e i) =
        M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (e j) :=
    fun i j => (he i).existsUnique inf_le_left inf_le_left _
  choose u hu huniq using hcoef

  have hcoefW : ∀ (i : ι) {W : X.Opens} (hW : W ≤ U i) (a b : Γ(X, W)),
      a • M.presheaf.map (homOfLE hW).op (e i) = b • M.presheaf.map (homOfLE hW).op (e i) → a = b :=
    fun i W hW a b h => ((he i) hW hW).1 h
  refine ⟨⟨u, fun i => ?_, fun i j k => ?_⟩, fun i j => (hu i j).symm⟩
  ·
    apply hcoefW i inf_le_left
    rw [hu i i, one_smul]
  ·
    let T : X.Opens := U i ⊓ U j ⊓ U k
    have hTi : T ≤ U i := inf_le_left.trans inf_le_left
    have hTij : T ≤ U i ⊓ U j := le_inf hTi (inf_le_left.trans inf_le_right)
    have hTjk : T ≤ U j ⊓ U k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have hTik : T ≤ U i ⊓ U k := le_inf hTi inf_le_right
    apply hcoefW i hTi

    have hij := congrArg (M.presheaf.map (homOfLE hTij).op) (hu i j)
    have hjk := congrArg (M.presheaf.map (homOfLE hTjk).op) (hu j k)
    have hik := congrArg (M.presheaf.map (homOfLE hTik).op) (hu i k)
    rw [map_smul', map_map, map_map] at hij hjk hik
    show (rO hTij (u i j) * rO hTjk (u j k)) • _ = rO hTik (u i k) • _
    rw [mul_comm, mul_smul]
    erw [hij, hjk, hik]

end S_AlgebraicGeometry_Scheme_Modules_exists_unitCocycle_map_eq_smul_of_isFrameOn
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_unitCocycle_map_eq_smul_of_isFrameOn (solution)
