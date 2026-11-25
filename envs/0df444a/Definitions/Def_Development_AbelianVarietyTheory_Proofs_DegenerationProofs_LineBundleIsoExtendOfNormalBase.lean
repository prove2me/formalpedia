-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_LineBundleIsoExtendOfNormalBase
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_LineBundleIsoExtendOfNormalBase
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T13:57:07.173032+00:00
-- url     : https://prove2.me/theorems/bc05e43c-6fe4-48e4-a187-0165add0d5ef
-- title:
--   Line Bundle Iso Extend Of Normal Base
-- statement:
--   Definitions and structural lemmas for Line Bundle Iso Extend Of Normal Base, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/LineBundleIsoExtendOfNormalBase.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueRigidifiedGeneratorExtendNormal
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_div
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.IsoExtend
variable {X Y Y' : Scheme.{0}}
theorem gm_div_pull (L M : LB X) (f : Y ⟶ X) (y : Y) (J J' : PUnit → M.ι × L.ι) (p q : (PUnit → M.ι) × (PUnit → L.ι))
    (ep : J PUnit.unit = (p.1 PUnit.unit, p.2 PUnit.unit)) (eq : J' PUnit.unit = (q.1 PUnit.unit, q.2 PUnit.unit))
    (hJ : y ∈ ((LB.div M L).pull f).U J) (hJ' : y ∈ ((LB.div M L).pull f).U J')
    (hp : y ∈ (M.pull f).U p.1 ⊓ (L.pull f).U p.2) (hq : y ∈ (M.pull f).U q.1 ⊓ (L.pull f).U q.2) :
    gm (𝟙 Y) y (((LB.div M L).pull f).U J ⊓ ((LB.div M L).pull f).U J') (((LB.div M L).pull f).g J J') =
      gm (𝟙 Y) y ((LB.div (M.pull f) (L.pull f)).U p ⊓ (LB.div (M.pull f) (L.pull f)).U q)
        ((LB.div (M.pull f) (L.pull f)).g p q) := by
  refine (gm_pull_g (LB.div M L) f (𝟙 Y) y J J' hJ hJ').trans ?_
  rw [ep, eq]
  refine (gm_div L M (𝟙 Y ≫ f) y (p.1 PUnit.unit, p.2 PUnit.unit) (q.1 PUnit.unit, q.2 PUnit.unit)
    ⟨⟨mem_pull.1 hp.1, mem_pull.1 hp.2⟩, mem_pull.1 hq.1, mem_pull.1 hq.2⟩).trans (Eq.symm ?_)
  refine (gm_div (L.pull f) (M.pull f) (𝟙 Y) y p q ⟨hp, hq⟩).trans ?_
  exact congrArg₂ (· * ·) (gm_pull_g M f (𝟙 Y) y p.1 q.1 hp.1 hq.1)
    (congrArg (·⁻¹) (gm_pull_g L f (𝟙 Y) y p.2 q.2 hp.2 hq.2))
def chartPullDiv (L M : LB X) (f : Y ⟶ X) :
    ChartPull ((LB.div M L).pull f) (LB.div (M.pull f) (L.pull f)) (𝟙 Y) :=
  have le : ∀ (J : PUnit → M.ι × L.ι) (y : Y), y ∈ ((LB.div M L).pull f).U J →
      y ∈ (M.pull f).U (fun _ => (J PUnit.unit).1) ⊓ (L.pull f).U (fun _ => (J PUnit.unit).2) := fun J y hy =>
    have h : f y ∈ M.U (J PUnit.unit).1 ⊓ L.U (J PUnit.unit).2 := (mem_pull (L := LB.div M L) (J := J)).1 hy
    ⟨mem_pull.2 h.1, mem_pull.2 h.2⟩
  { idx := fun J => (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
    le := le
    g := fun y J J' hJ hJ' => gm_div_pull L M f y J J' (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
      (fun _ => (J' PUnit.unit).1, fun _ => (J' PUnit.unit).2) rfl rfl hJ hJ' (le J y hJ) (le J' y hJ') }
def chartDivPull (L M : LB X) (f : Y ⟶ X) :
    ChartPull (LB.div (M.pull f) (L.pull f)) ((LB.div M L).pull f) (𝟙 Y) :=
  have le : ∀ (p : (PUnit → M.ι) × (PUnit → L.ι)) (y : Y), y ∈ (M.pull f).U p.1 ⊓ (L.pull f).U p.2 →
      y ∈ ((LB.div M L).pull f).U (fun _ => (p.1 PUnit.unit, p.2 PUnit.unit)) := fun p y hy =>
    (mem_pull (L := LB.div M L) (J := fun _ => (p.1 PUnit.unit, p.2 PUnit.unit))).2
      ⟨mem_pull.1 hy.1, mem_pull.1 hy.2⟩
  { idx := fun p _ => (p.1 PUnit.unit, p.2 PUnit.unit)
    le := le
    g := fun y p q hp hq => (gm_div_pull L M f y (fun _ => (p.1 PUnit.unit, p.2 PUnit.unit))
      (fun _ => (q.1 PUnit.unit, q.2 PUnit.unit)) p q rfl rfl (le p y hp) (le q y hq) hp hq).symm }
end GlobalTheory.IsoExtend


