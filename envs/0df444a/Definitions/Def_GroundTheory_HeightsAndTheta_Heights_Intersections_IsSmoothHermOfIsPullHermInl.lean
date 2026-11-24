-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermOfIsPullHermInl
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermOfIsPullHermInl
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:26:39.114454+00:00
-- url     : https://prove2.me/theorems/c0f3bd6d-8000-47bb-9e43-49a7c9238a88
-- title:
--   Is Smooth Herm Of Is Pull Herm Inl
-- statement:
--   Definitions and structural lemmas for Is Smooth Herm Of Is Pull Herm Inl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothHermOfIsPullHermInl.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermTensor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
section Patch
abbrev Amb : Type 1 := Σ (K : Type) (_ : Fintype K) (ι : K → Type), ∀ k, Fintype (ι k)
abbrev AmbFam (a : Amb) : Type :=
  letI := a.2.1; letI := a.2.2.2
  Ideal (MRing a.2.2.1) → (n : ℕ) → (Fin n → HermLine a.2.2.1) → ℝ
def AmbIsFam (a : Amb) (F : AmbFam a) : Prop :=
  letI := a.2.1; letI := a.2.2.2
  IsIntersectionFamily (ι := a.2.2.1) F
open Classical in

def patchFam (J : AllFam) (a : Amb) (F : AmbFam a) : AllFam :=
  fun K _ ι _ => if h : (⟨K, ‹_›, ι, ‹_›⟩ : Amb) = a then cast (congrArg AmbFam h.symm) F else J K ι
end Patch
section Lemmas
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
end Lemmas
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
namespace GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
end GroundTheory.Heights₂.Heights.Inter


