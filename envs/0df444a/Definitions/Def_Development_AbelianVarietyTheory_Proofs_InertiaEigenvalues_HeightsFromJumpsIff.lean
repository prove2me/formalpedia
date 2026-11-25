-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HeightsFromJumpsIff
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HeightsFromJumpsIff
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T02:03:41.378985+00:00
-- url     : https://prove2.me/theorems/08483010-0c4f-57ea-ab5a-1056fd569d40
-- title:
--   Heights From Jumps Iff
-- statement:
--   Definitions and structural lemmas for Heights From Jumps Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeightsFromJumpsIff.lean

import Mathlib
import Definitions.Def_Formalism_CoboundaryTransfers_Statement
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_PointRingCommRing
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_LocalRingStructure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeightsFromJumpsCompare
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.IndefiniteRowSideFullHecke
section Generic
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
variable {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
end Generic
end GlobalTheory.HeightsFromJumpsCompare


