-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaMatchingExistsRightTorusTorsion
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaMatchingExistsRightTorusTorsion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:44.199844+00:00
-- url     : https://prove2.me/theorems/289d6b3c-725e-4d0c-94be-d73a358a6373
-- title:
--   Theta Matching Exists Right Torus Torsion
-- statement:
--   Definitions and structural lemmas for Theta Matching Exists Right Torus Torsion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaMatchingExistsRightTorusTorsion.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TendstoTsumZeroOfEventuallyNotMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueAddEquivOfCompatibleCongr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex Module Filter
open scoped BigOperators Topology
namespace GlobalTheory.MatchTerm
section
variable {K X X' : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X']
end
section
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ} (μ : Match N N' n)
def Cl (j : ℕ) (x : N.X) (x' : N'.X) : Prop :=
  ∃ p p', μ.r (n ^ j) p p' ∧ p.1.1.toAdd = x ∧ p'.1.1.toAdd = x'
end
end GlobalTheory.MatchTerm


