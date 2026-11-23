-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily
-- name    : Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:57.360843+00:00
-- url     : https://prove2.me/theorems/90304a62-6050-4192-b15a-cf35fae57165
-- title:
--   Not Admissible Half Lattice Family
-- statement:
--   Definitions and structural lemmas for Not Admissible Half Lattice Family, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/NotAdmissibleHalfLatticeFamily.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
namespace GlobalTheory.SW.Model
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open Classical in

def indFam (E : Type) [Field E] [NumberField E] (n N : ℕ) : Fam E n N := fun Λ x =>
  if ColsIn Λ x then 1 else 0
open Classical in

def divFam (E : Type) [Field E] [NumberField E] (n N R : ℕ) : Fam E n N := fun Λ x =>
  if ColsIn Λ ((R : E) • x) then 1 else 0
end
end GlobalTheory.SW.Model


