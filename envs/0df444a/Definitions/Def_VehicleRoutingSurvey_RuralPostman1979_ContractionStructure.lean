-- Prove2me | Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_ContractionStructure
-- name    : VehicleRoutingSurvey_RuralPostman1979_ContractionStructure
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-21T16:11:39.413508+00:00
-- url     : https://prove2.me/theorems/a17ea5e7-4cf5-4cd4-82fa-fdc17be30af8
-- title:
--   Rural postman algorithm — contraction cycle read interface
-- statement:
--   The cycle reader layout and indexing functions specify the data needed to emit an archived contraction cycle.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_MatcherProofInterfaces

/-! matching/MatchingCycleRecordRAM.lean -/
section RppSource_MatchingCycleRecordRAM
namespace VehicleRoutingSurvey.Routing

















def matchingCycleChildCount (s : ArithmeticState) : ℕ := s.nr 13 + s.nr 14 + 1



def startMatchingCycleNat (s : ArithmeticState) : ℕ → ℕ :=
  Function.update (Function.update s.nm (s.nr 77 + s.nr 76) (s.nr 68))
    (s.nr 78 + s.nr 76) (matchingCycleChildCount s)



















end VehicleRoutingSurvey.Routing
end RppSource_MatchingCycleRecordRAM

/-! matching/MatchingCycleSequence.lean -/
section RppSource_MatchingCycleSequence
namespace VehicleRoutingSurvey.Routing



def leftCycleRepresentativeAt (s : ArithmeticState) (i : ℕ) : ℕ := s.nm (s.nr 83 + i)

def rightCycleRepresentativeAt (s : ArithmeticState) (i : ℕ) : ℕ := s.nm (s.nr 84 + i)

def leftCycleRecordAt (s : ArithmeticState) (i : ℕ) : MatchingCycleChild :=
  let v := leftCycleRepresentativeAt s i
  let e := matchingForestWitnessAt s.nm (s.nr 90) v
  ⟨v, s.nm (s.nr 74 + v), e.2, e.1⟩

def commonCycleRecord (s : ArithmeticState) : MatchingCycleChild :=
  let v := s.nr 12
  let e := if s.nr 14 = 0 then (s.nr 93, s.nr 92)
    else matchingForestWitnessAt s.nm (s.nr 90) (rightCycleRepresentativeAt s (s.nr 14 - 1))
  ⟨v, s.nm (s.nr 74 + v), e.1, e.2⟩

def rightCycleRecordAt (s : ArithmeticState) (i : ℕ) : MatchingCycleChild :=
  let backwards := s.nr 14 - (i + 1)
  let v := rightCycleRepresentativeAt s backwards
  let e := if backwards = 0 then (s.nr 93, s.nr 92)
    else matchingForestWitnessAt s.nm (s.nr 90) (rightCycleRepresentativeAt s (backwards - 1))
  ⟨v, s.nm (s.nr 74 + v), e.1, e.2⟩



















structure MatchingCycleReadSafety (s : ArithmeticState) : Prop where
  left : s.nr 83 + s.nr 13 ≤ s.nr 68
  right : s.nr 84 + s.nr 14 ≤ s.nr 68
  node : s.nr 74 + s.nr 55 ≤ s.nr 68
  witnesses : s.nr 90 + 2 * s.nr 55 ≤ s.nr 68
  leftValid : ∀ j < s.nr 13, leftCycleRepresentativeAt s j < s.nr 55
  rightValid : ∀ j < s.nr 14, rightCycleRepresentativeAt s j < s.nr 55
  baseValid : s.nr 12 < s.nr 55

















def matchingCycleRecordReference (s : ArithmeticState) : ArithmeticState :=
  {s with nm := startMatchingCycleNat s}







end VehicleRoutingSurvey.Routing
end RppSource_MatchingCycleSequence


