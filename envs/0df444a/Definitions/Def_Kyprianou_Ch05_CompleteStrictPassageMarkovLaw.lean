-- Prove2me | Definitions.Def_Kyprianou_Ch05_CompleteStrictPassageMarkovLaw
-- name    : Kyprianou_Ch05_CompleteStrictPassageMarkovLaw
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-26T15:44:13.92469+00:00
-- url     : https://prove2.me/theorems/dcff5ee6-4384-5c2c-b453-a47ddf9b82f8
-- title:
--   Complete-space strict passage stopped-path factor law
-- statement:
--   Uniform stopped-path factorisation at a strict upper passage on complete probability spaces, in the exact Chapter 3 completed natural filtration. This is a proposition, not a proof or axiom.
-- source:
--   Kyprianou (2006), Theorems 3.1 and 3.3; Exercise 5.5(i).

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Complete-space stopped future law for strict passage. -/
def CompleteStrictPassageMarkovLaw : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P] [P.IsComplete]
    (Y : NNReal → Omega → Real)
    (hLevy : ProbabilityTheory.IsLevyProcess Y P)
    (hCoord : ∀ t : NNReal, Measurable (Y t))
    (x : Real) (entranceTime finiteTime : Omega → NNReal)
    (hEntrance : ∀ w, Kyprianou.Ch03.firstEntranceTime Y (Set.Ioi x) w ≠ ⊤ →
      Kyprianou.Ch03.firstEntranceTime Y (Set.Ioi x) w = (entranceTime w : WithTop NNReal))
    (hFinite : ∀ w, Kyprianou.Ch03.firstHittingTime Y (Set.Ioi x) w ≠ ⊤ →
      Kyprianou.Ch03.firstHittingTime Y (Set.Ioi x) w = (finiteTime w : WithTop NNReal)) ,
    ∃ F : Filtration NNReal (inferInstance : MeasurableSpace Omega),
      Kyprianou.Ch03.IsCompletedNaturalFiltration P Y F ∧
      IsStoppingTime F (Kyprianou.Ch03.firstHittingTime Y (Set.Ioi x)) ∧
      ∀ A : Set Omega,
        (∀ s : NNReal, MeasurableSet[F s]
          (A ∩ {w : Omega | Kyprianou.Ch03.firstHittingTime Y (Set.Ioi x) w ≤
            (s : WithTop NNReal)})) →
        Measure.map
          (fun w : Omega => (Set.indicator A (fun _ : Omega => (1 : Real)) w,
            fun u : NNReal => Y (finiteTime w + u) w - Y (finiteTime w) w))
          (P.restrict {w : Omega | Kyprianou.Ch03.firstHittingTime Y (Set.Ioi x) w ≠ ⊤}) =
        (Measure.map (Set.indicator A (fun _ : Omega => (1 : Real)))
          (P.restrict {w : Omega | Kyprianou.Ch03.firstHittingTime Y (Set.Ioi x) w ≠ ⊤})).prod
          (Measure.map (fun w : Omega => fun u : NNReal => Y u w) P)

end Kyprianou.Ch05


