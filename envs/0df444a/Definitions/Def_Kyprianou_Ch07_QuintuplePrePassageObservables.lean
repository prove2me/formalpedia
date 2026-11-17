-- Prove2me | Definitions.Def_Kyprianou_Ch07_QuintuplePrePassageObservables
-- name    : Kyprianou_Ch07_QuintuplePrePassageObservables
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T15:00:40.644506+00:00
-- url     : https://prove2.me/theorems/f506f752-b0bb-409e-b76e-d9d249cecb6d
-- title:
--   Theorem 7.7: strict pre-passage running maximum and its last contact
-- statement:
--   At the first strictly positive upcrossing of level x, define the running supremum immediately before the crossing from values X_t with t<τ⁺_x and the last time prior to τ⁺_x when X_t equals the then-running maximum. These are the original left-limit supremum and last-supremum epoch in the quintuple law, avoiding contamination by the upward crossing jump itself.
-- source:
--   Kyprianou (2006), Theorem 7.7 and Figure 7.1, printed p.191, original PDF physical p.200, Windows Ky.pdf sheet 101.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch06_RunningMaximumAndContact
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Running maximum strictly before the original first strict upcrossing. -/
noncomputable def maximumBeforeUpcrossing
    {Omega : Type}
    (X : NNReal → Omega → Real)
    (x : Real) (omega : Omega) : Real :=
  let tau := Kyprianou.Ch05.passageFiniteTime
      X (fun _ => (⊤ : WithTop NNReal)) x omega
  sSup {h : Real | ∃ t : NNReal, t < tau ∧ h = X t omega}

/-- The last pre-upcrossing time at which X equals its running maximum. -/
noncomputable def lastMaximumContactBeforeUpcrossing
    {Omega : Type}
    (X : NNReal → Omega → Real)
    (x : Real) (omega : Omega) : NNReal :=
  let tau := Kyprianou.Ch05.passageFiniteTime
      X (fun _ => (⊤ : WithTop NNReal)) x omega
  sSup {t : NNReal | t < tau ∧
    X t omega = Kyprianou.Ch06.runningMaximum X t omega}

end Kyprianou.Ch07


