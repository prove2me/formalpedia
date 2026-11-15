-- Prove2me | Definitions.Def_Kyprianou_Ch03_IsSubordinator
-- name    : Kyprianou_Ch03_IsSubordinator
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-14T13:35:58.511976+00:00
-- url     : https://prove2.me/theorems/fb2b4b83-d51d-49f9-8372-d70dee1ff184
-- title:
--   Subordinators as increasing Levy processes
-- statement:
--   A real-valued Levy process with almost surely nondecreasing sample paths. Together with a separate infinity state this supports killed subordinators without replacing death by zero.
-- source:
--   Kyprianou (2006), Chapter 3, discussion preceding Corollary 3.14, printed p. 82.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace Kyprianou.Ch03
/-- A Levy process with almost-surely nondecreasing sample paths. -/
def IsSubordinator
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (S : NNReal -> Omega -> Real) : Prop :=
  ProbabilityTheory.IsLevyProcess S P ∧
    (∀ᵐ omega : Omega ∂ P,
      Monotone (fun t : NNReal => S t omega))
end Kyprianou.Ch03


