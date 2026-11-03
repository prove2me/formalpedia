-- Prove2me | Definitions.Def_levy_foundations_increment
-- name    : levy_foundations_increment
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T10:30:58.280672+00:00
-- url     : https://prove2.me/theorems/9e5a5a6c-bd40-4690-8ea0-0f5e9d717e17
-- title:
--   Increment of a process in a type with subtraction
-- statement:
--   For any index type ι, sample space Ω and state type E with subtraction, the increment of X : ι → Ω → E from s to t at sample ω is X(t, ω) minus X(s, ω). Nonnegative-time, real-valued processes are a special case.
-- source:
--   Adapted from Shmuel Link, LeanLevy (MIT), frozen commit 7e73fd9b23ad52956ec2756a815889a783131ce4, https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/StochasticProcess.lean#L40-L49. Generic time and state-space subtraction; private Prove2Me draft awaiting remote Lean compilation.

import Mathlib.MeasureTheory.Group.Arithmetic
open scoped NNReal

namespace LevyFoundations
/-- Difference of process observations at two arbitrary indices. -/
def increment {ι Ω E : Type*} [Sub E] (X : ι → Ω → E)
    (s t : ι) (ω : Ω) : E := X t ω - X s ω
end LevyFoundations


