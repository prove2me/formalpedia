-- Prove2me | Definitions.Def_LX_EventTrace
-- name    : LX_EventTrace
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:07:52.07187+00:00
-- url     : https://prove2.me/theorems/10e77a76-91c6-4c0f-bce0-d5ec7621af30
-- title:
--   Exchange event lists and repeated events
-- statement:
--   For a word acting on a lifted configuration on a positive cycle, record the current normalized pair key at each exchange and update the configuration after every letter. Rotation letters contribute no event entry. The repeated event predicate requires a decomposition into a prefix, an exchange, an intervening word, another exchange, and a suffix, with equal keys at the two exchange moments. The intervening word may be empty. This definition records repetition of lifted event data with the actual intermediate execution states.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/EventTrace.lean#L8-L43

/-
Adapted from https://github.com/snow-ghost/glushkov-lx-lean at 8cddcd222b591673dc63475d9d45b9ed5c6eb92c.
MIT License

Copyright (c) 2026 S. Uskov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

-/
import Mathlib
import Definitions.Def_LX_AffineCrossings
import Definitions.Def_LX_AffineLift
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_LiftedPair
import Definitions.Def_LX_LiftedRename
import Definitions.Def_LX_PairEvents
import Definitions.Def_LX_PhysicalModel

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace List
end List

/-! Exact event traces and detection of repeated lifted pairs in a literal word. -/
namespace LX.Core.LiftedModel
variable {n : ℕ} [NeZero n]

def events : List Letter → Configuration n → List (PairKey n)
  | [], _ => []
  | .x::w, s => eventKey s :: events w (step .x s)
  | .l::w, s => events w (step .l s)
  | .r::w, s => events w (step .r s)





def RepeatedEvents (w : List Letter) (s : Configuration n) : Prop :=
  ∃ u middle v, w=u++[.x]++middle++[.x]++v ∧
    eventKey (run u s)=eventKey (run middle (step .x (run u s)))





end LX.Core.LiftedModel


