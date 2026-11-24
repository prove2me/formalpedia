-- Prove2me | Definitions.Def_WaitTimePricing_Existence_Supplement_Control
-- name    : WaitTimePricing_Existence_Supplement_Control
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:38:32.171561+00:00
-- url     : https://prove2.me/theorems/4c37ed8c-3580-49cb-8071-8ae7a82d214a
-- title:
--   Predictable pricing and operational workload recursion
-- statement:
--   Every admissible price process is predictable for the natural arrival history and takes values in $[0,U'(0)]$. Starting from an empty system, compute the workload after each arrival by
--   $$z_0=t(p_{A_0},0),\qquad b_{n+1}=\max\{z_n-(A_{n+1}-A_n),0\},\qquad z_{n+1}=b_{n+1}+t(p_{A_{n+1}},b_{n+1}).$$
--   At an arbitrary time, the strictly earlier arrivals determine the previous postarrival workload, which drains at unit rate until that time. This implements (9), including balking and no abandonment.
--
--   A separate recursion implements any stationary feedback rule and then produces its price process. It assumes no optimality or admissibility of that feedback; those are theorem conclusions. All predictable competitors remain available, including policies depending on the entire arrival history.
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), pp. 9–10, (9), and p. 18, (26)

import Mathlib
import Mathlib.Probability.Process.Predictable
import Definitions.Def_WaitTimePricing_Existence_Supplement_Arrivals
import Definitions.Def_WaitTimePricing_Existence_Supplement_Rewards

set_option autoImplicit false
open scoped NNReal

namespace WaitTimePricing.Existence.Supplement
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
variable {Ω : Type*} [MeasurableSpace Ω]

/-- All policies Π of §3.2, pp. 9–10, not just stationary controls.
Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times,
SSRN 3709573 (version of October 12, 2020), (9)–(10).
Formalization Note: predictability uses Mathlib's predictable sigma algebra for the exact
natural arrival filtration; the queue is computed by recursion, not assumed to satisfy a reward identity. -/
def Admissible (M : Model) (A : Arrivals Ω) (p : PriceProcess Ω) : Prop :=
  IsStronglyPredictable A.history p ∧
  ∀ s ω, p s ω ∈ Icc 0 (deriv M.U 0)

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 10, (9); p. 18, (26).

Postarrival workload from (9), starting from w_{0-}=0, p. 10.
Each step first drains the old workload, then adds the actually chosen service of (6). -/
def postWork (M : Model) (A : Arrivals Ω) (p : PriceProcess Ω) (ω : Ω) : ℕ → ℝ
  | 0 => tJoin M (p (A.epoch 0 ω) ω) 0
  | n + 1 =>
    let w := max (postWork M A p ω n - ((A.epoch (n + 1) ω : ℝ) - A.epoch n ω)) 0
    w + tJoin M (p (A.epoch (n + 1) ω) ω) w

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 10, (9); p. 18, (26).

Strictly prearrival workload at every time, including arrival epochs. The finite index
is the number of strictly earlier arrivals; the empty history gives workload zero.
Lin, Shang, Sun, SSRN 3709573 (version of October 12, 2020), pp. 9–10, (9).
Formalization Note: positive strictly ordered nonexplosive epochs make every count finite. -/
def preFromPost (A : Arrivals Ω) (z : Ω → ℕ → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  let k := {n : ℕ | A.epoch n ω < s}.ncard
  if k = 0 then 0 else max (z ω (k - 1) - ((s : ℝ) - A.epoch (k - 1) ω)) 0

def preWork (M : Model) (A : Arrivals Ω) (p : PriceProcess Ω) : ℝ≥0 → Ω → ℝ :=
  preFromPost A (postWork M A p)

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 10, (9); p. 18, (26).

Operational recursion for a stationary rule F, resolving the feedback/dynamics recursion
before defining the process. No optimality, measurability or attainment is built into this object.
Lin, Shang, Sun, SSRN 3709573 (version of October 12, 2020), p. 18, (26) with (9). -/
def rulePost (M : Model) (A : Arrivals Ω) (F : ℝ → ℝ) (ω : Ω) : ℕ → ℝ
  | 0 => tJoin M (F 0) 0
  | n + 1 =>
    let w := max (rulePost M A F ω n - ((A.epoch (n + 1) ω : ℝ) - A.epoch n ω)) 0
    w + tJoin M (F w) w

def ruleProcess (M : Model) (A : Arrivals Ω) (F : ℝ → ℝ) : PriceProcess Ω :=
  fun s ω => F (preFromPost A (rulePost M A F) s ω)


end
end WaitTimePricing.Existence.Supplement


