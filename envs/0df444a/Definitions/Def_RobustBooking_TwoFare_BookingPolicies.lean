-- Prove2me | Definitions.Def_RobustBooking_TwoFare_BookingPolicies
-- name    : RobustBooking_TwoFare_BookingPolicies
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T22:42:56.240828+00:00
-- url     : https://prove2.me/theorems/df0c01f3-8103-4395-8b40-6b46d64751cd
-- title:
--   Nested protection levels, FCFS, partitioned protection levels, and the extreme instances I₁, I₂
-- statement:
--   Three deterministic online policies for the two-fare problem, and two instances.
--
--   - **Nested protection level** with protection level $\theta_1$ (pp. 951–953): a high-fare request is accepted in full while capacity remains; low-fare quantity is accepted only while the total low-fare quantity accepted stays at most the **booking limit** $n - \theta_1$ (and capacity remains). The $\theta_1$ units are protected for the high fare, but high-fare requests may use any remaining capacity.
--   - **First-come, first-served (FCFS)** (p. 955): every request is accepted in full while capacity remains.
--   - **Partitioned protection level (PPL)** with protection level $\theta_1$ (p. 955): high-fare quantity is accepted only up to a total of $\theta_1$, low-fare quantity only up to a total of $\theta_2 = n - \theta_1$; neither class may use the other's bucket.
--
--   **Instances** (p. 953): $I_1$ consists of a low-fare request for quantity $n$ followed by a high-fare request for quantity $n$; $I_2$ consists of a low-fare request for quantity $n$ only.
--
--   **Formalization Note.** Each policy proposes a quantity (for nested and PPL: the class limit minus the quantity of that class already accepted, read off the history) and the run clips it to $[0, \min(q, n - \text{sold})]$. The paper's "$n$ low-fare requests followed by $n$ high-fare requests" is rendered as one request of quantity $n$ per class, which is the continuous problem's sized-request form.
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, p. 951 (nested protection levels), p. 953 (protection level θ₁, instances I₁ and I₂), p. 955 (FCFS and PPL, §1.2)

import Mathlib
import Definitions.Def_RobustBooking_TwoFare_Booking

namespace RobustBooking.TwoFare

/-- Total quantity accepted so far from requests of class `c`, read off the history. -/
noncomputable def acceptedOfClass (c : FareClass) (hist : List (Request × ℝ)) : ℝ :=
  ((hist.filter (fun p => decide (p.1.cls = c))).map Prod.snd).sum

/-- The nested protection-level policy with protection level `θ₁` (pp. 951–953): a high-fare
request is accepted in full while capacity remains; low-fare quantity is accepted only while the
total low-fare quantity accepted stays at most the booking limit `n - θ₁` (and capacity remains).
The run clips each proposal to the remaining capacity and to `[0, qty]`. -/
noncomputable def nested (n θ₁ : ℝ) : DetPolicy := fun hist q =>
  match q.cls with
  | .high => q.qty
  | .low => (n - θ₁) - acceptedOfClass .low hist

/-- First-come, first-served (FCFS, p. 955): accept every request in full while capacity remains. -/
noncomputable def fcfs : DetPolicy := fun _ q => q.qty

/-- The partitioned protection-level policy (PPL, p. 955) with protection level `θ₁`: high-fare
quantity is accepted only up to a total of `θ₁`, low-fare quantity only up to a total of
`θ₂ = n - θ₁`; neither class may use the other's bucket. -/
noncomputable def ppl (n θ₁ : ℝ) : DetPolicy := fun hist q =>
  match q.cls with
  | .high => θ₁ - acceptedOfClass .high hist
  | .low => (n - θ₁) - acceptedOfClass .low hist

/-- Instance `I₁` (p. 953): a low-fare request for quantity `n` followed by a high-fare request for
quantity `n` (the paper's "n low-fare requests followed by n high-fare requests", as sized requests). -/
def instI1 (n : ℝ) (hn : 0 < n) : List Request :=
  [⟨.low, n, hn⟩, ⟨.high, n, hn⟩]

/-- Instance `I₂` (p. 953): a low-fare request for quantity `n` and no high-fare request. -/
def instI2 (n : ℝ) (hn : 0 < n) : List Request :=
  [⟨.low, n, hn⟩]

end RobustBooking.TwoFare


