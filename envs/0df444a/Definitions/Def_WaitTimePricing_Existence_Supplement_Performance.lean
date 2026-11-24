-- Prove2me | Definitions.Def_WaitTimePricing_Existence_Supplement_Performance
-- name    : WaitTimePricing_Existence_Supplement_Performance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:39:10.576256+00:00
-- url     : https://prove2.me/theorems/c5491850-e26a-42eb-980e-72252b9f139a
-- title:
--   Actual arrival rewards and the expected average objective
-- statement:
--   An arrival facing workload $w\in[0,\bar w]$ generates $v(p)-\alpha c(w)$ if $p\le\Gamma(w)$, and zero otherwise. Above $\bar w$ it generates zero. Sum these actual rewards over the finitely many arrivals through time $T$ to obtain $R_T(p)$. Define
--   $$G(p)=\liminf_{T\to\infty}\frac{\mathbb E[R_T(p)]}{T},\qquad g^*=\sup_{p\in\Pi}G(p).$$
--   Here $\Pi$ contains every admissible predictable process. The liminf remains outside the expectation. This objective is defined without reference to $g$, $V$, or any alleged optimal policy.
--
--   **Formalization Note** Real integrals, liminf and supremum are used. Integrability and finite bounds for the concrete rewards, nonempty competitors and boundedness of attainable averages are explicit conclusions of Theorem 2. The admission indicator of (10) is retained despite its omission from Appendix C's displayed formulas.
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), pp. 10–11, (10)

import Mathlib
import Mathlib.Probability.Process.Predictable
import Definitions.Def_WaitTimePricing_Existence_Supplement_Control

set_option autoImplicit false

namespace WaitTimePricing.Existence.Supplement
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 10, (10).

Actual reward in (10), pp. 10–11: balking arrivals contribute zero, including w>wbar.
Formalization Note: retains the admission indicator omitted from some Appendix C displays.
It never evaluates Gamma on states outside [0,wbar]. -/
def arrivalReward (M : Model) (R : Reward) (p w : ℝ) : ℝ :=
  if w ∈ Icc 0 (wbar M) then
    if p ≤ Gamma M w then R.value p - R.weight * M.c w else 0
  else 0

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 10, (10).

The counting-measure integral over [0,T] in (10), as a finite sum over all arrivals.
This definition is independent of the DDE, its value, and any policy being optimal. -/
def totalReward (M : Model) (R : Reward) (A : Arrivals Ω) (p : PriceProcess Ω)
    (T : ℝ) (ω : Ω) : ℝ :=
  ∑ n ∈ Finset.range (arrivalCount A.epoch (Real.toNNReal T) ω),
    arrivalReward M R (p (A.epoch n ω) ω) (preWork M A p (A.epoch n ω) ω)

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 10, (10).

Finite-horizon expected average in (10), p. 10. Formalization Note: used only at T>0;
integrability is concluded in the concrete optimality theorem, not assumed of competitors. -/
def average (M : Model) (R : Reward) (A : Arrivals Ω) (p : PriceProcess Ω) (T : ℝ) : ℝ :=
  (∫ ω, totalReward M R A p T ω ∂A.law) / T

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 10, (10).

G is the liminf of expected averages, with the liminf outside expectation, (10), p. 10.
Formalization Note: real liminf is protected by the theorem's uniform finite-horizon bounds. -/
def G (M : Model) (R : Reward) (A : Arrivals Ω) (p : PriceProcess Ω) : ℝ :=
  liminf (average M R A p) atTop

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 10, (10).

The supremum over every admissible predictable process, (10), p. 10.
Formalization Note: boundedness and nonemptiness of this real supremum are conclusions. -/
def gStar (M : Model) (R : Reward) (A : Arrivals Ω) : ℝ :=
  sSup (G M R A '' {p | Admissible M A p})

end
end WaitTimePricing.Existence.Supplement


