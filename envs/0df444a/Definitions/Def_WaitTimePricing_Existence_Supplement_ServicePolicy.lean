-- Prove2me | Definitions.Def_WaitTimePricing_Existence_Supplement_ServicePolicy
-- name    : WaitTimePricing_Existence_Supplement_ServicePolicy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:39:46.315188+00:00
-- url     : https://prove2.me/theorems/929b23bc-5678-479e-a18e-f2990e9aad14
-- title:
--   Service-time policy and the entire five-section predicate
-- statement:
--   For either concrete objective set $f(t,w)=v(U'(t))-\alpha c(w)$ and $\hat\xi(t,w)=f(t,w)+V(w+t)-V(w)$, where $V$ is the published constructed value function. The candidate $t^*(w)$ is selected from the argmax on $[L(w),C]$. For $w\in[0,\hat w]$, choose $T^*=t^*$ if $\hat\xi\ge0$, and zero otherwise, then $P^*=U'(T^*)$. For $\hat w<w\le\bar w$, put $q=(U(C)-c(w))/C$; choose $P^*=q$ if $v(q)-\alpha c(w)+V(w+C)-V(w)\ge0$, and $U'(0)$ otherwise, and set $T^*=t(P^*,w)$.
--
--   The `FiveSections` predicate contains the full printed conclusion: equality with greatest-price feedback, all ordered existential thresholds, and all five service and five price clauses. Monotonicity is weak on the actual half-open intervals, and the final interval is closed. It is a predicate to test, not an assumption that it holds. At $w=\hat w$ the definitions preserve (35)–(36), and equality in each acceptance test admits.
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), pp. 20–21, (35)–(39) and Theorem 3

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Supplement_Rewards
import Definitions.Def_WaitTimePricing_Existence_Algorithm1

set_option autoImplicit false

namespace WaitTimePricing.Existence.Supplement
noncomputable section
open Set

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times,
SSRN 3709573 (version of October 12, 2020), p. 20, f(t,w). -/
def f (M : Model) (obj : Objective) (t w : ℝ) : ℝ :=
  v M obj (deriv M.U t) - alpha obj * M.c w

def xiHat (M : Model) (obj : Objective) (t w : ℝ) : ℝ :=
  f M obj t w + Vbar M obj (w + t) - Vbar M obj w

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 20, (35)–(36); p. 21, (37)–(39) and Theorem 3.

The unique service maximizer of (35), p. 20, is encoded as the supremum of its argmax.
Formalization Note: no uniqueness or existence is assumed; they are checked in theorem_3's
counterexample as well as being mathematical obligations of the concrete optimization. -/
def serviceArgmax (M : Model) (obj : Objective) (w : ℝ) : Set ℝ :=
  {t ∈ Icc (Lw M w) M.C | ∀ u ∈ Icc (Lw M w) M.C, xiHat M obj u w ≤ xiHat M obj t w}

def tStar (M : Model) (obj : Objective) (w : ℝ) : ℝ := sSup (serviceArgmax M obj w)

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 20, (35)–(36); p. 21, (37)–(39) and Theorem 3.

Feasible price in (37)–(38), p. 21. Used only for what<w≤wbar, so C>0. -/
def qPrice (M : Model) (w : ℝ) : ℝ := (M.U M.C - M.c w) / M.C

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 20, (35)–(36); p. 21, (37)–(39) and Theorem 3.

Exactly (35)–(38), pp. 20–21, including the source's assignment w=what to (35),(36).
Formalization Note: equality of the acceptance test to zero admits; outside [0,wbar] rejects. -/
def PStar (M : Model) (obj : Objective) (w : ℝ) : ℝ :=
  if w ∈ Icc 0 (wbar M) then
    if w ≤ what M then
      deriv M.U (if 0 ≤ xiHat M obj (tStar M obj w) w then tStar M obj w else 0)
    else
      if 0 ≤ v M obj (qPrice M w) - alpha obj * M.c w +
          Vbar M obj (w + M.C) - Vbar M obj w then qPrice M w else deriv M.U 0
  else deriv M.U 0

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 20, (35)–(36); p. 21, (37)–(39) and Theorem 3.

Exactly (35),(39), pp. 20–21. Formalization Note: at w=what use (35), not (39). -/
def TStar (M : Model) (obj : Objective) (w : ℝ) : ℝ :=
  if w ∈ Icc 0 (wbar M) then
    if w ≤ what M then
      if 0 ≤ xiHat M obj (tStar M obj w) w then tStar M obj w else 0
    else tJoin M (PStar M obj w) w
  else 0

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 20, (35)–(36); p. 21, (37)–(39) and Theorem 3.

The entire printed Theorem 3 conclusion, p. 21: equality of policies, the threshold ordering,
and all five service and five price clauses. Formalization Note: weak monotonicity on the actual
half-open intervals, allowing coincident thresholds; final rejection interval is closed. -/
def FiveSections (M : Model) (obj : Objective) : Prop :=
  (∀ w ∈ Icc 0 (wbar M), PStar M obj w =
    feedback M (concreteReward M obj) (Vbar M obj) w) ∧
  ∃ W1 W2 W3 : ℝ,
    0 ≤ W1 ∧ W1 ≤ W2 ∧ W2 ≤ what M ∧ what M ≤ W3 ∧ W3 ≤ wbar M ∧
    (∀ w ∈ Ico 0 W1, TStar M obj w = M.C) ∧
    AntitoneOn (TStar M obj) (Ico W1 W2) ∧
    (∀ w ∈ Ico W2 (what M), TStar M obj w = Lw M w) ∧
    MonotoneOn (TStar M obj) (Ico W2 (what M)) ∧
    (∀ w ∈ Ico (what M) W3, TStar M obj w = M.C) ∧
    (∀ w ∈ Icc W3 (wbar M), TStar M obj w = 0) ∧
    (∀ w ∈ Ico 0 W1, PStar M obj w = deriv M.U M.C) ∧
    MonotoneOn (PStar M obj) (Ico W1 W2) ∧
    AntitoneOn (PStar M obj) (Ico W2 (what M)) ∧
    (∀ w ∈ Ico (what M) W3, PStar M obj w = qPrice M w) ∧
    AntitoneOn (PStar M obj) (Ico (what M) W3) ∧
    (∀ w ∈ Icc W3 (wbar M), PStar M obj w = deriv M.U 0)

end
end WaitTimePricing.Existence.Supplement


