-- Prove2me | Definitions.Def_SethiChengSS_Finite_Supplement_Calendar
-- name    : SethiChengSS_Finite_Supplement_Calendar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:24:39.466321+00:00
-- url     : https://prove2.me/theorems/836cc7eb-cf01-4503-af63-dbab52b18059
-- title:
--   §5.1 — no-ordering calendar, constrained policies, value and DP (5.1)
-- statement:
--   Let the inventory data, conditional demand densities, surplus dynamics, expected cost $J_n(i,x;U)$ and measurable history-dependent policy class be those of the published finite-horizon model. A deterministic calendar $\mathcal A\subseteq\mathbb N$ specifies the dates on which ordering is allowed. At date $n$, the feasible actions are
--   $$\mathcal U_n=\begin{cases}[0,\infty),&n\in\mathcal A,\\\{0\},&n\notin\mathcal A.\end{cases}$$
--   The calendar value is the infimum of $J_n$ over all policies respecting these action sets. Its separate backward recursion has terminal value $f_N$, and uses the constrained continuation in $z_n(i,y)=c_n^iy+F_{n+1}(v_{n+1})(i,y)$. Equation (5.1) is represented by $h_n=\inf_{y\ge x}[K_n^i\delta(y-x)+z_n(i,y)]$ on allowed dates and $h_n=z_n(i,x)$ otherwise. The feedback rule uses extended thresholds in the published order rule and returns zero on forbidden dates.
--
--   This extends the published model without changing its demands, fixed costs, dynamics or cost functional. All calendar restrictions are imposed on nonanticipative measurable policies, rather than on a class containing only feedback rules.
--
--   **Formalization Note** Periods retain base zero and states are `Fin L`. The real recursion is used only for $n\le N$; beyond the horizon its auxiliary value is $f_N$. Its integrability and bounded-infimum properties are conclusions of Theorem 5.1, not hypotheses in these definitions. The inherited law is the conditional-independence reading of (3.1), and the inherited terminal convention is $u_N=0$.
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, pp. 935–936, Section 5.1, equations (4.9), (4.11), (5.1)

import Mathlib
import Definitions.Def_SethiChengSS_Finite_Model

namespace SethiChengSS.Finite.Supplement

open MeasureTheory Filter Topology
open scoped ENNReal

variable {L : ℕ}

/-- The calendar is deterministic and independent of the demand state. -/
def calendarActions (allowed : ℕ → Prop) (n : ℕ) : Set ℝ :=
  {u | 0 ≤ u ∧ (¬ allowed n → u = 0)}

/-- Admissible history-dependent policies with zero orders in forbidden periods. -/
def CalendarAdmissible (allowed : ℕ → Prop) (N n : ℕ) (U : Policy L) : Prop :=
  Admissible (N - n) U ∧
    ∀ t < N - n, ∀ σ ξ, ¬ allowed (n + t) → U t σ ξ = 0

/-- The constrained value uses the published expected cost, not the unconstrained DP. -/
noncomputable def calendarValue (D : Data L) (allowed : ℕ → Prop) (N n : ℕ)
    (i : Fin L) (x : ℝ) : ℝ≥0∞ :=
  ⨅ U : Policy L, ⨅ (_ : CalendarAdmissible allowed N n U), J D N n i x U

/-- The integrand in (5.1), retaining the stored fixed cost in all periods. -/
noncomputable def calendarObjective (D : Data L) (n : ℕ) (b : Fin L → ℝ → ℝ)
    (i : Fin L) (x u : ℝ) : ℝ := orderCost D n i u + F D n b i (x + u)

/-- Backward recursion with the terminal cost f_N and calendar-restricted actions. -/
noncomputable def calendarAux (D : Data L) (allowed : ℕ → Prop) (N : ℕ) :
    ℕ → Fin L → ℝ → ℝ
  | 0 => D.f N
  | m + 1 => fun i x => D.f (N - (m + 1)) i x +
      sInf (calendarObjective D (N - (m + 1)) (calendarAux D allowed N m) i x ''
        calendarActions allowed (N - (m + 1)))

/-- Only n≤N is used; beyond the horizon this returns f_N. -/
noncomputable def calendarV (D : Data L) (allowed : ℕ → Prop) (N n : ℕ) :
    Fin L → ℝ → ℝ := calendarAux D allowed N (N - n)

/-- The z of (4.11) with the constrained continuation value. -/
noncomputable def calendarZ (D : Data L) (allowed : ℕ → Prop) (N n : ℕ)
    (i : Fin L) (y : ℝ) : ℝ :=
  D.c n i * y + F D n (calendarV D allowed N (n + 1)) i y

/-- Exactly (5.1). The allowed branch takes an infimum over y≥x. -/
noncomputable def calendarH (D : Data L) (allowed : ℕ → Prop) (N n : ℕ)
    (i : Fin L) (x : ℝ) : ℝ := by
  classical
  exact if allowed n then
    sInf ((fun y => D.K n i * delta (y - x) + calendarZ D allowed N n i y) '' Set.Ici x)
  else calendarZ D allowed N n i x

/-- The threshold rule is overridden by zero on forbidden dates. -/
noncomputable def calendarRule (allowed : ℕ → Prop)
    (s S : ℕ → Fin L → EReal) (n : ℕ) (i : Fin L) (x : ℝ) : ℝ := by
  classical
  exact if allowed n then orderSS (s n i) (S n i) x else 0

end SethiChengSS.Finite.Supplement


