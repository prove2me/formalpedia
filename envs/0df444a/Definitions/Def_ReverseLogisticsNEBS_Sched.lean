-- Prove2me | Definitions.Def_ReverseLogisticsNEBS_Sched
-- name    : ReverseLogisticsNEBS_Sched
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:51:02.746729+00:00
-- url     : https://prove2.me/theorems/7f9cf2ae-e844-4d4a-bd37-50166c7507b1
-- title:
--   Echelon schedules, feasible sets (6) and (9), period objective (8), and the optimality equations (7)/(10)
-- statement:
--   In echelon variables the state is the vector of **echelon inventories** $y_j = x_1 + \dots + x_j$, and a decision is a triple of **echelon schedules**: post-expedite positions $Y^E_j$, post-reverse-order positions $Y^R_j$ and post-regular-order positions $Y_j$. The installation orders are $X^E_j = Y^E_j - y_j$, $X^R_j = Y^E_j - Y^R_j$, $X_j = Y_j - Y^R_j$, and the next state is $y_{j,t+1} = Y_j - D_t$. A state is **nested** when $y_1 \le \dots \le y_N$.
--
--   The **original feasible set** (6) is
--   $$
--   Y^E_j \in [y_j, Y^E_{j+1}],\quad Y^R_1 \in [[Y^E_1]^-, Y^E_1],\quad Y^R_j \in [Y^E_{j-1}, Y^E_j]\ (j \ge 2),\quad Y_j \in [Y^R_j,\ Y^R_{j+1} - (Y^E_j - Y^R_j)],
--   $$
--   with $Y^E_{N+1} = Y^R_{N+1} := \infty$; the **relaxed set** (9) replaces the last interval by $[Y^R_j, Y^R_{j+1}]$.
--
--   With a continuation function $F = f_{t+1}$, the **period objective** (8) is
--   $$
--   v_t(\omega, Y^E, Y^R, Y) = \gamma_t(\omega, Y^R_1) + \sum_{j=1}^N \big(c^E_j Y^E_j + c_j Y_j - c^R_j Y^R_j\big) + \alpha\,\mathbb E_\omega\big[F(\omega_{t+1}, Y - D_t(\omega))\big].
--   $$
--
--   A decision is **optimal** if it is feasible, has a finite expected continuation, and minimizes (8) among feasible decisions with a finite expected continuation. A family $f_t$ **solves the optimality equations** (7) or (10) over the horizon $T$ if, in every period $t \in [1, T]$ and at every nested state, the minimum is attained and $f_t(\omega, y) = -\sum_j k^E_j y_j + \min v_t$.
--
--   A schedule is **unidirectional at $j$** if $Y^E_j = y_j$ and $Y_j = Y^R_j$, or $Y^R_j = Y^E_j$. A function $f:\mathbb R^N \to \mathbb R$ is **additively convex** if $f(y) = \sum_j f_j(y_j)$ with every $f_j$ convex.
--
--   **Formalization Note** The conventions $Y^E_{N+1} = Y^R_{N+1} = \infty$ are encoded by omitting the upper constraint at location $N$. A decision whose expected continuation is infinite is excluded from the comparison instead of receiving the junk value $0$ of a non-integrable Bochner integral. The terminal value $f_{T+1}$ is data and is not constrained by the optimality equations.
-- source:
--   Angelus–Özer, When Variability Trumps Volatility: Optimal Control and Value of Reverse Logistics in Supply Chains with Multiple Flows of Product, SSRN 3508009 (Dec. 21, 2019), §2–§3, pp.11–13: echelon change of variables p.11, (6) p.11, (7)–(8) p.12, (9) p.12, (10) p.13, unidirectional p.13, additive convexity p.12

import Mathlib
import Definitions.Def_ReverseLogisticsNEBS_Model

open MeasureTheory ProbabilityTheory

namespace ReverseLogisticsNEBS

/-- **Echelon schedules** (p.11): the post-expedite echelon positions `Y^E_j`, the
post-reverse-order echelon positions `Y^R_j` and the post-regular-order echelon positions `Y_j`
of one period, `j = 1, …, N`. With `y_j` the echelon inventory, the installation decisions are
`X^E_j = Y^E_j − y_j` (expedited), `X^R_j = Y^E_j − Y^R_j` (reverse) and `X_j = Y_j − Y^R_j`
(regular). The next echelon state is `y_{j,t+1} = Y_j − D_t`.

The module also defines the feasible sets (6) and (9), the period objective (8), the optimality
of a decision, the optimality equations (7)/(10) and unidirectionality (p.13).

**Formalization Note.** Locations are `Fin N` (index `j` = location `j + 1`). "Location `i` is
directly upstream of `j`" is written `i.val = j.val + 1`. The conventions
`Y^E_{N+1} = Y^R_{N+1} := ∞` of (6) are encoded by omitting the upper constraint at the top
index. A state `y` is **nested** (`Monotone y`, i.e. `y_1 ≤ ⋯ ≤ y_N`) exactly when the on-hand
inventories `x_j = y_j − y_{j−1}`, `j ≥ 2`, are nonnegative; the net inventory `x_1 = y_1` may be
negative. -/
structure Sched (N : ℕ) where
  /-- Post-expedite echelon positions `Y^E_j`. -/
  YE : Fin N → ℝ
  /-- Post-reverse-order echelon positions `Y^R_j`. -/
  YR : Fin N → ℝ
  /-- Post-regular-order echelon positions `Y_j`. -/
  Y : Fin N → ℝ

namespace Sched

variable {N : ℕ}

/-- The constraints shared by (6) and (9) (p.11–12):
`Y^E_j ∈ [y_j, Y^E_{j+1}]`, `Y^R_1 ∈ [[Y^E_1]^−, Y^E_1]`, `Y^R_j ∈ [Y^E_{j−1}, Y^E_j]` (`j ≥ 2`),
and `Y^R_j ≤ Y_j`. -/
def FeasCommon (y : Fin N → ℝ) (s : Sched N) : Prop :=
  (∀ j, y j ≤ s.YE j) ∧
  (∀ i j : Fin N, i.val = j.val + 1 → s.YE j ≤ s.YE i) ∧
  (∀ j : Fin N, j.val = 0 → negPartMin (s.YE j) ≤ s.YR j) ∧
  (∀ i j : Fin N, i.val = j.val + 1 → s.YE j ≤ s.YR i) ∧
  (∀ j, s.YR j ≤ s.YE j) ∧
  (∀ j, s.YR j ≤ s.Y j)

/-- The **feasible set (6)** `𝕐(y)` of the original problem (p.11): the common constraints and
`Y_j ≤ Y^R_{j+1} − (Y^E_j − Y^R_j)` for `j ≤ N − 1`. -/
def FeasOrig (y : Fin N → ℝ) (s : Sched N) : Prop :=
  FeasCommon y s ∧ ∀ i j : Fin N, i.val = j.val + 1 → s.Y j ≤ s.YR i - (s.YE j - s.YR j)

/-- The **relaxed feasible set (9)** `𝕐̃(y)` (p.12): the common constraints and
`Y_j ≤ Y^R_{j+1}` for `j ≤ N − 1`. -/
def FeasRelax (y : Fin N → ℝ) (s : Sched N) : Prop :=
  FeasCommon y s ∧ ∀ i j : Fin N, i.val = j.val + 1 → s.Y j ≤ s.YR i

/-- A schedule is **unidirectional at location `j`** (p.13, in echelon variables, Corollary 1):
either `X^E_j = X_j = 0` (`Y^E_j = y_j` and `Y_j = Y^R_j`) or `X^R_j = 0` (`Y^R_j = Y^E_j`). -/
def UnidirAt (y : Fin N → ℝ) (s : Sched N) (j : Fin N) : Prop :=
  (s.YE j = y j ∧ s.Y j = s.YR j) ∨ s.YR j = s.YE j

end Sched

namespace Model

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : Model N Ω)

/-- The next echelon state `Y_t − D` after demand `D` (p.11). -/
def nextState (s : Sched N) (d : ℝ) : Fin N → ℝ := fun j => s.Y j - d

/-- The continuation term `f(ω_{t+1}, Y_t − D_t)` of (8) is integrable under the period-`t`
law `κ t ω`. -/
def ContIntegrable (t : ℕ) (F : Ω → (Fin N → ℝ) → ℝ) (ω : Ω) (s : Sched N) : Prop :=
  Integrable (fun z : ℝ × Ω => F z.2 (nextState s z.1)) (M.κ t ω)

/-- The **period objective (8)** (p.12) with continuation function `F = f_{t+1}`:
`v_t(ω, Y^E, Y^R, Y) = γ_t(ω, Y^R_1) + Σ_j (c^E_j Y^E_j + c_j Y_j − c^R_j Y^R_j)
 + α E_ω[F(ω_{t+1}, Y − D_t(ω))]`. -/
noncomputable def stageObj (t : ℕ) (F : Ω → (Fin N → ℝ) → ℝ) (ω : Ω) (s : Sched N) : ℝ :=
  M.gamma t ω (firstLoc s.YR) + ∑ j, (M.cE j * s.YE j + M.c j * s.Y j - M.cR j * s.YR j) +
    M.α * ∫ z, F z.2 (nextState s z.1) ∂(M.κ t ω)

/-- `s` is an **optimal decision** in period `t` at Markov state `ω`, for the feasible set
`feas` and continuation `F`: it is feasible, its expected continuation is finite, and no feasible
decision with a finite expected continuation has a smaller objective (8).

**Formalization Note.** A feasible decision whose continuation is not integrable has, in the
paper, an infinite (or undefined) expected cost; it is excluded from the comparison rather than
given the junk value of a Bochner integral. -/
def IsOptimalDecision (t : ℕ) (F : Ω → (Fin N → ℝ) → ℝ) (feas : Sched N → Prop) (ω : Ω)
    (s : Sched N) : Prop :=
  feas s ∧ M.ContIntegrable t F ω s ∧
    ∀ s', feas s' → M.ContIntegrable t F ω s' → M.stageObj t F ω s ≤ M.stageObj t F ω s'

/-- `f` satisfies the **optimality equations** (7) (with `feas = Sched.FeasOrig`) or (10) (with
`feas = Sched.FeasRelax`) in every period `t ∈ [1, T]` at every nested state: the minimum in
`f_t(ω, y) = −Σ_j k^E_j y_j + min_{𝕐(y)} v_t(ω, ·)` is attained and equals `f_t(ω, y)`. The
terminal value `f (T + 1)` is the data of the problem and is not constrained here. -/
def SolvesDP (T : ℕ) (feas : (Fin N → ℝ) → Sched N → Prop)
    (f : ℕ → Ω → (Fin N → ℝ) → ℝ) : Prop :=
  ∀ t, 1 ≤ t → t ≤ T → ∀ ω (y : Fin N → ℝ), Monotone y →
    ∃ s, M.IsOptimalDecision t (f (t + 1)) (feas y) ω s ∧
      f t ω y = -∑ j, M.kE j * y j + M.stageObj t (f (t + 1)) ω s

end Model

/-- `f : ℝ^N → ℝ` is **additively convex** (p.12): `f(y) = Σ_j f_j(y_j)` for convex
`f_1, …, f_N : ℝ → ℝ`. -/
def AdditivelyConvex {N : ℕ} (f : (Fin N → ℝ) → ℝ) : Prop :=
  ∃ g : Fin N → ℝ → ℝ, (∀ j, ConvexOn ℝ Set.univ (g j)) ∧ ∀ y, f y = ∑ j, g j (y j)

end ReverseLogisticsNEBS


