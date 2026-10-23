-- Prove2me | Definitions.Def_StartupLaunch_Strategy_Model
-- name    : StartupLaunch_Strategy_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:01.795989+00:00
-- url     : https://prove2.me/theorems/c60bf421-d0e0-4b5b-8362-3e6de5f17317
-- title:
--   §3, (1)–(5), pp. 6–14 — established firm and cash-constrained startup: action values Π_LS, Π_LC, Π_DC and R_LS, R_LC, R_DC, Bellman systems, Proposition 1 thresholds
-- statement:
--   This file sets up the model of Bhaskaran, Erzurumlu and Ramachandran: a firm holds an **on-hand product**, ready to launch, and develops an **advanced product** whose development succeeds in each period with probability $p$.
--
--   **Parameters.** $v_o$ is the per-period payoff of the on-hand product and $v_a$ that of the advanced product; $c$ is the per-period development cost; $\delta$ is the discount factor; and $\alpha$ is the cannibalization factor: once the on-hand product is on the market, the advanced product earns only $(1-\alpha)v_a$ per period. The **standing assumptions** of §3 are
--   $$0 < v_o \le v_a,\qquad v_o < c,\qquad 0 < \delta < 1,\qquad 0 \le \alpha \le 1 .$$
--   The lifetime values are $V_o = v_o/(1-\delta)$ and $V_a = v_a/(1-\delta)$.
--
--   **Established firm**, equations (1)–(2). With $\Pi_0$ the value before and $\Pi_1$ the value after the launch of the on-hand product,
--   $$\Pi_0 = \max\{\Pi_{LS},\Pi_{LC},\Pi_{DC}\},\qquad \Pi_1 = \max\{\Pi_{LS},\Pi_{LC}\},$$
--   $$\Pi_{LS} = V_o,\quad \Pi_{LC} = v_o - c + p(1-\alpha)\delta V_a + (1-p)\delta\Pi_1,\quad \Pi_{DC} = -c + p\,\delta V_a + (1-p)\delta\Pi_0 .$$
--   (L/D: launch or defer the on-hand product; S/C: stop or continue development.) At a success probability $q$, the firm *launches and stops*, *launches and continues*, or *defers and continues* when that action attains the maximum in every solution of (1)–(2). A pair $p_1 \le p_2$ is a pair of **thresholds** in the sense of Proposition 1 when, for every $q \in [0,1]$: $q \le p_1$ gives launch-and-stop, $p_1 < q \le p_2$ gives launch-and-continue, and $q > p_2$ gives defer-and-continue.
--
--   **Startup**, equations (3)–(5). With cash $E$, next-period cash is $E_D = (E-c)/\delta$ after deferring and $E_L = (E+v_o-c)/\delta$ after launching. For value functions $R_0, R_1$ of the cash level,
--   $$R_{LS}(E) = E + V_o,\qquad R_{LC}(E) = p\bigl(E + v_o - c + \delta(1-\alpha)V_a\bigr) + (1-p)\delta R_1(E_L),$$
--   $$R_{DC}(E) = \begin{cases} p(E - c + \delta V_a) + (1-p)\delta R_0(E_D) & E \ge c,\\ E & E < c,\end{cases}$$
--   $$R_0(E) = \max\{R_{LS}(E), R_{DC}(E), R_{LC}(E)\},\qquad R_1(E) = \max\{R_{LS}(E), R_{LC}(E)\}.$$
--
--   These objects are the shared vocabulary of every statement in the mission.
--
--   **Formalization Note.** The paper allows $\delta = 1$, but $V_o = v_o/(1-\delta)$ needs $\delta < 1$, which is assumed; $v_o > 0$ is also assumed. The value functions are not constructed: every theorem quantifies over all solutions of the equations, and a separate milestone states that each system has exactly one solution. The startup's equations are imposed at every real $E$; the launch-and-continue option is available only when the period's development is funded, $c \le E + v_o$ (the paper's (4) is printed "when $E_t > c$"; the funded reading is the one Lemma 1(iii) and Proposition 2(i) use), and otherwise $R_1(E) = R_{LS}(E)$ and $R_0(E) = \max\{R_{LS}(E), R_{DC}(E)\}$. Among the solutions of (3)–(5), the value function is selected by requiring $R_0(E) - E$ and $R_1(E) - E$ to be bounded: above the interest break-even the recursion never terminates and unbounded spurious solutions exist. Thresholds are defined by the behaviour they induce, not by the proof's closed forms (whose printed $p_C$ is wrong), and are normalized to the probability range: $p_1 \le 1$, and $p_2 = 1$ when $p_1 = 1$. Without this normalization, when launch-and-stop is optimal at every $q \in [0,1]$, the pair $(p_1,p_2) = (1,5)$ would satisfy the conditions and make Proposition 2(ii) assert launch-and-continue at $p = 1$, which is false. The symbols $\Pi_0, \Pi_1$ are written `Pi0`, `Pi1` in Lean.
-- source:
--   Bhaskaran, Erzurumlu & Ramachandran, Sequential product development and introduction by cash-constrained start-ups, SSRN 3255345 (manuscript of February 2020), pp. 6–14 (PDF 7–15), §3, §4.1, §4.2, eqs. (1)–(5), Proposition 1

import Mathlib

namespace StartupLaunch.Strategy

/-- The model parameters of §3: per-period payoff `vo` of the on-hand product, per-period payoff
`va` of the advanced product, per-period development cost `c`, discount factor `δ` and
cannibalization factor `α`. -/
structure Params where
  vo : ℝ
  va : ℝ
  c : ℝ
  δ : ℝ
  α : ℝ

/-- Standing assumptions of §3: `0 < vo ≤ va`, `vo < c`, `0 < δ < 1`, `0 ≤ α ≤ 1`. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.vo ∧ P.vo ≤ P.va ∧ P.vo < P.c ∧ 0 < P.δ ∧ P.δ < 1 ∧ 0 ≤ P.α ∧ P.α ≤ 1

/-- Lifetime NPV of the on-hand product, `V_o = v_o / (1 - δ)`. -/
noncomputable def Params.Vo (P : Params) : ℝ := P.vo / (1 - P.δ)

/-- Lifetime NPV of the advanced product, `V_a = v_a / (1 - δ)`. -/
noncomputable def Params.Va (P : Params) : ℝ := P.va / (1 - P.δ)

/-! ### The established firm, equations (1)–(2) -/

/-- `Π_LS = V_o`: launch the on-hand product and stop development. -/
noncomputable def piLS (P : Params) : ℝ := P.Vo

/-- `Π_LC = v_o - c + p (1 - α) δ V_a + (1 - p) δ Π_1`: launch and continue development. -/
noncomputable def piLC (P : Params) (p Pi1 : ℝ) : ℝ :=
  P.vo - P.c + p * (1 - P.α) * P.δ * P.Va + (1 - p) * P.δ * Pi1

/-- `Π_DC = -c + p (δ V_a) + (1 - p) δ Π_0`: defer the launch and continue development. -/
noncomputable def piDC (P : Params) (p Pi0 : ℝ) : ℝ :=
  -P.c + p * (P.δ * P.Va) + (1 - p) * P.δ * Pi0

/-- `(Π_0, Π_1)` solves the established firm's equations (1)–(2) at success probability `p`. -/
def EstBellman (P : Params) (p Pi0 Pi1 : ℝ) : Prop :=
  Pi0 = max (max (piLS P) (piLC P p Pi1)) (piDC P p Pi0) ∧
    Pi1 = max (piLS P) (piLC P p Pi1)

/-- At success probability `q` the established firm launches the on-hand product and stops
development: launch-and-stop attains `Π_0` and `Π_1` in every solution of (1)–(2). -/
def EstLaunchStop (P : Params) (q : ℝ) : Prop :=
  ∀ Pi0 Pi1 : ℝ, EstBellman P q Pi0 Pi1 → Pi0 = piLS P ∧ Pi1 = piLS P

/-- At success probability `q` the established firm launches the on-hand product and continues
development until it succeeds: launch-and-continue attains `Π_0` and `Π_1` in every solution. -/
def EstLaunchContinue (P : Params) (q : ℝ) : Prop :=
  ∀ Pi0 Pi1 : ℝ, EstBellman P q Pi0 Pi1 → Pi0 = piLC P q Pi1 ∧ Pi1 = piLC P q Pi1

/-- At success probability `q` the established firm does not launch the on-hand product and
continues development: defer-and-continue attains `Π_0` in every solution. -/
def EstDeferContinue (P : Params) (q : ℝ) : Prop :=
  ∀ Pi0 Pi1 : ℝ, EstBellman P q Pi0 Pi1 → Pi0 = piDC P q Pi0

/-- `p1 ≤ p2` are thresholds as in Proposition 1 (i)–(iii), for success probabilities
`q ∈ [0, 1]`. They are normalized to the probability range: `p1 ≤ 1`, and `p2 = 1` when `p1 = 1`
(launch-and-stop optimal on all of `[0, 1]`). -/
def IsThresholds (P : Params) (p1 p2 : ℝ) : Prop :=
  p1 ≤ p2 ∧ p1 ≤ 1 ∧ (p1 = 1 → p2 = 1) ∧
    ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      (q ≤ p1 → EstLaunchStop P q) ∧
      (p1 < q → q ≤ p2 → EstLaunchContinue P q) ∧
      (p2 < q → EstDeferContinue P q)

/-! ### The cash-constrained startup, equations (3)–(5) -/

/-- Next-period cash after deferring and developing, `E_D = (E - c) / δ`. -/
noncomputable def ED (P : Params) (E : ℝ) : ℝ := (E - P.c) / P.δ

/-- Next-period cash after launching and developing, `E_L = (E + v_o - c) / δ`. -/
noncomputable def EL (P : Params) (E : ℝ) : ℝ := (E + P.vo - P.c) / P.δ

/-- `R_LS(E) = E + V_o`. -/
noncomputable def RLS (P : Params) (E : ℝ) : ℝ := E + P.Vo

/-- `R_LC(E) = p (E + v_o - c + δ (1 - α) V_a) + (1 - p) δ R_1(E_L)`. -/
noncomputable def RLC (P : Params) (p : ℝ) (R1 : ℝ → ℝ) (E : ℝ) : ℝ :=
  p * (E + P.vo - P.c + P.δ * (1 - P.α) * P.Va) + (1 - p) * P.δ * R1 (EL P E)

/-- `R_DC(E) = p (E - c + δ V_a) + (1 - p) δ R_0(E_D)` if `E ≥ c`, and `E` if `E < c`. -/
noncomputable def RDC (P : Params) (p : ℝ) (R0 : ℝ → ℝ) (E : ℝ) : ℝ :=
  if P.c ≤ E then p * (E - P.c + P.δ * P.Va) + (1 - p) * P.δ * R0 (ED P E) else E

/-- `(R_0, R_1)` solves the startup's equations (3)–(5) at every cash level, with launch-and-continue
available only when this period's development is funded (`c ≤ E + v_o`), and `R_I(E) - E` bounded
(this selects the value function among the solutions of (3)–(5)). -/
def StartupBellman (P : Params) (p : ℝ) (R0 R1 : ℝ → ℝ) : Prop :=
  (∀ E : ℝ, R1 E = if P.c ≤ E + P.vo then max (RLS P E) (RLC P p R1 E) else RLS P E) ∧
  (∀ E : ℝ, R0 E = if P.c ≤ E + P.vo then max (max (RLS P E) (RDC P p R0 E)) (RLC P p R1 E)
      else max (RLS P E) (RDC P p R0 E)) ∧
  ∃ M : ℝ, ∀ E : ℝ, |R0 E - E| ≤ M ∧ |R1 E - E| ≤ M

end StartupLaunch.Strategy


