-- Prove2me | Definitions.Def_AcquihiringMonopsony_PrivateInfo_Model
-- name    : AcquihiringMonopsony_PrivateInfo_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:08:07.636424+00:00
-- url     : https://prove2.me/theorems/16148587-b842-41f3-abf1-85d5b3b63fe7
-- title:
--   §6, pp. 15–18 — private-benefit model: uniform type on [0, B], wage game, expected profits, Lemma 5 wages, v̂_a, welfare
-- statement:
--   This file sets up the private-information model of §6 of Bar-Isaac, Johnson and Nocke.
--
--   **Parameters.** An employee generates value $v_a$ at a potential acquirer and $v_s$ at a startup. At the startup she also enjoys a private benefit $b$, which she alone observes and which is uniformly distributed on $[0,B]$. The standing assumptions of §6 are
--   $$0 < B < \min\{v_a, v_s\}, \qquad v_s - B < v_a < v_s + 2B .$$
--   Wages are not bounded below; instead the employee has an outside option worth $0$.
--
--   **Direct hiring.** The acquirer offers $w_a$ and the startup $w_s$, simultaneously. A type-$b$ employee joins the acquirer when $w_a > w_s + b$ and $w_a \ge 0$, and stays at the startup when $w_s + b \ge w_a$ and $w_s + b \ge 0$; otherwise she takes the outside option. The tie $b = w_a - w_s$ has probability zero and is sent to the startup. Expected profits average over $b \sim U[0,B]$:
--   $$\pi_a(w_a,w_s) = \frac1B\int_0^B (v_a-w_a)\,\mathbf 1\{\text{type } b \text{ joins } a\}\,db, \qquad \pi_s(w_a,w_s) = \frac1B\int_0^B (v_s-w_s)\,\mathbf 1\{\text{type } b \text{ stays}\}\,db,$$
--   and the poaching probability is $\frac1B\int_0^B \mathbf 1\{\text{type } b\text{ joins } a\}\,db$. A pair $(w_a,w_s)$ is a **direct-hiring equilibrium** when each offer is a best response to the other over **all** real wages.
--
--   **Named quantities.** Lemma 5's wages $w_a^* = (2v_a + v_s - B)/3$ and $w_s^* = (2v_s + v_a - 2B)/3$; the indifferent type $b^* = (v_a - v_s + B)/3$; the threshold $\hat v_a = v_s + \tfrac{7-3\sqrt5}{2}B$.
--
--   **Monopsony.** A monopsonistic startup offering $y$ keeps exactly the types with $y + b \ge 0$, so its expected profit is $\frac1B\int_0^B (v_s-y)\mathbf 1\{y+b\ge 0\}\,db$. A monopsonistic acquirer offering $x$ (the employee has no benefit there) earns $v_a - x$ if $x \ge 0$ and $0$ otherwise.
--
--   **Acquihiring.** By Lemma 2 of the paper with wage floor $0$ (as §6 states), the acquirer's acquihiring profit is $\max\{0, v_a - v_s\}$: it bids the startup's stand-alone profit $v_s$ and pays wage $0$ when $v_a > v_s$, and earns nothing otherwise. The employee's acquihiring payoff is $0$ when $v_a > v_s$ (wage $0$ at the acquirer) and $b$ otherwise (wage $0$ at the startup plus her benefit). Under direct hiring at offers $(w_a,w_s)$ a type-$b$ employee receives $\max\{w_a, w_s + b, 0\}$.
--
--   **Welfare.** Total surplus under direct hiring at Lemma 5's wages is $\frac1B\int_0^B \big(v_a\mathbf 1\{b < w_a^*-w_s^*\} + (v_s+b)\mathbf 1\{b \ge w_a^*-w_s^*\}\big)db$; under acquihiring the employee produces $v_a$ at the acquirer.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Expected values are interval integrals over $[0,B]$ scaled by $1/B$. Every integrand is bounded and piecewise constant in $b$, hence interval integrable, so each integral is the page's probability times a constant; a verification file evaluates $\pi_a(w_a^*,w_s^*)$ to its closed form at one instance. The acquihiring profit is defined through Lemma 2's formula rather than by re-encoding the bid stage; the milestone on the monopsonistic startup's wage and profit is what justifies that formula. The welfare under acquihiring is the allocation "employee at the acquirer", which is the comparison Corollary 4 makes.
-- source:
--   Bar-Isaac, Johnson, Nocke, Acquihiring for Monopsony Power, CRC TR 224 DP No. 500 (Jan. 2024), pp. 15–18 (PDF 16–19), §6 setup, Lemma 5, Proposition 5, Corollary 4; Lemma 2 p. 5 (PDF 6) with w̲ = 0

import Mathlib

namespace AcquihiringMonopsony.PrivateInfo

/-- The parameters of §6 (p. 15): the employee's productive value at the acquirer `va` (v_a) and at
the startup `vs` (v_s), and the upper end `B` of the support of her private benefit b ~ U[0, B]. -/
structure Params where
  va : ℝ
  vs : ℝ
  B  : ℝ

/-- p. 15: `0 < B < min {v_a, v_s}` and `v_s − B < v_a < v_s + 2B`. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.B ∧ P.B < P.va ∧ P.B < P.vs ∧ P.vs - P.B < P.va ∧ P.va < P.vs + 2 * P.B

/-- Under direct hiring with offers `wa`, `ws`, the employee of type `b` joins the acquirer:
its wage beats the startup's wage plus the private benefit, and the outside option `0`.
(The tie `b = wa − ws` has probability zero and is sent to the startup.) -/
def JoinsA (wa ws b : ℝ) : Prop := ws + b < wa ∧ 0 ≤ wa

/-- Under direct hiring with offers `wa`, `ws`, the employee of type `b` stays at the startup:
the startup's wage plus benefit weakly beats the acquirer's wage and the outside option `0`. -/
def StaysS (wa ws b : ℝ) : Prop := wa ≤ ws + b ∧ 0 ≤ ws + b

open Classical in
/-- The acquirer's expected profit under direct hiring, `b` uniform on `[0, B]`. -/
noncomputable def profitA (P : Params) (wa ws : ℝ) : ℝ :=
  (1 / P.B) * ∫ b in (0:ℝ)..P.B, if JoinsA wa ws b then P.va - wa else 0

open Classical in
/-- The startup's expected profit under direct hiring, `b` uniform on `[0, B]`. -/
noncomputable def profitS (P : Params) (wa ws : ℝ) : ℝ :=
  (1 / P.B) * ∫ b in (0:ℝ)..P.B, if StaysS wa ws b then P.vs - ws else 0

open Classical in
/-- The probability that the acquirer's offer is accepted (the employee is poached). -/
noncomputable def poachProb (P : Params) (wa ws : ℝ) : ℝ :=
  (1 / P.B) * ∫ b in (0:ℝ)..P.B, if JoinsA wa ws b then (1:ℝ) else 0

/-- A (pure) Nash equilibrium of the direct-hiring wage game: each firm's offer is a best
response, over all real wages, to the other's offer. -/
def IsDHEquilibrium (P : Params) (wa ws : ℝ) : Prop :=
  (∀ x : ℝ, profitA P x ws ≤ profitA P wa ws) ∧ (∀ y : ℝ, profitS P wa y ≤ profitS P wa ws)

/-- Lemma 5's acquirer wage `(2v_a + v_s − B)/3`. -/
noncomputable def waStar (P : Params) : ℝ := (2 * P.va + P.vs - P.B) / 3

/-- Lemma 5's startup wage `(2v_s + v_a − 2B)/3`. -/
noncomputable def wsStar (P : Params) : ℝ := (2 * P.vs + P.va - 2 * P.B) / 3

/-- The indifferent type `b* = (v_a − v_s + B)/3` (proof of Corollary 4, p. 17). -/
noncomputable def bStar (P : Params) : ℝ := (P.va - P.vs + P.B) / 3

/-- Proposition 5's threshold `v̂_a = v_s + ((7 − 3√5)/2) B`. -/
noncomputable def vHat (P : Params) : ℝ := P.vs + (7 - 3 * Real.sqrt 5) / 2 * P.B

open Classical in
/-- The startup's expected profit as a monopsonist offering wage `y`: type `b` stays iff
`y + b ≥ 0` (outside option normalized to zero), p. 15. -/
noncomputable def monoProfitS (P : Params) (y : ℝ) : ℝ :=
  (1 / P.B) * ∫ b in (0:ℝ)..P.B, if 0 ≤ y + b then P.vs - y else 0

open Classical in
/-- The acquirer's expected profit as a monopsonist (after an acquisition) offering wage `x`:
the employee has no private benefit at the acquirer and accepts iff `x ≥ 0`, p. 15. -/
noncomputable def monoProfitA (P : Params) (x : ℝ) : ℝ :=
  (1 / P.B) * ∫ _b in (0:ℝ)..P.B, if 0 ≤ x then P.va - x else 0

/-- The acquirer's profit under acquihiring: Lemma 2 with `w̲ = 0` (p. 15). It bids the
startup's stand-alone profit `v_s` and pays wage `0` when `v_a > v_s`; otherwise it earns `0`. -/
noncomputable def ahProfitA (P : Params) : ℝ := max 0 (P.va - P.vs)

/-- The type-`b` employee's payoff under direct hiring at offers `wa`, `ws`: the best of the
acquirer's wage, the startup's wage plus benefit, and the outside option `0`. -/
noncomputable def dhPayoffE (wa ws b : ℝ) : ℝ := max (max wa (ws + b)) 0

open Classical in
/-- The type-`b` employee's payoff under acquihiring (Lemma 2 with `w̲ = 0`): wage `0` at the
acquirer if the acquisition succeeds (`v_a > v_s`), otherwise wage `0` plus benefit `b` at the
monopsonistic startup. -/
noncomputable def ahPayoffE (P : Params) (b : ℝ) : ℝ := if P.vs < P.va then 0 else b

open Classical in
/-- Expected total surplus under direct hiring at Lemma 5's wages: `v_a` for the types poached by
the acquirer, `v_s + b` for the types retained by the startup. -/
noncomputable def welfareDH (P : Params) : ℝ :=
  (1 / P.B) * ∫ b in (0:ℝ)..P.B, if JoinsA (waStar P) (wsStar P) b then P.va else P.vs + b

/-- Total surplus under acquihiring (Corollary 4): the employee works at the acquirer and
produces `v_a`, with no private benefit. -/
def welfareAH (P : Params) : ℝ := P.va

end AcquihiringMonopsony.PrivateInfo


