-- Prove2me | Definitions.Def_AcquihiringMonopsony_Baseline_Model
-- name    : AcquihiringMonopsony_Baseline_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:08:07.297812+00:00
-- url     : https://prove2.me/theorems/1e5ae4e1-d44d-430d-979f-bfaabfb9209d
-- title:
--   pp. 4–5 — baseline parameters, direct-hiring and acquihiring subgames, continuation equilibria in undominated strategies
-- statement:
--   This file sets up the baseline model of Bar-Isaac, Johnson and Nocke's *Acquihiring for Monopsony Power*: a startup $s$, an employee $e$ who is essential to it, and a potential acquirer $a$.
--
--   **Parameters.** The employee generates value $v_s$ at the startup and $v_a$ at the acquirer. At either firm she is paid a wage of at least the floor $\underline{w}$, and at the startup she also enjoys a private benefit $b$. The standing assumptions of the paper are
--   $$
--   b > 0, \qquad \min\{v_a, v_s\} > b + \underline{w}.
--   $$
--
--   **Direct hiring.** The acquirer and the startup simultaneously offer wages $w_a, w_s \ge \underline{w}$, and the employee then chooses where to work. A profile consists of the two offers and the employee's acceptance rule at *every* pair of offers $(x, y)$. Payoffs are $v_a - x$ to the acquirer if she joins it (else $0$), $v_s - y$ to the startup if she stays (else $0$), and $x$, respectively $y + b$, to the employee. A **continuation equilibrium in undominated strategies** is a profile in which
--   1. each offer is feasible and at most the firm's willingness to pay: $\underline{w} \le w_a \le v_a$ and $\underline{w} \le w_s \le v_s$;
--   2. at every pair of offers the employee chooses an employer that gives her the larger payoff (at a tie she may choose either);
--   3. neither firm can raise its payoff by switching to another feasible offer.
--
--   **Acquihiring.** The acquirer bids a price $p$ for the startup. If the startup accepts, the acquirer makes a wage offer $w_a \ge \underline{w}$; otherwise the startup makes a wage offer $w_s \ge \underline{w}$. The employee has no other offer at that stage. A profile consists of the bid, the startup's accept/decline rule at every bid, and the two wage offers. Payoffs are $v_a - w_a - q$ to the acquirer if its bid $q$ is accepted (else $0$), $q$ to the startup if it accepts (else $v_s - w_s$), and $w_a$, respectively $w_s + b$, to the employee. A **continuation equilibrium in undominated strategies** is a profile in which
--   1. the employing firm pays the lowest feasible wage, $\underline{w}$, since the employee has no competing offer;
--   2. the startup accepts or declines optimally at every bid;
--   3. the bid is at most the acquirer's willingness to pay, $p \le v_a - w_a$;
--   4. no other bid gives the acquirer a larger payoff against the startup's rule.
--
--   **Total surplus.** Wages and the price are transfers, so the total surplus of an outcome is $v_a$ if the employee works for the acquirer and $v_s + b$ if she stays at the startup. An outcome is efficient when its surplus equals $\max\{v_a, v_s + b\}$.
--
--   These objects are the common ground of Lemma 1, Lemma 2 and Proposition 1: every statement of the mission quantifies over the continuation equilibria defined here.
--
--   **Formalization Note.** The employee's choice is a `Bool`-valued function of both offers; the two weak inequalities let her break a tie either way. With continuous offers this is needed: if she always stayed at a tie, the acquirer's best offer when $v_a > v_s + b$ would be the unattained infimum $v_s + b$, and no equilibrium would exist. "Undominated" (footnote 13: a firm does not bid more than its willingness to pay) is encoded as the caps $w_a \le v_a$, $w_s \le v_s$, $p \le v_a - w_a$. The page states the post-acquisition wage $\underline{w}$ in words ("it must pay $\underline{w}$ to keep the employee"); here it is derived as the employer's cost minimization over feasible wages, which forces $w_a = w_s = \underline{w}$.
-- source:
--   Bar-Isaac, Johnson, Nocke, Acquihiring for Monopsony Power, CRC TR 224 DP No. 500 (Jan. 2024), pp. 4–5 (PDF 5–6), §2 The Baseline Model, §3 first paragraph, and footnote 13

import Mathlib

namespace AcquihiringMonopsony.Baseline

/-- The baseline parameters (p. 4): the employee's value `va` at the acquirer, her value `vs`
at the startup, her private benefit `b` from working at the startup, and the wage floor `wl`
(written w̲ in the paper). -/
structure Params where
  va : ℝ
  vs : ℝ
  b : ℝ
  wl : ℝ

/-- The standing assumptions (pp. 4–5): `b > 0` and `min {v_a, v_s} > b + w̲`. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.b ∧ P.b + P.wl < P.va ∧ P.b + P.wl < P.vs

/-! ### Direct hiring (p. 5) -/

/-- A strategy profile of the direct-hiring subgame: the acquirer's wage offer `wa`, the
startup's wage offer `ws`, and the employee's acceptance rule at every pair of offers:
`acceptA x y = true` means that, offered `x` by the acquirer and `y` by the startup, she joins
the acquirer. -/
structure DHProfile where
  wa : ℝ
  ws : ℝ
  acceptA : ℝ → ℝ → Bool

/-- The acquirer's payoff when the offers are `(x, y)` and the employee uses rule `acc`. -/
def dhPayoffA (P : Params) (acc : ℝ → ℝ → Bool) (x y : ℝ) : ℝ :=
  if acc x y then P.va - x else 0

/-- The startup's payoff when the offers are `(x, y)` and the employee uses rule `acc`. -/
def dhPayoffS (P : Params) (acc : ℝ → ℝ → Bool) (x y : ℝ) : ℝ :=
  if acc x y then 0 else P.vs - y

/-- The employee's payoff when the offers are `(x, y)` and she uses rule `acc`: her wage, plus
the private benefit `b` if she stays at the startup. -/
def dhPayoffE (P : Params) (acc : ℝ → ℝ → Bool) (x y : ℝ) : ℝ :=
  if acc x y then x else y + P.b

/-- Continuation equilibrium of the direct-hiring subgame in undominated strategies (p. 5 and
footnote 13): feasible offers (at least `w̲`) that do not exceed the firm's willingness to pay;
an employee who accepts the better offer at every pair of offers (either choice at a tie); and
offers that are best responses among all feasible offers. -/
def IsDHEquilibrium (P : Params) (σ : DHProfile) : Prop :=
  (P.wl ≤ σ.wa ∧ σ.wa ≤ P.va) ∧ (P.wl ≤ σ.ws ∧ σ.ws ≤ P.vs) ∧
  (∀ x y, σ.acceptA x y = true → y + P.b ≤ x) ∧ (∀ x y, σ.acceptA x y = false → x ≤ y + P.b) ∧
  (∀ x, P.wl ≤ x → dhPayoffA P σ.acceptA x σ.ws ≤ dhPayoffA P σ.acceptA σ.wa σ.ws) ∧
  (∀ y, P.wl ≤ y → dhPayoffS P σ.acceptA σ.wa y ≤ dhPayoffS P σ.acceptA σ.wa σ.ws)

/-! ### Acquihiring (p. 5) -/

/-- A strategy profile of the acquihiring subgame: the acquirer's bid `p` for the startup, the
startup's acceptance rule `acceptBid` (it accepts bid `q` iff `acceptBid q = true`), the
acquirer's wage offer `wa` after an accepted bid, and the startup's wage offer `ws` after a
declined bid. -/
structure AHProfile where
  p : ℝ
  acceptBid : ℝ → Bool
  wa : ℝ
  ws : ℝ

/-- The acquirer's payoff when it bids `q`: `v_a − w_a − q` if the bid is accepted, else `0`. -/
def ahPayoffA (P : Params) (σ : AHProfile) (q : ℝ) : ℝ :=
  if σ.acceptBid q then P.va - σ.wa - q else 0

/-- The startup's payoff when the acquirer bids `q`: the price `q` if it accepts, else the
profit `v_s − w_s` from retaining the employee. -/
def ahPayoffS (P : Params) (σ : AHProfile) (q : ℝ) : ℝ :=
  if σ.acceptBid q then q else P.vs - σ.ws

/-- The employee's payoff on the path of play of `σ`. -/
def ahPayoffE (P : Params) (σ : AHProfile) : ℝ :=
  if σ.acceptBid σ.p then σ.wa else σ.ws + P.b

/-- Continuation equilibrium of the acquihiring subgame in undominated strategies (p. 5 and
footnote 13). In the wage stage the employer faces no competing offer, so it pays the lowest
feasible wage; the startup accepts or declines optimally at every bid; the bid does not exceed
the acquirer's willingness to pay `v_a − w_a`; and the bid is optimal against the startup's
rule. -/
def IsAHEquilibrium (P : Params) (σ : AHProfile) : Prop :=
  (P.wl ≤ σ.wa ∧ ∀ x, P.wl ≤ x → σ.wa ≤ x) ∧ (P.wl ≤ σ.ws ∧ ∀ y, P.wl ≤ y → σ.ws ≤ y) ∧
  (∀ q, σ.acceptBid q = true → P.vs - σ.ws ≤ q) ∧ (∀ q, σ.acceptBid q = false → q ≤ P.vs - σ.ws) ∧
  σ.p ≤ P.va - σ.wa ∧
  ∀ q, ahPayoffA P σ q ≤ ahPayoffA P σ σ.p

/-! ### Total surplus -/

/-- Total surplus of an outcome (wages and the price are transfers): `v_a` if the employee works
for the acquirer (`hiredByA = true`), and `v_s + b` if she stays at the startup. An outcome is
efficient iff its surplus equals `max v_a (v_s + b)`. -/
def surplus (P : Params) (hiredByA : Bool) : ℝ :=
  if hiredByA then P.va else P.vs + P.b

end AcquihiringMonopsony.Baseline


