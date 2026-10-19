-- Prove2me | Definitions.Def_EntrepChoice_TestChoice_Setting
-- name    : EntrepChoice_TestChoice_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:10:41.006841+00:00
-- url     : https://prove2.me/theorems/fbd500bf-aad7-4f6a-a45d-cff8f2b174a8
-- title:
--   §2–§3, pp. 6–12 — idea × strategy prior, the conflated signal table, Bayes posteriors, (A1), period-1 actions and the value of a test V_0(λ_v, λ_s)
-- statement:
--   This file sets up the two-period testing model of Agrawal, Gans and Stern.
--
--   **Parameters and standing assumptions (§2, pp. 6–7).** An entrepreneur has an idea of value $v$ (state $h$) or $0$ (state $l$), with prior $p_0 = \Pr[h]$. Value is realized only by implementing an effective strategy (state $g$, versus ineffective $b$); any given strategy is effective with prior probability $e_0$, independently across strategies and of the idea. Implementing a strategy costs $C$, testing one costs $c$. The standing assumptions are
--   $$0<p_0<1,\qquad 0<e_0<1,\qquad v>0,\qquad V_0 = e_0p_0v - C = 0,\qquad c < C .$$
--
--   **Tests and signals (§3.1, p. 9).** A test of the selected strategy has precisions $(\lambda_v,\lambda_s)\in[0,1]^2$ and emits one of the four signals $(H,G),(H,B),(L,G),(L,B)$ according to the table
--
--   | | $h$ | $l$ |
--   |---|---|---|
--   | $g$ | $(H,G)$ w.p. $1$ | $(L,G)$ w.p. $\lambda_s$; $(H,B)$ w.p. $1-\lambda_s$ |
--   | $b$ | $(H,B)$ w.p. $\lambda_v$; $(L,G)$ w.p. $1-\lambda_v$ | $(L,B)$ w.p. $1$ |
--
--   The prior over the four states $(i,s)$ is the product $\Pr[i]\Pr[s]$. For a signal $\sigma$, $\Pr(\sigma)$, $\Pr(h,\sigma)$ and $\Pr(g,\sigma)$ are the corresponding joint probabilities, and the Bayes posteriors are $p_1(\sigma) = \Pr(h,\sigma)/\Pr(\sigma)$ and $e_1(\sigma) = \Pr(g,\sigma)/\Pr(\sigma)$.
--
--   **Assumption (A1) (p. 9).** Tests are weakly informative:
--   $$p_1(H,B)\ge p_0,\quad p_1(L,G)\le p_0,\quad e_1(H,B)\le e_0,\quad e_1(L,G)\ge e_0 .$$
--
--   **Period-1 actions and the value of a test (§3.2–3.3, p. 10).** After the signal, the entrepreneur either implements the tested strategy (payoff $v - C$ in state $(h,g)$, $-C$ otherwise), implements another randomly selected strategy (effective with probability $e_0$ independently, so payoff $e_0v - C$ if the idea is $h$ and $-C$ if it is $l$), or abandons (payoff $0$). The value of an action after $\sigma$ is $\Pr(\sigma)$ times its conditional expected payoff, $V_1(\sigma)$ is the best of the three, and the value of testing is
--   $$V_0(\lambda_v,\lambda_s) = \sum_{\sigma}\Pr(\sigma)\,V_1(\sigma) - c .$$
--
--   These objects are the common ground of every statement in the mission: Proposition 1 compares the three actions after each signal, and Proposition 2 compares $V_0$ at two tests.
--
--   **Formalization Note.** Action values are kept unnormalized ($\Pr(\sigma)\cdot\mathbb E[\text{payoff}\mid\sigma]$), so a signal of probability $0$ contributes $0$ and no division is needed in $V_0$. (A1) is stored cross-multiplied by $\Pr(\sigma)$ (e.g. $p_0\Pr(H,B)\le \Pr(h,H,B)$), which agrees with the posterior form whenever $\Pr(\sigma)>0$ and is harmless when $\Pr(\sigma)=0$. In Lean `p1`, `e1` use real division, so they are $0$ on a probability-zero signal. $V_0 = 0$ is kept as a hypothesis on a free parameter $C$, not substituted. The paper writes $V_0$ both for $e_0p_0v - C$ and for $V_0(\lambda_v,\lambda_s)$; the latter is `testValue`.
-- source:
--   Agrawal, Gans & Stern, Enabling Entrepreneurial Choice, NBER Working Paper 27379 (June 2020), §2 pp. 6–7, §3.1 p. 9 (signal table, Bayes-law display, (A1)), §3.2–3.3 p. 10 (timeline, V_0(λ_v, λ_s), cases 1–2)

import Mathlib

namespace EntrepChoice.TestChoice

/-- The parameters of the baseline model (§2, pp. 6–7): the prior `p0` that the idea has high
value, the prior `e0` that a given strategy is effective, the value `v` of a high-value idea
implemented with an effective strategy, the implementation cost `C`, and the test cost `c`. -/
structure Params where
  p0 : ℝ
  e0 : ℝ
  v : ℝ
  C : ℝ
  c : ℝ

/-- Standing assumptions of §2: `0 < p₀ < 1`, `0 < e₀ < 1`, `v > 0`,
`V₀ = e₀p₀v − C = 0` (p. 6) and `c < C` (p. 7). -/
structure Standing (P : Params) : Prop where
  p0_pos : 0 < P.p0
  p0_lt_one : P.p0 < 1
  e0_pos : 0 < P.e0
  e0_lt_one : P.e0 < 1
  v_pos : 0 < P.v
  V0_eq_zero : P.e0 * P.p0 * P.v - P.C = 0
  c_lt_C : P.c < P.C

/-- A test with precisions `(λ_v, λ_s)` (§3.1, p. 9). -/
structure Test where
  lv : ℝ
  ls : ℝ

/-- The precisions of a test are probabilities. -/
structure Test.Valid (T : Test) : Prop where
  lv_nonneg : 0 ≤ T.lv
  lv_le_one : T.lv ≤ 1
  ls_nonneg : 0 ≤ T.ls
  ls_le_one : T.ls ≤ 1

/-- Value of the idea: `h` (high) or `l` (low). -/
inductive Idea
  | high
  | low
  deriving DecidableEq

/-- Effectiveness of the tested strategy: `g` (good) or `b` (bad). -/
inductive Strat
  | good
  | bad
  deriving DecidableEq

/-- The four signals `(H,G)`, `(H,B)`, `(L,G)`, `(L,B)` of a test. -/
inductive Sig
  | HG
  | HB
  | LG
  | LB
  deriving DecidableEq

/-- Period-1 actions: implement the tested strategy, switch to (implement) another randomly
selected strategy, or abandon the venture. -/
inductive Act
  | implement
  | switch
  | abandon
  deriving DecidableEq

/-- Prior probability of the state (idea value, tested strategy's effectiveness); the two are
independent (p. 6). -/
def prior (P : Params) : Idea → Strat → ℝ
  | .high, .good => P.p0 * P.e0
  | .high, .bad => P.p0 * (1 - P.e0)
  | .low, .good => (1 - P.p0) * P.e0
  | .low, .bad => (1 - P.p0) * (1 - P.e0)

/-- The signal table of §3.1 (p. 9): probability of each signal in each state. -/
def sigProb (T : Test) : Idea → Strat → Sig → ℝ
  | .high, .good, .HG => 1
  | .low, .good, .LG => T.ls
  | .low, .good, .HB => 1 - T.ls
  | .high, .bad, .HB => T.lv
  | .high, .bad, .LG => 1 - T.lv
  | .low, .bad, .LB => 1
  | _, _, _ => 0

/-- Joint probability of a state and a signal. -/
def joint (P : Params) (T : Test) (i : Idea) (s : Strat) (σ : Sig) : ℝ :=
  prior P i s * sigProb T i s σ

/-- Sum over the four states. -/
def sumStates (f : Idea → Strat → ℝ) : ℝ :=
  f .high .good + f .high .bad + f .low .good + f .low .bad

/-- `Pr(σ)`. -/
def sigMass (P : Params) (T : Test) (σ : Sig) : ℝ :=
  sumStates (fun i s => joint P T i s σ)

/-- `Pr(h, σ)`. -/
def ideaMass (P : Params) (T : Test) (σ : Sig) : ℝ :=
  joint P T .high .good σ + joint P T .high .bad σ

/-- `Pr(tested strategy is g, σ)`. -/
def stratMass (P : Params) (T : Test) (σ : Sig) : ℝ :=
  joint P T .high .good σ + joint P T .low .good σ

/-- Posterior `p₁(σ)` that the idea has high value (Lean's `x / 0 = 0` if `Pr(σ) = 0`). -/
noncomputable def p1 (P : Params) (T : Test) (σ : Sig) : ℝ :=
  ideaMass P T σ / sigMass P T σ

/-- Posterior `e₁(σ)` that the tested strategy is effective (Lean's `x / 0 = 0` if `Pr(σ) = 0`). -/
noncomputable def e1 (P : Params) (T : Test) (σ : Sig) : ℝ :=
  stratMass P T σ / sigMass P T σ

/-- Period-1 payoff of an action in a state. The tested strategy pays `v − C` in `(h, g)` and `−C`
otherwise; another randomly selected strategy is effective with probability `e₀`, independently,
so it pays `e₀v − C` if the idea is high and `−C` if it is low; abandoning pays `0`. -/
def payoff (P : Params) : Act → Idea → Strat → ℝ
  | .implement, .high, .good => P.v - P.C
  | .implement, _, _ => -P.C
  | .switch, .high, _ => P.e0 * P.v - P.C
  | .switch, .low, _ => -P.C
  | .abandon, _, _ => 0

/-- Unnormalized value of an action after signal `σ`: `Pr(σ) · E[payoff | σ]`. -/
def actVal (P : Params) (T : Test) (σ : Sig) (a : Act) : ℝ :=
  sumStates (fun i s => joint P T i s σ * payoff P a i s)

/-- Unnormalized value of the optimal period-1 action after `σ`: `Pr(σ) · V₁(σ)`. -/
noncomputable def bestVal (P : Params) (T : Test) (σ : Sig) : ℝ :=
  max (actVal P T σ .implement) (max (actVal P T σ .switch) (actVal P T σ .abandon))

/-- `V₀(λ_v, λ_s)` (§3.3, p. 10): the period-0 value of testing a strategy, with optimal period-1
actions after each signal, net of the test cost `c`. -/
noncomputable def testValue (P : Params) (T : Test) : ℝ :=
  bestVal P T .HG + bestVal P T .HB + bestVal P T .LG + bestVal P T .LB - P.c

/-- Assumption (A1) (p. 9), cross-multiplied by `Pr(σ)`:
`p₁(H,B) ≥ p₀`, `p₁(L,G) ≤ p₀`, `e₁(H,B) ≤ e₀`, `e₁(L,G) ≥ e₀`. -/
structure A1 (P : Params) (T : Test) : Prop where
  hb_idea : P.p0 * sigMass P T .HB ≤ ideaMass P T .HB
  lg_idea : ideaMass P T .LG ≤ P.p0 * sigMass P T .LG
  hb_strat : stratMass P T .HB ≤ P.e0 * sigMass P T .HB
  lg_strat : P.e0 * sigMass P T .LG ≤ stratMass P T .LG

end EntrepChoice.TestChoice


