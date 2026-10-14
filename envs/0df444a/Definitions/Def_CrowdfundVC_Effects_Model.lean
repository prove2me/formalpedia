-- Prove2me | Definitions.Def_CrowdfundVC_Effects_Model
-- name    : CrowdfundVC_Effects_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:57.636274+00:00
-- url     : https://prove2.me/theorems/eddba47d-d4fb-4bdb-b331-6a4d8d1fa669
-- title:
--   §3, (1), §4–§5, PDF pp. 7–18 — parameters, investment level κ, Bayes updates, VC1's surpluses and decisions, the startup's payoffs, α0, Δa, αᶜ and the expected investment levels
-- statement:
--   This module fixes the model of Hu, Jin and Keppo, *The Crowdfunding Effects on Venture Capital Investment* (§3–§5).
--
--   **Parameters.** A startup needs at least $R_0$ to launch its project, whose revenue is $R_s$ if it succeeds (state $s$) and $R_f$ if it fails (state $f$). Two venture capital firms VC$_1$, VC$_2$ believe that the startup succeeds with probabilities $p_1 \ge p_2$, and the startup itself believes so with probability $p_a$. A crowdfunding campaign with target $K$ produces a signal $\Theta \in \{S, F\}$ with $P(S\mid s) = P(F\mid f) = \tfrac12 + \tfrac{\rho}{2}$, where $\rho$ is the signal's accuracy; $\beta$ is the startup's negotiation power. The startup offers an equity share $\alpha$.
--
--   **Revenues and beliefs.** Under a belief $p$ the expected revenue is $pR_s + (1-p)R_f$; this gives $e_1, e_2, e_a$ under the priors. The probability of the signal $S$ under the belief $p$ is
--   $$P(S\mid p) = p\Big(\tfrac12 + \tfrac\rho2\Big) + (1-p)\Big(\tfrac12 - \tfrac\rho2\Big),$$
--   and $P(F\mid p) = 1 - P(S\mid p)$. The posteriors are the printed closed forms
--   $$\tilde p|S = \frac{(1+\rho)p}{2\rho p + 1 - \rho}, \qquad \tilde p|F = \frac{(1-\rho)p}{-2\rho p + 1 + \rho},$$
--   and $\tilde e_i|\Theta$ is the expected revenue under the posterior of $i \in \{1, 2, a\}$ after $\Theta$.
--
--   **Investment level** (1): for valuations $v_1 \ge v_2$ and a requirement $R$,
--   $$\kappa(v_1, v_2, R) = \begin{cases} 0 & v_1 < R,\\ \beta v_1 + (1-\beta)\max\{v_2, R\} & v_1 \ge R.\end{cases}$$
--
--   **VC$_1$'s decision.** At $t_0$ the valuations are $v_i = \alpha e_i$ and VC$_1$'s surplus from investing is $\pi_1 = v_1 - \kappa(v_1, v_2, R_0)$. After $S$ the share becomes $\alpha' = (R_0-K)\alpha/R_0$ and the requirement $R_0 - K$; after $F$ they stay $\alpha$ and $R_0$. VC$_1$'s surplus at $t_1$ after $\Theta$ is $\tilde v_1|\Theta - \kappa(\tilde v_1|\Theta, \tilde v_2|\Theta, R)$ if $\tilde v_1|\Theta \ge R$ and $0$ otherwise, where $\tilde v_i|S = \alpha'\tilde e_i|S$ and $\tilde v_i|F = \alpha\tilde e_i|F$. Its expected surplus from waiting is $\tilde\pi_1 = P(S\mid p_1)\tilde\pi_1|S + P(F\mid p_1)\tilde\pi_1|F$ and its value of waiting is $\Delta_1 = \tilde\pi_1 - \pi_1$. VC$_1$ invests at $t_0$ iff $v_1 \ge R_0$ and $\Delta_1 \le 0$ (ties favour investing now); otherwise it invests at $t_1$ after $S$ iff $\alpha'\tilde e_1|S \ge R_0 - K$, and after $F$ iff $\alpha\tilde e_1|F \ge R_0$. Without crowdfunding VC$_1$ invests iff $v_1 \ge R_0$.
--
--   **Thresholds** of Proposition 2, as printed:
--   $$T_1 = \frac{R_0}{e_1 - P(S\mid p_1)\frac{R_0-K}{R_0}(\tilde e_1|S - \tilde e_2|S)}, \qquad T_2 = \frac{R_0 - P(S\mid p_1)(R_0-K)}{e_1 - P(S\mid p_1)\,\tilde e_1|S\,\frac{R_0-K}{R_0}},$$
--   and $\alpha_0 = T_2$ if $\tilde e_2|S \le R_0/T_2$, $\alpha_0 = T_1$ otherwise.
--
--   **The startup.** Its payoff without crowdfunding is $(1-\alpha)e_a$ if VC$_1$ invests and $0$ otherwise. With crowdfunding it is $(1-\alpha)e_a$ if VC$_1$ invests at $t_0$, and otherwise $P(S\mid p_a)\,(1-\alpha')\tilde e_a|S$ (if VC$_1$ invests after $S$) plus $P(F\mid p_a)\,(1-\alpha)\tilde e_a|F$ (if VC$_1$ invests after $F$). Further,
--   $$\pi_a = (1-\alpha_0)e_a, \qquad \tilde\pi_a = \Big(1 - \frac{R_0-K}{\tilde e_1|S}\Big)\tilde e_a|S\cdot P(S\mid p_a), \qquad \Delta_a = \tilde\pi_a - \pi_a,$$
--   and $\alpha^c = \alpha_0$ if $\Delta_a \le 0$, $\alpha^c = R_0/\tilde e_1|S$ if $\Delta_a > 0$.
--
--   **Investment levels.** Without crowdfunding the level at the share $\alpha$ is $\kappa(v_1, v_2, R_0)$. With crowdfunding, the expected level with respect to the unconditional belief $P(\theta = s) = \tfrac12$ is $\kappa(v_1, v_2, R_0)$ if VC$_1$ invests at $t_0$, and otherwise
--   $$P(S\mid \tfrac12)\,\kappa(\tilde v_1|S, \tilde v_2|S, R_0 - K) + P(F\mid \tfrac12)\,\kappa(\tilde v_1|F, \tilde v_2|F, R_0).$$
--
--   Every result of the paper is a statement about these objects: Propositions 1–6 and Corollaries 1–2 characterize VC$_1$'s decision, the startup's optimal share and the investment level they produce.
--
--   **Formalization Note** The parameters are a plain record of nine reals; all assumptions on them appear as explicit hypotheses of the theorems. A VC that cannot meet the requirement after a signal gets surplus $0$ (the printed $\max\{\tilde v_1|\Theta - \kappa, 0\}$ would give it $\tilde v_1|\Theta$, since $\kappa = 0$ there; the paper's proof of Proposition 2 uses $0$). $P(S\mid p)$ is not printed in the paper; it is the mixture implied by the signal's accuracy. VC$_1$'s decisions, the startup's payoffs and the investment levels are defined from the surpluses and from $\kappa$; the paper's closed forms for the threshold, the startup's objective and the investment level are theorems, not definitions. Lean's division by zero returns $0$; the posterior denominators vanish only at $\rho = 1$ with $p \in \{0, 1\}$, where the value is either correct or multiplied by a zero probability.
-- source:
--   Hu, Jin & Keppo, The Crowdfunding Effects on Venture Capital Investment, SSRN author manuscript (abstract 3512638, 2024-03-15; Management Science DOI 10.1287/mnsc.2022.00994), PDF pp. 7–18: §3 (model, (1), signal, timeline, Assumption (I)), §4 (p. 12), §5.1 (Bayes update, surpluses, Δ1, p. 13–14), Proposition 2 (T1, T2, α0, p. 14), §5.2 (πa, π̃a, p. 18), Proposition 4 (Δa, αᶜ); expected investment level from the proof of Proposition 6, Online Appendix D, PDF p. 52 (OA p. 25); surplus convention from the proof of Proposition 2, PDF p. 44 (OA p. 17)

import Mathlib

namespace CrowdfundVC.Effects

/-- The exogenous parameters of §3 (Hu, Jin & Keppo, pp. 7–11). Data only: every assumption on
them is stated explicitly on the theorems that use it.
* `Rs`, `Rf` : the project's revenue if the startup succeeds (state `s`) or fails (state `f`);
* `R0` : the startup's minimum funding requirement;
* `K` : the crowdfunding target (funds collected when the campaign succeeds);
* `ρ` : the accuracy of the crowdfunding signal;
* `β` : the startup's negotiation power relative to the VC firms;
* `p1`, `p2` : the prior beliefs of VC1 and VC2 that the startup succeeds;
* `pa` : the startup's own prior belief that it succeeds. -/
structure Params where
  Rs : ℝ
  Rf : ℝ
  R0 : ℝ
  K : ℝ
  ρ : ℝ
  β : ℝ
  p1 : ℝ
  p2 : ℝ
  pa : ℝ

/-- The investment level (1), p. 8: `κ(v1, v2, R) = 0` if `v1 < R`, and
`β v1 + (1 − β) max{v2, R}` if `v1 ≥ R`. -/
noncomputable def kappa (β v1 v2 R : ℝ) : ℝ :=
  if v1 < R then 0 else β * v1 + (1 - β) * max v2 R

/-- The project's expected revenue under the belief `p` that the startup succeeds:
`p Rs + (1 − p) Rf` (pp. 7–8 and p. 13). -/
def rev (P : Params) (p : ℝ) : ℝ := p * P.Rs + (1 - p) * P.Rf

/-- The Bayes posterior after the signal `S`, as printed on p. 13: `p̃|S = (1 + ρ)p / (2ρp + 1 − ρ)`. -/
noncomputable def postS (P : Params) (p : ℝ) : ℝ := (1 + P.ρ) * p / (2 * P.ρ * p + 1 - P.ρ)

/-- The Bayes posterior after the signal `F`, as printed on p. 13: `p̃|F = (1 − ρ)p / (−2ρp + 1 + ρ)`. -/
noncomputable def postF (P : Params) (p : ℝ) : ℝ := (1 - P.ρ) * p / (-2 * P.ρ * p + 1 + P.ρ)

/-- `P(S|p)`, the probability of the signal `S` under the belief `p`, from
`P(S|s) = 1/2 + ρ/2` and `P(S|f) = 1/2 − ρ/2` (p. 9). The probability of `F` is `1 − P(S|p)`. -/
noncomputable def probS (P : Params) (p : ℝ) : ℝ := p * (1 / 2 + P.ρ / 2) + (1 - p) * (1 / 2 - P.ρ / 2)

/-- `e1`, `e2`, `ea`: expected revenues under the priors of VC1, VC2 and the startup (pp. 7–8). -/
def e1 (P : Params) : ℝ := rev P P.p1
def e2 (P : Params) : ℝ := rev P P.p2
def ea (P : Params) : ℝ := rev P P.pa

/-- `ẽ1|S`, `ẽ2|S`, `ẽa|S`: expected revenues under the posteriors after `S` (p. 13). -/
noncomputable def e1S (P : Params) : ℝ := rev P (postS P P.p1)
noncomputable def e2S (P : Params) : ℝ := rev P (postS P P.p2)
noncomputable def eaS (P : Params) : ℝ := rev P (postS P P.pa)

/-- `ẽ1|F`, `ẽ2|F`, `ẽa|F`: expected revenues under the posteriors after `F` (p. 13). -/
noncomputable def e1F (P : Params) : ℝ := rev P (postF P P.p1)
noncomputable def e2F (P : Params) : ℝ := rev P (postF P P.p2)
noncomputable def eaF (P : Params) : ℝ := rev P (postF P P.pa)

/-- The equity share after a successful campaign, `α′ = (R0 − K)α / R0` (pp. 10, 13). -/
noncomputable def alphaS (P : Params) (α : ℝ) : ℝ := (P.R0 - P.K) * α / P.R0

/-- VC1's surplus from investing at `t0`, `π1 = v1 − κ(v1, v2, R0)` with `vi = α ei` (p. 13). It is
used only when VC1 can invest (`v1 ≥ R0`), see `investsAt0`. -/
noncomputable def pi1 (P : Params) (α : ℝ) : ℝ :=
  α * e1 P - kappa P.β (α * e1 P) (α * e2 P) P.R0

/-- VC1's surplus at `t1` after the signal `S` (p. 13 and the proof of Proposition 2, PDF 44): the
valuation `ṽ1|S = α′ ẽ1|S` minus the investment level `κ(ṽ1|S, ṽ2|S, R0 − K)` when
`ṽ1|S ≥ R0 − K`, and `0` when VC1 cannot meet the requirement `R0 − K`. -/
noncomputable def pi1S (P : Params) (α : ℝ) : ℝ :=
  if alphaS P α * e1S P < P.R0 - P.K then 0
  else alphaS P α * e1S P - kappa P.β (alphaS P α * e1S P) (alphaS P α * e2S P) (P.R0 - P.K)

/-- VC1's surplus at `t1` after the signal `F` (p. 13 and the proof of Proposition 2, PDF 45): the
valuation `ṽ1|F = α ẽ1|F` minus `κ(ṽ1|F, ṽ2|F, R0)` when `ṽ1|F ≥ R0`, and `0` otherwise. -/
noncomputable def pi1F (P : Params) (α : ℝ) : ℝ :=
  if α * e1F P < P.R0 then 0
  else α * e1F P - kappa P.β (α * e1F P) (α * e2F P) P.R0

/-- VC1's expected surplus from waiting, `π̃1 = P(S|p1) π̃1|S + P(F|p1) π̃1|F` (p. 13). -/
noncomputable def pi1Tilde (P : Params) (α : ℝ) : ℝ :=
  probS P P.p1 * pi1S P α + (1 - probS P P.p1) * pi1F P α

/-- VC1's value of waiting, `Δ1 = π̃1 − π1` (p. 14). -/
noncomputable def delta1 (P : Params) (α : ℝ) : ℝ := pi1Tilde P α - pi1 P α

/-- Without crowdfunding, VC1 invests iff its valuation meets the requirement, `v1 ≥ R0` (p. 12). -/
def investsNoCF (P : Params) (α : ℝ) : Prop := P.R0 ≤ α * e1 P

/-- With crowdfunding, VC1 invests at `t0` iff it can (`v1 ≥ R0`) and does not prefer to wait
(`Δ1 ≤ 0`; ties are broken in favour of investing now, p. 14). -/
def investsAt0 (P : Params) (α : ℝ) : Prop := P.R0 ≤ α * e1 P ∧ delta1 P α ≤ 0

/-- At `t1` after `S`, VC1 invests iff `ṽ1|S = α′ ẽ1|S ≥ R0 − K` (pp. 13, 15). -/
def investsAfterS (P : Params) (α : ℝ) : Prop := P.R0 - P.K ≤ alphaS P α * e1S P

/-- At `t1` after `F`, VC1 invests iff `ṽ1|F = α ẽ1|F ≥ R0` (pp. 13, 15). -/
def investsAfterF (P : Params) (α : ℝ) : Prop := P.R0 ≤ α * e1F P

/-- `T1` of Proposition 2 (p. 14), as printed:
`T1 = R0 / (e1 − P(S|p1) ((R0 − K)/R0) (ẽ1|S − ẽ2|S))`. -/
noncomputable def T1 (P : Params) : ℝ :=
  P.R0 / (e1 P - probS P P.p1 * ((P.R0 - P.K) / P.R0) * (e1S P - e2S P))

/-- `T2` of Proposition 2 (p. 14), as printed:
`T2 = (R0 − P(S|p1)(R0 − K)) / (e1 − P(S|p1) ẽ1|S ((R0 − K)/R0))`. -/
noncomputable def T2 (P : Params) : ℝ :=
  (P.R0 - probS P P.p1 * (P.R0 - P.K)) / (e1 P - probS P P.p1 * e1S P * ((P.R0 - P.K) / P.R0))

/-- `α0` of Proposition 2 (p. 14), as printed: `α0 = T2` if `ẽ2|S ≤ R0/T2`, and `T1` otherwise. -/
noncomputable def alpha0 (P : Params) : ℝ := if e2S P ≤ P.R0 / T2 P then T2 P else T1 P

open scoped Classical in
/-- The startup's anticipated payoff without crowdfunding, with respect to its own belief (p. 12):
`(1 − α) ea` if VC1 invests, and `0` otherwise. -/
noncomputable def payoffNoCF (P : Params) (α : ℝ) : ℝ :=
  if investsNoCF P α then (1 - α) * ea P else 0

open scoped Classical in
/-- The startup's anticipated payoff with crowdfunding, with respect to its own belief, computed from
VC1's responses (§5.1–5.2): `(1 − α) ea` if VC1 invests at `t0`; otherwise, with probability
`P(S|pa)` the campaign succeeds and the startup gets `(1 − α′) ẽa|S` if VC1 then invests, and with
probability `P(F|pa)` it fails and the startup gets `(1 − α) ẽa|F` if VC1 then invests. -/
noncomputable def payoffCF (P : Params) (α : ℝ) : ℝ :=
  if investsAt0 P α then (1 - α) * ea P
  else probS P P.pa * (if investsAfterS P α then (1 - alphaS P α) * eaS P else 0)
     + (1 - probS P P.pa) * (if investsAfterF P α then (1 - α) * eaF P else 0)

/-- The startup's payoff from inducing investment at `t0`, `πa = (1 − α0) ea` (p. 18). -/
noncomputable def piA (P : Params) : ℝ := (1 - alpha0 P) * ea P

/-- The startup's payoff from inducing investment after a successful campaign,
`π̃a = (1 − (R0 − K)/ẽ1|S) ẽa|S · P(S|pa)` (p. 18). -/
noncomputable def piATilde (P : Params) : ℝ := (1 - (P.R0 - P.K) / e1S P) * eaS P * probS P P.pa

/-- The startup's value of waiting, `Δa = π̃a − πa` (Proposition 4, p. 18). -/
noncomputable def deltaA (P : Params) : ℝ := piATilde P - piA P

/-- The equity share `αᶜ` of Proposition 4 (p. 18): `α0` if `Δa ≤ 0`, and `R0/ẽ1|S` if `Δa > 0`. -/
noncomputable def alphaC (P : Params) : ℝ := if deltaA P ≤ 0 then alpha0 P else P.R0 / e1S P

/-- The VC investment level without crowdfunding at the equity share `α`: `κ(v1, v2, R0)`, which is
`0` exactly when VC1 does not invest (`v1 < R0`) (p. 12; proof of Proposition 6, PDF 52). -/
noncomputable def invLevelNoCF (P : Params) (α : ℝ) : ℝ := kappa P.β (α * e1 P) (α * e2 P) P.R0

open scoped Classical in
/-- The expected VC investment level with crowdfunding at the equity share `α`, with respect to the
unconditional belief `P(θ = s) = P(θ = f) = 1/2` (proof of Proposition 6, PDF 52), along VC1's
decisions: `κ(v1, v2, R0)` if VC1 invests at `t0`; otherwise the average, with the probabilities
`P(S|1/2)` and `P(F|1/2)`, of the levels `κ(ṽ1|S, ṽ2|S, R0 − K)` and `κ(ṽ1|F, ṽ2|F, R0)` at `t1`
(each `0` when VC1 does not invest after that signal). -/
noncomputable def invLevelCF (P : Params) (α : ℝ) : ℝ :=
  if investsAt0 P α then kappa P.β (α * e1 P) (α * e2 P) P.R0
  else probS P (1 / 2) * kappa P.β (alphaS P α * e1S P) (alphaS P α * e2S P) (P.R0 - P.K)
     + (1 - probS P (1 / 2)) * kappa P.β (α * e1F P) (α * e2F P) P.R0

end CrowdfundVC.Effects


