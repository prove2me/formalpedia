-- Prove2me | Definitions.Def_ReferralPriority_Optimal_Model
-- name    : ReferralPriority_Optimal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:26.977574+00:00
-- url     : https://prove2.me/theorems/91b1e4f0-c2dc-4962-a5f2-fbe8f5626bc0
-- title:
--   §3–§4, pp. 7–12 — referral waitlist: Problem 1 (IR, IC, OA, stability), the first-best problem, r^FB, r^SB, the cubic g and the priority-scheme predicates
-- statement:
--   The referral waitlist of Yang (§3). A firm's sign-up waitlist is a single-server queue with exponential service of rate $\mu$ (the capacity). Base customers arrive as a Poisson process of rate $\Lambda$, the **base market size**. Each customer values service at $V$ and pays $c$ per unit time in the system. A customer joins with probability $\alpha\in[0,1]$; a joining customer exerts **referral effort** $r\in[0,1]$ at cost $kr$, and with probability $r$ her friend arrives and makes the same decisions. The firm posts the expected delay $W_1$ for customers whose referral succeeded (the friend joined) and $W_0$ for everyone else.
--
--   **Parameters.** $\mu$, $c$, $V$, $k$ are bundled as an environment; $\Lambda$ is a separate argument. The standing assumptions are $\mu>0$, $c>0$, $k>0$ and Assumption 1 (p. 12): $V>c/\mu$.
--
--   **Problem 1** (pp. 11–12). The system throughput is $\Lambda\alpha/(1-r\alpha)$. A joining customer's utility from effort $r'$ is $U(r')=V-kr'-c[r'\alpha W_1+(1-r'\alpha)W_0]$. A tuple $(W_1,W_0,r,\alpha)$ with $W_1,W_0\ge0$ and $r,\alpha\in[0,1]$ is **feasible for Problem 1** if
--   $$\begin{aligned}&U(r)\ge 0 &&\text{(4, IR)}\\ &U(r')\le U(r)\ \text{ for all } r'\in[0,1] &&\text{(5, IC)}\\ &r\alpha W_1+(1-r\alpha)W_0\ge \tfrac{1}{\mu(1-r\alpha)-\Lambda\alpha} &&\text{(6a)}\\ &W_1\ge \tfrac{1}{\mu(1-r\alpha)-\Lambda r\alpha^2} &&\text{(6b)}\\ &W_0\ge \tfrac{1}{\mu-\Lambda\alpha} &&\text{(6c)}\\ &\Lambda\alpha<\mu(1-r\alpha) &&\text{(7)}\end{aligned}$$
--   The **first-best problem** (§4) drops (5). The first best is **achieved** by a Problem-1-feasible tuple whose throughput is the maximum of the first-best problem; a tuple is **optimal in the second best** if it is feasible for Problem 1 and its throughput is the maximum over all Problem-1-feasible tuples.
--
--   **Schemes** (pp. 10–11). A tuple is **work-conserving** if (6a) holds with equality; **full priority** if (6a) and (6b) both hold with equality; **partial priority** if (6a) holds with equality, (6b) does not, and $W_1<W_0$; **strategic delay** if (6a) holds strictly.
--
--   **Closed forms.** The first-best effort of Proposition 1 (i),
--   $$r^{FB}=\frac{-\sqrt{4k\mu(c+\Lambda V-\mu V)+(-k\Lambda+k\mu+\mu V)^2}-k\Lambda+k\mu+\mu V}{2k\mu},$$
--   the partial-priority delays $W_1=\frac{1}{\mu(1-r^{FB})-\Lambda}-\frac{k(1-r^{FB})}{c}$, $W_0=\frac{1}{\mu(1-r^{FB})-\Lambda}+\frac{kr^{FB}}{c}$ of Proposition 4 (i); the second-best effort $r^{SB}=\frac{\mu(V-k)-c}{(V-k)(\mu+\Lambda)}$ with delays $W_1=\frac{1}{\mu(1-r^{SB})-\Lambda r^{SB}}$, $W_0=W_1+k/c$ of Proposition 4 (iii); the cubic $g(r)=(\mu(1-r)^2(V-rk)+rc)(V-k)-c(V-rk)$ and, for a root $r^*$ of $g$, the cutoff $\Lambda^*=\mu(1-r^*)-c/(V-r^*k)$ (proof of Proposition 4).
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** All quantities are real numbers. Stability (7), printed $\Lambda\alpha/(1-r\alpha)<\mu$, is written multiplied out as $\Lambda\alpha<\mu(1-r\alpha)$: the two agree when $r\alpha<1$, and at $r\alpha=1$ the multiplied form is false while Lean's quotient would be $0$. Under (7) every denominator in (6a)–(6c) is positive. The IC constraint is the exact best-response condition over $r'\in[0,1]$, the range implicit in §3. The first-best value is the maximum of the relaxed problem, never the closed form $\Lambda/(1-r^{FB})$. Positivity of $\mu$, $c$, $k$ is added to the standing assumptions; the paper uses it implicitly.
-- source:
--   Yang, Invite your friend and you'll move up in line: optimal design of referral priority programs, accepted manuscript (MSOM 23(5), 2021; eScholarship 2528d4dx), pp. 7–15 (PDF 8–16), §3, §3.1 Problem 1 (3)–(7), Assumption 1, §4, Propositions 1 and 4; Online Appendix p. 2 (PDF 35), proof of Proposition 4 (g and Λ∗)

import Mathlib

namespace ReferralPriority.Optimal

/-- The parameters of the referral waitlist (§3, pp. 7–8): `mu` = µ, the service capacity (exponential
service with mean 1/µ); `c`, the waiting cost per unit time in the system; `V`, the value of service;
`k`, the marginal referral cost (effort `r` costs `k * r`). The base market size Λ (the Poisson arrival
rate of base customers) is not a field: it is a separate argument `Lam` of every definition. -/
structure Env where
  mu : ℝ
  c : ℝ
  V : ℝ
  k : ℝ

/-- Standing assumptions. Assumption 1 (p. 12): V > c/µ. Added (implicit in the paper): µ > 0, c > 0,
k > 0 (capacity and costs are positive; r^FB divides by k). -/
def Env.Standing (E : Env) : Prop :=
  0 < E.mu ∧ 0 < E.c ∧ 0 < E.k ∧ E.c / E.mu < E.V

/-- The system throughput Λα/(1 − rα), the objective (3) of Problem 1 (p. 11). -/
noncomputable def throughput (Lam r α : ℝ) : ℝ :=
  Lam * α / (1 - r * α)

/-- A joining customer's expected utility V − kr′ − c[r′αW1 + (1 − r′α)W0] when she exerts referral effort
`r'` and the other (referred) customers join with probability `α` (p. 8). -/
def payoff (E : Env) (W1 W0 α r' : ℝ) : ℝ :=
  E.V - E.k * r' - E.c * (r' * α * W1 + (1 - r' * α) * W0)

/-- (4), the IR constraint. -/
def IR (E : Env) (W1 W0 r α : ℝ) : Prop :=
  0 ≤ payoff E W1 W0 α r

/-- (5), the IC constraint: `r` maximizes the joining customer's utility over all efforts r′ ∈ [0, 1]. -/
def IC (E : Env) (W1 W0 r α : ℝ) : Prop :=
  ∀ r' ∈ Set.Icc (0 : ℝ) 1, payoff E W1 W0 α r' ≤ payoff E W1 W0 α r

/-- (6a), OA constraint: rαW1 + (1 − rα)W0 ≥ 1/(µ(1 − rα) − Λα). -/
def OA6a (E : Env) (Lam W1 W0 r α : ℝ) : Prop :=
  1 / (E.mu * (1 - r * α) - Lam * α) ≤ r * α * W1 + (1 - r * α) * W0

/-- (6b), OA constraint: W1 ≥ 1/(µ(1 − rα) − Λrα²). -/
def OA6b (E : Env) (Lam W1 r α : ℝ) : Prop :=
  1 / (E.mu * (1 - r * α) - Lam * r * α ^ 2) ≤ W1

/-- (6c), OA constraint: W0 ≥ 1/(µ − Λα). -/
def OA6c (E : Env) (Lam W0 α : ℝ) : Prop :=
  1 / (E.mu - Lam * α) ≤ W0

/-- (7), stability Λα/(1 − rα) < µ, written multiplied out as Λα < µ(1 − rα) (equivalent for rα < 1;
false at rα = 1, where the quotient would take Lean's junk value 0). -/
def Stable (E : Env) (Lam r α : ℝ) : Prop :=
  Lam * α < E.mu * (1 - r * α)

/-- Feasibility in the first-best problem (§4, p. 12): Problem 1 without the IC constraint (5). -/
def FBFeasible (E : Env) (Lam W1 W0 r α : ℝ) : Prop :=
  0 ≤ W1 ∧ 0 ≤ W0 ∧ r ∈ Set.Icc (0 : ℝ) 1 ∧ α ∈ Set.Icc (0 : ℝ) 1 ∧
    IR E W1 W0 r α ∧ OA6a E Lam W1 W0 r α ∧ OA6b E Lam W1 r α ∧ OA6c E Lam W0 α ∧
    Stable E Lam r α

/-- Feasibility in Problem 1 (pp. 11–12), the second-best problem: all of (4), (5), (6a)–(6c), (7). -/
def SBFeasible (E : Env) (Lam W1 W0 r α : ℝ) : Prop :=
  FBFeasible E Lam W1 W0 r α ∧ IC E W1 W0 r α

/-- The throughputs of first-best-feasible tuples. -/
def FBValues (E : Env) (Lam : ℝ) : Set ℝ :=
  {x | ∃ W1 W0 r α, FBFeasible E Lam W1 W0 r α ∧ x = throughput Lam r α}

/-- The throughputs of Problem-1-feasible tuples. -/
def SBValues (E : Env) (Lam : ℝ) : Set ℝ :=
  {x | ∃ W1 W0 r α, SBFeasible E Lam W1 W0 r α ∧ x = throughput Lam r α}

/-- The tuple (W1, W0, r, α) achieves the first best: it is feasible for Problem 1 and its throughput
is the maximum of the first-best problem. -/
def AchievesFB (E : Env) (Lam W1 W0 r α : ℝ) : Prop :=
  SBFeasible E Lam W1 W0 r α ∧ IsGreatest (FBValues E Lam) (throughput Lam r α)

/-- The first best can be achieved: some Problem-1-feasible tuple achieves it. -/
def FBAchievable (E : Env) (Lam : ℝ) : Prop :=
  ∃ W1 W0 r α, AchievesFB E Lam W1 W0 r α

/-- The tuple is optimal in the second best: feasible for Problem 1, with the maximum throughput over all
Problem-1-feasible tuples. -/
def SBOptimal (E : Env) (Lam W1 W0 r α : ℝ) : Prop :=
  SBFeasible E Lam W1 W0 r α ∧ IsGreatest (SBValues E Lam) (throughput Lam r α)

/-- Work-conserving (pp. 10–11): the OA constraint (6a) is binding. -/
def WorkConserving (E : Env) (Lam W1 W0 r α : ℝ) : Prop :=
  r * α * W1 + (1 - r * α) * W0 = 1 / (E.mu * (1 - r * α) - Lam * α)

/-- The OA constraint (6b) is binding. -/
def OA6bBinding (E : Env) (Lam W1 r α : ℝ) : Prop :=
  W1 = 1 / (E.mu * (1 - r * α) - Lam * r * α ^ 2)

/-- Full priority (p. 10): (6a) and (6b) both binding. -/
def FullPriority (E : Env) (Lam W1 W0 r α : ℝ) : Prop :=
  WorkConserving E Lam W1 W0 r α ∧ OA6bBinding E Lam W1 r α

/-- Partial priority (p. 11): (6a) binding, (6b) not binding, and W1 < W0. -/
def PartialPriority (E : Env) (Lam W1 W0 r α : ℝ) : Prop :=
  WorkConserving E Lam W1 W0 r α ∧ ¬ OA6bBinding E Lam W1 r α ∧ W1 < W0

/-- Strategic delay (p. 11): (6a) is not binding. -/
def StrategicDelay (E : Env) (Lam W1 W0 r α : ℝ) : Prop :=
  ¬ WorkConserving E Lam W1 W0 r α

/-- The first-best referral effort of Proposition 1 (i) (p. 12):
r^FB = (−√(4kµ(c + ΛV − µV) + (−kΛ + kµ + µV)²) − kΛ + kµ + µV)/(2kµ). -/
noncomputable def rFB (E : Env) (Lam : ℝ) : ℝ :=
  (-Real.sqrt (4 * E.k * E.mu * (E.c + Lam * E.V - E.mu * E.V) +
      (-E.k * Lam + E.k * E.mu + E.mu * E.V) ^ 2)
    - E.k * Lam + E.k * E.mu + E.mu * E.V) / (2 * E.k * E.mu)

/-- The partial-priority delay W1 = 1/(µ(1 − r^FB) − Λ) − k(1 − r^FB)/c of Proposition 4 (i). -/
noncomputable def W1pp (E : Env) (Lam : ℝ) : ℝ :=
  1 / (E.mu * (1 - rFB E Lam) - Lam) - E.k * (1 - rFB E Lam) / E.c

/-- The partial-priority delay W0 = 1/(µ(1 − r^FB) − Λ) + kr^FB/c of Proposition 4 (i). -/
noncomputable def W0pp (E : Env) (Lam : ℝ) : ℝ :=
  1 / (E.mu * (1 - rFB E Lam) - Lam) + E.k * rFB E Lam / E.c

/-- The second-best referral effort r^SB = (µ(V − k) − c)/((V − k)(µ + Λ)) of Proposition 4 (iii). -/
noncomputable def rSB (E : Env) (Lam : ℝ) : ℝ :=
  (E.mu * (E.V - E.k) - E.c) / ((E.V - E.k) * (E.mu + Lam))

/-- The strategic-delay delay W1 = 1/(µ(1 − r^SB) − Λr^SB) of Proposition 4 (iii). -/
noncomputable def W1sd (E : Env) (Lam : ℝ) : ℝ :=
  1 / (E.mu * (1 - rSB E Lam) - Lam * rSB E Lam)

/-- The strategic-delay delay W0 = W1 + k/c of Proposition 4 (iii). -/
noncomputable def W0sd (E : Env) (Lam : ℝ) : ℝ :=
  W1sd E Lam + E.k / E.c

/-- The cubic g(r) = (µ(1 − r)²(V − rk) + rc)(V − k) − c(V − rk) of the proof of Proposition 4
(Online Appendix p. 2). -/
def gcubic (E : Env) (r : ℝ) : ℝ :=
  (E.mu * (1 - r) ^ 2 * (E.V - r * E.k) + r * E.c) * (E.V - E.k) - E.c * (E.V - r * E.k)

/-- The cutoff Λ∗ = µ(1 − r∗) − c/(V − r∗k) determined by a root r∗ of g (proof of Proposition 4, Online
Appendix p. 2). -/
noncomputable def Lstar (E : Env) (rs : ℝ) : ℝ :=
  E.mu * (1 - rs) - E.c / (E.V - rs * E.k)

end ReferralPriority.Optimal


