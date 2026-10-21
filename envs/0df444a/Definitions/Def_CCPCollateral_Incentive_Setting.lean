-- Prove2me | Definitions.Def_CCPCollateral_Incentive_Setting
-- name    : CCPCollateral_Incentive_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:21:35.047244+00:00
-- url     : https://prove2.me/theorems/fdeaa4f1-803c-4188-85dc-944f5ed61df9
-- title:
--   §2–§3.3, (8)–(9), (13)–(14), (16), (18), (A2), (A3), (A13)–(A14), (A18), (A29) — CCP model: member value, loss-sharing cost X^g, hedging game, IC cutoff F̂(I), Î(0), H(l)
-- statement:
--   **Primitives** (§2, pp. 7–13). There are $N$ clearing members (dealers). A credit event occurs with probability $p_c$. Each member holds a risky asset and chooses an action $a\in\{s,r\}$: hedging $s$ (prudent risk management) or risk-shifting $r$. Under action $a$ the asset returns $0$ in the bad state, which has probability $q_a$, and $R_a$ in the good state; its expected return is $\mu_a=(1-q_a)R_a$. Every member owes $D$ to protection buyers in a credit event and has initial assets $A_0$. Buyers have risk aversion $\gamma$, and the centrally cleared price (8) and the balance-sheet size are
--   $$P_{CCP}=p_cD\bigl(1+\gamma D(1-p_c)\bigr),\qquad A_{CCP}=A_0+P_{CCP}.$$
--   The **pledgeability** (9) is $\mathcal P=(\mu_s-\mu_r)/(p_c(q_r-q_s))$. A member posts initial margin $I$ and default fund $F$; $\delta$ is the extra unit cost of default-fund posting and $\alpha$ the unit financing cost of ex-post loss-sharing contributions.
--
--   **Standing assumptions**, one per label: $0<p_c<1$, $A_0>D$, $\gamma>0$, $\delta>0$; (1) $0<q_s<q_r$, $R_s<R_r$; (2) $\mu_s>\mu_r>1$; (3) $0<\alpha<(\mu_s-1)/(p_cq_s)$; Assumption 1, $\gamma>\underline\gamma$ with $\underline\gamma$ the explicit quotient (A18) built from $\Theta=\mu_s-1+p_c-p_c(1-q_s)\mathcal P$ and $\Delta=(1+\alpha)(q_s-q_s^N)/(1-q_s)$; Assumption 2 (9), $\mathcal P<D/A_{CCP}$. In addition $N\ge 2$, $D>0$ and $q_r<1$.
--
--   **Default law and loss-sharing cost.** When $g$ of the other $N-1$ members hedge, the number $\mathcal N_d$ of defaults among them has law (A29),
--   $$f^g(k)=\sum_{j=0}^{k}\binom{g}{j}q_s^j(1-q_s)^{g-j}\binom{N-1-g}{k-j}q_r^{k-j}(1-q_r)^{N-1-g-(k-j)},$$
--   and the expected loss-sharing contribution plus financing cost (14), (16) of a surviving member is
--   $$X^g(I,F)=\sum_{k=0}^{N-1}f^g(k)\left[\frac{k(D-I-F)}{N-k}+\alpha\Bigl(\frac{k(D-I-F)}{N-k}-F\Bigr)^+\right].$$
--   The member value (13) of a member taking action $a$ when $g$ others hedge is
--   $$V(a,g;I,F)=-\delta F+(1-p_c)(I+F)+(1-q_a)\bigl[(A_{CCP}-I-F)R_a-p_c(D-I-F+X^g(I,F))\bigr].$$
--
--   **The hedging game.** A profile assigns an action to each of the $N$ members; member $i$ earns $V(a_i,g_i;I,F)$ where $g_i$ is the number of other members who hedge. A (pure-strategy) **Nash equilibrium** is a profile from which no member gains by a unilateral change of action; a **Pareto-dominant Nash equilibrium** is a Nash equilibrium that gives every member at least its payoff in any Nash equilibrium.
--
--   **Cutoffs.** The hedging condition (A2) when $g$ others hedge is $D-I-F+X^g(I,F)\le(A_{CCP}-I-F)\mathcal P$; equation (18) is this condition with equality at $g=N-1$, and (A3) at $g=0$. The cutoff $\hat F(I)$ is the least $F\in[0,D-I]$ satisfying the hedging condition with $g=N-1$, $\bar F(I)$ the least with $g=0$, and $\hat I(0)$ the least $I\in[0,D]$ satisfying it with $g=N-1$ and $F=0$. The setting also records the slope ratio
--   $$H(l)=\frac{\alpha\,\mathbb E^s[\mathbb 1_{\mathcal N_d\ge l}]}{\mathbb E^s\!\left[\frac{N}{N-\mathcal N_d}\right]-\mathcal P+\alpha\,\mathbb E^s\!\left[\frac{N}{N-\mathcal N_d}\mathbb 1_{\mathcal N_d\ge l}\right]}$$
--   of (A7), (A9), (A10), with $\mathbb E^s$ the expectation under $f^{N-1}$, and the step functions $y_l^{(N)}(q_s)$, $z_l^{(N)}(q_s)$ of (A13)–(A14).
--
--   These objects carry every statement of the mission: Proposition 2 characterizes the hedging equilibrium through $\hat F$ and describes $\hat F$ as a function of $I$.
--
--   **Formalization Note** Members are `Fin N`; all quantities are real. The expectation in (14) is written as the finite sum against $f^g$ of (A29), which is the paper's statement (16) that $X$ depends on the others' actions only through the number $g$ of hedgers. Natural-number subtractions in the exponents of (A29) only truncate where the binomial coefficient in front is zero. $\hat F(I)$, $\bar F(I)$ and $\hat I(0)$ are infima of sets that are bounded below by $0$ and contain $F=D-I$ (resp. $I=D$), so they never take the junk value of an empty infimum. The Nash equilibrium is the published generic pure-Nash relation `CarbonDoubleCount.Planner.IsPureNash` with every action feasible. $\underline\gamma$ is the literal real quotient of (A18); $N\ge2$, $D>0$, $q_r<1$ are not stated on the page and are added because the model degenerates without them ($X\equiv0$ when $N=1$).
-- source:
--   Wang, Capponi & Zhang, A Theory of Collateral Requirements for Central Counterparties, author's manuscript (2021; Management Sci. doi:10.1287/mnsc.2021.4145), §2 (1)–(3), (8)–(9), Assumptions 1–2, pp. 7–13; §3.2 (13)–(14), p. 15; (16), (18), p. 19; Appendix (A2)–(A3), p. 45, (A7), p. 46, (A13)–(A14), p. 48, (A18), p. 49; Online Appendix (A29), p. OA-1

import Mathlib
import Definitions.Def_CarbonDoubleCount_Planner_PureGame

namespace CCPCollateral.Incentive

/-- A clearing member's risk-management action (§2, p. 8): `s` hedges (prudent risk management),
`r` risk-shifts. -/
inductive Action
  | s
  | r
  deriving DecidableEq

/-- The primitives of the model (§2, pp. 7–13): the number of clearing members `N`, the probability
`pc` of the credit event, the bad-state probabilities `qs`, `qr` and good-state returns `Rs`, `Rr` of
the hedged and the risk-shifted asset, the buyers' risk aversion `γ`, the exposure `D`, the initial
assets `A0`, the unit financing cost `α` of end-of-waterfall contributions, and the unit cost `δ` of
default-fund posting. -/
structure Params where
  N : ℕ
  pc : ℝ
  qs : ℝ
  qr : ℝ
  Rs : ℝ
  Rr : ℝ
  γ : ℝ
  D : ℝ
  A0 : ℝ
  α : ℝ
  δ : ℝ

namespace Params

variable (m : Params)

/-- Bad-state probability `q_a` of action `a` (p. 8). -/
def q : Action → ℝ
  | .s => m.qs
  | .r => m.qr

/-- Good-state return `R_a` of action `a` (p. 8). -/
def R : Action → ℝ
  | .s => m.Rs
  | .r => m.Rr

/-- Expected return `µ_a = (1 − q_a) R_a` (p. 9). -/
def mu (a : Action) : ℝ := (1 - m.q a) * m.R a

/-- The centrally cleared price (8): `P_CCP = p_c D (1 + γ D (1 − p_c))`. -/
def Pccp : ℝ := m.pc * m.D * (1 + m.γ * m.D * (1 - m.pc))

/-- Balance-sheet size of a centrally clearing dealer (p. 13): `A_CCP = A_0 + P_CCP`. -/
def Accp : ℝ := m.A0 + m.Pccp

/-- The asset pledgeability 𝒫 of (9): `𝒫 = (µ_s − µ_r) / (p_c (q_r − q_s))`. -/
noncomputable def pledge : ℝ := (m.mu .s - m.mu .r) / (m.pc * (m.qr - m.qs))

/-- `Θ = µ_s − 1 + p_c − p_c (1 − q_s) 𝒫` (p. 23). -/
noncomputable def Theta : ℝ := m.mu .s - 1 + m.pc - m.pc * (1 - m.qs) * m.pledge

/-- `Δ = (1 + α)(q_s − q_s^N)/(1 − q_s)` (p. 49). -/
noncomputable def Delta : ℝ := (1 + m.α) * (m.qs - m.qs ^ m.N) / (1 - m.qs)

/-- The risk-aversion bound γ̲ of (A18) (p. 49), transcribed literally as a real quotient. -/
noncomputable def gammaLow : ℝ :=
  ((1 / (1 - m.pledge) - (m.Delta + 1) / (m.Delta + 1 - m.pledge)) * m.Theta * (m.A0 - m.D)
      - ((m.Delta + 1) * m.Theta / (m.Delta + 1 - m.pledge)
          - m.Theta * (1 - m.qs) / (1 - m.pledge) + (1 - m.pc) * m.qs) * m.pc * m.D)
    / (((1 - m.pc + (m.Delta + 1) * m.Theta / (m.Delta + 1 - m.pledge)) * (1 - m.pc)
          - (m.Theta / (1 - m.pledge) + 1 - m.pc) * (1 - m.qs) * (1 - m.pc - m.pc * m.qs))
        * m.pc * m.D ^ 2)

/-- The law (A29) of the number `k` of defaults among the `N − 1` other members when `g` of them
hedge: `f^g(k) = Σ_{j=0}^{k} C(g,j) q_s^j (1−q_s)^{g−j} C(N−1−g,k−j) q_r^{k−j} (1−q_r)^{N−1−g−(k−j)}`.
(Whenever a natural-number subtraction in an exponent truncates, the binomial coefficient in front
of it is zero.) -/
noncomputable def defaultLaw (g k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    (g.choose j : ℝ) * m.qs ^ j * (1 - m.qs) ^ (g - j) *
      ((m.N - 1 - g).choose (k - j) : ℝ) * m.qr ^ (k - j) * (1 - m.qr) ^ (m.N - 1 - g - (k - j))

/-- The expected loss-sharing contribution and financing cost (14) of a surviving member when `g` of
the other `N − 1` members hedge, i.e. `X^g(I, F)` of (16):
`X^g(I,F) = Σ_{k=0}^{N−1} f^g(k) [k(D−I−F)/(N−k) + α (k(D−I−F)/(N−k) − F)^+]`. -/
noncomputable def X (g : ℕ) (I F : ℝ) : ℝ :=
  ∑ k ∈ Finset.range m.N, m.defaultLaw g k *
    ((k : ℝ) * (m.D - I - F) / ((m.N : ℝ) - k) +
      m.α * max ((k : ℝ) * (m.D - I - F) / ((m.N : ℝ) - k) - F) 0)

/-- The member value (13) of a member taking action `a` when `g` of the other members hedge:
`V = −δF + (1 − p_c)(I + F) + (1 − q_a)[(A_CCP − I − F) R_a − p_c (D − I − F + X^g(I, F))]`. -/
noncomputable def V (a : Action) (g : ℕ) (I F : ℝ) : ℝ :=
  -m.δ * F + (1 - m.pc) * (I + F) +
    (1 - m.q a) * ((m.Accp - I - F) * m.R a - m.pc * (m.D - I - F + m.X g I F))

/-- The number of members other than `i` who hedge in the profile `a`. -/
def hedgers (a : Fin m.N → Action) (i : Fin m.N) : ℕ :=
  (Finset.univ.filter (fun j => j ≠ i ∧ a j = Action.s)).card

/-- Member `i`'s expected profit (13) in the profile `a`. -/
noncomputable def payoff (I F : ℝ) (a : Fin m.N → Action) (i : Fin m.N) : ℝ :=
  m.V (a i) (m.hedgers a i) I F

/-- Pure-strategy Nash equilibrium of the `N`-member hedging game under collateral `(I, F)`
(the published `CarbonDoubleCount.Planner.IsPureNash`, every action feasible). -/
def IsNash (I F : ℝ) (a : Fin m.N → Action) : Prop :=
  CarbonDoubleCount.Planner.IsPureNash (strategy := fun _ : Fin m.N => Action)
    (fun _ => Set.univ) (fun i b => m.payoff I F b i) a

/-- A Pareto-dominant Nash equilibrium: a Nash equilibrium that gives every member at least the
payoff it gets in any Nash equilibrium. -/
def IsParetoDominantNash (I F : ℝ) (a : Fin m.N → Action) : Prop :=
  m.IsNash I F a ∧ ∀ b, m.IsNash I F b → ∀ i, m.payoff I F b i ≤ m.payoff I F a i

/-- The hedging (incentive-compatibility) condition (A2) when `g` other members hedge:
`D − I − F + X^g(I, F) ≤ (A_CCP − I − F) 𝒫`. -/
def IsIC (g : ℕ) (I F : ℝ) : Prop :=
  m.D - I - F + m.X g I F ≤ (m.Accp - I - F) * m.pledge

/-- Equation (18): `D − I − F + X^{N−1}(I, F) = (A_CCP − I − F) 𝒫`. -/
def Eq18 (I F : ℝ) : Prop :=
  m.D - I - F + m.X (m.N - 1) I F = (m.Accp - I - F) * m.pledge

/-- Equation (A3): `D − I − F + X^0(I, F) = (A_CCP − I − F) 𝒫`. -/
def EqA3 (I F : ℝ) : Prop :=
  m.D - I - F + m.X 0 I F = (m.Accp - I - F) * m.pledge

/-- `F̂(I)`: the least default fund in `[0, D − I]` that makes hedging a best response when all
other members hedge. For `I ≤ D` the set contains `F = D − I`. -/
noncomputable def Fhat (I : ℝ) : ℝ :=
  sInf {F | 0 ≤ F ∧ F ≤ m.D - I ∧ m.IsIC (m.N - 1) I F}

/-- `F̄(I)`: the least default fund in `[0, D − I]` that makes hedging a best response when no
other member hedges. For `I ≤ D` the set contains `F = D − I`. -/
noncomputable def Fbar (I : ℝ) : ℝ :=
  sInf {F | 0 ≤ F ∧ F ≤ m.D - I ∧ m.IsIC 0 I F}

/-- `Î(0)`: the least initial margin in `[0, D]` that makes hedging a best response when all other
members hedge and `F = 0` (p. 24: "the value of initial margin when setting F = 0 in Eq. (18)").
The set contains `I = D`. -/
noncomputable def Ihat0 : ℝ :=
  sInf {I | 0 ≤ I ∧ I ≤ m.D ∧ m.IsIC (m.N - 1) I 0}

/-- The right-hand side of (A7), (A9), (A10) at `l` (the paper's `H(l)`, p. 24):
`α E^s[1{k ≥ l}] / (E^s[N/(N − k)] − 𝒫 + α E^s[N/(N − k) 1{k ≥ l}])`, with `E^s` the law
`f^{N−1}`. -/
noncomputable def H (l : ℕ) : ℝ :=
  m.α * (∑ k ∈ (Finset.range m.N).filter (fun k => l ≤ k), m.defaultLaw (m.N - 1) k) /
    ((∑ k ∈ Finset.range m.N, m.defaultLaw (m.N - 1) k * m.N / ((m.N : ℝ) - k)) - m.pledge +
      m.α * ∑ k ∈ (Finset.range m.N).filter (fun k => l ≤ k),
        m.defaultLaw (m.N - 1) k * m.N / ((m.N : ℝ) - k))

/-- `y_l^{(N)}(q_s)` of (A13): `Σ_{k=l}^{N−1} C(N−1,k) q_s^k (1−q_s)^{N−1−k} N/(N−k)`. -/
noncomputable def y (l : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range m.N).filter (fun k => l ≤ k),
    ((m.N - 1).choose k : ℝ) * m.qs ^ k * (1 - m.qs) ^ (m.N - 1 - k) * (m.N / ((m.N : ℝ) - k))

/-- `z_l^{(N)}(q_s)` of (A14): `Σ_{k=l}^{N−1} C(N−1,k) q_s^k (1−q_s)^{N−1−k}`. -/
noncomputable def z (l : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range m.N).filter (fun k => l ≤ k),
    ((m.N - 1).choose k : ℝ) * m.qs ^ k * (1 - m.qs) ^ (m.N - 1 - k)

end Params

/-- The standing assumptions of the paper (§2, pp. 7–13), one field per label, plus the disclosed
`N ≥ 2`, `D > 0`, `q_r < 1`. -/
structure Standing (m : Params) : Prop where
  two_le_N : 2 ≤ m.N
  D_pos : 0 < m.D
  A0_gt_D : m.D < m.A0
  pc_mem : 0 < m.pc ∧ m.pc < 1
  cond1 : 0 < m.qs ∧ m.qs < m.qr ∧ m.Rs < m.Rr
  qr_lt_one : m.qr < 1
  cond2 : 1 < m.mu .r ∧ m.mu .r < m.mu .s
  cond3 : 0 < m.α ∧ m.α < (m.mu .s - 1) / (m.pc * m.qs)
  γ_pos : 0 < m.γ
  δ_pos : 0 < m.δ
  assumption1 : m.gammaLow < m.γ
  assumption2 : m.pledge < m.D / m.Accp

end CCPCollateral.Incentive


