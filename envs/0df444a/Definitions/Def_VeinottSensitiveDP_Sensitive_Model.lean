-- Prove2me | Definitions.Def_VeinottSensitiveDP_Sensitive_Model
-- name    : VeinottSensitiveDP_Sensitive_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:59.179977+00:00
-- url     : https://prove2.me/theorems/442f7191-974a-4381-8cbb-10122ec99cac
-- title:
--   §2/§4 model: states, action sets A_s, rewards r(s,a), substochastic p(t|s,a), policies, Pᴺ(π), transient policies, Q, P*, H, V_ρ(π), v_ρ(g,π)
-- statement:
--   A system is observed at times $1,2,\dots$ in one of finitely many states $s$ (the paper's $1,\dots,S$) or "stopped". In state $s$ an action $a$ is chosen from a finite nonempty set $A_s$, a reward $r(s,a)$ of any sign is received, and the system moves to state $t$ with probability $p(t\mid s,a)\ge 0$, where $\sum_t p(t\mid s,a)\le 1$; the missing mass is the probability of stopping.
--
--   1. A **decision rule** is $f\in F=\times_s A_s$; a **policy** is a sequence $\pi=(f_1,f_2,\dots)$ of decision rules; $f^\infty=(f,f,\dots)$ is a **stationary policy**, and $(g,\pi)=(g,f_1,f_2,\dots)$.
--   2. $r(f)$ is the vector with components $r(s,f(s))$, $P(f)$ the matrix with entries $p(t\mid s,f(s))$, $Q(f)=P(f)-I$, $P^*(f)$ the Cesàro limit of the powers of $P(f)$ and $H(f)=(I-P(f)+P^*(f))^{-1}-P^*(f)$.
--   3. $P^N(\pi)=P(f_1)\cdots P(f_N)$, $P^0(\pi)=I$; $\pi$ is **transient** if $\sum_{N\ge0}P^N(\pi)$ converges, and **the transient case** is the case in which every stationary policy is transient.
--   4. For a rate of interest $\rho>-1$ and discount factor $\beta=(1+\rho)^{-1}$, the expected total discounted return of $\pi$ is
--   $$V_\rho(\pi)=\sum_{N=1}^\infty \beta^N P^{N-1}(\pi)\,r(f_N).$$
--   5. For $g\in F$ and a policy $\pi$, $v_\rho(g,\pi)=r(g)+Q(g)V_\rho(\pi)-\rho V_\rho(\pi)$.
--
--   This is the model in which all of the paper's discount optimality criteria are defined.
--
--   **Formalization Note** Policies are indexed from $0$: `π 0` is $f_1$. Each state has its own action type `A s`. The condition $\|P(g)\|\le1$ for all $g\in F$ is stated per state and action as $\sum_t p(t\mid s,a)\le 1$, which is equivalent because $p\ge0$. $V_\rho$ keeps Veinott's extra factor $\beta$ ("the usual formula being here multiplied by $\beta$") and is a `tsum`, the genuine sum wherever the series converges ($\rho>0$ always; $\rho\le0$ near $0$ in the transient case); theorems carry the hypotheses that make it converge. $P^*(f)$ and $H(f)$ are the published `limitMatrix` and `deviationMatrix` of $P(f)$.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, pp. 1636 (§2 model, (1)), 1642 (Q, P*), 1643 (H ≡ H₀), 1644 (§4: ‖P(g)‖ ≦ 1, β, V_ρ(π), transient case), 1647 ((30))

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_VeinottSensitiveDP_Sensitive_Matrix
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottSensitiveDP.Sensitive

/-- Veinott's finite decision model of §2 under the standing assumption of §4.

There are finitely many states `s : St` (the paper's `1, …, S`, with `S = Fintype.card St`) and,
in each state `s`, a finite nonempty set `A s` of actions. Taking action `a` in state `s` earns the
reward `r s a` (any sign) and moves the system to state `t` with weight `p s a t ≧ 0`
(`p(t | s, a)`); the remaining mass `1 − Σₜ p(t | s, a)` is the probability of having stopped.

Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria,
Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1636, §2, and p. 1644,
§4 ("We assume throughout that ‖P(g)‖ ≦ 1 for all g ε F").

**Formalization Note.** Since the entries are nonnegative, `‖P(g)‖ = maxₛ Σₜ p(t | s, g(s)) ≦ 1` for
all `g ε F` is the same as `Σₜ p(t | s, a) ≦ 1` for every state `s` and action `a ε A_s`
(field `p_rowsum_le_one`). -/
structure Model (St : Type) [Fintype St] (A : St → Type) where
  /-- The reward `r(s, a)`. -/
  r : (s : St) → A s → ℝ
  /-- The transition weight `p(t | s, a)`. -/
  p : (s : St) → A s → St → ℝ
  p_nonneg : ∀ s a t, 0 ≤ p s a t
  p_rowsum_le_one : ∀ s a, ∑ t, p s a t ≤ 1

variable {St : Type} [Fintype St] [DecidableEq St] {A : St → Type}

/-- A decision rule `f ε F = ×ₛ A_s`: one action `f s ε A_s` for every state.
Veinott (1969), p. 1636, §2. -/
abbrev DecisionRule (A : St → Type) := (s : St) → A s

/-- A policy `π = (f₁, f₂, ⋯)`, a sequence of decision rules.

Veinott (1969), p. 1636, §2.

**Formalization Note.** Indexed from `0`: `π 0` is the paper's `f₁`, `π N` is `f_{N+1}`. -/
abbrev Policy (A : St → Type) := ℕ → DecisionRule A

/-- The stationary policy `f^∞ = (f, f, ⋯)`. Veinott (1969), p. 1636, §2. -/
def stationary (f : DecisionRule A) : Policy A := fun _ => f

/-- The policy `(g, π) = (g, f₁, f₂, ⋯)`: use `g` first, then `π`. Veinott (1969), p. 1637, §2. -/
def cons (g : DecisionRule A) (π : Policy A) : Policy A
  | 0 => g
  | N + 1 => π N

/-- The discount factor `β ≡ (1 + ρ)⁻¹` at the rate of interest `ρ`, `−1 < ρ < ∞`.
Veinott (1969), p. 1644, §4. -/
noncomputable def beta (ρ : ℝ) : ℝ := (1 + ρ)⁻¹

namespace Model

variable (M : Model St A)

/-- `r(f)`: the `S`-vector whose `s`th component is `r(s, f(s))`. Veinott (1969), p. 1636, §2. -/
def rv (f : DecisionRule A) : St → ℝ := fun s => M.r s (f s)

/-- `P(f)`: the `S × S` matrix whose `st`th element is `p(t | s, f(s))`.
Veinott (1969), p. 1636, §2. -/
def P (f : DecisionRule A) : Matrix St St ℝ := fun s t => M.p s (f s) t

/-- `Q(f) ≡ P(f) − I`. Veinott (1969), p. 1645, §4 ("Q(f), P*(f), and H(f) denote the matrices
defined in Section 3 associated with the substochastic matrix P(f)"; `Q ≡ P − I`, p. 1642). -/
def Q (f : DecisionRule A) : Matrix St St ℝ := M.P f - 1

/-- `P*(f)`: the Cesàro limit `lim_{N→∞} (N + 1)⁻¹ Σ_{i=0}^N P(f)^i` (published `limitMatrix`).
Veinott (1969), p. 1642, §3, and p. 1645, §4. That the limit exists is (15), a theorem. -/
noncomputable def Pstar (f : DecisionRule A) : Matrix St St ℝ := limitMatrix (M.P f)

/-- `H(f) ≡ H₀`, the reduced resolvent of `Q(f)` at `0`, which is the deviation matrix
`(I − P(f) + P*(f))⁻¹ − P*(f)` (published `deviationMatrix`).
Veinott (1969), p. 1643, §3 ("On letting H ≡ H₀"), and p. 1645, §4. -/
noncomputable def H (f : DecisionRule A) : Matrix St St ℝ := deviationMatrix (M.P f)

/-- `Pᴺ(π) = P(f₁) ⋯ P(f_N)` (ordered product), `P⁰(π) = I`. Veinott (1969), p. 1636, §2. -/
def Pmat (π : Policy A) : ℕ → Matrix St St ℝ
  | 0 => 1
  | N + 1 => Pmat π N * M.P (π N)

/-- A policy `π` is **transient** if `Σ_{N=0}^∞ Pᴺ(π)` converges (entrywise; the entries are
nonnegative). Veinott (1969), p. 1636, §2. -/
def IsTransient (π : Policy A) : Prop := Summable (M.Pmat π)

/-- **The transient case**: every stationary policy is transient.
Veinott (1969), p. 1644, §4 ("the transient case, i.e., where every stationary policy is
transient"). -/
def TransientCase : Prop := ∀ f : DecisionRule A, M.IsTransient (stationary f)

/-- `V_ρ(π) = Σ_{N=1}^∞ β^N P^{N−1}(π) r(f_N)`, the `S`-vector of expected total discounted returns
of the policy `π` at the interest rate `ρ`, `β = (1 + ρ)⁻¹`.

Veinott (1969), DOI 10.1214/aoms/1177697379, p. 1644, §4.

**Formalization Note.** Written with `N` shifted by one: `Σ_{N≥0} β^{N+1} Pᴺ(π) r(π N)`, where
`π N` is the paper's `f_{N+1}`. Veinott's normalization carries the extra factor `β` ("the usual
formula being here multiplied by β"); it is kept. The series is a `tsum`, which is `0` when the
series does not converge; it converges for every policy when `ρ > 0`, and, in the transient case,
for every policy when `ρ ≦ 0` is close enough to `0` (p. 1644). Statements about `V_ρ` carry the
hypotheses that make the series genuine. -/
noncomputable def V (ρ : ℝ) (π : Policy A) : St → ℝ :=
  ∑' N : ℕ, (beta ρ) ^ (N + 1) • (M.Pmat π N *ᵥ M.rv (π N))

/-- `v_ρ(g, π) ≡ r(g) + Q(g)V_ρ(π) − ρV_ρ(π)`, the test quantity of the policy improvement method.

Veinott (1969), DOI 10.1214/aoms/1177697379, p. 1647, §4, (30) (first expression). The second
expression of (30), `(1 + ρ)[V_ρ(g, π) − V_ρ(π)]`, is part of the theorem formalizing (31). -/
noncomputable def vrho (ρ : ℝ) (g : DecisionRule A) (π : Policy A) : St → ℝ :=
  M.rv g + M.Q g *ᵥ M.V ρ π - ρ • M.V ρ π

end Model

end VeinottSensitiveDP.Sensitive


