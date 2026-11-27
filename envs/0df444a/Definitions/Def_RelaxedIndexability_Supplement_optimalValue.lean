-- Prove2me | Definitions.Def_RelaxedIndexability_Supplement_optimalValue
-- name    : RelaxedIndexability_Supplement_optimalValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:00:57.563732+00:00
-- url     : https://prove2.me/theorems/2d5b358e-9606-4558-808b-bcda475101a1
-- title:
--   Optimal value, optimal action values and optimal passive times of the single-armed bandit with subsidy
-- statement:
--   Fix one arm with transition matrix $\mathbf P$ and reward vector $B$, a discount factor $\beta$ and a **subsidy** $m$ paid in every passive slot. A single-arm policy $\pi$ earns $xB'$ when it activates the arm at belief $x$ and $m$ when it leaves it passive.
--
--   1. The **value** of $\pi$ from belief $x$ is its expected total discounted reward under these rewards, and its **passive time** is $\mathbb E_\pi[\sum_{t\ge1}\beta^{t-1}\mathbb 1(u(t)=0)\mid\omega(1)=x]$, the same object with reward $0$ when active and $1$ when passive.
--   2. The **optimal value** is the supremum over all single-arm policies,
--   $$
--   V_{\beta,m}(x)=\sup_{\pi}\ \mathbb E_\pi\Big[\sum_{t=1}^{\infty}\beta^{t-1}\big(\mathbb 1(u(t)=1)\,B_{S(t)}+\mathbb 1(u(t)=0)\,m\big)\Big|\ \omega(1)=x\Big].
--   $$
--   3. The **optimal action values** (13)–(14) are
--   $$
--   V_{\beta,m}(x;u=1)=xB'+\beta\,x\big(V_{\beta,m}(p_0),\dots,V_{\beta,m}(p_{K-1})\big)',\qquad V_{\beta,m}(x;u=0)=m+\beta V_{\beta,m}(\mathcal T^1(x)).
--   $$
--   4. $\Pi^*_{sa}(m)$ is the set of policies whose value from $x$ equals $V_{\beta,m}(x)$, and the **optimal passive times** are the passive times from $x$ of the policies in $\Pi^*_{sa}(m)$. The maximum of this set is $D_{\beta,m}(x)$ in (22).
--
--   These are the optimal-policy objects of §2.2–§2.4. They differ from the threshold-policy objects $\hat V$, $\hat D$ of the published mission.
--
--   **Formalization Note** The supremum is a real `⨆` over the nonempty set of policies; on the belief simplex the values are bounded for $0<\beta<1$, so it is the true supremum. The Bellman equation (12) is not part of the definition. $D_{\beta,m}(x)$ is not defined as a number: the theorems assert that the set of optimal passive times has a greatest element (`IsGreatest`).
-- source:
--   Liu, Relaxed Indexability and Index Policy for Partially Observable Restless Bandits, arXiv:2107.11939v4, (11), p.9; V_{β,m} p.10; (13)–(14), p.11; Π*_sa(m) and (22), p.15

import Mathlib
import Definitions.Def_RelaxedIndexability_policyValue
import Definitions.Def_RelaxedIndexability_Supplement_historyValue

open Matrix

namespace RelaxedIndexability.Supplement

variable {K : ℕ}

/-- **The value of a single-arm policy with subsidy `m`** (Liu, arXiv:2107.11939v4, (11), p.9):
the reward is `x B′` when active at belief `x` and `m` when passive. -/
noncomputable def subsidyValue (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ) (B : Fin K → ℝ) (m : ℝ)
    (π : Policy K) (x : Fin K → ℝ) : ℝ :=
  historyValue β P (fun y => y ⬝ᵥ B) (fun _ => m) π x

/-- **The expected total discounted passive time of a single-arm policy**,
`𝔼_π[∑_{t=1}^{∞} β^{t−1} 𝟙(u(t) = 0) | ω(1) = x]` (Liu, arXiv:2107.11939v4, (22), p.15): the value
with reward `0` when active and `1` when passive. -/
noncomputable def policyPassiveTime (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ) (π : Policy K)
    (x : Fin K → ℝ) : ℝ :=
  historyValue β P (fun _ => 0) (fun _ => 1) π x

/-- **The optimal value `V_{β,m}(x)` of the single-armed bandit with subsidy `m`**
(Liu, arXiv:2107.11939v4, (11), p.9, and p.10): the supremum over all single-arm policies of their
values from `x`.

**Formalization Note.** The set of policies is nonempty and, for `0 < β < 1`, a row-stochastic `P`
and `x` in the simplex, their values are bounded, so the real supremum is the mathematical one. The
Bellman equation (12) is not part of the definition. -/
noncomputable def optimalValue (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ) (B : Fin K → ℝ) (m : ℝ)
    (x : Fin K → ℝ) : ℝ :=
  ⨆ π : Policy K, subsidyValue β P B m π x

/-- **The optimal action values `V_{β,m}(x; u)`** (Liu, arXiv:2107.11939v4, (13)–(14), p.11):
`V(x; 1) = x B′ + β x (V(p₀), …, V(p_{K−1}))′` and `V(x; 0) = m + β V(T¹(x))`, with the optimal value
as continuation (`u = true` is active).

**Formalization Note.** This differs from `RelaxedIndexability.thresholdActionValue`, whose
continuation is the linear threshold policy. -/
noncomputable def optimalActionValue (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ) (B : Fin K → ℝ) (m : ℝ)
    (u : Bool) (x : Fin K → ℝ) : ℝ :=
  RelaxedIndexability.beliefStep β P (fun y => y ⬝ᵥ B) (fun _ => m) u (optimalValue β P B m) x

/-- **`Π*_sa(m)`**, the set of all optimal single-arm policies achieving `V_{β,m}(x)` with initial
belief `x` (Liu, arXiv:2107.11939v4, Theorem 1, p.15). -/
def optimalPolicies (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ) (B : Fin K → ℝ) (m : ℝ)
    (x : Fin K → ℝ) : Set (Policy K) :=
  {π | subsidyValue β P B m π x = optimalValue β P B m x}

/-- **The passive times of the optimal policies**: the set whose maximum is `D_{β,m}(x)` in (22)
(Liu, arXiv:2107.11939v4, p.15).

**Formalization Note.** `D_{β,m}(x)` is referred to as a greatest element of this set
(`IsGreatest`), so that the maximum is asserted to be attained. -/
def optimalPassiveTimes (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ) (B : Fin K → ℝ) (m : ℝ)
    (x : Fin K → ℝ) : Set ℝ :=
  (fun π => policyPassiveTime β P π x) '' optimalPolicies β P B m x

end RelaxedIndexability.Supplement


