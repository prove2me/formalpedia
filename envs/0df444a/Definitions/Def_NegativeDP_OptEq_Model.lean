-- Prove2me | Definitions.Def_NegativeDP_OptEq_Model
-- name    : NegativeDP_OptEq_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:06.737988+00:00
-- url     : https://prove2.me/theorems/407657c0-831d-409f-82a0-9937fb9740e8
-- title:
--   Strauch's negative dynamic programming problem: returns $I(\pi)$, $I_n(\pi,v)$, the optimal return $v^*$, $(p,\varepsilon)$-optimality, and the operators $T$, $T_a$, $U$
-- statement:
--   This file sets up the **negative dynamic programming problem** of Strauch (1966), §3, and the objects of §5–§8 built on it.
--
--   **The problem.** The states $S$ and the actions $A$ are non-empty Borel sets. The law of motion $q(\cdot\mid s,a)$ is a probability kernel from $S\times A$ to $S$. The return $r(s,a,t)$ is a Borel function on $S\times A\times S$ with
--   $$-\infty < r(s,a,t) \le 0 \qquad\text{and}\qquad \int r(s,a,t)\,dq(t\mid s,a) > -\infty$$
--   for all $s,a,t$: both the actual return and the expected one-step return are finite. There is no discounting ($\beta = 1$).
--
--   **Policies and returns.** A policy $\pi=(\pi_1,\pi_2,\dots)$ chooses the $n$th action $a_n$ from a probability kernel $\pi_n(\cdot\mid s_1,a_1,\dots,a_{n-1},s_n)$; it may be randomized and history-dependent. A Markov policy $(f_1,f_2,\dots)$ uses measurable maps $f_n:S\to A$. Starting from $s_1=s$, the expected return of $\pi$ is
--   $$I(\pi)(s) = \sum_{n=1}^{\infty} E^{\pi}_{s}\big[r(s_n,a_n,s_{n+1})\big] \in [-\infty,0],$$
--   and for $v\in M(S)$ the $n$-stage return with terminal reward $v$ is
--   $$I_n(\pi,v)(s) = E^{\pi}_{s}\Big[\sum_{j=1}^{n} r(s_j,a_j,s_{j+1}) + v(s_{n+1})\Big].$$
--   Here $M(S)$ is the set of non-positive, extended real-valued Borel functions on $S$. The **optimal return** is
--   $$v^*(s) = \sup_{\pi} I(\pi)(s),$$
--   the supremum over all policies. For a probability $p$ on $S$ and $\varepsilon>0$, a policy $\pi^*$ is **$(p,\varepsilon)$-optimal** if $p\{s : I(\pi^*)(s) \ge v^*(s)-\varepsilon\} = 1$.
--
--   **Operators.** For a measurable $f:S\to A$ and $u\in M(S)$,
--   $$Tu(s) = \int \big[r(s,f(s),t) + u(t)\big]\,dq(t\mid s,f(s)),$$
--   $T_a$ is the operator of the constant map $f\equiv a$, and for a Markov policy $\pi=(f_1,f_2,\dots)$ with operators $T_n$, $Uu = \sup_n T_n u$. The operator $U$ **conserves** $v\in M(S)$ if $Uv\ge v$, and $u$ is **excessive** for $U$ if $Uu\le u$. For a Markov policy $\pi=(f_1,f_2,\dots)$, ${}^n\pi = (f_{n+1},f_{n+2},\dots)$.
--
--   These are the objects in which the optimality equation $v^* = \sup_a T_a v^*$ and its supporting results are stated.
--
--   **Formalization Note** Borel sets are non-empty standard Borel spaces and "Baire function" means Borel measurable. Policies are the plans of the published Blackwell model (`DiscountedDP.Stationary.Plan`, `MarkovPlan`), with decisions numbered from $0$: Lean's history `Hist S A n` is the paper's $H_{n+1}$ and `π.κ n` is the paper's $\pi_{n+1}$. Returns take values in `EReal` and are computed as minus the lower Lebesgue integral (`lintegral`) of the loss $-r-u\ge 0$, which is exact because $r\le0$ and $u\le0$, and which never turns $-\infty$ into $0$. $I(\pi)$ is written as the series of stage expectations, which equals the paper's $e_\pi\rho$ by monotone convergence. $v^*$ is the supremum over every plan (randomized, history-dependent). $(p,\varepsilon)$-optimality is "for $p$-almost every $s$", the completion reading the paper gives. `Conserves` includes $v\in M(S)$; the hypothesis $u\in M(S)$ of the operator statements is stated separately as `IsNegM u`. `T`, `Ta`, `U`, `In` read $u$ through `(-u).toENNReal`, which is exact only for $u\le0$. Only the negative case of the paper is modelled.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), pp. 873–885: §2 (p. 873, M(X)), §3 (pp. 874–875, the problem, policies, I(π), I_n(π, v), (p, ε)-optimality), §5 (pp. 878–879, T and U), §6 (p. 881 conserves; p. 882 ⁿπ; p. 883 excessive), §7 (p. 883, v*), §8 (p. 885, T_a)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_NegativeDP_Stationary_Model

namespace NegativeDP.OptEq

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan)

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- `(p, ε)`-optimality (p. 875): `p{NegativeDP.Stationary.I(π) ≥ v* − ε} = 1`, read in the completion of `p`. -/
def IsPEOptimal (P : NegativeDP.Stationary.Problem S A) (p : Measure S) (ε : ℝ) (π : Plan (S := S) (A := A)) :
    Prop :=
  IsProbabilityMeasure p ∧
    ∀ᵐ s ∂p, NegativeDP.Stationary.vstar P s - (ε : EReal) ≤ NegativeDP.Stationary.I P π s

/-- `T_a`, the operator of the constant rule `f ≡ a` (p. 885). -/
noncomputable def Ta (P : NegativeDP.Stationary.Problem S A) (a : A) (u : S → EReal) (s : S) : EReal :=
  -((∫⁻ t, ENNReal.ofReal (-P.r (s, a, t)) + (-(u t)).toENNReal ∂P.q (s, a) : ℝ≥0∞) : EReal)

/-- The operator of a Markov plan `π = (f₁, f₂, …)` (p. 879): `Uu = supₙ Tₙu`. -/
noncomputable def U (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) (u : S → EReal) (s : S) : EReal :=
  ⨆ n : ℕ, NegativeDP.Stationary.T P (π n) u s

/-- `U` conserves `v ∈ M(S)` if `Uv ≥ v` (p. 881). -/
def Conserves (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) (v : S → EReal) : Prop :=
  NegativeDP.Stationary.IsNegM v ∧ ∀ s, v s ≤ U P π v s

/-- `u` is excessive for `U` if `Uu ≤ u` (p. 883); `u ∈ M(S)` is stated separately. -/
def IsExcessive (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) (u : S → EReal) : Prop :=
  ∀ s, U P π u s ≤ u s

/-- `ⁿπ = (fₙ₊₁, fₙ₊₂, …)` for a Markov plan `π = (f₁, f₂, …)` (p. 874). -/
def shift (π : MarkovPlan S A) (n : ℕ) : MarkovPlan S A := fun k => π (k + n)

end NegativeDP.OptEq


