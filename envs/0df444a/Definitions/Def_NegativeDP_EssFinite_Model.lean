-- Prove2me | Definitions.Def_NegativeDP_EssFinite_Model
-- name    : NegativeDP_EssFinite_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:21:08.62614+00:00
-- url     : https://prove2.me/theorems/d56eb2ed-53d5-4f50-a55f-18eec0e292ed
-- title:
--   Strauch's negative dynamic programming problem (§3): returns I(π), optimal return v*, the operators T and U, equivalent actions and essential finiteness (§9)
-- statement:
--   This file fixes the objects of R. E. Strauch's *negative dynamic programming* problem that the mission's statements use.
--
--   **The problem** (§3, p. 874, negative case). The state space $S$ and the action space $A$ are non-empty Borel sets, i.e. Borel subsets of complete separable metric spaces with their Borel $\sigma$-fields. The **law of motion** $q(\cdot\mid s,a)$ is a probability measure on $S$ for each state–action pair $(s,a)$, depending measurably on $(s,a)$. The **return** $r(s,a,t)$, received when action $a$ is taken in state $s$ and the next state is $t$, is a Borel function with
--   $$-\infty < r(s,a,t) \le 0, \qquad \int r(s,a,t)\,dq(t\mid s,a) > -\infty \quad\text{for all } (s,a).$$
--   There is no discounting ($\beta=1$). The class $M(X)$ of the negative case (p. 873) is the set of non-positive, extended real-valued Borel functions on $X$.
--
--   **Policies.** A policy $\pi=(\pi_1,\pi_2,\dots)$ chooses the $n$th action at random according to a probability $\pi_n(\cdot\mid h)$ that depends measurably on the whole history $h=(s_1,a_1,\dots,a_{n-1},s_n)$. A (non-random) Markov policy is a sequence $(f_1,f_2,\dots)$ of measurable maps $S\to A$, and the stationary policy $f^{(\infty)}$ uses the same map $f$ at every stage. These objects are those of the published model `DiscountedDP.Stationary.Model`/`Return`, which this file imports.
--
--   **Returns.** Starting from $s_1=s$, a policy and the law of motion determine the joint law of the history. The **expected return** of $\pi$ is
--   $$I(\pi)(s)=\sum_{n=1}^{\infty} \pi_1 q\,\pi_2 q\cdots\pi_n q\, r\,(s)\in[-\infty,0],$$
--   the sum over stages of the expected stage return (p. 875). The **optimal return** is $v^*(s)=\sup_\pi I(\pi)(s)$, the supremum over all policies (p. 883), and a policy $\pi^*$ is **optimal** if $I(\pi^*)(s)\ge v^*(s)$ for every state $s$ (p. 875).
--
--   **Operators** (§5, pp. 878–879). For a measurable $f:S\to A$ and $u\in M(S)$,
--   $$Tu(s)=\int \big[r(s,f(s),t)+u(t)\big]\,dq(t\mid s,f(s)),$$
--   and for a Markov policy $\pi=(f_1,f_2,\dots)$ the associated operator is $Uu=\sup_n T_n u$, where $T_n$ is the operator of $f_n$.
--
--   **Equivalent actions and essential finiteness** (§9, p. 887). Actions $a$ and $b$ are **equivalent at state $s$** if $r(s,a,\cdot)=r(s,b,\cdot)$ as functions and $q(\cdot\mid s,a)=q(\cdot\mid s,b)$ as measures. $A$ is **essentially finite by** $\pi^*=(f_1,f_2,\dots)$ if there is a partition of $S$ into Borel sets $S_1,S_2,\dots$ such that for every $(s,a)$ with $s\in S_n$, at least one of the actions $f_1(s),\dots,f_n(s)$ is equivalent to $a$ at $s$.
--
--   These are the shared objects of every statement in the mission.
--
--   **Formalization Note** Borel sets are non-empty standard Borel types and "Baire function" means Borel measurable. The return is real-valued and non-positive, and "$qr>-\infty$" is integrability of $r(s,a,\cdot)$ against $q(\cdot\mid s,a)$. Returns take values in `EReal` and are computed as minus the `lintegral` of the loss $-r$ (and $-u$), which is exact because $r\le0$ and $u\le0$ and keeps the value $-\infty$ (a Bochner integral would return $0$ on a non-integrable function). $I(\pi)$ is written as the sum of the stage expectations, which equals the paper's $e_\pi\rho$ by monotone convergence. $v^*$ is the supremum over all randomized history-dependent plans. `T` and `U` read their argument through $(-u)^+$, so they agree with the paper on $M(S)$; statements apply them only to non-positive functions. Stages are numbered from $0$ in Lean: the plan's kernel `κ n` is the paper's $\pi_{n+1}$, and the Markov plan's `π n` is $f_{n+1}$. Essential finiteness is zero-based accordingly: Lean's piece `n` is the paper's $S_{n+1}$ and allows the rules `π 0, …, π n`, i.e. $f_1,\dots,f_{n+1}$; pieces are measurable, pairwise disjoint, cover $S$, and may be empty. Only the negative case is formalized.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), pp. 873–875 (§2–§3), pp. 878–879 (§5, operators T and U), p. 883 (v*), p. 887 (§9, equivalent actions, essential finiteness)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_NegativeDP_OptEq_Model
import Definitions.Def_NegativeDP_Stationary_Model

namespace NegativeDP.EssFinite

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan)

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Actions `a` and `b` are equivalent at state `s` (§9, p. 887): `r(s, a, ·) = r(s, b, ·)` and
`q(· | s, a) = q(· | s, b)`. -/
def ActEquiv (P : NegativeDP.Stationary.Problem S A) (s : S) (a b : A) : Prop :=
  (∀ t, P.r (s, a, t) = P.r (s, b, t)) ∧ P.q (s, a) = P.q (s, b)

/-- `A` is essentially finite by `π* = (f_1, f_2, …)` (§9, p. 887): a partition of `S` into Borel
sets `S_1, S_2, …` such that for every `(s, a)` with `s ∈ S_n` one of `f_1(s), …, f_n(s)` is
equivalent to `a` at `s`. Zero-based: Lean's piece `n` is the paper's `S_{n+1}` and allows the
rules `π 0, …, π n`, i.e. `f_1, …, f_{n+1}`. Pieces may be empty. -/
def EssentiallyFinite (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) : Prop :=
  ∃ pieces : ℕ → Set S,
    (∀ n, MeasurableSet (pieces n)) ∧
    (∀ i j, i ≠ j → Disjoint (pieces i) (pieces j)) ∧
    (⋃ n, pieces n) = Set.univ ∧
    ∀ n s, s ∈ pieces n → ∀ a, ∃ i ≤ n, ActEquiv P s ((π i).1 s) a

end NegativeDP.EssFinite


