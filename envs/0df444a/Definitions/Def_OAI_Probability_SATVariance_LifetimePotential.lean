-- Prove2me | Definitions.Def_OAI_Probability_SATVariance_LifetimePotential
-- name    : OAI_Probability_SATVariance_LifetimePotential
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:26:54.912783+00:00
-- url     : https://prove2.me/theorems/75ca65d1-2acc-49e3-9e03-30ef62819423
-- title:
--   Cumulative rewards of time-inhomogeneous Markov operators, scheduled clause-or-mask steps and the occupation reward
-- statement:
--   Assignments on $u$ Boolean variables are maps $[u]\to\{\mathrm T,\mathrm F\}$ with $[u]=\{0,\dots,u-1\}$. A $k$-clause is a set of $k$ distinct variables with a sign for each, satisfied by an assignment that agrees with at least one sign; $\mathrm{Sat}(c)$ is the set of assignments satisfying $c$. The one-clause operator is $(P_{u,k}f)(S)=\operatorname{avg}_{c}f\big(S\cap\mathrm{Sat}(c)\big)$, the average over all $k$-clauses $c$ on $u$ variables, for real functions $f$ on sets $S$ of assignments.
--
--   1. **Cumulative reward.** Let $X$ be a set, $P=(P_i)_{i\ge0}$ a sequence of operators acting on real functions on $X$, and $f:X\to\mathbb R$. Define $\Sigma_0(P,f)=0$ and
--   $$
--   \Sigma_{m+1}(P,f)(x)=f(x)+P_0\big(\Sigma_m(P^{+},f)\big)(x),
--   $$
--   where $P^{+}=(P_{i+1})_{i\ge0}$ is the shifted sequence. When the $P_i$ are linear (for instance Markov transition operators), $\Sigma_m(P,f)=\sum_{i=0}^{m-1}P_0P_1\cdots P_{i-1}f$ is the expected reward collected during the first $m$ steps of the time-inhomogeneous chain with transitions $P_0,P_1,\dots$ started at $x$.
--   2. **Scheduled step.** Given a predicate on times declaring which times are *ordinary*, and masks $M_i$ (sets of assignments), the operator at time $i$ is
--   $$
--   (Q_if)(S)=\begin{cases}(P_{u,k}f)(S)&\text{if } i \text{ is ordinary},\\ f(S\cap M_i)&\text{otherwise.}\end{cases}
--   $$
--   An ordinary step adds a uniformly random $k$-clause; any other step intersects with a prescribed mask.
--   3. **Occupation exponent.** $\gamma_k=k-\beta_k$ with $\beta_k=k/(k-1)$; for $k\ge2$ this is $\gamma_k=k(k-2)/(k-1)$.
--   4. **Occupation reward.** For $r,d\in\mathbb N$ and a set $S$ of assignments,
--   $$
--   \rho_{u,r,d}(S)=\begin{cases}R_{u,r}(S,d)^{\gamma_{r+1}}&\text{if } S\ne\emptyset,\\0&\text{if } S=\emptyset,\end{cases}
--   $$
--   where $R_{u,r}(S,d)$ is the probability that $d$ independent uniformly random $r$-clauses on $u$ variables leave no member of $S$ satisfying all of them.
--
--   The expected lifetime of a solution set (the expected time until a stream of uniform $k$-clauses kills it) serves as a potential for these dynamics: for $k\le u$, $\operatorname{alive}(S)+(Q_i\operatorname{life})(S)\le\operatorname{life}(S)+\mathbf 1[i\text{ is not ordinary}]$, where $\operatorname{alive}(S)=\mathbf 1[S\ne\emptyset]$. Such a drift inequality bounds a cumulative reward $\Sigma_m$ by the potential plus the number of non-ordinary steps. Applied to the occupation reward, which is large on states that a block of $d$ shorter clauses would likely kill, it shows: for $k=r+1$ with $2\le r$, $r+1\le u$, $d\ge1$, and at most $d$ non-ordinary steps among the first $M$, the cumulative occupation reward over $M$ steps is at most $4(C_k+1)\,d^{\beta_k}$ when $k\ge4$, and at most $4(C_k+1)\,d^{\beta_k}\big(1+\log(M+1)\big)$ in the critical case $k=3$, where $C_k=4\,(2K_k)^{1/(k-1)}$ with $K_k=\big(2^k(k-1)\big)^{k-1}$ is the lifetime constant. This is one of the inputs to the variance upper bound for the first unsatisfiability time of random $k$-SAT.
--
--   **Formalization Note** In `markovSum` the operators are arbitrary maps on real functions, so the closed formula in item 1 holds only for linear operators; in general the recursion is the definition. `occupationGamma` uses `lifetimeBeta`, which takes $k-1$ in $\mathbb N$ and has $\beta_0=\beta_1=0$ by the convention $1/0=0$. The power in `occupationReward` is the real power.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/LifetimePotential.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/LifetimePotential.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SATVariance mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def markovSum.{u_1} {X : Type u_1} (P : ℕ → (X → ℝ) → X → ℝ) (f : X → ℝ) : ℕ → X → ℝ
  | 0 => fun _ => 0
  | m+1 => fun x => f x + P 0 (markovSum (fun i => P (i+1)) f m) x

def scheduledStep (u k : ℕ) (ordinary : ℕ → Prop) [DecidablePred ordinary]
    (mask : ℕ → Finset (Assignment u)) (i : ℕ)
    (f : Finset (Assignment u) → ℝ) (S : Finset (Assignment u)) : ℝ :=
  if ordinary i then clauseStep u k f S else f (S ∩ mask i)

def occupationGamma (k : ℕ) : ℝ := (k : ℝ)-lifetimeBeta k

def occupationReward (u r d : ℕ) (S : Finset (Assignment u)) : ℝ :=
  if S.Nonempty then (blockKill u r S d)^(occupationGamma (r+1)) else 0

end RandomKSAT

end

end OAI


