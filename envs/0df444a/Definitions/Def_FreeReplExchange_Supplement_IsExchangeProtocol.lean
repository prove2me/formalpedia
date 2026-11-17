-- Prove2me | Definitions.Def_FreeReplExchange_Supplement_IsExchangeProtocol
-- name    : FreeReplExchange_Supplement_IsExchangeProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:31:39.07127+00:00
-- url     : https://prove2.me/theorems/f6ffe74c-566f-426b-9c5c-495826f35e62
-- title:
--   Exchange-protocol validity, DSIC, Pareto efficiency, and LEC/HEC
-- statement:
--   This file extends the published pairwise-exchange model with the notions used by Theorems 1--4 and 14--15.
--
--   An **exchange protocol** terminates within the finite published horizon and, at every reachable history, posts only well-formed proposals between participants, never reposts a rejected proposal, and posts only proposals that would change the current allocation. It is **dominant-strategy incentive compatible (DSIC)** if accepting every proposal is a best response for every participant against every strategy profile of all other agents.
--
--   For allocations $x,y$, $y$ **Pareto-dominates** $x$ when every agent weakly prefers $y$ and at least one strictly prefers it. An allocation is Pareto-efficient in a class $C$ if it lies in $C$ and no member of $C$ Pareto-dominates it. The class $X(x^{(0)},P)$ consists of published feasible pairwise-exchange outcomes, while $Y(x^{(0)})=\{x:x\ge x^{(0)}\}$ contains every allocation extending the initial holdings. The unrestricted pairwise-reachability class used by Theorem 4 contains every finite execution of well-formed exchanges of initially owned goods.
--
--   Under ESC, write $h_i(x)=\sum_r x_{i,r}$ and $b_i=\sum_{j\ne i}\beta_{ij}$. A coalition has **low externality competition (LEC)** when $b_i<1$ for every $i$, and **high externality competition (HEC)** when $b_i\ge1$ for every $i$.
-- source:
--   Yang--Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967...), Desideratum 1, p.15 (PDF p.17); Theorem 4, p.23 (PDF p.25); section 6, pp.39--40 (PDF pp.41--42)

import Mathlib
import Definitions.Def_FreeReplExchange_IsEfficient
import Definitions.Def_FreeReplExchange_M3

set_option autoImplicit false

namespace FreeReplExchange.Supplement

/-- A protocol in the exchange model of Yang--Kandasamy, *Pairwise Exchanges of
Freely Replicable Goods with Negative Externalities*, arXiv:2603.12403 (held version, sha256
3ae07967...), section 2.2, pp. 13--15 (PDF pp. 15--17).

The protocol terminates by the published finite horizon.  At every history that can arise, every
posted proposal is well formed for the initial allocation and participating set, has not already
been rejected, and changes the current allocation if executed.

**Formalization Note.** These are the standing protocol rules surrounding Desiderata 1--6.  A
previously executed exchange cannot be posted again because both of its receiving slots are then
filled, while a previously rejected exchange is excluded explicitly. -/
def IsExchangeProtocol {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ}
    (x0 : A → Fin m → Bool) (M : Protocol A m) : Prop :=
  TerminatesByHorizon M ∧
    ∀ (P : Finset A) (σ : A → Strategy A m) (t : ℕ) (p : Exchange A m),
      p ∈ M P (hist M P σ t) →
        WellFormed x0 P p ∧ p ∉ rejectedSet (hist M P σ t) ∧
          exec (alloc x0 (hist M P σ t)) {p} ≠ alloc x0 (hist M P σ t)

/-- Dominant-strategy incentive compatibility, Desideratum 1, p. 15 (PDF p. 17): for every
participating set, accepting every proposal is a best response for each participant against every
strategy profile of the other participants. -/
def IsDSIC {A : Type*} [Fintype A] [DecidableEq A] {m : ℕ}
    (x0 : A → Fin m → Bool) (U : A → A → Fin m → ℝ) (M : Protocol A m) : Prop :=
  ∀ (P : Finset A) (i : A), i ∈ P → ∀ (σother : A → Strategy A m) (σi : Strategy A m),
    util U i (xInf x0 M P (Function.update σother i σi)) ≤
      util U i (xInf x0 M P (Function.update σother i (acceptAll i)))

/-- The number `h_i(x) = sum_r x_{i,r}` of distinct goods held by agent `i`, section 6, p. 39
(PDF p. 41). -/
def holdingsCount {A : Type*} {m : ℕ} (x : A → Fin m → Bool) (i : A) : ℕ :=
  ∑ r, if x i r then 1 else 0

/-- Allocation `y` Pareto-dominates allocation `x`: every agent weakly prefers `y`, and some agent
strictly prefers it, section 6, p. 39 (PDF p. 41). -/
def ParetoDominates {A : Type*} [Fintype A] {m : ℕ} (U : A → A → Fin m → ℝ)
    (y x : A → Fin m → Bool) : Prop :=
  (∀ i, util U i x ≤ util U i y) ∧ ∃ i, util U i x < util U i y

/-- Pareto efficiency of `x` relative to a comparison class `C`, section 6, p. 39 (PDF p. 41). -/
def ParetoEfficientIn {A : Type*} [Fintype A] {m : ℕ} (U : A → A → Fin m → ℝ)
    (C : Set (A → Fin m → Bool)) (x : A → Fin m → Bool) : Prop :=
  x ∈ C ∧ ¬ ∃ y ∈ C, ParetoDominates U y x

/-- The comparison class `X(x0,P)` of allocations obtained by executing one of the published
feasible exchange sets at the initial allocation, equations (11)--(12), p. 18 (PDF p. 20). -/
def exchangeOutcomes {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ}
    (x0 : A → Fin m → Bool) (U : A → A → Fin m → ℝ) (P : Finset A) :
    Set (A → Fin m → Bool) :=
  {x | ∃ S ∈ feasibleSets x0 U P x0, x = exec x0 S}

/-- Allocations obtainable from `x0` by pairwise exchanges of initially owned goods, without the
MIC/feasibility restriction defining `X`.  Because there is no onward sharing and execution only
unions receiving slots, every finite sequential execution has this form.  This is the comparison
class in Theorem 4, p. 23 (PDF p. 25). -/
def pairwiseExchangeOutcomes {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ}
    (x0 : A → Fin m → Bool) (P : Finset A) : Set (A → Fin m → Bool) :=
  {x | ∃ S : Finset (Exchange A m), (∀ p ∈ S, WellFormed x0 P p) ∧ x = exec x0 S}

/-- An allocation is stable for participating set `P` when it has no feasible exchange that
strictly benefits both participants.  This is the allocation-level condition used in Theorems 4,
14 and 15; the rejected-exchange exception belongs to the protocol-level `IsStable`. -/
def IsStableAllocation {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ}
    (x0 : A → Fin m → Bool) (U : A → A → Fin m → ℝ) (P : Finset A)
    (x : A → Fin m → Bool) : Prop :=
  ∀ p ∈ feasible x0 U P x, ¬ (0 < delta U x p.i p ∧ 0 < delta U x p.j p)

/-- The larger comparison class `Y(x0)` of every allocation containing the initial allocation,
section 6, p. 39 (PDF p. 41). -/
def dominatingAllocations {A : Type*} {m : ℕ} (x0 : A → Fin m → Bool) :
    Set (A → Fin m → Bool) :=
  {x | Dominates x0 x}

/-- Aggregate competition `b_i = sum_{j != i} beta_ij`, section 6, p. 39 (PDF p. 41). -/
def aggregateCompetition {A : Type*} [Fintype A] [DecidableEq A]
    (β : A → A → ℝ) (i : A) : ℝ :=
  ∑ j ∈ (Finset.univ.erase i), β i j

/-- Low externality competition (LEC): `b_i < 1` for every agent, section 6, p. 39
(PDF p. 41). -/
def IsLEC {A : Type*} [Fintype A] [DecidableEq A] (β : A → A → ℝ) : Prop :=
  ∀ i, aggregateCompetition β i < 1

/-- High externality competition (HEC): `b_i >= 1` for every agent, section 6, p. 39
(PDF p. 41). -/
def IsHEC {A : Type*} [Fintype A] [DecidableEq A] (β : A → A → ℝ) : Prop :=
  ∀ i, 1 ≤ aggregateCompetition β i

end FreeReplExchange.Supplement


