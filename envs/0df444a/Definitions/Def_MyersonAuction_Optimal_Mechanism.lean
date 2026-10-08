-- Prove2me | Definitions.Def_MyersonAuction_Optimal_Mechanism
-- name    : MyersonAuction_Optimal_Mechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:33:18.245976+00:00
-- url     : https://prove2.me/theorems/0b8007ac-5e83-48d7-944c-46f840d7bb11
-- title:
--   Direct mechanisms, feasibility, seller utility and virtual surplus
-- statement:
--   A direct mechanism specifies an allocation probability $p_i(t)$ and expected payment $x_i(t)$ for each bidder $i$ at every reported profile $t$. Let $U_i(p,x,s)$ denote bidder $i$’s expected utility when her true estimate and report are $s$, integrating the other bidders’ estimates. Let $U_0(p,x)$ be the seller’s expected utility. The interim win probability is
--
--   $$Q_i(p,s)=\int_{T_{-i}}p_i(t_{-i},s)f_{-i}(t_{-i})\,dt_{-i}.$$
--
--   Feasibility means the allocation probabilities are nonnegative and sum to at most one; each $U_i(p,x,s)$ is nonnegative; and for every true estimate $s$ and possible report $r$, truthful reporting gives at least the utility of reporting $r$. An optimal mechanism is feasible and maximizes $U_0$ over all feasible direct mechanisms. The virtual-surplus objective in Lemma 3 is
--
--   $$\int_T\sum_i(c_i(t_i)-t_0)p_i(t)f(t)\,dt.$$
--
--   These definitions state the seller’s optimization problem and its intermediate allocation problem.
--
--   **Formalization Note** Payments may be negative or nonzero when a bidder loses. Feasibility includes integrability of allocations, payments and every report section, making all expected utilities well defined. The other-coordinate integral is represented by integrating after replacing bidder $i$’s coordinate under the normalized product law.
-- source:
--   Myerson, Optimal Auction Design, Math. Oper. Res. 6(1) (1981), pp. 61–65, §3–§4, eqs. (3.1)–(3.5), (4.1)–(4.4), (4.7)

import Definitions.Def_MyersonAuction_Optimal_Environment

noncomputable section

namespace MyersonAuction.Optimal

open MeasureTheory

abbrev Outcome (ι : Type) := ι → (ι → ℝ) → ℝ

/-- Integrability of all quantities that occur in the auction's expected utilities. -/
def WellDefined {ι : Type} [Fintype ι] [DecidableEq ι] (E : Environment ι)
    (p x : Outcome ι) : Prop :=
  ∀ i, Integrable (p i) (distribution E) ∧
    Integrable (x i) (distribution E) ∧
    ∀ s ∈ Set.Icc (E.a i) (E.b i),
      Integrable (fun t => p i (Function.update t i s)) (distribution E) ∧
      Integrable (fun t => x i (Function.update t i s)) (distribution E)

/-- Myerson's interim utility (3.1), integrating out all other bidders. -/
def interimUtility {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : Environment ι) (p x : Outcome ι) (i : ι) (s : ℝ) : ℝ :=
  ∫ t, (bidderValue E i (Function.update t i s) *
    p i (Function.update t i s) - x i (Function.update t i s)) ∂distribution E

/-- Expected utility of a true type `s` that reports `r`, as in (3.5). -/
def reportUtility {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : Environment ι) (p x : Outcome ι) (i : ι) (s r : ℝ) : ℝ :=
  ∫ t, (bidderValue E i (Function.update t i s) *
    p i (Function.update t i r) - x i (Function.update t i r)) ∂distribution E

/-- The seller's objective (3.2). -/
def sellerUtility {ι : Type} [Fintype ι]
    (E : Environment ι) (p x : Outcome ι) : ℝ :=
  ∫ t, (sellerValue E t * (1 - ∑ j, p j t) + ∑ j, x j t) ∂distribution E

/-- The ex post single-object probability constraint (3.3). -/
def ProbabilityCondition {ι : Type} [Fintype ι]
    (E : Environment ι) (p : Outcome ι) : Prop :=
  ∀ t ∈ support E, (∑ j, p j t) ≤ 1 ∧ ∀ i, 0 ≤ p i t

/-- The interim win probability (4.1). -/
def Q {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : Environment ι) (p : Outcome ι) (i : ι) (s : ℝ) : ℝ :=
  ∫ t, p i (Function.update t i s) ∂distribution E

/-- Weak monotonicity (4.2). -/
def MonotoneQ {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : Environment ι) (p : Outcome ι) : Prop :=
  ∀ i, ∀ s ∈ Set.Icc (E.a i) (E.b i), ∀ r ∈ Set.Icc (E.a i) (E.b i),
    s ≤ r → Q E p i s ≤ Q E p i r

/-- Equations (4.3)–(4.4). -/
def EnvelopeAndBaseIR {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : Environment ι) (p x : Outcome ι) : Prop :=
  (∀ i, ∀ s ∈ Set.Icc (E.a i) (E.b i),
    interimUtility E p x i s = interimUtility E p x i (E.a i) +
      ∫ r in E.a i..s, Q E p i r) ∧
  (∀ i, 0 ≤ interimUtility E p x i (E.a i))

/-- Feasibility: (3.3), (3.4), (3.5), with well-defined expected utilities. -/
def Feasible {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : Environment ι) (p x : Outcome ι) : Prop :=
  WellDefined E p x ∧ ProbabilityCondition E p ∧
  (∀ i, ∀ s ∈ Set.Icc (E.a i) (E.b i), 0 ≤ interimUtility E p x i s) ∧
  (∀ i, ∀ s ∈ Set.Icc (E.a i) (E.b i), ∀ r ∈ Set.Icc (E.a i) (E.b i),
    reportUtility E p x i s r ≤ interimUtility E p x i s)

/-- A feasible direct mechanism attaining the seller's maximum. -/
def IsOptimal {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : Environment ι) (p x : Outcome ι) : Prop :=
  Feasible E p x ∧ ∀ p' x', Feasible E p' x' →
    sellerUtility E p' x' ≤ sellerUtility E p x

/-- The objective (4.7) from Lemma 3. -/
def virtualObjective {ι : Type} [Fintype ι]
    (E : Environment ι) (p : Outcome ι) : ℝ :=
  ∫ t, (∑ i, (virtualValue E i (t i) - E.t0) * p i t) ∂distribution E

/-- Regularity for an allocation, without payments. -/
def AdmissibleAllocation {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : Environment ι) (p : Outcome ι) : Prop :=
  ProbabilityCondition E p ∧ MonotoneQ E p ∧
  (∀ i, Integrable (p i) (distribution E) ∧
    ∀ s ∈ Set.Icc (E.a i) (E.b i),
      Integrable (fun t => p i (Function.update t i s)) (distribution E))

end MyersonAuction.Optimal


