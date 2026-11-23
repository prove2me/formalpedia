-- Prove2me | Definitions.Def_StrategicRFx_Benefit_Supplement_Primitives
-- name    : StrategicRFx_Benefit_Supplement_Primitives
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:02:50.783015+00:00
-- url     : https://prove2.me/theorems/a28f1b68-0d45-4a81-9f99-f3ea508a6c7d
-- title:
--   §§2.1–2.4 — quantities, unrestricted contracts, sourcing, payoffs and primitive assumptions
-- statement:
--   There is one buyer and two suppliers. Quantities range over the nonnegative real quadrant. Revenue is $V(q_1,q_2)$ and production costs are $C_i(q_i)$, so total profit is
--
--   $$\Pi(q_1,q_2)=V(q_1,q_2)-C_1(q_1)-C_2(q_2).$$
--
--   The unique interior first best and both exclusive optima are represented by their quantity witnesses and maximizing properties. Bargaining powers lie in $(0,1)$. The normalized technology is twice differentiable and has strictly negative mixed partial Lebesgue almost everywhere on the quadrant; continuity of second derivatives is not imposed. This is the deterministic interpretation of “almost surely” in Assumption 2.
--
--   A contract consists of two unrestricted real payment functions on positive quantities: normal payment and exclusive payment. No deal forbids procurement from that supplier. Actual sourcing maximizes buyer profit over all available strictly positive dual and exclusive orders and no transaction. Conditional dual and exclusive maximizers are separate relations. Exclusive supplier profit is nonnegative at an attained optimal exclusive order (Assumption 3). No blanket attainment condition is imposed on arbitrary payment functions.
--
--   The definitions give every player's payoff, coordination as equality to the unrestricted first-best profit, Pareto improvement, constant-markup contracts, the exact four cost-plus replacements of Theorem 3, and reduced scalar parameters computed from the technology. No proof of the bridge to the published Standing predicate is included in this definition.
--
--   **Formalization Note** Suppliers 1 and 2 are represented by `Fin 2`. The no-transaction option uses the p. 7 normalization and p. 8 no-deal convention. Maxima are witnessed, never totalized using a default supremum. First-best and exclusive quantity witnesses name the maxima already used in the source; they do not impose compactness. The replacement constructor alone does not assert its equilibrium implementation.
-- source:
--   Chu, Rong & Zheng, The Strategic Benefit of Request for Proposal/Quotation, SSRN 3200030 (2019 preprint; Oper. Res. doi:10.1287/opre.2019.1964), §§2.1–2.4, pp. 7–10; Theorem 3, p. 11

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Setting

namespace StrategicRFx.Benefit.Supplement

/-- §2.1: quantities are unrestricted nonnegative real numbers. -/
def quadrant : Set (ℝ × ℝ) := {q | 0 ≤ q.1 ∧ 0 ≤ q.2}

structure Technology where
  revenue : ℝ × ℝ → ℝ
  cost : Fin 2 → ℝ → ℝ
  power : Fin 2 → ℝ

def chainProfit (M : Technology) (q : ℝ × ℝ) : ℝ :=
  M.revenue q - M.cost 0 q.1 - M.cost 1 q.2

def exclusiveQuantity (i : Fin 2) (q : ℝ) : ℝ × ℝ :=
  if i = 0 then (q, 0) else (0, q)

def exclusiveProfit (M : Technology) (i : Fin 2) (q : ℝ) : ℝ :=
  chainProfit M (exclusiveQuantity i q)

/-- Witnesses for the maxima denoted by max on p. 7. They carry no default value. -/
structure FirstBest where
  dual : ℝ × ℝ
  exclusive : Fin 2 → ℝ

/-- Assumptions 1–2 and the normalization, pp. 7, 10. Twice differentiable
is expressed by differentiability of the derivative, without continuity of it.
The deterministic 'almost surely' is read as Lebesgue almost everywhere. -/
def TechnologyAssumptions (M : Technology) (b : FirstBest) : Prop :=
  M.revenue (0, 0) = 0 ∧ (∀ i, M.cost i 0 = 0) ∧
  (∀ i, 0 < M.power i ∧ M.power i < 1) ∧
  0 < b.dual.1 ∧ 0 < b.dual.2 ∧
  (∀ q ∈ quadrant, chainProfit M q ≤ chainProfit M b.dual) ∧
  (∀ q ∈ quadrant, chainProfit M q = chainProfit M b.dual → q = b.dual) ∧
  (∀ i, 0 ≤ b.exclusive i ∧ ∀ q : ℝ, 0 ≤ q →
    exclusiveProfit M i q ≤ exclusiveProfit M i (b.exclusive i)) ∧
  DifferentiableOn ℝ (chainProfit M) quadrant ∧
  DifferentiableOn ℝ (fderivWithin ℝ (chainProfit M) quadrant) quadrant ∧
  (∀ᵐ q ∂(MeasureTheory.volume.restrict quadrant),
    (fderivWithin ℝ (fderivWithin ℝ (chainProfit M) quadrant) quadrant q (1, 0)) (0, 1) < 0)

/-- The published reduced parameters, now computed from the primitive technology. -/
def toParams (M : Technology) (b : FirstBest) : Params where
  θ := M.power
  Pi := chainProfit M b.dual
  PiEx := fun i => exclusiveProfit M (other i) (b.exclusive (other i))
  PiExAt := fun i => exclusiveProfit M (other i)
    (if other i = 0 then b.dual.1 else b.dual.2)

/-- All quantity-dependent transfer functions of §2.1; no continuity, concavity,
compactness or bound is imposed. The domain of use is q > 0. -/
structure Payment where
  normal : ℝ → ℝ
  exclusive : ℝ → ℝ

/-- `none` is the no-deal contract; it forbids positive procurement. -/
abbrev Contract := Option Payment
abbrev Contracts := Fin 2 → Contract

structure Payoff where
  buyer : ℝ
  supplier : Fin 2 → ℝ

def WeaklyImproves (v w : Payoff) : Prop :=
  w.buyer ≤ v.buyer ∧ ∀ i, w.supplier i ≤ v.supplier i

def StrictlyImproves (v w : Payoff) : Prop :=
  WeaklyImproves v w ∧ (w.buyer < v.buyer ∨ ∃ i, w.supplier i < v.supplier i)

/-- Dual sourcing, exclusive sourcing, and no transaction. Positive sourcing
branches enforce strictly positive orders as in (1)–(2). -/
inductive Sourcing where
  | none
  | dual (q : ℝ × ℝ)
  | single (i : Fin 2) (q : ℝ)

def sourcingQuantity : Sourcing → ℝ × ℝ
  | .none => (0, 0)
  | .dual q => q
  | .single i q => exclusiveQuantity i q

def Available (c : Contracts) : Sourcing → Prop
  | .none => True
  | .dual q => 0 < q.1 ∧ 0 < q.2 ∧ (c 0).isSome ∧ (c 1).isSome
  | .single i q => 0 < q ∧ (c i).isSome

/-- Finite real transfers are evaluated only on Available branches. The zero
function on no deal is never used to permit positive procurement. -/
def normalTransfer (c : Contract) (q : ℝ) : ℝ :=
  match c with | none => 0 | some t => t.normal q

def exclusiveTransfer (c : Contract) (q : ℝ) : ℝ :=
  match c with | none => 0 | some t => t.exclusive q

def outcomePayoff (M : Technology) (c : Contracts) : Sourcing → Payoff
  | .none => ⟨0, fun _ => 0⟩
  | .dual q =>
    ⟨M.revenue q - normalTransfer (c 0) q.1 - normalTransfer (c 1) q.2,
      fun i => normalTransfer (c i) (if i = 0 then q.1 else q.2) -
        M.cost i (if i = 0 then q.1 else q.2)⟩
  | .single i q =>
    ⟨M.revenue (exclusiveQuantity i q) - exclusiveTransfer (c i) q,
      fun j => if j = i then exclusiveTransfer (c i) q - M.cost i q else 0⟩

/-- Equation (2), including the no-transaction alternative. A failed or
unbounded optimization has no witness, rather than the numerical value zero. -/
def IsExclusiveOrder (M : Technology) (c : Contract) (i : Fin 2) (s : Sourcing) : Prop :=
  (s = .none ∨ ∃ q, s = .single i q) ∧
  Available (fun j => if j = i then c else none) s ∧
  ∀ r, (r = .none ∨ ∃ q, r = .single i q) →
    Available (fun j => if j = i then c else none) r →
    (outcomePayoff M (fun j => if j = i then c else none) r).buyer ≤
      (outcomePayoff M (fun j => if j = i then c else none) s).buyer

def exclusivePayoff (M : Technology) (c : Contract) (i : Fin 2) (s : Sourcing) : Payoff :=
  outcomePayoff M (fun j => if j = i then c else none) s

/-- Equation (1): conditional optimum on the strictly positive dual branch. -/
def IsDualOrder (M : Technology) (c : Contracts) (q : ℝ × ℝ) : Prop :=
  Available c (.dual q) ∧ ∀ r, Available c (.dual r) →
    (outcomePayoff M c (.dual r)).buyer ≤ (outcomePayoff M c (.dual q)).buyer

/-- §2.2: actual sourcing also compares both exclusive branches and no deal. -/
def IsBuyerOrder (M : Technology) (c : Contracts) (s : Sourcing) : Prop :=
  Available c s ∧ ∀ r, Available c r →
    (outcomePayoff M c r).buyer ≤ (outcomePayoff M c s).buyer

/-- Assumption 3 restricts the contracts used in a bargain. It does not impose
pointwise nonnegative markups away from an optimal exclusive order. -/
def Admissible (M : Technology) (c : Contract) (i : Fin 2) : Prop :=
  ∃ s, IsExclusiveOrder M c i s ∧ 0 ≤ (exclusivePayoff M c i s).supplier i

def IsCoordinated (M : Technology) (b : FirstBest) (s : Sourcing) : Prop :=
  chainProfit M (sourcingQuantity s) = chainProfit M b.dual

/-- A contract's normal and exclusive profit are constant in positive quantity. -/
def IsCostPlus (M : Technology) (i : Fin 2) (c : Contract) : Prop :=
  ∃ t a e, c = some t ∧
    (∀ q : ℝ, 0 < q → t.normal q = M.cost i q + a) ∧
    (∀ q : ℝ, 0 < q → t.exclusive q = M.cost i q + e)

/-- The four exact replacement formulas of Theorem 3. `v` is the original
normal payoff and `e i` the original exclusive sourcing outcome with supplier i. -/
def replacement (M : Technology) (b : FirstBest) (c : Contracts)
    (v : Payoff) (e : Fin 2 → Sourcing) : Contracts := fun i =>
  some { normal := fun q => M.cost i q + v.supplier i
         exclusive := fun q => M.cost i q +
           exclusiveProfit M i (b.exclusive i) - (exclusivePayoff M (c i) i (e i)).buyer }

end StrategicRFx.Benefit.Supplement


