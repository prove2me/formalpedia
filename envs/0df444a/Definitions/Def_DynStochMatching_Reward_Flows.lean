-- Prove2me | Definitions.Def_DynStochMatching_Reward_Flows
-- name    : DynStochMatching_Reward_Flows
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T20:39:28.355557+00:00
-- url     : https://prove2.me/theorems/dc5a59a3-5704-4cc9-a94c-1b3ddac54d59
-- title:
--   Cost, reward and quadratic flow benchmarks
-- statement:
--   Nonnegative directed type-pair flows, abandonment flows and unused-passive flows define CB, RB and QB with their exact balance and rate constraints. An immediate type has zero outgoing active match flow, avoiding infinite-rate products. CB permits infinite forbidden costs. Optimal values use complete extended orders; the benchmark statements separately assert attainment. The arbitrary transformation divides RB match flow by four; the bipartite transformation retains the better directed partition and fills unused balance exactly as B.2. The RB matrix includes explicit slack variables and a concrete finite index encoding, with no extra hypothesis hidden in the LP representation.
-- source:
--   Aouad and Sarıtaç (2022), Dynamic Stochastic Matching Under Limited Time, https://doi.org/10.1287/opre.2022.2293, held published-basis manuscript, §3, §5.1 and B.2, printed 10–11, 21–22, 40–42 / PDF 11–12, 22–23, 41–43

import Definitions.Def_DynStochMatching_Reward_Policies
import Definitions.Def_DynStochMatching_Reward_LinearPrograms

open scoped ENNReal Classical

namespace DynStochMatching.Reward

structure Flow (n : ℕ) where
  edge : Fin n → Fin n → ℝ
  abandon : Fin n → ℝ
  unused : Fin n → ℝ

noncomputable def passiveRate {n : ℕ} (x : Flow n) (j : Fin n) : ℝ :=
  x.unused j + ∑ i, x.edge i j

noncomputable def outgoing {n : ℕ} (x : Flow n) (i : Fin n) : ℝ := ∑ j, x.edge i j
noncomputable def incoming {n : ℕ} (x : Flow n) (i : Fin n) : ℝ := ∑ j, x.edge j i

noncomputable def rateConstraint (l : Lifetime) (f p a : ℝ) : Prop :=
  match l with
  | .exponential μ _ => μ * f ≤ p * a
  | .immediate => f = 0

noncomputable def rbFeasible {n : ℕ} (D : Instance n) (x : Flow n) : Prop :=
  (∀ i j, 0 ≤ x.edge i j) ∧ (∀ i, 0 ≤ x.abandon i) ∧
  (∀ i, incoming x i + outgoing x i + x.abandon i = D.arrivalRate i) ∧
  (∀ i j, rateConstraint (D.lifetime i) (x.edge i j) (D.arrivalRate j) (x.abandon i)) ∧
  (∀ i, x.unused i = 0)

noncomputable def qbFeasible {n : ℕ} (D : Instance n) (x : Flow n) : Prop :=
  (∀ i j, 0 ≤ x.edge i j) ∧ (∀ i, 0 ≤ x.abandon i ∧ 0 ≤ x.unused i) ∧
  (∀ i, incoming x i + outgoing x i + x.abandon i + x.unused i = D.arrivalRate i) ∧
  (∀ i j, rateConstraint (D.lifetime i) (x.edge i j) (passiveRate x j) (x.abandon i))

noncomputable def flowReward {n : ℕ} (D : Instance n) (x : Flow n) : ℝ :=
  ∑ i, ∑ j, D.reward i j * x.edge i j

noncomputable def rbValue {n : ℕ} (D : Instance n) : EReal :=
  ⨆ x : {x : Flow n // rbFeasible D x}, (flowReward D x.val : EReal)

noncomputable def qbValue {n : ℕ} (D : Instance n) : EReal :=
  ⨆ x : {x : Flow n // qbFeasible D x}, (flowReward D x.val : EReal)

noncomputable def flowCost {n : ℕ} (C : Costs n) (x : Flow n) : ℝ≥0∞ :=
  (∑ i, C.abandonment i * ENNReal.ofReal (x.abandon i)) +
    ∑ i, ∑ j, C.edge i j * ENNReal.ofReal (x.edge i j)

noncomputable def cbValue {n : ℕ} (D : Instance n) (C : Costs n) : ℝ≥0∞ :=
  ⨅ x : {x : Flow n // rbFeasible D x}, flowCost C x.val

/-- Exact B.2 arbitrary-graph transformation, without an unprinted saturation step. -/
noncomputable def quarterFlow {n : ℕ} (D : Instance n) (x : Flow n) : Flow n where
  edge i j := x.edge i j / 4
  unused i := D.arrivalRate i / 2 - incoming x i / 4
  abandon i := D.arrivalRate i / 2 - outgoing x i / 4

noncomputable def directedReward {n : ℕ} (D : Instance n) (x : Flow n)
    (side : Fin n → Bool) : ℝ :=
  ∑ i, ∑ j, if side i = true ∧ side j = false then D.reward i j * x.edge i j else 0

noncomputable def orientSide {n : ℕ} (D : Instance n) (x : Flow n)
    (side : Fin n → Bool) : Fin n → Bool :=
  if directedReward D x side ≥ directedReward D x (fun i => !(side i)) then side
  else fun i => !(side i)

noncomputable def bipartiteFlow {n : ℕ} (D : Instance n) (x : Flow n)
    (side : Fin n → Bool) : Flow n := by
  classical
  let e := fun i j => if side i = true ∧ side j = false then x.edge i j else 0
  let a := fun i => if side i then x.abandon i else 0
  exact ⟨e, a, fun i => D.arrivalRate i - a i - (∑ j, e j i) - ∑ j, e i j⟩

abbrev FlowColumn (n : ℕ) := (Fin n × Fin n) ⊕ (Fin n ⊕ (Fin n × Fin n))
abbrev FlowRow (n : ℕ) := Fin n ⊕ (Fin n × Fin n)

def rowEquiv (n : ℕ) : FlowRow n ≃ Fin (n + n * n) :=
  (Equiv.sumCongr (Equiv.refl (Fin n)) finProdFinEquiv).trans finSumFinEquiv

def columnEquiv (n : ℕ) : FlowColumn n ≃ Fin (n * n + (n + n * n)) :=
  (Equiv.sumCongr finProdFinEquiv
    ((Equiv.sumCongr (Equiv.refl (Fin n)) finProdFinEquiv).trans finSumFinEquiv)).trans finSumFinEquiv

noncomputable def rbCoefficient {n : ℕ} (D : Instance n)
    (r : FlowRow n) (c : FlowColumn n) : ℝ := by
  classical
  exact match r, c with
  | .inl i, .inl (j, k) => (if i = j then 1 else 0) + (if i = k then 1 else 0)
  | .inl i, .inr (.inl j) => if i = j then 1 else 0
  | .inl _, .inr (.inr _) => 0
  | .inr (i, j), .inl (k, l) => if i = k ∧ j = l then
      match D.lifetime i with | .exponential μ _ => μ | .immediate => 1
    else 0
  | .inr (i, j), .inr (.inl k) => if i = k then
      match D.lifetime i with | .exponential _ _ => -D.arrivalRate j | .immediate => 0
    else 0
  | .inr (i, j), .inr (.inr (k, l)) => if i = k ∧ j = l then 1 else 0

noncomputable def rbProgram {n : ℕ} (D : Instance n) : LinearProgram where
  rows := n + n * n
  cols := n * n + (n + n * n)
  matrix r c := rbCoefficient D ((rowEquiv n).symm r)
    ((columnEquiv n).symm c)
  rhs r := match (rowEquiv n).symm r with
    | .inl i => D.arrivalRate i | .inr _ => 0
  objective c := match (columnEquiv n).symm c with
    | .inl (i, j) => D.reward i j | .inr _ => 0

noncomputable def solveRB {n : ℕ} (O : LinearOracle) (D : Instance n) : Flow n where
  edge i j := O.solve (rbProgram D) (columnEquiv n (.inl (i, j)))
  abandon i := O.solve (rbProgram D) (columnEquiv n (.inr (.inl i)))
  unused _ := 0

end DynStochMatching.Reward


