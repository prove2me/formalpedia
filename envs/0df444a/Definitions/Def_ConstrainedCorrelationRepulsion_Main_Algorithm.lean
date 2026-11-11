-- Prove2me | Definitions.Def_ConstrainedCorrelationRepulsion_Main_Algorithm
-- name    : ConstrainedCorrelationRepulsion_Main_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:25:33.085597+00:00
-- url     : https://prove2.me/theorems/d201865e-073f-4e43-865d-bc20d865cd7e
-- title:
--   Operational approximation and uniform resource bounds
-- statement:
--   The input oracle exposes only the three encoded pair sets, with an additional real pair-cost interface in the probability-weighted regime. The initial state contains $n$ and zero memory. Output words encode partition labels. All supported outputs must be feasible, and their finite-distribution expected disagreement cost is compared with the constrained optimum.
--
--   Polynomial time means one finite program and constants fixed before the instance, with a bound $C\max(2,n)^d$ on charged execution. The headline resource bound is
--   $$\left\lceil C\left(\frac{\max(2,n)}{\min(\varepsilon,1)}\right)^{k/\min(\varepsilon,1)^2}\right\rceil.$$
--   Its constants $C,k$ are uniform in the accuracy and the instance. This is the paper's $(n/\varepsilon)^{O(\varepsilon^{-2})}$ convention for $0<\varepsilon\le1$, extended using accuracy one when $\varepsilon>1$. Input feasibility supplies no optimizer, sampler, work certificate, or output distribution.
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Theorems 1.1, 2.2, 3.3; §6.3, printed pp.1, 15–16, 34–35 (PDF pp.2, 16–17, 35–36)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Instance
import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Program

namespace ConstrainedCorrelationRepulsion.Main

open Classical
open scoped BigOperators ENNReal

noncomputable def inputOracle {n : ℕ} (I : Instance n) : ℕ → ℕ → ℕ → ℝ :=
  fun bank u v => if h : u < n ∧ v < n then
    let a : Fin n := ⟨u,h.1⟩
    let b : Fin n := ⟨v,h.2⟩
    if bank = 0 then (if I.positive.Adj a b then 1 else 0)
    else if bank = 1 then (if I.mustLink.Adj a b then 1 else 0)
    else if bank = 2 then (if I.cannotLink.Adj a b then 1 else 0) else 0
  else 0

noncomputable def weightedOracle {n : ℕ} (I : Instance n) (w : PairCosts n) : ℕ → ℕ → ℕ → ℝ :=
  fun bank u v => if h : u < n ∧ v < n then
    if bank = 3 then w.separate s((⟨u,h.1⟩ : Fin n), (⟨v,h.2⟩ : Fin n))
    else if bank = 4 then w.together s((⟨u,h.1⟩ : Fin n), (⟨v,h.2⟩ : Fin n))
    else inputOracle I bank u v
  else 0

/-- Initial state contains only n (register 0); the n output-word reads are charged here.
All information about the instance is read through the charged input oracle. -/
def initialState (n : ℕ) : MachineState :=
  {natReg := Function.update (fun _ => 0) 0 n, work := n + 1}

/-- Output labels are reduced modulo n. The function has no inputs when n=0; for each
actual vertex n>0, so the modulus is never zero. -/
def outputPartition {n : ℕ} (s : MachineState) : Partition n :=
  fun v => ⟨s.natMem v.val % n, Nat.mod_lt _ (by have hv := v.isLt; omega)⟩

noncomputable def outputLaw {n : ℕ} (code : Program) (oracle : ℕ → ℕ → ℕ → ℝ)
    (initial : MachineState) (B : ℕ) (bitModel : Bool := true) : PMF (Partition n) :=
  (machineRun bitModel code oracle initial B).map outputPartition

noncomputable def expectedCost {n : ℕ} (I : Instance n) (p : PMF (Partition n)) : ℝ :=
  ∑ P, (p P).toReal * (cost I P : ℝ)

noncomputable def expectedWeightedCost {n : ℕ} (w : PairCosts n)
    (p : PMF (Partition n)) : ℝ := ∑ P, (p P).toReal * weightedCost w P

/-- Concrete operational approximation guarantee. Running time is measured by the interpreter;
every supported output, including rare ones, satisfies the hard constraints. -/
def Approximates {n : ℕ} (code : Program) (I : Instance n) (ratio : ℝ) (B : ℕ) : Prop :=
  BoundedRun true code (inputOracle I) (initialState n) B ∧
  (∀ P ∈ (outputLaw code (inputOracle I) (initialState n) B).support, Feasible I P) ∧
  expectedCost I (outputLaw code (inputOracle I) (initialState n) B) ≤ ratio * (OPT I : ℝ)

def WeightedApproximates {n : ℕ} (code : Program) (I : Instance n) (w : PairCosts n)
    (ratio : ℝ) (B : ℕ) : Prop :=
  BoundedRun false code (weightedOracle I w) (initialState n) B ∧
  (∀ P ∈ (outputLaw code (weightedOracle I w) (initialState n) B false).support, Feasible I P) ∧
  expectedWeightedCost w (outputLaw code (weightedOracle I w) (initialState n) B false) ≤
    ratio * weightedOPT I w

def polynomialBound (C d n : ℕ) : ℕ := C * (max 2 n) ^ d

/-- Uniform constants for the conventional 0<ε≤1 regime, with ε>1 handled at ε=1,
and max(2,n) taking care of empty and one-vertex instances. -/
noncomputable def resourceBound (C k : ℕ) (epsilon : ℝ) (n : ℕ) : ℕ :=
  ⌈(C : ℝ) * ((max 2 n : ℕ) / min epsilon 1) ^ ((k : ℝ) / (min epsilon 1) ^ 2)⌉₊

def PolynomialApproximation (ratio : ℝ) (onlyCannotLinks : Bool) : Prop :=
  ∃ code : Program, ∃ C d : ℕ, 0 < C ∧ 0 < d ∧
    ∀ n (I : Instance n), FeasibleInput I → (onlyCannotLinks = true → I.mustLink = ⊥) →
      Approximates code I ratio (polynomialBound C d n)

def WeightedPolynomialApproximation (ratio : ℝ) : Prop :=
  ∃ code : Program, ∃ C d : ℕ, 0 < C ∧ 0 < d ∧
    ∀ n (I : Instance n) (p : ProbabilityWeights n), FeasibleInput I → I.mustLink = ⊥ →
      WeightedApproximates code I (probabilityCosts p) ratio (polynomialBound C d n)

end ConstrainedCorrelationRepulsion.Main


