-- Prove2me | Definitions.Def_JointParametricPricing_PSC_Optimization
-- name    : JointParametricPricing_PSC_Optimization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T08:46:05.949395+00:00
-- url     : https://prove2.me/theorems/213c4fb8-162e-4fe0-96d1-0a9b29879c3a
-- title:
--   Capacity programs, derivatives, and attained optima
-- statement:
--   A capacity program maximizes a real continuous objective on a compact domain in Euclidean space subject to finitely many linear resource inequalities. The feasible set is the intersection of the domain and those inequalities. Its optimum is an actual maximizer selected using the extreme value theorem, with a compiled attainment proof. The Lagrangian for maximization is $f(x)+\sum_i\mu_i(b_i-A_i x)$; a dual optimum minimizes its supremum over the domain among nonnegative multipliers. No Slater condition, row independence, or dual uniqueness is imposed. Coordinate derivatives and Euclidean vectors are shared notation. The pricing model instantiates this general program with $b=C/T$.
-- source:
--   Chen, Jasin and Duenyas (2021), Technical Note—Joint Learning and Optimization of Multi-Product Pricing with Finite Resource Capacity and Unknown Demand Parameters, DOI:10.1287/opre.2020.2078; held LBS manuscript/online appendix (published citation basis); §2, printed 9 / PDF 10; general capacity-program substrate

import Mathlib

open scoped BigOperators
noncomputable section

namespace JointParametricPricing.PSC

abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

def coordinate {n : ℕ} (j : Fin n) : Vec n := WithLp.toLp 2 (Pi.single j 1)

def coordDeriv {n : ℕ} (f : Vec n → ℝ) (x : Vec n) (j : Fin n) : ℝ :=
  deriv (fun t : ℝ => f (x + t • coordinate j)) 0

def secondPartial {n : ℕ} (f : Vec n → ℝ) (x : Vec n) (i j : Fin n) : ℝ :=
  coordDeriv (fun z => coordDeriv f z j) x i

/-- A capacity-constrained maximization problem; no constraint qualification is bundled. -/
structure CapacityProgram (n m : ℕ) where
  domain : Set (Vec n)
  objective : Vec n → ℝ
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ

namespace CapacityProgram
variable {n m : ℕ}
def load (Q : CapacityProgram n m) (x : Vec n) (i : Fin m) : ℝ :=
  ∑ j, Q.A i j * x j

def feasible (Q : CapacityProgram n m) : Set (Vec n) :=
  Q.domain ∩ {x | ∀ i, Q.load x i ≤ Q.b i}

def lagrangian (Q : CapacityProgram n m) (μ : Fin m → ℝ) (x : Vec n) : ℝ :=
  Q.objective x + ∑ i, μ i * (Q.b i - Q.load x i)

/-- Used only for a nonempty compact domain and a continuous objective. -/
def dualValue (Q : CapacityProgram n m) (μ : Fin m → ℝ) : ℝ :=
  sSup (Q.lagrangian μ '' Q.domain)

def IsDualOptimum (Q : CapacityProgram n m) (μ : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ μ i) ∧ ∀ ν : Fin m → ℝ, (∀ i, 0 ≤ ν i) → Q.dualValue μ ≤ Q.dualValue ν

theorem feasible_compact (Q : CapacityProgram n m) (h : IsCompact Q.domain) :
    IsCompact Q.feasible := by
  apply h.inter_right
  have heq : {x | ∀ i, Q.load x i ≤ Q.b i} = ⋂ i, {x | Q.load x i ≤ Q.b i} := by
    ext x; simp
  rw [heq]
  apply isClosed_iInter (fun i => ?_)
  exact isClosed_le (by unfold load; fun_prop) continuous_const

/-- Extreme-value selection, with an actual attainment proof. -/
def optimum (Q : CapacityProgram n m) (h : IsCompact Q.domain)
    (hne : Q.feasible.Nonempty) (hf : ContinuousOn Q.objective Q.domain) : Vec n :=
  Classical.choose ((Q.feasible_compact h).exists_isMaxOn hne (hf.mono Set.inter_subset_left))

theorem optimum_spec (Q : CapacityProgram n m) (h : IsCompact Q.domain)
    (hne : Q.feasible.Nonempty) (hf : ContinuousOn Q.objective Q.domain) :
    Q.optimum h hne hf ∈ Q.feasible ∧
      ∀ x ∈ Q.feasible, Q.objective x ≤ Q.objective (Q.optimum h hne hf) :=
  Classical.choose_spec ((Q.feasible_compact h).exists_isMaxOn hne
    (hf.mono Set.inter_subset_left))
end CapacityProgram
end JointParametricPricing.PSC


