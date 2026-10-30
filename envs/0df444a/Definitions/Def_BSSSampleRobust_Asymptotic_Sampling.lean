-- Prove2me | Definitions.Def_BSSSampleRobust_Asymptotic_Sampling
-- name    : BSSSampleRobust_Asymptotic_Sampling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T22:26:46.552229+00:00
-- url     : https://prove2.me/theorems/ff52a587-dffa-4f80-a63d-ebd4c0e161cd
-- title:
--   Joint sampling law, uncertainty balls and asymptotic rates
-- statement:
--   A sampling setting is a Borel probability law on a finite-dimensional real $\ell_p$ space and a known convex superset $\Xi$ of its topological support, with $P(\Xi)=1$. The law of infinite sequences is the countable iid product law. The $N$th uncertainty sets intersect $\Xi$ with closed radius-$\epsilon_N$ balls centered at the first $N$ observations; their union is $S_N$. The light-tail predicate is the existence of $a>1$ with finite exponential moment $E_P\exp(\|\xi\|^a)$. The radius predicate is exactly $\epsilon_N=\kappa N^{-1/\max\{3,d+1\}}$ at every positive $N$, for one $\kappa>0$. The empirical transport rate has its separate $d=1$ and $d\ge2$ formulas. The error coefficient and coverage scaling are exactly $M_N=N^{-1/((d+1)(d+2))}\log N$ and $N^{1/(d+1)}/(\log N)^{d+1}$. Predicates define assumptions; no rate conclusion is a structure field.
-- source:
--   Bertsimas, Shtern and Sturt (2023), A Data-Driven Approach to Multistage Stochastic Linear Optimization, Management Science, https://doi.org/10.1287/mnsc.2022.4352; published basis, supplied manuscript/e-companion artifact; §§1.2–4.2, PDF/printed 6–12; Theorem 3, PDF/printed 15; Lemma EC.3, PDF 61 / ec19

import Mathlib
import Definitions.Def_BSSSampleRobust_Asymptotic_Policy
import Definitions.Def_BSSSampleRobust_Asymptotic_Transport

open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

open scoped ENNReal Classical

namespace BSSSampleRobust.Asymptotic

/-- A Borel law and a known convex superset of its topological support. -/
structure Sampling (p : ℝ≥0∞) [Fact (1 ≤ p)] (ι : Type) [Fintype ι] where
  law : Measure (Vec p ι)
  probability : IsProbabilityMeasure law
  known : Set (Vec p ι)
  convex_known : Convex ℝ known
  support_subset : law.support ⊆ known
  full_known : law known = 1

attribute [instance] Sampling.probability

def sampleLaw {p : ℝ≥0∞} [Fact (1 ≤ p)] {ι : Type} [Fintype ι]
    (S : Sampling p ι) : Measure (ℕ → Vec p ι) :=
  Measure.infinitePi (fun _ : ℕ => S.law)

def sampleBall {p : ℝ≥0∞} [Fact (1 ≤ p)] {ι : Type} [Fintype ι]
    (S : Sampling p ι) (ω : ℕ → Vec p ι) (ε : ℕ → ℝ) (N j : ℕ) : Set (Vec p ι) :=
  {z | z ∈ S.known ∧ ‖z - ω j‖ ≤ ε N}

def sampleUnion {p : ℝ≥0∞} [Fact (1 ≤ p)] {ι : Type} [Fintype ι]
    (S : Sampling p ι) (ω : ℕ → Vec p ι) (ε : ℕ → ℝ) (N : ℕ) : Set (Vec p ι) :=
  ⋃ j : Fin N, sampleBall S ω ε N j.val

def lightTail {p : ℝ≥0∞} [Fact (1 ≤ p)] {ι : Type} [Fintype ι]
    (P : Measure (Vec p ι)) : Prop :=
  ∃ a : ℝ, 1 < a ∧ expectation P (fun z => (Real.exp (‖z‖ ^ a) : EReal)) < ⊤

def radiusRate (d : ℕ) (ε : ℕ → ℝ) : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∀ N : ℕ, 1 ≤ N →
    ε N = κ * (N : ℝ) ^ (-(1 : ℝ) / (max 3 (d + 1) : ℕ))

def empiricalRate (d : ℕ) (κ : ℝ) (N : ℕ) : ℝ :=
  if d = 1 then κ * (N : ℝ) ^ (-(1 : ℝ) / 2) * Real.log N
  else κ * (N : ℝ) ^ (-(1 : ℝ) / d) * (Real.log N) ^ 2

def uniformError (d N : ℕ) : ℝ :=
  (N : ℝ) ^ (-(1 : ℝ) / ((d + 1) * (d + 2) : ℕ)) * Real.log N

def coverageScale (d N : ℕ) : ℝ :=
  (N : ℝ) ^ ((1 : ℝ) / (d + 1 : ℕ)) / (Real.log N) ^ (d + 1)

end BSSSampleRobust.Asymptotic


