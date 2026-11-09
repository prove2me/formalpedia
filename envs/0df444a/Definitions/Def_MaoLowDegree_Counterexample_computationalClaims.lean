-- Prove2me | Definitions.Def_MaoLowDegree_Counterexample_computationalClaims
-- name    : MaoLowDegree_Counterexample_computationalClaims
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:13.039834+00:00
-- url     : https://prove2.me/theorems/ae16af4c-0bb3-462b-a88d-d9da87dc01eb
-- title:
--   Strong distinction, polynomial tests, exact advice sampling, and Conjecture 1.1
-- statement:
--   A fixed program strongly distinguishes a graph-law family $R_n$ from $Q_n$ when its unconditional Planted probability under $R_n$ and its unconditional Null probability under $Q_n$ both converge to one. Tests receive no noise-rate or advice input. Randomized polynomial-time tests halt within $C(n+1)^p$ actual transitions on every graph and every coin stream and output exactly one label bit. Deterministic quadratic-time tests have no coin instruction and halt in $O(n^2)$ transitions.
--
--   An exact advice sampler is one finite randomized program with fixed advice strings $a_n$, such that its unconditional output law is $P_n$ at every $n$, with
--   $$|a_n|=O\bigl(n\log_2 n+(\log_2 n)^{2r}\bigr),\qquad \mathbb E\tau_n\le C(n+1)^p.$$
--
--   All constants and programs precede $n$; advice never depends on the fresh coins. The expectation is extended nonnegative, so a positive nonhalting probability cannot masquerade as a finite time.
--
--   Conjecture 1.1 quantifies over every permutation-invariant graph-law family. If, for some fixed $c>0$ and integer degrees $D_n\ge(\log_2 n)^{1+c}$ eventually, the degree-$D_n$ advantage is $O(1)$, then every fixed $\varepsilon\in(0,1)$ forbids every randomized polynomial-time strong test. Finite prefixes are ignored only in these asymptotic hypotheses. This is the universal conjecture, not its restriction to the alternating-form family.
-- source:
--   Songtao Mao, STOC 2027 submission #509 (October 2026), Conjecture 1.1, p.4; Theorem 1.2, p.5; §3.4, pp.14–15

import Definitions.Def_MaoLowDegree_Counterexample_bitRAM
import Definitions.Def_MaoLowDegree_Counterexample_rankTest

open Classical Filter
open scoped ENNReal Topology
noncomputable section
set_option autoImplicit false

namespace MaoLowDegree.Counterexample

/-- Unconditional probability of a label, including all internal test randomness. -/
def labelProbability {n : ℕ} (A : BitProgram) (P : GraphLaw n) (label : Bool) : ℝ :=
  (∑ Y : Graph n, P Y * outputMass A n (graphInput Y) [] [label]).toReal

/-- Both testing errors tend to zero. The fixed program has neither noise rate nor advice input. -/
def StronglyDistinguishes (A : BitProgram) (P : GraphFamily) : Prop :=
  Tendsto (fun n => labelProbability A (P n) true) atTop (nhds 1) ∧
  Tendsto (fun n => labelProbability A (nullLaw n) false) atTop (nhds 1)

/-- A polynomial-time randomized binary test: actual halting in a fixed polynomial number
of transitions on every graph and coin stream, with exactly one output bit. -/
def PolynomialTest (A : BitProgram) : Prop :=
  0 < A.wordFactor ∧ ∃ C p : ℕ, 0 < C ∧
    ∀ n : ℕ, ∀ Y : Graph n, HaltsWithin A n (graphInput Y) [] (C * (n + 1) ^ p) ∧
      ∀ coins : ℕ → Bool, ∀ t : ℕ,
        (runBits A n (graphInput Y) [] coins t).halted = true →
        (runBits A n (graphInput Y) [] coins t).output = [false] ∨
        (runBits A n (graphInput Y) [] coins t).output = [true]

/-- Deterministic, ε-independent O(n²) time. The finite initial segment has no asymptotic
runtime restriction, but the program still halts there and outputs a decision. -/
def QuadraticTest (A : BitProgram) : Prop :=
  HasNoCoins A ∧ 0 < A.wordFactor ∧ ∃ C N : ℕ, 0 < C ∧
    (∀ n ≥ N, ∀ Y : Graph n, HaltsWithin A n (graphInput Y) [] (C * n ^ 2)) ∧
    ∀ n : ℕ, ∀ Y : Graph n, ∃ t : ℕ,
      (runBits A n (graphInput Y) [] (fun _ => false) t).halted = true ∧
      ((runBits A n (graphInput Y) [] (fun _ => false) t).output = [false] ∨
       (runBits A n (graphInput Y) [] (fun _ => false) t).output = [true])

/-- Uniform finite-program realization of Algorithm 1, with no computational rank oracle. -/
def ImplementsRankTest (A : BitProgram) (a σ : ℚ) : Prop :=
  ∀ n : ℕ, ∀ Y : Graph n, ∃ t : ℕ,
    (runBits A n (graphInput Y) [] (fun _ => false) t).halted = true ∧
    (runBits A n (graphInput Y) [] (fun _ => false) t).output = [rankTest a σ Y]

/-- Exact bounded-advice sampling from P at every n. Time is the expectation of the
untruncated stopping time, and advice is fixed before the fresh fair stream. -/
def ExactAdviceSampler (r : ℕ) (P : GraphFamily) : Prop :=
  ∃ S : BitProgram, 0 < S.wordFactor ∧ ∃ advice : ℕ → List Bool,
    (∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ((advice n).length : ℝ) ≤ C * ((n : ℝ) * log₂ n + (log₂ n) ^ (2 * r))) ∧
    (∃ C p : ℕ, 0 < C ∧ ∀ n : ℕ,
      expectedSteps S n (unaryInput n) (advice n) ≤ (C * (n + 1) ^ p : ℕ)) ∧
    ∀ n : ℕ, ∀ Y : Graph n,
      outputMass S n (unaryInput n) (advice n) (graphBits Y) = P n Y

/-- Conjecture 1.1 over all permutation-invariant graph laws, with real low-degree
advantage and arbitrary randomized polynomial-time tests. Finite prefixes do not affect
its degree or O(1) advantage assumptions. -/
def PolynomialTimeLowDegreeConjecture : Prop :=
  ∀ P : GraphFamily, (∀ n, PermutationInvariant (P n)) →
    (∃ c : ℝ, 0 < c ∧ ∃ D : ℕ → ℕ,
      (∀ᶠ n : ℕ in atTop, (log₂ n) ^ (1 + c) ≤ (D n : ℝ)) ∧
      (∃ C : ℝ, ∀ᶠ n : ℕ in atTop, advantage (P n) (D n) ≤ C)) →
    ∀ ε : Rate, 0 < ε.val → ε.val < 1 → ∀ A : BitProgram,
      PolynomialTest A → ¬ StronglyDistinguishes A (fun n => noise ε (P n))

end MaoLowDegree.Counterexample


