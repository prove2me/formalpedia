-- Prove2me | Definitions.Def_RandomStreamCI_CodeIntersection_Probability
-- name    : RandomStreamCI_CodeIntersection_Probability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:26:11.80903+00:00
-- url     : https://prove2.me/theorems/9dd83ca7-5e2b-4eac-93a7-354c42f0834a
-- title:
--   Finite probability, classical min-entropy and restoring partitions
-- statement:
--   For a finite law $p$ and event $E$, event mass is $\sum_{x\in E}p(x)$ and conditioning divides each weight in $E$ by its mass. Zero conditioning mass gives the zero function. Classical min-entropy is
--
--   $$H_\infty(p)=\min_{p(x)>0}\log_2(1/p(x)).$$
--
--   Marginals are actual pushforwards onto subsets of Boolean coordinates. Density tests all marginal subsets. Ordered partition data record parts, fixed coordinates and assignments; the restoring-partition predicate states support partition, fixed assignments, density and the signed tail-entropy inequality. It asserts no existence theorem. Probability laws in the theorems are normalized PMFs; the zero function is never passed to an entropy theorem as a probability law. These definitions support finite information arguments beyond this stream problem.
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Definitions 8 and 10, Lemma 11, p. 9; conditional-law convention (10), p. 8

import Mathlib

noncomputable section

namespace RandomStreamCI.CodeIntersection

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- All logarithms in the source, p. 5, are base two. -/
def log₂ (x : ℝ) : ℝ := Real.logb 2 x

/-- Finite event mass, also used for the zero posterior on an unreachable event. -/
def eventMass {α : Type*} [Fintype α] (p : α → ℝ) (E : α → Prop) : ℝ :=
  ∑ x, if E x then p x else 0

/-- Real weights of a Mathlib probability mass function. -/
def weights {α : Type*} (p : PMF α) (x : α) : ℝ := (p x).toReal

/-- Conditional weights; zero conditioning mass gives the source's zero function (10). -/
def conditioned {α : Type*} [Fintype α] (p : α → ℝ) (E : α → Prop) (x : α) : ℝ :=
  if E x then p x / eventMass p E else 0

/-- Uniform finite event probability; applications have a nonempty sample space. -/
def uniformProbability {α : Type*} [Fintype α] (E : α → Prop) : ℝ :=
  eventMass (fun _ : α => (Fintype.card α : ℝ)⁻¹) E

/-- Unsmoothed min-entropy, Definition 8 (15), over positive support only.
The value on the zero function is the real infimum convention 0; entropy assertions
below are only made for probability laws or positive-mass conditionings. -/
def minEntropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  sInf {h : ℝ | ∃ x, 0 < p x ∧ h = log₂ (1 / p x)}

/-- Restriction law on exactly the coordinates in I. -/
def marginal {J : Type*} [Fintype J] (p : (J → Bool) → ℝ) (I : Finset J)
    (y : I → Bool) : ℝ :=
  eventMass p (fun x => (fun i : I => x i) = y)

/-- Definition 10: every marginal, including the empty marginal, is dense. -/
def IsDense {J : Type*} [Fintype J] (p : (J → Bool) → ℝ) (γ : ℝ) : Prop :=
  ∀ I : Finset J, γ * I.card ≤ minEntropy (marginal p I)

/-- Bare ordered partition data; no entropy property is assumed by the data type. -/
structure PartitionData (J : Type*) [Fintype J] where
  r : ℕ
  part : Fin r → Finset (J → Bool)
  fixed : Fin r → Finset J
  assignment : (j : Fin r) → fixed j → Bool

/-- Ordered tail in Lemma 11, with its original (nonpositive) logarithm. -/
def tailMass {J : Type*} [Fintype J] (p : (J → Bool) → ℝ)
    (P : PartitionData J) (j : Fin P.r) : ℝ :=
  eventMass p (fun x => ∃ i : Fin P.r, j ≤ i ∧ x ∈ P.part i)

/-- All three conclusions of Lemma 11 plus a partition of the positive support. -/
def IsRestoringPartition {J : Type*} [Fintype J] [DecidableEq J]
    (p : (J → Bool) → ℝ) (γ : ℝ) (P : PartitionData J) : Prop :=
  (∀ x, 0 < p x ↔ ∃! j : Fin P.r, x ∈ P.part j) ∧
  (∀ j, (P.part j).Nonempty) ∧
  (∀ j, ∀ x ∈ P.part j, 0 < p x) ∧
  ∀ j,
    (∀ x ∈ P.part j, ∀ i : P.fixed j, x i = P.assignment j i) ∧
    IsDense (marginal (conditioned p (fun x => x ∈ P.part j)) (P.fixed j)ᶜ) γ ∧
    minEntropy p - γ * (P.fixed j).card + log₂ (tailMass p P j) ≤
      minEntropy (marginal (conditioned p (fun x => x ∈ P.part j)) (P.fixed j)ᶜ)

end RandomStreamCI.CodeIntersection


