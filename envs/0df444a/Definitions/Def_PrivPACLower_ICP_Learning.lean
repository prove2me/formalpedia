-- Prove2me | Definitions.Def_PrivPACLower_ICP_Learning
-- name    : PrivPACLower_ICP_Learning
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T13:46:22.821408+00:00
-- url     : https://prove2.me/theorems/3c26dadd-2a45-486b-b79d-c0893a5708a7
-- title:
--   Randomized improper private PAC learning and extended sample complexity
-- statement:
--   Let $X$ be any domain, $H\subseteq\{0,1\}^X$ a class, and $S\in(X\times\{0,1\})^n$ an ordered database. A learner $M$ assigns a general probability measure on all binary hypotheses to every database. Domain distributions $\mu$ are probability mass functions. Empirical and population errors are
--
--   $$\operatorname{err}_S(h)=\frac1n\sum_{i=1}^n\mathbf1\{h(x_i)\ne y_i\},\qquad \operatorname{err}_\mu(h)=\sum_z\mu(z)\mathbf1\{h(z_x)\ne z_y\}.$$
--
--   Realizability means that some member of $H$ has zero error. PAC failure probability averages the output measure of the error event over all i.i.d. samples, so it includes both sources of randomness. $M$ is an $(\alpha,\beta)$-PAC learner when this failure probability is at most $\beta$ for every realizable $\mu$. The private sample complexity is
--
--   $$m_{\rm priv}(H;\varepsilon,\delta,\alpha,\beta)=\inf\{n\in\mathbb N:\exists M\text{ satisfying both DP and PAC}\}\in\mathbb N\cup\{\infty\}.$$
--
--   The module also defines empirical guarantees, joint expected errors, and non-triviality: two hypotheses agree at one point and disagree at another. These are the shared interfaces used by all lower bounds.
--
--   **Formalization Note** Samples of size zero have empirical error zero. The infimum of an empty feasible set is infinity. PAC predicates extend to nonnegative thresholds outside $(0,1)$ to express the paper's $12\alpha$ amplification conclusion. No membership of the output in $H$ is required. Output events use the product sigma-algebra. The PMF interpretation on arbitrary domains and its effect on theorem strength are declared separately on each theorem.
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 10–11, Section 2 and Definition 3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP

abbrev Learner (X : Type*) (n : ℕ) :=
  PrivateUniformGen.Characterization.Mechanism (X × Bool) (X → Bool) n

noncomputable def empiricalError {X : Type*} {n : ℕ}
    (S : Fin n → X × Bool) (h : X → Bool) : ℝ≥0∞ :=
  (∑ i, if h (S i).1 ≠ (S i).2 then 1 else 0) / (n : ℝ≥0∞)

def RealizableDB {X : Type*} {n : ℕ} (H : Set (X → Bool))
    (S : Fin n → X × Bool) : Prop :=
  ∃ h ∈ H, ∀ i, h (S i).1 = (S i).2

noncomputable def populationError {X : Type*} (μ : PMF (X × Bool))
    (h : X → Bool) : ℝ≥0∞ :=
  ∑' z, μ z * (if h z.1 ≠ z.2 then 1 else 0)

def RealizableLaw {X : Type*} (H : Set (X → Bool)) (μ : PMF (X × Bool)) : Prop :=
  ∃ h ∈ H, populationError μ h = 0

noncomputable def sampleWeight {Z : Type*} {n : ℕ}
    (μ : PMF Z) (S : Fin n → Z) : ℝ≥0∞ := ∏ i, μ (S i)

noncomputable def PACFailure {X : Type*} {n : ℕ} (M : Learner X n)
    (μ : PMF (X × Bool)) (α : ℝ) : ℝ≥0∞ :=
  ∑' S, sampleWeight μ S * (M S : Measure (X → Bool))
    {h | ENNReal.ofReal α < populationError μ h}

def PACAt {X : Type*} {n : ℕ} (M : Learner X n)
    (μ : PMF (X × Bool)) (α β : ℝ) : Prop :=
  PACFailure M μ α ≤ ENNReal.ofReal β

def IsPACLearner {X : Type*} {n : ℕ} (H : Set (X → Bool))
    (M : Learner X n) (α β : ℝ) : Prop :=
  ∀ μ : PMF (X × Bool), RealizableLaw H μ → PACAt M μ α β

noncomputable def mpriv {X : Type*} (H : Set (X → Bool)) (ε δ α β : ℝ) : ℕ∞ :=
  sInf {s | ∃ n : ℕ, s = (n : ℕ∞) ∧ ∃ M : Learner X n,
    PrivateUniformGen.Characterization.IsDP M ε δ ∧ IsPACLearner H M α β}

/-- Preserve infinity when moving sample complexities into the real bound. -/
noncomputable def costReal (s : ℕ∞) : ℝ≥0∞ :=
  (s : ℝ≥0∞)

def NontrivialClass {X : Type*} (H : Set (X → Bool)) : Prop :=
  ∃ h₁ ∈ H, ∃ h₂ ∈ H, ∃ x x' : X, h₁ x = h₂ x ∧ h₁ x' ≠ h₂ x'

def EmpiricalGuarantee {X : Type*} {n : ℕ} (H : Set (X → Bool))
    (M : Learner X n) (α β : ℝ) : Prop :=
  ∀ S, RealizableDB H S →
    (M S : Measure (X → Bool)) {h | ENNReal.ofReal α < empiricalError S h} ≤
      ENNReal.ofReal β

noncomputable def expectedEmpirical {X : Type*} {n : ℕ}
    (ν : PMF (Fin n → X × Bool)) (M : Learner X n) : ℝ≥0∞ :=
  ∑' S, ν S * ∫⁻ h, empiricalError S h ∂(M S : Measure (X → Bool))

noncomputable def expectedPopulation {X : Type*} {n : ℕ}
    (μ : PMF (X × Bool)) (M : Learner X n) : ℝ≥0∞ :=
  ∑' S, sampleWeight μ S * ∫⁻ h, populationError μ h ∂(M S : Measure (X → Bool))

noncomputable def expectedSampleError {X : Type*} {n : ℕ}
    (μ : PMF (X × Bool)) (M : Learner X n) : ℝ≥0∞ :=
  ∑' S, sampleWeight μ S * ∫⁻ h, empiricalError S h ∂(M S : Measure (X → Bool))

end PrivPACLower.ICP


