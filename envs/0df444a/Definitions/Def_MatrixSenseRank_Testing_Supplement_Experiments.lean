-- Prove2me | Definitions.Def_MatrixSenseRank_Testing_Supplement_Experiments
-- name    : MatrixSenseRank_Testing_Supplement_Experiments
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:05:44.039752+00:00
-- url     : https://prove2.me/theorems/4e525921-b0d3-49d7-8fc2-30a14e53eb3a
-- title:
--   Full-Gaussian and full-vector experiments
-- statement:
--   Let $A\in\mathbb R^{n\times m}$ be a fixed unknown rectangular matrix. A full-Gaussian observation draws a matrix $X$ with independent standard normal entries and independent noise $\eta\sim N(0,\sigma^2)$, and returns the entire pair
--
--   $$ (X,\langle A,X\rangle_F+\eta),\qquad \langle A,X\rangle_F=\sum_{i,j}A_{ij}X_{ij}. $$
--
--   The case $\sigma=0$ is noiseless. The vector experiment draws independent product-normal coordinates $x_i=G_iH_i$ and independent standard normal noise, returning $(x,w\cdot x+\eta)$ for any signed vector $w$. Full observations, including all covariates, are retained.
--
--   For a fixed randomized Boolean test and a fixed sample size, the rank guarantee universally quantifies all hidden unit-Frobenius matrices satisfying an optional promise, with acceptance at least $p$ at rank at most $k$ and acceptance at most $1-p$ at normalized rank distance at least $\varepsilon$. The vector guarantee uses unit vectors, $p=9/10$, and strict distance greater than $\varepsilon$. Independent observation tuples and test randomization use the published statistical-test interface.
--
--   These laws distinguish the two access models used by the companion theorems. The accuracy scale is $k^{-3/2}=1/(k\sqrt{k})$ for positive $k$.
-- source:
--   Yiqiao Bao, Anindya De, Shivam Nadimpalli, Rocco A. Servedio, Chenyang Sun, Nathan White, Matrix sensing meets property testing: Sample-optimal testing for low rank, STOC 2027 submission #380 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/380.pdf, PDF SHA-256 6e4e46ced4dfe65bbe94e4cec3e8230032914efef9d87b0f544bbea151a00c3b; §§1.2, 3.1–3.2, Eq. (5), Theorem 15, printed p. 2–3, 12, 21–22, 28–29, PDF p. 3–4, 13, 22–23, 29–30 (1-based).

import Mathlib
import Definitions.Def_MatrixSenseRank_Testing_Experiment

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace MatrixSenseRank.Testing.Supplement

abbrev Mat (n m : ℕ) := Matrix (Fin n) (Fin m) ℝ
abbrev Observation (n m : ℕ) := Mat n m × ℝ

def frobeniusInner {n m : ℕ} (A B : Mat n m) : ℝ :=
  ∑ i, ∑ j, A i j * B i j

/-- Independent entries, rather than rank-one measurement matrices. -/
noncomputable def fullGaussian (n m : ℕ) : Measure (Mat n m) :=
  Measure.map (fun f : Fin n → Fin m → ℝ => Matrix.of f)
    (Measure.pi (fun _ : Fin n => coordinateLaw (gaussianReal 0 1) m))

/-- sigma is a standard deviation; sigma=0 is exactly noiseless. -/
noncomputable def noiseLaw (σ : ℝ) : Measure ℝ := gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩

noncomputable def fullObservationLaw {n m : ℕ} (σ : ℝ) (A : Mat n m) :
    Measure (Observation n m) :=
  Measure.map (fun p : Mat n m × ℝ => (p.1, frobeniusInner A p.1 + p.2))
    ((fullGaussian n m).prod (noiseLaw σ))

noncomputable def vectorObservationLaw {n : ℕ} (w : Fin n → ℝ) :
    Measure ((Fin n → ℝ) × ℝ) :=
  Measure.map (fun p : (Fin n → ℝ) × ℝ => (p.1, linearLabel w p))
    ((coordinateLaw productNormal n).prod (gaussianReal 0 1))

/-- The target is universally quantified AFTER the fixed test. -/
def RankGuarantee {n m T : ℕ} (test : StatisticalTest (Observation n m) T)
    (law : Mat n m → Measure (Observation n m)) (k : ℕ) (ε p : ℝ)
    (promise : Mat n m → Prop := fun _ => True) : Prop :=
  ∀ A : Mat n m, frobenius A = 1 → promise A →
    (A.rank ≤ k → p ≤ acceptance test (law A)) ∧
    (ε ≤ rankDistance k A → acceptance test (law A) ≤ 1 - p)

/-- Theorem 15 has STRICT distance soundness and observes the entire pair. -/
def VectorGuarantee {n T : ℕ} (test : StatisticalTest ((Fin n → ℝ) × ℝ) T)
    (k : ℕ) (ε : ℝ) : Prop :=
  ∀ w : Fin n → ℝ, vectorNorm w = 1 →
    (IsSparse k w → (9 : ℝ) / 10 ≤ acceptance test (vectorObservationLaw w)) ∧
    (ε < sparseDistance k w → acceptance test (vectorObservationLaw w) ≤ (1 : ℝ) / 10)

/-- k^(-3/2), with no integer truncation in the exponent. -/
noncomputable def accuracyScale (k : ℕ) : ℝ := 1 / ((k : ℝ) * Real.sqrt k)

end MatrixSenseRank.Testing.Supplement


