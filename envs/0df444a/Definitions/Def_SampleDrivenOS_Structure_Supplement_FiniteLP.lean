-- Prove2me | Definitions.Def_SampleDrivenOS_Structure_Supplement_FiniteLP
-- name    : SampleDrivenOS_Structure_Supplement_FiniteLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:41:39.444805+00:00
-- url     : https://prove2.me/theorems/7717108d-ce82-477f-a7a5-3cf1a004f61f
-- title:
--   Finite stopping LP feasibility and offline rank coefficients
-- statement:
--   For integers 0≤h<N and 1≤j≤h+1, the offline rank coefficient and its cumulative mass are
--   $$
--   A_j=\frac{N-h}{N-j+1}\prod_{s=0}^{j-2}\frac{h-s}{N-s},\qquad
--   C_k=\sum_{j=1}^k A_j.
--   $$
--   The product is empty and equals 1 at j=1. Nonnegative finite stopping masses x_{i,ℓ}, for h+1≤i≤N and 1≤ℓ≤i, obey
--   $$
--   i x_{i,\ell}+\sum_{r=h+1}^{i-1}\sum_{s=1}^r x_{r,s}\le1.
--   $$
--   The finite selection coefficient is the printed binomial coefficient in LP_h,N, with impossible ℓ>i cases set to zero. The full SDLP additionally requires α≤(cumulative selection mass)/C_k for every 1≤k≤h+1.
--
--   The error scale used in Theorem 13 is
--   $$
--   E(N,p)=\frac{(\log N)^2}{(1-p)^2\sqrt N}.
--   $$
--   These definitions support the exact coefficient comparison and both finite-error estimates. They do not define the finite optimal policy value by an LP certificate.
--
--   **Formalization Note** All LP indices are one-based. `range (j-1)` represents the j−1 factors of the printed product without a spurious factor at j=1. Real subtraction is used in A_j. The theorem binds the domain on which every denominator is positive.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 6, (2); p. 14, SDLP_h,N; p. 39, Lemma 19 (27)

import Mathlib

open scoped BigOperators

namespace SampleDrivenOS.Structure.Supplement
noncomputable section

/-- Probability that the best online item has global rank j. The product has j-1 factors;
at j=1 it is empty. Real subtraction preserves the printed formula. -/
def offlineCoefficient (N h j : ℕ) : ℝ :=
  ((N : ℝ) - h) / ((N : ℝ) - j + 1) *
    ∏ s ∈ Finset.range (j - 1), ((h : ℝ) - s) / ((N : ℝ) - s)

def cumulativeOffline (N h k : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 k, offlineCoefficient N h j

/-- Full finite stopping feasibility (2), with 1-based step and relative-rank indices. -/
def IsFiniteFeasible (N h : ℕ) (x : ℕ → ℕ → ℝ) : Prop :=
  ∀ i ∈ Finset.Icc (h + 1) N, ∀ ℓ ∈ Finset.Icc 1 i,
    0 ≤ x i ℓ ∧ (i : ℝ) * x i ℓ +
      (∑ r ∈ Finset.Ico (h + 1) i, ∑ s ∈ Finset.Icc 1 r, x r s) ≤ 1

/-- The binomial coefficient is zero in the impossible case ℓ>i; that case must not be
encoded using truncated i-ℓ alone. -/
def finiteRankCoefficient (N i j ℓ : ℕ) : ℝ :=
  if ℓ ≤ i ∧ ℓ ≤ j ∧ j ≤ N then
    (i : ℝ) / N * ((j - 1).choose (ℓ - 1) : ℝ) *
      ((N - j).choose (i - ℓ) : ℝ) / ((N - 1).choose (i - 1) : ℝ)
  else 0

def finiteCumulativeSelection (N h k : ℕ) (x : ℕ → ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 k, ∑ i ∈ Finset.Icc (h + 1) N,
    ∑ ℓ ∈ Finset.Icc 1 j, x i ℓ * finiteRankCoefficient N i j ℓ

/-- SDLP_h,N, with no truncation of its k or i ranges. -/
def IsSDLPFeasible (N h : ℕ) (x : ℕ → ℕ → ℝ) (a : ℝ) : Prop :=
  IsFiniteFeasible N h x ∧
    ∀ k ∈ Finset.Icc 1 (h + 1), a ≤ finiteCumulativeSelection N h k x / cumulativeOffline N h k

def finiteError (N : ℕ) (p : ℝ) : ℝ :=
  Real.log (N : ℝ) ^ 2 / ((1 - p) ^ 2 * Real.sqrt (N : ℝ))

end
end SampleDrivenOS.Structure.Supplement


