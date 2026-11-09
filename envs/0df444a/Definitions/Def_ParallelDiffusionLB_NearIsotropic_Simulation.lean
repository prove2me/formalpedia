-- Prove2me | Definitions.Def_ParallelDiffusionLB_NearIsotropic_Simulation
-- name    : ParallelDiffusionLB_NearIsotropic_Simulation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:57.898388+00:00
-- url     : https://prove2.me/theorems/a51bb49d-4ac1-4695-9081-ec8b415ddeea
-- title:
--   Prefix dependence, suffix laws and progressive interactions
-- statement:
--   For finite-valued independent coordinates $\Theta_1,\ldots,\Theta_n$ with laws $\mu_j$, two configurations agree on a prefix of length $k$ when their first $k$ coordinates coincide. Prefix dependence means that changing later coordinates cannot change the specified function when the seed is fixed. A supported version ignores configurations outside the support of the coordinate laws.
--
--   For fixed prefix values, the suffix law is
--   $$\bigotimes_{j\le k}\delta_{\theta_j}\ \otimes\ \bigotimes_{j>k}\mu_j.$$
--   A prefix is in support when each fixed coordinate has positive singleton probability. The progressive transcript and output run the same algorithm and seed, answering round $r$ with its $r$-truncated oracle. These are computed recursively, with no correctness or indistinguishability built into their definitions.
--
--   This interface states the hypotheses and conclusions of the generic simulation lemma independently of Gaussian scores or codebooks.
-- source:
--   Yimeng Wang, Yiwen Kou, Lower Bounds for Parallel Diffusion Sampling, STOC 2027 submission #660 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/660.pdf, Lemma A.13 and proof, p. 27

import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Algorithm

open MeasureTheory
noncomputable section

namespace ParallelDiffusionLB.NearIsotropic

/-- Equality of the first k coordinates. All coordinates have their original types. -/
def PrefixEq {n : ℕ} {Θ : Fin n → Type*} (k : ℕ) (θ θ' : (j : Fin n) → Θ j) : Prop :=
  ∀ j, j.val < k → θ j = θ' j

/-- A deterministic dependence property, including every seed, not an a.e. condition. -/
def DependsOnPrefix {n : ℕ} {Θ : Fin n → Type*} {Ω Out : Type*}
    (k : ℕ) (f : ((j : Fin n) → Θ j) × Ω → Out) : Prop :=
  ∀ θ θ' ω, PrefixEq k θ θ' → f (θ,ω) = f (θ',ω)

/-- Resample the independent suffix while fixing precisely the first k coordinates. -/
def suffixLaw {n : ℕ} {Θ : Fin n → Type*} [∀ j, MeasurableSpace (Θ j)]
    (μ : (j : Fin n) → Measure (Θ j)) (θ : (j : Fin n) → Θ j) (k : ℕ) :
    Measure ((j : Fin n) → Θ j) :=
  Measure.pi (fun j => if j.val < k then Measure.dirac (θ j) else μ j)

/-- Prefix values in the support, which for finite discrete coordinates means positive mass. -/
def PrefixInSupport {n : ℕ} {Θ : Fin n → Type*} [∀ j, MeasurableSpace (Θ j)]
    (μ : (j : Fin n) → Measure (Θ j)) (θ : (j : Fin n) → Θ j) (k : ℕ) : Prop :=
  ∀ j, j.val < k → 0 < μ j {θ j}

/-- Prefix dependence on the support of the finite coordinate law; null coordinate values do not matter. -/
def SupportedDependsOnPrefix {n : ℕ} {Θ : Fin n → Type*} [∀ j, MeasurableSpace (Θ j)]
    {Ω Out : Type*} (μ : (j : Fin n) → Measure (Θ j)) (k : ℕ)
    (f : ((j : Fin n) → Θ j) × Ω → Out) : Prop :=
  ∀ θ θ' ω, PrefixInSupport μ θ n → PrefixInSupport μ θ' n →
    PrefixEq k θ θ' → f (θ,ω) = f (θ',ω)

/-- The canonical same-instance, same-seed progressive transcript of Lemma A.13. -/
def progressiveTranscript {n P R : ℕ} {Θ : Fin n → Type*} {Q Ans Out Ω : Type*}
    [MeasurableSpace Q] [MeasurableSpace Ans] [MeasurableSpace Out] [MeasurableSpace Ω]
    (A : ParallelAlgorithm Q Ans Out Ω P R) (hR : R ≤ n)
    (trunc : Fin n → ((j : Fin n) → Θ j) → Q → Ans)
    (θω : ((j : Fin n) → Θ j) × Ω) : History Ans P R :=
  A.transcript (fun r => trunc (Fin.castLE hR r) θω.1) θω.2

def progressiveResult {n P R : ℕ} {Θ : Fin n → Type*} {Q Ans Out Ω : Type*}
    [MeasurableSpace Q] [MeasurableSpace Ans] [MeasurableSpace Out] [MeasurableSpace Ω]
    (A : ParallelAlgorithm Q Ans Out Ω P R) (hR : R ≤ n)
    (trunc : Fin n → ((j : Fin n) → Θ j) → Q → Ans)
    (θω : ((j : Fin n) → Θ j) × Ω) : Out :=
  A.output (θω.2, progressiveTranscript A hR trunc θω)

end ParallelDiffusionLB.NearIsotropic


