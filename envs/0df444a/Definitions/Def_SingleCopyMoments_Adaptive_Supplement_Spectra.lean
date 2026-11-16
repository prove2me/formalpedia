-- Prove2me | Definitions.Def_SingleCopyMoments_Adaptive_Supplement_Spectra
-- name    : SingleCopyMoments_Adaptive_Supplement_Spectra
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:37:50.352309+00:00
-- url     : https://prove2.me/theorems/4df2bd1b-6dcd-438a-8671-e5b6503d19a2
-- title:
--   Power sums, zero padding and full-spectrum additive success
-- statement:
--   A sorted probability vector of length $r$ is nonincreasing, nonnegative and sums to one; the published definition includes zero and repeated coordinates. Its power sums and the full $\ell^1$ distance are
--   $$p_j(\lambda)=\sum_i\lambda_i^j,\qquad
--   \|\lambda-\mu\|_1=\sum_i|\lambda_i-\mu_i|.$$
--   For a state of rank at most $r$ in dimension $d$, an estimator returns a measurable sorted probability vector of length $s=\min(r,d)$ and appends $d-s$ zeros. It succeeds when the normalized transcript law assigns probability at least $1-\delta$ to the measurable event that this padded vector is within $\epsilon$ in full $\ell^1$ distance of the published nonincreasing eigenvalue vector of $\rho$.
--
--   This interface keeps every eigenvalue with its multiplicity, includes $d=1$ and $r>d$, and imposes no eigenvalue gap. The spectrum is computed from the state, rather than supplied as an unrelated parameter.
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), Lemma 9 and Theorem 28, printed pp.14, 29–30 (PDF pp.16, 31–32); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf

import Definitions.Def_SingleCopyMoments_Adaptive_Estimation
import Definitions.Def_OptimalSpectrum_Entangled_SortedProbVec
import Definitions.Def_OptimalSpectrum_Entangled_spec

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Topology Matrix.Norms.L2Operator
set_option autoImplicit false
noncomputable section

namespace SingleCopyMoments.Adaptive.Supplement

/-- No gap or strict positivity is built into the published simplex. -/
abbrev SortedProbVec := OptimalSpectrum.Entangled.SortedProbVec

def powerSumVector {r : ℕ} (lam : SortedProbVec r) (j : ℕ) : ℝ :=
  ∑ i, (lam.val i) ^ j

def l1Distance {r : ℕ} (lam mu : Fin r → ℝ) : ℝ := ∑ i, |lam i - mu i|

/-- Append zeros to a length min(r,d) candidate, retaining a full d-entry output. -/
def padSpectrum {d r : ℕ} (lam : SortedProbVec (min r d)) : Fin d → ℝ :=
  fun i => if h : i.val < min r d then lam.val ⟨i.val,h⟩ else 0

def SpectrumSucceeds {d : ℕ} (P : Protocol d) (T r : ℕ)
    (out : Record P → SortedProbVec (min r d)) (ε δ : ℝ) : Prop :=
  Measurable out ∧ ∀ ρ : State d, ρ.val.rank ≤ r →
    IsProbabilityMeasure (law P ρ T) ∧
    MeasurableSet {H | l1Distance (padSpectrum (out H))
      (OptimalSpectrum.Entangled.spec ρ.val) ≤ ε} ∧
    ENNReal.ofReal (1 - δ) ≤ (law P ρ T)
      {H | l1Distance (padSpectrum (out H)) (OptimalSpectrum.Entangled.spec ρ.val) ≤ ε}

end SingleCopyMoments.Adaptive.Supplement


