-- Prove2me | Definitions.Def_OnlineRealSampling_Exact_Supplement_Observables
-- name    : OnlineRealSampling_Exact_Supplement_Observables
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:38:08.952206+00:00
-- url     : https://prove2.me/theorems/7a763e4e-8dae-46b4-858c-c627af4af657
-- title:
--   Universal exactness and extended peak-space observables
-- statement:
--   For a causal target rule, the mass assigned to a public output history is the product of the successive conditional probability masses. A sampler is exact if, for every valid causal oracle rule, each finite prefix terminates almost surely under the published fair-bit law and each output-history cylinder has precisely that product mass. This quantifies over all valid replacement oracles as well as the input under analysis. Fixing the independent external seed of any published admissible environment gives such a causal rule, so the laws hold conditional on that seed.
--
--   Overall space S_n is the peak storage recorded up to the nth emission, and is infinity if the prefix does not terminate. The maximum output logarithm is max over i=1,...,n of slog(X_i), where slog(x)=ln(max(x,e)); its empty-prefix value is zero. On nontermination, default outputs are zero, immaterial for exact samplers. The two expectations integrate these nonnegative extended quantities under the published independent product law of the environment seed and the fair bits. Infinite expected space and infinite logarithmic output moments are retained.
--
--   Exactness includes no precision tail or resource bound. Measurability follows from finite-execution cylinders: a finite execution observes finitely many fair bits and integer-valued oracle answers; completion is a countable union of those events. Admissible environments supply measurable answer coordinates. This is the probability and resource interface used by the two universal lower-bound statements.
-- source:
--   Draper, Harris and Saad, Online Random Sampling with Real Probabilities, STOC 2027 submission #103, manuscript dated 2026-11-02. Citation basis: preprint; pinned source.pdf SHA-256 66aeb5c181baf97cefba69aa26d29299e888a7a86c837a71af5b77d35f11c3e1; no arXiv identifier/version exists in the artifact, so cite the dated hash-pinned submission with the paper's own result number. PDF 1 is unnumbered; For PDF pages 2–24, printed page = PDF page − 1; PDF 1 is unnumbered. Source artifact: https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/103.pdf. §1 PDF 2 / printed 1; §3 PDF 7–8 / printed 6–7; §7.2 PDF 17–19 / printed 16–18.

import Mathlib
import Definitions.Def_OnlineRealSampling_Exact_Supplement_Sampler
import Definitions.Def_OnlineRealSampling_Exact_Online

namespace OnlineRealSampling.Exact.Supplement

open MeasureTheory
open scoped ENNReal
noncomputable section

/-- Product of the successive conditional masses along a public output history. -/
def historyMass (orc : List ℕ → CDFOracle) (xs : List ℕ) : ℝ≥0∞ :=
  ∏ i ∈ Finset.range xs.length,
    ENNReal.ofReal (pmf (orc (xs.take i)).F (xs.getD i 0))

/-- Exactness for every valid causal target rule: every finite prefix terminates almost
surely, and each output-history cylinder has the product conditional law. Fixing any external
seed in an AdmissibleEnv gives such a rule; hence exactness is conditional on that seed,
as well as on the public history. This predicate contains no precision or resource bounds.
It quantifies over all valid replacement oracles, not just one input instance. -/
def IsExact {σ : Type} (A : Sampler σ) : Prop :=
  ∀ orc : List ℕ → CDFOracle, (∀ h, (orc h).Valid) →
    (∀ n, ∀ᵐ ω ∂coinMeasure, Terminates A orc ω n) ∧
    (∀ xs : List ℕ, coinMeasure (outputEvent A orc xs) = historyMass orc xs)

/-- Overall space in bits, with infinity on nontermination. All intermediate storage,
precision-k answer charges and emitted output buffers enter the same peak. -/
def space {σ : Type} (A : Sampler σ) (orc : List ℕ → CDFOracle)
    (n : ℕ) (ω : ℕ → Bool) : ℝ≥0∞ :=
  match finish A orc ω n with
  | none => ⊤
  | some c => (c.peak : ℝ≥0∞)

/-- Maximum clipped output logarithm, with maximum inside the expectation. On the null
event of nontermination the default outputs are zero (whose clipped logarithm is one).
The empty-prefix maximum is zero. This is an observable, not a storage charge. -/
def maxLog {σ : Type} (A : Sampler σ) (orc : List ℕ → CDFOracle)
    (n : ℕ) (ω : ℕ → Bool) : ℝ≥0∞ :=
  let xs := ((finish A orc ω n).map Trace.history).getD (List.replicate n 0)
  (xs.map (fun x => ENNReal.ofReal (slog (x : ℝ)))).foldr max 0

/-- Extended expectations under the published independent seed/fair-bit product law.
AdmissibleEnv is required by statements, not replaced by a new or narrower environment. -/
def expectedSpace {σ Ξ : Type} [MeasurableSpace Ξ] (A : Sampler σ)
    (μ : Measure Ξ) (env : Ξ → List ℕ → CDFOracle) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ p, space A (env p.1) n p.2 ∂onlineMeasure μ

def expectedMaxLog {σ Ξ : Type} [MeasurableSpace Ξ] (A : Sampler σ)
    (μ : Measure Ξ) (env : Ξ → List ℕ → CDFOracle) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ p, maxLog A (env p.1) n p.2 ∂onlineMeasure μ

end
end OnlineRealSampling.Exact.Supplement


