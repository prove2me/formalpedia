-- Prove2me | Definitions.Def_KoanaKPaths_GraphEstimator
-- name    : KoanaKPaths_GraphEstimator
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T01:25:35.663675+00:00
-- url     : https://prove2.me/theorems/d6b8df30-7934-4d88-9fac-d214c9957749
-- title:
--   Walk coefficient tensor and amplified sketch estimate
-- statement:
--   For a directed graph, the walk coefficient tensor assigns coefficient one to each ordered $k$-tuple whose consecutive vertices are arcs, and zero to every other tuple. A trial uses the determinant-weighted sketch with width $k$. Its nonnegative integer numerator and common denominator are
--
--   $$
--   Z=\|S_k\|_F^2,\qquad D=k^k k!.
--   $$
--
--   For controls $a,b$, a group contains $m=1024k^3 4^a$ independent trials. The estimate is the median of $2b+1$ group averages, written with common denominator $mD$ and the median of the integer group sums as numerator.
--
--   This is the mathematical output specification. The tensor sum does not prescribe an implementation by enumerating walks: efficient computation by the exterior-algebra dynamic program and its fair-bit machine implementation remain separate obligations.
-- source:
--   Tomohiro Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, printed p. 5 / PDF p. 6, Section 3 (median-of-means), printed p. 8 / PDF p. 9, Lemma 6 and its following paragraph; graph coefficient tensor: printed p. 9 / PDF p. 10, Section 4.1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf

import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_PathCount2k_Graph
import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_KoanaKPaths_MedianOfMeans

noncomputable section
open scoped BigOperators
namespace KoanaKPaths.Main

/-- The zero-one tensor of all directed walks on `k` vertices. -/
def walkTensor (n : ℕ) (arcs : List (Fin n × Fin n)) (k : ℕ) (τ : Fin k → Fin n) : ℤ :=
  if ∀ (i : Fin k) (h : i.val+1 < k), (τ i,τ ⟨i.val+1,h⟩) ∈ arcs.toFinset then 1 else 0

/-- Common denominator of a trial with sketch width `k`. -/
def trialDenominator (k : ℕ) : ℕ := k^k * k.factorial

/-- The nonnegative squared-norm numerator of one trial, specified by the tensor sketch. -/
def trialNumerator {n k : ℕ} (c : (Fin k → Fin n) → ℤ)
    (w : Labels n k × SketchSigns n k k) : ℕ :=
  (sketchFrobSq c w.1 w.2 k).toNat

/-- A fixed explicit sample size for one group at accuracy control `a`. -/
def groupTrials (k a : ℕ) : ℕ := 1024*k^3*4^a

/-- The median of independent group averages, written with its common positive denominator.
This is a mathematical specification; efficient evaluation is a separate machine obligation. -/
def estimateFraction {n k : ℕ} (c : (Fin k → Fin n) → ℤ) (a b : ℕ)
    (w : Fin (2*b+1) → Fin (groupTrials k a) → Labels n k × SketchSigns n k k) :
    HypergraphUnreliability.FPRAS.Frac where
  num := KoanaKPaths.Sampling.median b (fun i => ∑ j, trialNumerator c (w i j))
  den := groupTrials k a * trialDenominator k

end KoanaKPaths.Main


