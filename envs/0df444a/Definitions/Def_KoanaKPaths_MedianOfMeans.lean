-- Prove2me | Definitions.Def_KoanaKPaths_MedianOfMeans
-- name    : KoanaKPaths_MedianOfMeans
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T01:23:56.104996+00:00
-- url     : https://prove2.me/theorems/66d8c560-74a6-4bab-885e-dff97e66babf
-- title:
--   Finite sample means and the middle order statistic
-- statement:
--   For $2b+1$ values $x_1,\ldots,x_{2b+1}$ in a linearly ordered set, define the middle order statistic by
--
--   $$
--   \operatorname{med}(x)=\max_{|S|=b+1}\min_{i\in S}x_i.
--   $$
--
--   This specifies the usual median independently of a selection implementation. The module also defines the arithmetic mean of a finite group and the number of group entries satisfying a specified bad event. These data describe the amplification step of the counting estimator; probability and machine-time guarantees are separate theorems.
-- source:
--   Tomohiro Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, printed p. 5 / PDF p. 6, Section 3 (median-of-means), printed p. 8 / PDF p. 9, Lemma 6 and its following paragraph; graph coefficient tensor: printed p. 9 / PDF p. 10, Section 4.1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf

import Mathlib

open scoped BigOperators
namespace KoanaKPaths.Sampling

/-- Minimum on a nonempty selected set of sample positions. -/
def selectedMin {α : Type} [LinearOrder α] [Inhabited α] {q : ℕ}
    (s : Finset (Fin q)) (x : Fin q → α) : α :=
  if h : s.Nonempty then s.inf' h x else default

/-- The middle order statistic of `2*b+1` values, expressed as the largest minimum
of any `b+1` selected positions. This definition specifies the value independently of a
sorting or selection implementation. -/
def median {α : Type} [LinearOrder α] [Inhabited α] (b : ℕ) (x : Fin (2*b+1) → α) : α :=
  (Finset.univ.powersetCard (b+1)).sup'
    (Finset.powersetCard_nonempty.mpr (by simp; omega)) (fun s => selectedMin s x)

/-- Arithmetic average of a fixed-size independent sample group. -/
noncomputable def sampleMean {Ω : Type} (f : Ω → ℝ) {m : ℕ} (w : Fin m → Ω) : ℝ :=
  (∑ i, f (w i)) / m

/-- Number of bad samples in a fixed-length group. -/
def badCount {Ω : Type} (p : Ω → Prop) [DecidablePred p] {q : ℕ} (w : Fin q → Ω) : ℕ :=
  ∑ i, if p (w i) then 1 else 0

end KoanaKPaths.Sampling


