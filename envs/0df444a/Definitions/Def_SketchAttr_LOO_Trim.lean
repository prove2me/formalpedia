-- Prove2me | Definitions.Def_SketchAttr_LOO_Trim
-- name    : SketchAttr_LOO_Trim
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:25:34.630739+00:00
-- url     : https://prove2.me/theorems/643ce1f3-e229-4d75-9c49-4aeff4ae58d8
-- title:
--   Definition 4.7 — integer-count trimmed mean
-- statement:
--   Let $y_1,\ldots,y_m$ be real numbers, and write $y_{(1)}\le\cdots\le y_{(m)}$ for their nondecreasing rearrangement. For an integer $0\le k<m/2$, the trimmed mean is
--   $$\operatorname{Trim}_k(y)=\frac1{m-2k}\sum_{j=k+1}^{m-k}y_{(j)}.$$
--   Thus it removes the $k$ smallest and $k$ largest observations and averages what remains. This estimator is used by the value and variance estimates as well as the finite-variance concentration theorem.
--
--   **Formalization Note** The implementation sorts the finite list, drops $k$ entries and takes the next $m-2k$. Its total extension outside $2k<m$ is not assigned a statistical meaning. The concentration theorem and the goal's chosen parameters imply the strict trimming-domain condition.
-- source:
--   Liaw, Mehta, Velegkas, Zhou, Sketching Language Models for Context Attribution, STOC 2027 submission #9 (PDF sha256 86af2569e45c55b1009e7453d4f53047b5820d44868a7f528bdb6fed1a2ef0e2), p. 13, Definition 4.7; canonical PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/9.pdf

import Mathlib

namespace SketchAttr.LOO

/-- The source uses this only when 2*k < m; outside that domain this total
extension is not assigned a statistical meaning. -/
noncomputable def trim {m : ℕ} (k : ℕ) (y : Fin m → ℝ) : ℝ :=
  let ys := (List.ofFn y).mergeSort (fun a b => decide (a ≤ b))
  ((ys.drop k).take (m-2*k)).sum / (m-2*k : ℕ)

end SketchAttr.LOO


