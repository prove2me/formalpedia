-- Prove2me | Definitions.Def_OnlinePerceptronIsolation_Binary_Supplement_RectangleShrink
-- name    : OnlinePerceptronIsolation_Binary_Supplement_RectangleShrink
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:09:26.045671+00:00
-- url     : https://prove2.me/theorems/822b84d7-12e6-4802-88bc-b073e880d3e2
-- title:
--   Definition 4.3 — inward shrink with extended endpoints
-- statement:
--   For the coordinate intervals $I_j$ of a rectangle $B$, let $u_j=\inf I_j$ and $v_j=\sup I_j$, computed in $[-\infty,+\infty]$. For $\delta>0$, define
--   $$B^{-\delta}=\begin{cases}\varnothing,&B=\varnothing,\\ \prod_{j=1}^m[u_j+\delta,v_j-\delta],&B\ne\varnothing.\end{cases}$$
--   Coordinates of this product are real, with inequalities against extended endpoints. Infinite endpoints remain infinite, and reversed endpoints give an empty interval. The new intervals are closed even when the original ones are open. The explicit empty-carrier guard preserves the source convention. Extended-real infima and suprema retain unbounded endpoints instead of replacing them by zero.
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Definition 4.3, printed p. 16, PDF p. 18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
import Definitions.Def_OnlinePerceptronIsolation_Binary_Supplement_Rectangle
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary.Supplement

/-- Extended endpoints retain -infinity and +infinity on unbounded intervals. -/
noncomputable def Rectangle.lower {m : ℕ} (B : Rectangle m) (j : Fin m) : EReal :=
  sInf ((fun x : ℝ => (x : EReal)) '' B.interval j)

noncomputable def Rectangle.upper {m : ℕ} (B : Rectangle m) (j : Fin m) : EReal :=
  sSup ((fun x : ℝ => (x : EReal)) '' B.interval j)

/-- Definition 4.3: move finite endpoints inward, use closed intervals, and explicitly
preserve an empty rectangle. Only positive delta is used in the source lemmas. -/
noncomputable def Rectangle.shrink {m : ℕ} (B : Rectangle m) (δ : ℝ) : Set (Fin m → ℝ) := by
  classical
  exact if B.carrier = ∅ then ∅ else
    {x | ∀ j, B.lower j + (δ : EReal) ≤ (x j : EReal) ∧
      (x j : EReal) ≤ B.upper j - (δ : EReal)}

end OnlinePerceptronIsolation.Binary.Supplement


