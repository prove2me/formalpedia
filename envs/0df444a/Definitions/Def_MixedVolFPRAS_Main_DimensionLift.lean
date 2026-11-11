-- Prove2me | Definitions.Def_MixedVolFPRAS_Main_DimensionLift
-- name    : MixedVolFPRAS_Main_DimensionLift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:29:47.835237+00:00
-- url     : https://prove2.me/theorems/42b5b4ef-7bef-4a40-b6c0-958d1815d370
-- title:
--   Lifting sets of ℝᵈ into the hyperplane ℝᵈ × {0} and the unit segment [0, e_{d+1}] (§A.1)
-- statement:
--   For $K\subseteq\mathbb{R}^d$ let $\tilde K=K\times\{0\}\subseteq\mathbb{R}^{d+1}$, the image of $K$ under $x\mapsto(x,0)$, and let
--
--   $$S=[0,e_{d+1}]=\{s\,e_{d+1}:0\le s\le1\}$$
--
--   be the unit segment along the new coordinate axis. These are the sets of the dimension-lifting identity of Appendix A.1.
--
--   **Formalization Note.** `liftPoint x` has coordinates $x_1,\dots,x_d,0$; `liftSet K = liftPoint '' K`; `unitSegment d = segment ℝ 0 (EuclideanSpace.single (Fin.last d) 1)`.
-- source:
--   Chen, Liu, An FPRAS for Mixed Volumes, STOC 2027 submission (manuscript sha256 0acf8d97…), pp. 33–34, Appendix A.1

import Mathlib
import Definitions.Def_MixedVolFPRAS_Main_ConvexGeometry

noncomputable section

namespace MixedVolFPRAS.Main

/-!
# Lifting sets from `ℝᵈ` to the hyperplane `ℝᵈ × {0}` of `ℝᵈ⁺¹` (§A.1)

Chen, Liu, *An FPRAS for Mixed Volumes*, pp. 33–34, Appendix A.1.

* `liftPoint x = (x, 0)`, `liftSet K = K × {0} ⊆ ℝᵈ⁺¹`.
* `unitSegment d = [0, e_{d+1}]`, the segment from the origin to the last standard basis vector.
-/

/-- `x ↦ (x, 0)`. -/
def liftPoint {d : ℕ} (x : E d) : E (d + 1) :=
  WithLp.toLp 2 (fun i : Fin (d + 1) => if h : i.val < d then x ⟨i.val, h⟩ else 0)

/-- `K̃ = K × {0}`. -/
def liftSet {d : ℕ} (K : Set (E d)) : Set (E (d + 1)) := liftPoint '' K

/-- The segment `S = [0, e_{d+1}]`. -/
def unitSegment (d : ℕ) : Set (E (d + 1)) :=
  segment ℝ 0 (EuclideanSpace.single (Fin.last d) 1)

end MixedVolFPRAS.Main


