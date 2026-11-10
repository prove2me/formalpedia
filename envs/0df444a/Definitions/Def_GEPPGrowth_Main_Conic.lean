-- Prove2me | Definitions.Def_GEPPGrowth_Main_Conic
-- name    : GEPPGrowth_Main_Conic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T23:35:08.285323+00:00
-- url     : https://prove2.me/theorems/d3f110b1-564c-4add-84db-0090f3e56476
-- title:
--   Definition 4.4 — conic subsets of Euclidean space
-- statement:
--   A subset $E\subseteq\mathbb R^d$ is conic when it is invariant under multiplication by positive scalars:
--
--   $$y\in E,\ t>0\quad\Longrightarrow\quad ty\in E.$$
--
--   No convexity, closedness, pointedness or measurability is included. This is the source domain of the Gaussian comparison inequality.
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), Definition 4.4, printed p.8, PDF p.9

import Definitions.Def_GEPPGrowth_Main_Gaussian
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Definition 4.4: closure under positive scaling; no convexity or measurability. -/
def Conic {d : ℕ} (E : Set (Vec d)) : Prop :=
  ∀ y ∈ E, ∀ t : ℝ, 0 < t → (fun i => t * y i) ∈ E

end GEPPGrowth.Main


