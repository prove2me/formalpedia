-- Prove2me | Definitions.Def_IdentityTesting39_ExactRadius_Reservoir
-- name    : IdentityTesting39_ExactRadius_Reservoir
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:49.869521+00:00
-- url     : https://prove2.me/theorems/7c7c8398-f725-4d5c-91bf-15afd2c73b5a
-- title:
--   Reservoir collapse and the reference-proportional lift
-- statement:
--   For a subset $\mathcal R$ of a finite label set, collapse all its labels into a single head. The collapsed label set is $\{0\}\sqcup(\iota\setminus\mathcal R)$ and the collapsed reference has $Q_0=\sum_{i\in\mathcal R}q_i$, $Q_i=q_i$ elsewhere. For a collapsed vector $P$, define
--
--   $$p_i=P_0q_i/Q_0\quad(i\in\mathcal R),\qquad p_i=P_i\quad(i\notin\mathcal R).$$
--
--   The lifted prior is the pushforward under this explicit linear map. The reservoir theorem guarantees $Q_0\in[1/4,3/8)$, so the denominator is nonzero, proves measurability, and asserts probability preservation, exact preservation of total variation, and contraction of the Poisson-mixture comparison. No reservoir is chosen in this definition; the theorem must construct one from its moment witness.
-- source:
--   Zhijie Zheng, An Exact-Radius Convex Characterization of Discrete Identity Testing, STOC 2027 submission #39 (October 2026), p.10, §7, display (13) and the lift on p.11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/39.pdf

import Definitions.Def_IdentityTesting39_ExactRadius_PoissonExperiments

open MeasureTheory
open scoped BigOperators
noncomputable section

namespace IdentityTesting39.ExactRadius

/-- §7: R is merged into one head; every other label retains its identity. -/
abbrev CollapsedLabels {ι : Type} (R : Finset ι) := Option {i : ι // i ∉ R}

def collapsedReference {ι : Type} [Fintype ι] (q : ι → ℝ) (R : Finset ι) :
    CollapsedLabels R → ℝ
  | none => ∑ i ∈ R, q i
  | some i => q i.val

/-- This linear map refines the collapsed head proportionally to the reference. -/
def liftVector {ι : Type} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (R : Finset ι) (P : CollapsedLabels R → ℝ) (i : ι) : ℝ :=
  if hi : i ∈ R then P none*q i/(∑ j ∈ R, q j) else P (some ⟨i,hi⟩)

def liftPrior {ι : Type} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (R : Finset ι) (π : Measure (CollapsedLabels R → ℝ)) : Measure (ι → ℝ) :=
  Measure.map (liftVector q R) π

end IdentityTesting39.ExactRadius


