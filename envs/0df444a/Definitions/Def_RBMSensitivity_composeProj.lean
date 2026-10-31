-- Prove2me | Definitions.Def_RBMSensitivity_composeProj
-- name    : RBMSensitivity_composeProj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:25.131013+00:00
-- url     : https://prove2.me/theorems/03ac8011-1919-413e-b5a4-72a618032135
-- title:
--   The product $\mathcal L_{x_K}\cdots\mathcal L_{x_1}y$
-- statement:
--   For maps $\mathcal L_1,\dots,\mathcal L_K$ this is the product $\mathcal L_K\cdots\mathcal L_1y$, in which $\mathcal L_1$ is applied first.
--
--   It appears in the contraction bound (4.12).
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Lemma 4.20, (4.12), p.15

import Mathlib
import Definitions.Def_RBMSensitivity_E
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- The product `L_K ⋯ L_1 y`, with `L_1` applied first: arXiv:1907.00472v2, (4.12), p.15. -/
def composeProj {J K : ℕ} (L : Fin K → E J → E J) (y : E J) : E J :=
  (List.ofFn L).foldl (fun v M => M v) y

end RBMSensitivity


