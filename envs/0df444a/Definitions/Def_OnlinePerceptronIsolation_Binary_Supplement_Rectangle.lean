-- Prove2me | Definitions.Def_OnlinePerceptronIsolation_Binary_Supplement_Rectangle
-- name    : OnlinePerceptronIsolation_Binary_Supplement_Rectangle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:08:50.789682+00:00
-- url     : https://prove2.me/theorems/89c883a3-8659-45c1-a5a0-c2f53e433043
-- title:
--   Definition 4.3 — products of arbitrary intervals
-- statement:
--   A rectangle in $\mathbb R^m$ is specified by real intervals $I_1,\ldots,I_m$, with carrier
--   $$B=\prod_{j=1}^mI_j=\{x\in\mathbb R^m:\forall j,\ x_j\in I_j\}.$$
--   Each interval is an order-connected set. Open, closed, half-open, single-point, empty and unbounded intervals are admitted, with their actual endpoint inclusions. This general object is separate from perceptron feasibility. The published half-open rectangle class for Berry–Esseen does not express this full class and is not substituted for it.
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Definition 4.3, printed p. 16, PDF p. 18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary.Supplement

/-- Definition 4.3: arbitrary real intervals, including empty, open and unbounded ones. -/
structure Rectangle (m : ℕ) where
  interval : Fin m → Set ℝ
  ordConnected : ∀ j, Set.OrdConnected (interval j)

/-- The product of the coordinate intervals, with their actual endpoint inclusions. -/
def Rectangle.carrier {m : ℕ} (B : Rectangle m) : Set (Fin m → ℝ) :=
  {x | ∀ j, x j ∈ B.interval j}

end OnlinePerceptronIsolation.Binary.Supplement


