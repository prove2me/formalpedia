-- Prove2me | Definitions.Def_Eden_CartesianDerivative
-- name    : Eden_CartesianDerivative
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:04:54.339299+00:00
-- url     : https://prove2.me/theorems/53290c75-08b1-49b9-8302-90c0ac69003c
-- title:
--   Cartesian Derivative
-- statement:
--   Definitions and structural lemmas for Cartesian Derivative, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CartesianDerivative.lean

import Definitions.Def_Eden_InitialDerivative
import Mathlib.Analysis.Calculus.FDeriv.Pow
set_option autoImplicit true
noncomputable section
namespace Eden
def planarDerivativeX (Ω t x y dx dy : ℝ) : ℝ :=
  planarAmplitude t (x ^ 2 + y ^ 2) * (dx * Real.cos (Ω * t) - dy * Real.sin (Ω * t)) +
    2 * deriv (planarAmplitude t) (x ^ 2 + y ^ 2) * (x * dx + y * dy) *
      (x * Real.cos (Ω * t) - y * Real.sin (Ω * t))
def planarDerivativeY (Ω t x y dx dy : ℝ) : ℝ :=
  planarAmplitude t (x ^ 2 + y ^ 2) * (dx * Real.sin (Ω * t) + dy * Real.cos (Ω * t)) +
    2 * deriv (planarAmplitude t) (x ^ 2 + y ^ 2) * (x * dx + y * dy) *
      (x * Real.sin (Ω * t) + y * Real.cos (Ω * t))
section Composition
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ} {p : E}
end Composition
end Eden


