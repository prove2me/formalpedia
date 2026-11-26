-- Prove2me | Definitions.Def_Eden_PlanarFlow
-- name    : Eden_PlanarFlow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:01:58.503609+00:00
-- url     : https://prove2.me/theorems/d95abe40-3da8-46b0-8327-f09e73ab429b
-- title:
--   Planar Flow
-- statement:
--   Definitions and structural lemmas for Planar Flow, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarFlow.lean

import Definitions.Def_Eden_ScalarCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
set_option autoImplicit true
noncomputable section
namespace Eden
def planarX (Ω t x y : ℝ) : ℝ :=
  planarAmplitude t (x ^ 2 + y ^ 2) *
    (x * Real.cos (Ω * t) - y * Real.sin (Ω * t))
def planarY (Ω t x y : ℝ) : ℝ :=
  planarAmplitude t (x ^ 2 + y ^ 2) *
    (x * Real.sin (Ω * t) + y * Real.cos (Ω * t))
end Eden


