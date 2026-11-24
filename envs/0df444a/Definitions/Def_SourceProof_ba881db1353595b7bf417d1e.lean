-- Prove2me | Definitions.Def_SourceProof_ba881db1353595b7bf417d1e
-- name    : SourceProof_ba881db1353595b7bf417d1e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:13:11.520603+00:00
-- url     : https://prove2.me/theorems/eb865ba1-071e-470c-8c35-1b3c88a6f326
-- title:
--   StochLean source theorem: StochLean.contDiff_complex_coordinate_component

import Definitions.Def_StochLean_ForMathlib_Analysis_ComplexCoordinateDerivatives_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Real coordinate derivatives of complex analytic functions

The coordinate map sends (x,y) to x + iy. Real and imaginary components
are handled uniformly by a real continuous linear functional. The two
Hessian indices are ordered, and the second imaginary derivative has its
actual negative sign through I squared.
-/

@[expose] public section

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_ba881db1353595b7bf417d1e {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (L : ℂ →L[ℝ] ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun x : Fin 2 → ℝ ↦ L (f (complexCoordinates x))) :=
  L.contDiff.comp ((hf.contDiff.restrict_scalars ℝ).comp StochLean.complexCoordinates.contDiff)
end StochLean


