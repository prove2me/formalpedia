-- Prove2me | Definitions.Def_Transport_Continuation
-- name    : Transport_Continuation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:51.945926+00:00
-- url     : https://prove2.me/theorems/13761da4-ae59-4c1c-aec3-178ac54fa55b
-- title:
--   Continuation
-- statement:
--   Definitions and structural lemmas for Continuation, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Continuation.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Continuation
set_option autoImplicit false
namespace RH.Transport
noncomputable section
open Filter Asymptotics MeasureTheory
open OAI.SevenEighths.Continuation
def continuationBoundary (B β ω σ : ℝ) : ℝ := max (B + ω) (β - σ)
def continuationMargin (B β ω σ : ℝ) : ℝ := min (β - B - ω) σ
end
end RH.Transport


