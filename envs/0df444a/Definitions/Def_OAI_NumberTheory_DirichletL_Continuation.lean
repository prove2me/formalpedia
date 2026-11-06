-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Continuation
-- name    : OAI_NumberTheory_DirichletL_Continuation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:28.557433+00:00
-- url     : https://prove2.me/theorems/74c75e64-d9b2-4e4e-8316-e94221a093ed
-- title:
--   Continuation
-- statement:
--   Definitions and structural lemmas for Continuation, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Continuation.lean

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_OAI_NumberTheory_DirichletL_Supremum
set_option autoImplicit false
namespace OAI
noncomputable section
open Filter Asymptotics MeasureTheory
open scoped Topology
namespace SevenEighths.Continuation
def signalMellin (f : ℝ → ℂ) (c : ℝ) (s : ℂ) : ℂ :=
  mellin f (-(s + (c : ℂ)))
def RapidDecayAtZero (f : ℝ → ℂ) : Prop :=
  ∀ B : ℝ, f =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ B)
def gaussianMultiplier (H : ℂ → ℂ) (s : ℂ) : ℂ :=
  Complex.exp ((s - 5 / 6) ^ 2) * H s
end SevenEighths.Continuation
end
end OAI


