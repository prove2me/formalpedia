-- Prove2me | Definitions.Def_Eden_ScalarFlow
-- name    : Eden_ScalarFlow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:00:44.345574+00:00
-- url     : https://prove2.me/theorems/4d4b1be9-4690-4026-a485-f406007257de
-- title:
--   Scalar Flow
-- statement:
--   Definitions and structural lemmas for Scalar Flow, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarFlow.lean

import Definitions.Def_Eden_Algebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
set_option autoImplicit true
noncomputable section
namespace Eden
def radialDiscriminant (t s : ℝ) : ℝ :=
  Real.exp (-4 * t) + (1 - Real.exp (-4 * t)) * (s - 1) ^ 2
def squaredRadiusEvolution (t s : ℝ) : ℝ :=
  1 + (s - 1) / Real.sqrt (radialDiscriminant t s)
def amplitudeSq (t s : ℝ) : ℝ :=
  (1 + (s - 2) * (1 - Real.exp (-4 * t)) /
    (Real.sqrt (radialDiscriminant t s) + 1)) /
      Real.sqrt (radialDiscriminant t s)
end Eden


