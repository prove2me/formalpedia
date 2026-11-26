-- Prove2me | Definitions.Def_Eden_Basic
-- name    : Eden_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:59:39.207124+00:00
-- url     : https://prove2.me/theorems/7f22f490-c6a0-4c6c-b447-64630e251591
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Basic.lean

import Mathlib.Analysis.InnerProductSpace.PiL2
set_option autoImplicit true
noncomputable section
namespace Eden
abbrev PhaseSpace := EuclideanSpace ℝ (Fin 5)
def radiusSq₁ (p : PhaseSpace) : ℝ := p 0 ^ 2 + p 1 ^ 2
def radiusSq₂ (p : PhaseSpace) : ℝ := p 2 ^ 2 + p 3 ^ 2
def q (s : ℝ) : ℝ := -(s - 1) * (s - 2)
def radialField (r : ℝ) : ℝ := -r * (r ^ 2 - 1) * (r ^ 2 - 2)
def vectorField (c : ℝ) (p : PhaseSpace) : PhaseSpace :=
  !₂[q (radiusSq₁ p) * p 0 - p 1,
     q (radiusSq₁ p) * p 1 + p 0,
     q (radiusSq₂ p) * p 2 - Real.sqrt 2 * p 3,
     q (radiusSq₂ p) * p 3 + Real.sqrt 2 * p 2,
     -c * p 4]
def attractor : Set PhaseSpace :=
  {p | radiusSq₁ p ≤ 2 ∧ radiusSq₂ p ≤ 2 ∧ p 4 = 0}
def torus : Set PhaseSpace :=
  {p | radiusSq₁ p = 1 ∧ radiusSq₂ p = 1 ∧ p 4 = 0}
def radialRate (s : ℝ) : ℝ := -5 * s ^ 2 + 9 * s - 2
def tangentialRate (s : ℝ) : ℝ := -s ^ 2 + 3 * s - 2
def targetDimension (c : ℝ) : ℝ := 4 + 4 / c
end Eden


