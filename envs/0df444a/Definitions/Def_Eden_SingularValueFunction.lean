-- Prove2me | Definitions.Def_Eden_SingularValueFunction
-- name    : Eden_SingularValueFunction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:17:57.010879+00:00
-- url     : https://prove2.me/theorems/e3d5c35f-b2c4-4f13-a342-1af44e8b5e22
-- title:
--   Singular Value Function
-- statement:
--   Definitions and structural lemmas for Singular Value Function, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
set_option autoImplicit true
noncomputable section
open Set
namespace Eden
def singularWeight (i : ℕ) (d : ℝ) : ℝ := min 1 (max 0 (d - i))
def spectralProduct (n : ℕ) (a : ℕ → ℝ) (d : ℝ) : ℝ :=
  ∏ i ∈ Finset.range n, a i ^ singularWeight i d
def singularValueFunction (A : PhaseSpace →ₗ[ℝ] PhaseSpace) (d : ℝ) : ℝ :=
  spectralProduct 5 A.singularValues d
def admissibleDimensions (A : PhaseSpace →ₗ[ℝ] PhaseSpace) : Set ℝ :=
  {d | d ∈ Icc 0 5 ∧ 1 ≤ singularValueFunction A d}
def mapLyapunovDimension (A : PhaseSpace →ₗ[ℝ] PhaseSpace) : ℝ := sSup (admissibleDimensions A)
def finiteTimeDimension (c t : ℝ) (p : PhaseSpace) : ℝ :=
  mapLyapunovDimension (fderiv ℝ (evolution c t) p).toLinearMap
def globalLyapunovDimension (c : ℝ) (K : Set PhaseSpace) : ℝ :=
  sInf {v : ℝ | ∃ t : ℝ, 0 < t ∧ v = sSup (finiteTimeDimension c t '' K)}
end Eden


