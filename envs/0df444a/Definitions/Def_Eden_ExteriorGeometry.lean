-- Prove2me | Definitions.Def_Eden_ExteriorGeometry
-- name    : Eden_ExteriorGeometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:22:43.012119+00:00
-- url     : https://prove2.me/theorems/5e290dc2-9190-57eb-8124-74625330f380
-- title:
--   Exterior Geometry
-- statement:
--   Definitions and structural lemmas for Exterior Geometry, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorGeometry.lean

import Definitions.Def_Eden_DerivativeDecomposition
import Mathlib.Analysis.InnerProductSpace.ExteriorPower
set_option autoImplicit true
noncomputable section
namespace Eden
abbrev ExteriorSpace (k : ℕ) := ⋀[ℝ]^k PhaseSpace
abbrev ExteriorIndex (k : ℕ) := Set.powersetCard (Fin 5) k
def exteriorEvolution (k : ℕ) (c t : ℝ) (p : PhaseSpace) :
    ExteriorSpace k →ₗ[ℝ] ExteriorSpace k :=
  exteriorPower.map k (fderiv ℝ (evolution c t) p).toLinearMap
def exteriorBasis (k : ℕ) : OrthonormalBasis (ExteriorIndex k) ℝ (ExteriorSpace k) :=
  (EuclideanSpace.basisFun (Fin 5) ℝ).exteriorPower k
def exteriorFactor (k : ℕ) (d : PhaseSpace) (s : ExteriorIndex k) : ℝ :=
  ∏ i : Fin k, d (Set.powersetCard.ofFinEmbEquiv.symm s i)
def exteriorInitialCoordinates (k : ℕ) (p : PhaseSpace) (v : ExteriorSpace k) :
    EuclideanSpace ℝ (ExteriorIndex k) :=
  (exteriorBasis k).repr (exteriorPower.map k (radialFrame p).symm.toLinearMap v)
end Eden


