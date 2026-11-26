-- Prove2me | Definitions.Def_Eden_ExteriorGram
-- name    : Eden_ExteriorGram
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:34:04.472826+00:00
-- url     : https://prove2.me/theorems/e90ee983-1972-4b16-8b64-50bc38ce40f0
-- title:
--   Exterior Gram
-- statement:
--   Definitions and structural lemmas for Exterior Gram, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorGram.lean

import Definitions.Def_Eden_ExteriorOperatorNorm
set_option autoImplicit true
noncomputable section
open scoped RealInnerProductSpace
namespace Eden
def singularVectorBasis (A : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    OrthonormalBasis (Fin 5) ℝ PhaseSpace :=
  A.isSymmetric_adjoint_comp_self.eigenvectorBasis (finrank_euclideanSpace_fin)
def singularExteriorBasis (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    OrthonormalBasis (ExteriorIndex k) ℝ (ExteriorSpace k) :=
  (singularVectorBasis A).exteriorPower k
def selectedSingularProduct (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (s : ExteriorIndex k) : ℝ :=
  ∏ i : Fin k, A.singularValues (Set.powersetCard.ofFinEmbEquiv.symm s i)
end Eden


