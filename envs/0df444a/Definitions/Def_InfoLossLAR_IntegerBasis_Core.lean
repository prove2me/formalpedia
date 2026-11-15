-- Prove2me | Definitions.Def_InfoLossLAR_IntegerBasis_Core
-- name    : InfoLossLAR_IntegerBasis_Core
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T01:46:02.765639+00:00
-- url     : https://prove2.me/theorems/a4cf0292-12f0-406e-9176-9f28fc33f28c
-- title:
--   The original integer input basis as a real basis and a discrete lattice
-- statement:
--   For every nonsingular square integer matrix B, these definitions use the columns of that same B as a real basis and define its integer span L(B). They provide the coordinate linear equivalence, its action on coefficients, the exact column formula for the basis, and the discrete full-rank lattice instances. The ten original declarations and their short verification proofs are preserved. No alternate input basis or lattice is selected.
-- source:
--   Extracted from Solutions.RegevBridgeIntegerBasis using exact official Lean AST declaration ranges, with only the ten basic interfaces retained. Original source SHA-256: d6cc68b8400bc8e48f5bfe1a1ce2a4a9c8c171850f9fd2ebbd8d352582abc3a5. Current extracted module SHA-256: 5358d7d4edebc5458c7575ffd15e9f8466e40af9b5a7b2db377c917a0b8e478a. Every one of the 26 resulting kernel declaration types and values is definitionally equal to the original; recursive standard-three audit passed.

import Definitions.Def_InfoLossLAR_WorstCase_LatticeProblems
import Mathlib

namespace InfoLossLAR.WorstCase.GaussianProjection
end InfoLossLAR.WorstCase.GaussianProjection



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis
open scoped BigOperators
open GaussianProjection
noncomputable section
variable {dimension : ℕ}
abbrev Space := EuclideanSpace ℝ (Fin dimension)

def realMatrix (basis : Matrix (Fin dimension) (Fin dimension) ℤ) : Matrix (Fin dimension) (Fin dimension) ℝ :=
  basis.map (fun value => (value : ℝ))

theorem realMatrix_det_ne_zero (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    (realMatrix basis).det≠0 := by
  rw [realMatrix,←Int.cast_det]
  exact_mod_cast hdet

/-- The actual nonsingular input matrix defines a continuous real linear
equivalence from its coordinate space to the ambient Euclidean space. -/
def coordinateEquiv (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    (Fin dimension → ℝ) ≃L[ℝ] Space (dimension:=dimension) :=
  ((Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin dimension)) (realMatrix basis)
    (isUnit_iff_ne_zero.mpr (realMatrix_det_ne_zero basis hdet))).trans
      (EuclideanSpace.equiv (Fin dimension) ℝ).symm.toLinearEquiv).toContinuousLinearEquiv

theorem coordinateEquiv_apply (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (value : Fin dimension → ℝ) :
    coordinateEquiv basis hdet value=WithLp.toLp 2 ((realMatrix basis).mulVec value) := by
  rfl


/-- The columns of the actual input matrix, as a real basis. -/
def realBasis (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    Module.Basis (Fin dimension) ℝ (Space (dimension:=dimension)) :=
  (Pi.basisFun ℝ (Fin dimension)).map (coordinateEquiv basis hdet).toLinearEquiv

theorem realBasis_apply (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) (index : Fin dimension) :
    realBasis basis hdet index=WithLp.toLp 2 (fun row => (basis row index : ℝ)) := by
  simp only [realBasis,Module.Basis.map_apply,ContinuousLinearEquiv.coe_toLinearEquiv,coordinateEquiv_apply,
    Pi.basisFun_apply,Matrix.mulVec_single,MulOpposite.op_one,one_smul]
  rfl

/-- The exact full-rank discrete submodule used by the Gaussian theorems. -/
def inputLattice (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    Submodule ℤ (Space (dimension:=dimension)) := Submodule.span ℤ (Set.range (realBasis basis hdet))

instance inputLattice_discrete (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    DiscreteTopology (inputLattice basis hdet) := by unfold inputLattice;infer_instance

instance inputLattice_full_rank (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    IsZLattice ℝ (inputLattice basis hdet) := by unfold inputLattice;infer_instance





















end
end InfoLossLAR.WorstCase.IntegerBasis


