-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidueLinear
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidueLinear
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:35:07.767213+00:00
-- url     : https://prove2.me/theorems/93d00bf2-9721-439e-ae66-315de5bcf72e
-- title:
--   Simple Pole Residue Linear
-- statement:
--   Definitions and structural lemmas for Simple Pole Residue Linear, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Global/SimplePoleResidueLinear.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_Nonnegative_add

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc
namespace Differential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
theorem isGlobalSimplePole_zero :
    IsGlobalSimplePole (k := k) (F := F) (0 : Differential k F) := by
  intro P
  exact (simplePoleDifferentialLattice P).zero_mem
theorem IsGlobalSimplePole.add {omega eta : Differential k F}
    (homega : IsGlobalSimplePole (k := k) (F := F) omega)
    (heta : IsGlobalSimplePole (k := k) (F := F) eta) :
    IsGlobalSimplePole (k := k) (F := F) (omega + eta) := by
  intro P
  exact (simplePoleDifferentialLattice P).add_mem (homega P) (heta P)
theorem IsGlobalSimplePole.finset_sum {ι : Type*} (s : Finset ι)
    (omega : ι → Differential k F)
    (homega : ∀ i, IsGlobalSimplePole (k := k) (F := F) (omega i)) :
    IsGlobalSimplePole (k := k) (F := F) (∑ i ∈ s, omega i) := by
  intro P
  exact Submodule.sum_mem (simplePoleDifferentialLattice P)
    (fun i _ => homega i P)
end Differential
end QEC.Coding.AlgebraicGeometry


