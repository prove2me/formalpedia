-- Prove2me | Definitions.Def_BasicResults_Auerbach
-- name    : BasicResults_Auerbach
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:27:05.985649+00:00
-- url     : https://prove2.me/theorems/d1d8a6e4-41c4-4ca0-94fd-46a6563bef1a
-- title:
--   Auerbach
-- statement:
--   Definitions and structural lemmas for Auerbach, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Auerbach.lean

module
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Instances.Matrix
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open Module FiniteDimensional Metric
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
structure IsAuerbachBasis (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι] (b : Basis ι ℝ V) : Prop where
  norm_basis : ∀ i, ‖b i‖ = 1
  norm_coord : ∀ i, ‖(b.coord i).toContinuousLinearMap‖ = 1
noncomputable def coordFunOfDet {n : ℕ} (b₀ : Basis (Fin n) ℝ V)
    (e : Fin n → V) (_h_det : b₀.det e ≠ 0) (i : Fin n) : V →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((b₀.det e)⁻¹ • b₀.det.toMultilinearMap.toLinearMap e i)
omit [FiniteDimensional ℝ V] in
/-- If `b₀.det e ≠ 0`, the vectors `e` form a basis of `V`: they are linearly
    independent and span the whole space.  This packages Mathlib's
    `Basis.is_basis_iff_det`, using that over the field `ℝ` a determinant is a
    unit iff it is nonzero (`isUnit_iff_ne_zero`). -/
theorem isBasis_of_det_ne_zero {n : ℕ} (b₀ : Basis (Fin n) ℝ V)
    (e : Fin n → V) (h_det : b₀.det e ≠ 0) :
    LinearIndependent ℝ e ∧ Submodule.span ℝ (Set.range e) = ⊤ :=
  (b₀.is_basis_iff_det).mpr (isUnit_iff_ne_zero.mpr h_det)
def basisOfMaximizer {n : ℕ} (b₀ : Basis (Fin n) ℝ V)
    (e : Fin n → V) (h_det : b₀.det e ≠ 0) : Basis (Fin n) ℝ V :=
  Basis.mk (isBasis_of_det_ne_zero b₀ e h_det).1
    (isBasis_of_det_ne_zero b₀ e h_det).2.ge
end


