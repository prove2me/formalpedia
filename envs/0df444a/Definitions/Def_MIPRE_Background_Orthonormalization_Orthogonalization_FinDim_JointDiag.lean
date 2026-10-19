-- Prove2me | Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_JointDiag
-- name    : MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_JointDiag
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:51:30.164265+00:00
-- url     : https://prove2.me/theorems/7bc41d0f-f1f2-483a-b52c-78dbc41cb32a
-- title:
--   Definitions of JointDiag: Elementary consequences of the eigen-equations
-- statement:
--   The definitions of the module `MIPRE.Background.Orthonormalization.Orthogonalization.FinDim.JointDiag` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). ### Elementary consequences of the eigen-equations
--
--   The module is vendored read-only from the `orthogonalization` development of [vidick/commuting-repetition](https://github.com/vidick/commuting-repetition) (Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-repetition.py`.
--
--   **Definitions** (5): `Orthogonalization.FinDim.JointEigenbasis` (A **joint orthonormal eigenbasis** for a pair of operators `x a : H →L[ℂ] H`: an orthonormal basis `basis` of `H`, indexed by `Fin (finrank…); `Orthogonalization.FinDim.JointEigenbasis.P` (The orthogonal projection onto the line spanned by the `k`-th joint eigenvector, i.e.); `Orthogonalization.FinDim.JointEigenbasis.shiftOne` (Adding `δ` to the `k`-th eigenvalue only: the operator `x + δ • P k` is still diagonal in `J.basis`, and still has `a` as a joint partner.); `Orthogonalization.FinDim.JointEigenbasis.shiftPair` (Adding `δ` to the `k`-th eigenvalue and subtracting `δ` from the `l`-th one: the operator `x + δ • (P k - P l)` is still diagonal in…); `Orthogonalization.FinDim.JointEigenbasis.swap` (Exchanging the roles of the two operators.).
--
--   **Embedded lemmas** (16): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `P_apply`, `P_apply_basis`, `P_apply_basis'`, `P_apply_basis_self`, `P_isStarProjection`, `P_mul_self`, `inner_basis`, `inner_basis_self`, `norm_basis`, `shiftOne_basis`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.Orthonormalization.Orthogonalization.FinDim.JointDiag` (`MIPRE/Background/Orthonormalization/Orthogonalization/FinDim/JointDiag.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/Orthonormalization/Orthogonalization/FinDim/JointDiag.lean

/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/FinDim/JointDiag.lean
-/
/-
# Joint diagonalization of two commuting self-adjoint operators (finite dimension)

Toolkit for Lemma 3.1 of M. de la Salle, *Orthogonalization of Positive Operator
Valued Measures* (arXiv:2103.14126v2), in the finite-dimensional case (`PLAN.md`
§3, tier T1a). The perturbation argument of that lemma takes a pair `(x, a)` of
commuting self-adjoint operators on a finite-dimensional complex Hilbert space
`H`, diagonalizes them simultaneously, and moves an amount `δ` of one eigenvalue
of `x` onto another, keeping the trace and the commutation with `a` and staying
inside the operator interval `[0, 1]`.

This file packages exactly that: a `JointEigenbasis x a` (an orthonormal basis of
`H` made of joint eigenvectors of `x` and `a`, with *real* eigenvalue functions
`lam` and `mu`), its existence for commuting self-adjoint operators, the rank-one
spectral projections `P k`, the spectral decomposition and trace formula, the
translation between the Loewner order on `x` and the pointwise order on `lam`,
the characterisation of the projections among such `x`, and the two eigenvalue
shifts (`shiftPair`, `shiftOne`).

Everything here is elementary and internal to the proof; no result of this file
is a statement of the paper, so it carries no fidelity-ledger entry.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Orthonormalization/Orthogonalization/FinDim/JointDiag.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.IsApply
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.SetLike.Basic
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Pairwise
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Defs
import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.Notation
import Mathlib.Order.SetNotation
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs

set_option autoImplicit true

namespace Orthogonalization.FinDim

open scoped BigOperators ComplexOrder InnerProductSpace
open Module

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- A **joint orthonormal eigenbasis** for a pair of operators `x a : H →L[ℂ] H`:
an orthonormal basis `basis` of `H`, indexed by `Fin (finrank ℂ H)`, each of whose
vectors is an eigenvector of `x` with real eigenvalue `lam k` and an eigenvector
of `a` with real eigenvalue `mu k`.

Such a datum exists exactly when `x` and `a` are commuting self-adjoint operators:
see `Orthogonalization.FinDim.exists_jointEigenbasis` for one direction and
`JointEigenbasis.isSelfAdjoint_fst`, `JointEigenbasis.isSelfAdjoint_snd`,
`JointEigenbasis.commute` for the other. -/
structure JointEigenbasis (x a : H →L[ℂ] H) where
  /-- The orthonormal basis of joint eigenvectors. -/
  basis : OrthonormalBasis (Fin (finrank ℂ H)) ℂ H
  /-- The (real) eigenvalues of the first operator `x`. -/
  lam : Fin (finrank ℂ H) → ℝ
  /-- The (real) eigenvalues of the second operator `a`. -/
  mu : Fin (finrank ℂ H) → ℝ
  /-- `basis k` is an eigenvector of `x` for the eigenvalue `lam k`. -/
  apply_fst : ∀ k, x (basis k) = (lam k : ℂ) • basis k
  /-- `basis k` is an eigenvector of `a` for the eigenvalue `mu k`. -/
  apply_snd : ∀ k, a (basis k) = (mu k : ℂ) • basis k

section Existence

end Existence

namespace JointEigenbasis

variable {x a : H →L[ℂ] H} (J : JointEigenbasis x a)

include J

-- Most lemmas below only use the eigen-equations, not finite-dimensionality of `H`
-- (which enters only through `exists_jointEigenbasis`); silence the resulting noise.
set_option linter.unusedSectionVars false

/-! ### Elementary consequences of the eigen-equations -/

theorem norm_basis (k : Fin (finrank ℂ H)) : ‖J.basis k‖ = 1 := J.basis.orthonormal.1 k

theorem inner_basis (k l : Fin (finrank ℂ H)) :
    inner ℂ (J.basis k) (J.basis l) = if k = l then (1 : ℂ) else 0 :=
  orthonormal_iff_ite.mp J.basis.orthonormal k l

@[simp] theorem inner_basis_self (k : Fin (finrank ℂ H)) :
    inner ℂ (J.basis k) (J.basis k) = (1 : ℂ) := by simp

/-- Exchanging the roles of the two operators. -/
def swap : JointEigenbasis a x where
  basis := J.basis
  lam := J.mu
  mu := J.lam
  apply_fst := J.apply_snd
  apply_snd := J.apply_fst

@[simp] theorem swap_basis : J.swap.basis = J.basis := rfl
@[simp] theorem swap_lam : J.swap.lam = J.mu := rfl
@[simp] theorem swap_mu : J.swap.mu = J.lam := rfl

/-! ### The rank-one spectral projections -/

/-- The orthogonal projection onto the line spanned by the `k`-th joint
eigenvector, i.e. the `k`-th rank-one spectral projection of the pair. -/
noncomputable def P (k : Fin (finrank ℂ H)) : H →L[ℂ] H := (ℂ ∙ J.basis k).starProjection

theorem P_apply (k : Fin (finrank ℂ H)) (w : H) :
    J.P k w = (inner ℂ (J.basis k) w : ℂ) • J.basis k :=
  Submodule.starProjection_unit_singleton ℂ (J.norm_basis k) w

/-- Each `P k` is an orthogonal (star) projection: self-adjoint and idempotent. -/
theorem P_isStarProjection (k : Fin (finrank ℂ H)) : IsStarProjection (J.P k) :=
  isStarProjection_starProjection

theorem P_apply_basis (k l : Fin (finrank ℂ H)) :
    J.P k (J.basis l) = if k = l then J.basis k else 0 := by
  rw [J.P_apply, J.inner_basis]
  by_cases h : k = l <;> simp [h]

@[simp] theorem P_apply_basis_self (k : Fin (finrank ℂ H)) : J.P k (J.basis k) = J.basis k := by
  simp [J.P_apply_basis]

/-- A variant of `P_apply_basis` phrased as a scalar multiple of `basis l`, convenient
for `module`-style computations. -/
theorem P_apply_basis' (k l : Fin (finrank ℂ H)) :
    J.P k (J.basis l) = (if l = k then (1 : ℂ) else 0) • J.basis l := by
  by_cases h : k = l
  · subst h; simp
  · simp [J.P_apply_basis, h, Ne.symm h]

@[simp] theorem P_mul_self (k : Fin (finrank ℂ H)) : J.P k * J.P k = J.P k :=
  (J.P_isStarProjection k).isIdempotentElem

/-! ### Spectral decomposition -/

/-! ### Commutation with the spectral projections -/

/-! ### Trace -/

/-! ### The Loewner order and the eigenvalues -/

/-! ### The projections among the operators of a joint eigenbasis -/

/-! ### Perturbations: moving eigenvalue mass between two basis vectors

These are the operations Lemma 3.1 performs on an extreme point of its convex
set: they preserve the joint eigenbasis (hence the commutation with `a` and the
self-adjointness), preserve or shift the trace by a controlled amount, and stay
inside `[0, 1]` as long as the perturbed eigenvalues do. -/

/-- Adding `δ` to the `k`-th eigenvalue and subtracting `δ` from the `l`-th one:
the operator `x + δ • (P k - P l)` is still diagonal in `J.basis`, and still has
`a` as a joint partner. -/
noncomputable def shiftPair (k l : Fin (finrank ℂ H)) (δ : ℝ) :
    JointEigenbasis (x + (δ : ℂ) • (J.P k - J.P l)) a where
  basis := J.basis
  lam := fun m => J.lam m + (if m = k then δ else 0) - (if m = l then δ else 0)
  mu := J.mu
  apply_fst := by
    intro m
    rw [add_apply, smul_apply, sub_apply, J.apply_fst, J.P_apply_basis', J.P_apply_basis']
    split_ifs <;> push_cast <;> module
  apply_snd := J.apply_snd

@[simp] theorem shiftPair_basis (k l : Fin (finrank ℂ H)) (δ : ℝ) :
    (J.shiftPair k l δ).basis = J.basis := rfl

@[simp] theorem shiftPair_mu (k l : Fin (finrank ℂ H)) (δ : ℝ) :
    (J.shiftPair k l δ).mu = J.mu := rfl

/-- Adding `δ` to the `k`-th eigenvalue only: the operator `x + δ • P k` is still
diagonal in `J.basis`, and still has `a` as a joint partner. -/
noncomputable def shiftOne (k : Fin (finrank ℂ H)) (δ : ℝ) :
    JointEigenbasis (x + (δ : ℂ) • J.P k) a where
  basis := J.basis
  lam := fun m => J.lam m + (if m = k then δ else 0)
  mu := J.mu
  apply_fst := by
    intro m
    rw [add_apply, smul_apply, J.apply_fst, J.P_apply_basis']
    split_ifs <;> push_cast <;> module
  apply_snd := J.apply_snd

@[simp] theorem shiftOne_basis (k : Fin (finrank ℂ H)) (δ : ℝ) :
    (J.shiftOne k δ).basis = J.basis := rfl

@[simp] theorem shiftOne_mu (k : Fin (finrank ℂ H)) (δ : ℝ) :
    (J.shiftOne k δ).mu = J.mu := rfl

end JointEigenbasis

end Orthogonalization.FinDim


