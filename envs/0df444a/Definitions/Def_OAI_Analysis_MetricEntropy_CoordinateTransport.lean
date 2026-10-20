-- Prove2me | Definitions.Def_OAI_Analysis_MetricEntropy_CoordinateTransport
-- name    : OAI_Analysis_MetricEntropy_CoordinateTransport
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:40:28.660606+00:00
-- url     : https://prove2.me/theorems/491b9a70-6794-4398-811f-cf0bbf0e3822
-- title:
--   Relabelling the coordinates of a finite real space
-- statement:
--   These notions belong to a counterexample to the duality conjecture for metric entropy. For every $a,b\ge1$ there are $n$ and a symmetric convex body $K\subset\mathbb R^n$ with $\log N(K,Q_n)>b\log N(Q_n^\circ,a^{-1}K^\circ)$. Here $Q_n=[-1,1]^n$ is the cube, $K^\circ=\{y:\langle x,y\rangle\le1\text{ for all }x\in K\}$ is the polar (so $Q_n^\circ$ is the $\ell_1$ ball), and $N(A,B)$ is the least number of translates of $B$ covering $A$.
--
--   1. **Coordinate equivalence.** For a bijection $e:\iota\to\kappa$ of finite index sets, $\Phi_e:\mathbb R^\iota\to\mathbb R^\kappa$ is $(\Phi_ex)_j=x_{e^{-1}(j)}$. It is a linear homeomorphism with inverse $\Phi_{e^{-1}}$, and $y\in\Phi_e(A)$ iff $\Phi_e^{-1}y\in A$.
--   2. **Transfer to $\mathrm{Fin}\,n$.** For a finite type $\iota$, the identification
--   $$
--   \mathbb R^\iota\cong\mathbb R^{\{0,\dots,|\iota|-1\}}
--   $$
--   is $\Phi_e$ for a chosen enumeration $e$. It maps cubes to cubes and preserves the pairing, so polars and covering numbers transfer.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/CoordinateTransport.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/CoordinateTransport.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MetricEntropyDuality mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Monotone.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Definitions.Def_MetricEntropyDuality
import Definitions.Def_OAI_Analysis_MetricEntropy_FormDimension
import Definitions.Def_OAI_Analysis_MetricEntropy_Parameters
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricIndex
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricForms
import Definitions.Def_OAI_Analysis_MetricEntropy_Basic
import Definitions.Def_OAI_Analysis_MetricEntropy_EntropyPair
import Definitions.Def_OAI_Analysis_MetricEntropy_SupportPolar
import Definitions.Def_OAI_Analysis_MetricEntropy_PolarCover

namespace OAI

universe uι uκ

/-!
# Relabelling finite real coordinates

The coordinate map is a linear homeomorphism of the full ambient spaces.
It transports all translation centers, rather than restricting them to the
body being covered. Consequently equality of covering numbers follows from
equality of the sets of admissible natural cover counts.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators Pointwise

variable {ι : Type uι} {κ : Type uκ}

/-- Relabel coordinates using `e`; no coordinate is removed or adjoined. -/
def coordinateEquiv (e : ι ≃ κ) : (ι → ℝ) ≃L[ℝ] (κ → ℝ) where
  toFun x j := x (e.symm j)
  invFun y i := y (e i)
  left_inv x := by funext i; simp
  right_inv y := by funext j; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_pi fun j => continuous_apply (e.symm j)
  continuous_invFun := continuous_pi fun i => continuous_apply (e i)

@[simp] theorem coordinateEquiv_apply (e : ι ≃ κ) (x : ι → ℝ) (j : κ) :
    coordinateEquiv e x j = x (e.symm j) := rfl

@[simp] theorem coordinateEquiv_symm_apply (e : ι ≃ κ) (y : κ → ℝ) (i : ι) :
    (coordinateEquiv e).symm y i = y (e i) := rfl

@[simp] theorem coordinateEquiv_symm (e : ι ≃ κ) :
    (coordinateEquiv e).symm = coordinateEquiv e.symm := by
  ext y i
  rfl

@[simp] theorem mem_coordinate_image_iff (e : ι ≃ κ)
    (A : Set (RealSpace ι)) (y : RealSpace κ) :
    y ∈ coordinateEquiv e '' A ↔ (coordinateEquiv e).symm y ∈ A := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx
  · intro hy
    exact ⟨(coordinateEquiv e).symm y, hy,
      (coordinateEquiv e).apply_symm_apply y⟩

section FiniteCoordinates

variable [Fintype ι] [Fintype κ]

end FiniteCoordinates

/-- The terminal ambient-space identification is a genuine linear
homeomorphism, not a cardinality-only relabelling. -/
def coordinatesToFin [Fintype ι] : (ι → ℝ) ≃L[ℝ] (Fin (Fintype.card ι) → ℝ) :=
  coordinateEquiv (Fintype.equivFin ι)

end MetricEntropyDuality

end

end OAI


