-- Prove2me | Definitions.Def_OAI_Analysis_MetricEntropy_FormContraction
-- name    : OAI_Analysis_MetricEntropy_FormContraction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:48:07.085187+00:00
-- url     : https://prove2.me/theorems/8aaae511-22f0-4642-ac54-3628103402e0
-- title:
--   Contraction of a symmetric form along a vector
-- statement:
--   These notions belong to a counterexample to the duality conjecture for metric entropy. For every $a,b\ge1$ there are $n$ and a symmetric convex body $K\subset\mathbb R^n$ with $\log N(K,Q_n)>b\log N(Q_n^\circ,a^{-1}K^\circ)$. Here $Q_n=[-1,1]^n$ is the cube, $K^\circ=\{y:\langle x,y\rangle\le1\text{ for all }x\in K\}$ is the polar (so $Q_n^\circ$ is the $\ell_1$ ball), and $N(A,B)$ is the least number of translates of $B$ covering $A$. In the construction the rows are the symmetric $h$-linear forms on $\mathbb F_p^r$. Their coefficients are indexed by multisets of size $h$, so there are $p^D$ of them with $D=\binom{r+h-1}{h}$. They are labelled by their contractions $F\mapsto F(t_i,\cdot,\dots,\cdot)$ along directions $t_1,\dots,t_u\in\mathbb F_p^r$.
--
--   1. **Contraction.** For $v\in K^r$ and a symmetric $(j+1)$-linear form $F$, the contraction $F_v$ is the symmetric $j$-linear form with coefficients
--   $$
--   F_v(s)=\sum_{a=1}^rv_a\,F(\{\!\{a\}\!\}+s) .
--   $$
--   Its evaluation is $F(v,\cdot,\dots,\cdot)$.
--   2. **Linearity.** $F\mapsto F_v$ is $K$-linear. It is used as the partition label of $F$ for the direction $v$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/FormContraction.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/FormContraction.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_MetricEntropy_CoordinateTransport
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionTuples
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteProductCounting
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionSampling
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricMultiplicity
import Definitions.Def_OAI_Analysis_MetricEntropy_FormPolynomials
import Definitions.Def_OAI_Analysis_MetricEntropy_PolynomialZeroBound

namespace OAI

universe uK

/-!
# Contraction of symmetric forms

The coefficients of a contraction are obtained by summing the original
coefficients against the fixed vector.  Evaluation is literally evaluation of
that original form with the vector in the first slot.  The proof reindexes all
ordered basis tuples, including repeated indices and the empty remaining tuple.
-/

namespace MetricEntropyDuality
namespace SymmetricForm

open scoped BigOperators

variable {K : Type uK} {r j : ℕ}

section CommSemiring

variable [CommSemiring K]

/-- Fix the first vector of a symmetric form, retaining its multiset coefficients. -/
def contract (v : Fin r → K) (F : SymmetricForm K r (j + 1)) :
    SymmetricForm K r j :=
  fun s => ∑ a : Fin r, v a * F (Sym.cons a s)

@[simp] theorem contract_apply (v : Fin r → K) (F : SymmetricForm K r (j + 1))
    (s : Sym (Fin r) j) :
    contract v F s = ∑ a : Fin r, v a * F (Sym.cons a s) := rfl

@[simp] theorem contract_zero (v : Fin r → K) :
    contract v (0 : SymmetricForm K r (j + 1)) = 0 := by
  funext s
  simp [contract]

@[simp] theorem contract_add (v : Fin r → K) (F G : SymmetricForm K r (j + 1)) :
    contract v (F + G) = contract v F + contract v G := by
  funext s
  simp [contract, mul_add, Finset.sum_add_distrib]

@[simp] theorem contract_smul (v : Fin r → K) (c : K)
    (F : SymmetricForm K r (j + 1)) :
    contract v (c • F) = c • contract v F := by
  funext s
  change (∑ a : Fin r, v a * (c * F (Sym.cons a s))) =
    c * ∑ a : Fin r, v a * F (Sym.cons a s)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ac_rfl

/-- The actual contraction map used as a partition label. -/
def contractLinearMap (v : Fin r → K) :
    SymmetricForm K r (j + 1) →ₗ[K] SymmetricForm K r j where
  toFun := contract v
  map_add' := contract_add v
  map_smul' := contract_smul v

@[simp] theorem contractLinearMap_apply (v : Fin r → K)
    (F : SymmetricForm K r (j + 1)) : contractLinearMap v F = contract v F := rfl

end CommSemiring

section CommRing

variable [CommRing K]

@[simp] theorem contract_sub (v : Fin r → K) (F G : SymmetricForm K r (j + 1)) :
    contract v (F - G) = contract v F - contract v G :=
  (contractLinearMap v).map_sub F G

end CommRing

end SymmetricForm
end MetricEntropyDuality

end OAI


