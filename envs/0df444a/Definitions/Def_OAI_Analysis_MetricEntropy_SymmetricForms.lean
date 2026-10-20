-- Prove2me | Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricForms
-- name    : OAI_Analysis_MetricEntropy_SymmetricForms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:36:51.591281+00:00
-- url     : https://prove2.me/theorems/9440b5a8-161d-4954-a164-1ab4778dd490
-- title:
--   Symmetric multilinear forms given by multiset coefficients
-- statement:
--   These notions belong to a counterexample to the duality conjecture for metric entropy. For every $a,b\ge1$ there are $n$ and a symmetric convex body $K\subset\mathbb R^n$ with $\log N(K,Q_n)>b\log N(Q_n^\circ,a^{-1}K^\circ)$. Here $Q_n=[-1,1]^n$ is the cube, $K^\circ=\{y:\langle x,y\rangle\le1\text{ for all }x\in K\}$ is the polar (so $Q_n^\circ$ is the $\ell_1$ ball), and $N(A,B)$ is the least number of translates of $B$ covering $A$.
--
--   1. **Symmetric forms.** A symmetric $j$-linear form on $K^r$ is given by a coefficient $F(s)\in K$ for every multiset $s$ of size $j$ from $\{1,\dots,r\}$. The coefficients are free; degree $0$ is allowed.
--   2. **Evaluation.** For vectors $v_1,\dots,v_j\in K^r$,
--   $$
--   F(v_1,\dots,v_j)=\sum_{a:\{1..j\}\to\{1..r\}}F(\mathrm{sym}(a))\prod_{i=1}^jv_i(a_i),
--   $$
--   summing over all ordered tuples, repeated indices included.
--   3. **Multilinear map.** This evaluation is an actual multilinear map, and it is additive and homogeneous in $F$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/SymmetricForms.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/SymmetricForms.lean by skeleton subtraction
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

namespace OAI

universe uK

/-!
# Literal coefficients and actual symmetric multilinear forms

A coefficient is assigned freely to every multiset of basis indices, including
repetitions. Summing over ordered tuples gives an actual multilinear map. Basis
evaluation recovers every coefficient, and every permutation-invariant
multilinear map arises this way. The degree-zero case is included.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators

/-- Free literal coefficients on multisets of basis indices. -/
abbrev SymmetricForm (K : Type uK) (r j : ℕ) := Sym (Fin r) j → K

namespace SymmetricForm

variable {K : Type uK} [CommSemiring K] {r j : ℕ}

/-- Evaluation sums over ordered basis tuples; repeated indices are retained. -/
def eval (F : SymmetricForm K r j) (v : Fin j → (Fin r → K)) : K :=
  ∑ a : Fin j → Fin r, F (tupleSym a) * ∏ i, v i (a i)

@[simp] theorem eval_zero (v : Fin j → (Fin r → K)) :
    eval (0 : SymmetricForm K r j) v = 0 := by
  simp [eval]

@[simp] theorem eval_add (F G : SymmetricForm K r j) (v : Fin j → (Fin r → K)) :
    eval (F + G) v = eval F v + eval G v := by
  simp [eval, add_mul, Finset.sum_add_distrib]

@[simp] theorem eval_smul (c : K) (F : SymmetricForm K r j)
    (v : Fin j → (Fin r → K)) : eval (c • F) v = c * eval F v := by
  simp only [eval, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

 def coordinateProduct (a : Fin j → Fin r) :
    MultilinearMap K (fun _ : Fin j => Fin r → K) K :=
  (MultilinearMap.mkPiAlgebra K (Fin j) K).compLinearMap
    (fun i => LinearMap.proj (a i))

 theorem coordinateProduct_apply (a : Fin j → Fin r)
    (v : Fin j → (Fin r → K)) : coordinateProduct a v = ∏ i, v i (a i) := rfl

/-- The coefficient formula is an actual multilinear map, not an assumed law. -/
def toMultilinearMap (F : SymmetricForm K r j) :
    MultilinearMap K (fun _ : Fin j => Fin r → K) K :=
  ∑ a : Fin j → Fin r, F (tupleSym a) • coordinateProduct a

@[simp] theorem toMultilinearMap_apply (F : SymmetricForm K r j)
    (v : Fin j → (Fin r → K)) : toMultilinearMap F v = eval F v := by
  simp only [toMultilinearMap, _root_.sum_apply, _root_.smul_apply,
    coordinateProduct_apply, smul_eq_mul, eval]

@[simp] theorem toMultilinearMap_add (F G : SymmetricForm K r j) :
    toMultilinearMap (F + G) = toMultilinearMap F + toMultilinearMap G := by
  ext v
  simp only [toMultilinearMap_apply, _root_.add_apply, eval_add]

@[simp] theorem toMultilinearMap_smul (c : K) (F : SymmetricForm K r j) :
    toMultilinearMap (c • F) = c • toMultilinearMap F := by
  ext v
  simp only [toMultilinearMap_apply, _root_.smul_apply, eval_smul, smul_eq_mul]

section Ring

variable {K : Type uK} [CommRing K] {r j : ℕ}

@[simp] theorem eval_neg (F : SymmetricForm K r j) (v : Fin j → (Fin r → K)) :
    eval (-F) v = -eval F v := by
  simp [eval, Finset.sum_neg_distrib]

@[simp] theorem eval_sub (F G : SymmetricForm K r j) (v : Fin j → (Fin r → K)) :
    eval (F - G) v = eval F v - eval G v := by
  simp [eval, sub_mul, Finset.sum_sub_distrib]

end Ring

end SymmetricForm

end MetricEntropyDuality

end

end OAI


