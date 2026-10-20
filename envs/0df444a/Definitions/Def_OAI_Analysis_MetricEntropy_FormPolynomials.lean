-- Prove2me | Definitions.Def_OAI_Analysis_MetricEntropy_FormPolynomials
-- name    : OAI_Analysis_MetricEntropy_FormPolynomials
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:45:47.34169+00:00
-- url     : https://prove2.me/theorems/edfb5126-b4de-4979-bbd0-7cc9ecfa7ed3
-- title:
--   Polynomials attached to symmetric forms
-- statement:
--   These notions belong to a counterexample to the duality conjecture for metric entropy. For every $a,b\ge1$ there are $n$ and a symmetric convex body $K\subset\mathbb R^n$ with $\log N(K,Q_n)>b\log N(Q_n^\circ,a^{-1}K^\circ)$. Here $Q_n=[-1,1]^n$ is the cube, $K^\circ=\{y:\langle x,y\rangle\le1\text{ for all }x\in K\}$ is the polar (so $Q_n^\circ$ is the $\ell_1$ ball), and $N(A,B)$ is the least number of translates of $B$ covering $A$. In the construction the rows are the symmetric $h$-linear forms on $\mathbb F_p^r$. Their coefficients are indexed by multisets of size $h$, so there are $p^D$ of them with $D=\binom{r+h-1}{h}$. They are labelled by their contractions $F\mapsto F(t_i,\cdot,\dots,\cdot)$ along directions $t_1,\dots,t_u\in\mathbb F_p^r$. Let $F$ be a symmetric $h$-linear form on $K^r$ with coefficients $F(s)$.
--
--   1. **Exponent vector.** A multiset $s$ gives the exponent vector $k\mapsto\mathrm{mult}_s(k)$. This map is injective.
--   2. **Diagonal polynomial.** In variables $X_1,\dots,X_r$,
--   $$
--   P_F=\sum_{b:\{1..h\}\to\{1..r\}}F(\mathrm{sym}(b))\prod_{j=1}^hX_{b_j},
--   $$
--   the evaluation $F(x,\dots,x)$ written symbolically.
--   3. **Tuple polynomial.** For a tuple $a$ of direction indices in $\{1..u\}$, in variables $X_{(i,k)}$ ($i\le u$, $k\le r$),
--   $$
--   P_{F,a}=\sum_bF(\mathrm{sym}(b))\prod_jX_{(a_j,b_j)} .
--   $$
--   This is the symbolic value $F(t_{a_1},\dots,t_{a_h})$ when $X_{(i,k)}$ stands for the $k$-th coordinate of $t_i$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/FormPolynomials.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/FormPolynomials.lean by skeleton subtraction
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

namespace OAI

universe uK

/-!
# Actual polynomials of symmetric forms

The definitions sum over ordered basis tuples, exactly as the multilinear
form evaluation does. The diagonal coefficient of a basis multiset is its
ordered-tuple fiber cardinality times the value of the form. This coefficient
is nonzero in characteristic greater than the degree. Renaming every vector
block to the same coordinate proves nonvanishing for every index tuple,
including tuples with repeated indices.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators
open MvPolynomial

/-- The exponent vector of a multiset of basis indices. -/
def symExponent {r h : ℕ} (s : Sym (Fin r) h) : Fin r →₀ ℕ :=
  (s : Multiset (Fin r)).toFinsupp

theorem symExponent_injective {r h : ℕ} :
    Function.Injective (@symExponent r h) := by
  intro s t hst
  apply Subtype.ext
  exact Multiset.toFinsupp.injective hst

@[simp] theorem symExponent_eq_iff {r h : ℕ} (s t : Sym (Fin r) h) :
    symExponent s = symExponent t ↔ s = t :=
  symExponent_injective.eq_iff

/-- The diagonal polynomial, formed from the actual ordered-tuple expansion. -/
def diagonalPolynomial {K : Type uK} [CommSemiring K] {r h : ℕ}
    (F : SymmetricForm K r h) : MvPolynomial (Fin r) K :=
  ∑ b : Fin h → Fin r, C (F (tupleSym b)) * ∏ j : Fin h, X (b j)

/-- The actual symbolic evaluation on a tuple of vector blocks. -/
def tuplePolynomial {K : Type uK} [CommSemiring K] {r h u : ℕ}
    (F : SymmetricForm K r h) (a : Fin h → Fin u) :
    MvPolynomial (Fin u × Fin r) K :=
  ∑ b : Fin h → Fin r, C (F (tupleSym b)) * ∏ j : Fin h, X (a j, b j)

end MetricEntropyDuality

end

end OAI


