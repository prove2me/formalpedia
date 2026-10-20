-- Prove2me | Definitions.Def_OAI_Analysis_MetricEntropy_DirectionTuples
-- name    : OAI_Analysis_MetricEntropy_DirectionTuples
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:41:23.758001+00:00
-- url     : https://prove2.me/theorems/eeec17cd-b3a7-4851-b74e-ae9ea8a136a4
-- title:
--   Supports and bad events for tuples of sampled directions
-- statement:
--   These notions belong to a counterexample to the duality conjecture for metric entropy. For every $a,b\ge1$ there are $n$ and a symmetric convex body $K\subset\mathbb R^n$ with $\log N(K,Q_n)>b\log N(Q_n^\circ,a^{-1}K^\circ)$. Here $Q_n=[-1,1]^n$ is the cube, $K^\circ=\{y:\langle x,y\rangle\le1\text{ for all }x\in K\}$ is the polar (so $Q_n^\circ$ is the $\ell_1$ ball), and $N(A,B)$ is the least number of translates of $B$ covering $A$. In the construction the rows are the symmetric $h$-linear forms on $\mathbb F_p^r$. Their coefficients are indexed by multisets of size $h$, so there are $p^D$ of them with $D=\binom{r+h-1}{h}$. They are labelled by their contractions $F\mapsto F(t_i,\cdot,\dots,\cdot)$ along directions $t_1,\dots,t_u\in\mathbb F_p^r$. The directions $t:U\to E$ are sampled uniformly from all functions on a finite index set $U$.
--
--   1. **Tuple support.** For a tuple $a:\{1..h\}\to U$ (repetitions allowed), $\mathrm{supp}(a)=\{a_1,\dots,a_h\}$, the set of distinct entries.
--   2. **Disjoint lists.** A list $L_1,\dots,L_w$ of tuples has disjoint supports if $\mathrm{supp}(L_i)\cap\mathrm{supp}(L_j)=\varnothing$ for $i\ne j$.
--   3. **Tuple events.** For a property $\mathrm{bad}$ of $h$-tuples of values,
--   $$
--   \mathcal E_{\mathrm{bad}}(a)=\{t:U\to E:\ \mathrm{bad}(t(a_1),\dots,t(a_h))\} .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/DirectionTuples.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/DirectionTuples.lean by skeleton subtraction
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

namespace OAI

universe uU uE

/-!
# Supports and events for direction tuples

Tuples are arbitrary functions from `Fin h`; repeated indices are allowed.
The support records distinct indices, so its cardinality can be smaller than `h`.
-/

namespace MetricEntropyDuality

variable {U : Type uU} {E : Type uE} {h w : ℕ}

/-- The set of indices appearing in an ordered tuple, including repeated-index tuples. -/
noncomputable def tupleSupport (a : Fin h → U) : Finset U := by
  classical
  exact Finset.univ.image a

@[simp] theorem mem_tupleSupport {a : Fin h → U} {x : U} :
    x ∈ tupleSupport a ↔ ∃ j, a j = x := by
  classical
  simp [tupleSupport]

/-- Different tuples in the list use disjoint sets of indices. -/
def DisjointSupports (L : Fin w → Fin h → U) : Prop :=
  Pairwise fun i j => Disjoint (tupleSupport (L i)) (tupleSupport (L j))

/-- Samples for which the specified tuple of sampled values satisfies `bad`. -/
noncomputable def tupleEvent [Fintype U] [Fintype E]
    (bad : (Fin h → E) → Prop) (a : Fin h → U) : Finset (U → E) := by
  classical
  exact Finset.univ.filter fun t => bad (fun j => t (a j))

@[simp] theorem mem_tupleEvent [Fintype U] [Fintype E]
    {bad : (Fin h → E) → Prop} {a : Fin h → U} {t : U → E} :
    t ∈ tupleEvent bad a ↔ bad (fun j => t (a j)) := by
  classical
  simp [tupleEvent]

end MetricEntropyDuality

end OAI


