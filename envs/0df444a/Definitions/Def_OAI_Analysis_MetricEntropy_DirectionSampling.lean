-- Prove2me | Definitions.Def_OAI_Analysis_MetricEntropy_DirectionSampling
-- name    : OAI_Analysis_MetricEntropy_DirectionSampling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:43:30.330996+00:00
-- url     : https://prove2.me/theorems/7b85b4fe-dad8-42d0-8786-792b750345fe
-- title:
--   Bad samples witnessed by disjoint lists of zero tuples
-- statement:
--   These notions belong to a counterexample to the duality conjecture for metric entropy. For every $a,b\ge1$ there are $n$ and a symmetric convex body $K\subset\mathbb R^n$ with $\log N(K,Q_n)>b\log N(Q_n^\circ,a^{-1}K^\circ)$. Here $Q_n=[-1,1]^n$ is the cube, $K^\circ=\{y:\langle x,y\rangle\le1\text{ for all }x\in K\}$ is the polar (so $Q_n^\circ$ is the $\ell_1$ ball), and $N(A,B)$ is the least number of translates of $B$ covering $A$. In the construction the rows are the symmetric $h$-linear forms on $\mathbb F_p^r$. Their coefficients are indexed by multisets of size $h$, so there are $p^D$ of them with $D=\binom{r+h-1}{h}$. They are labelled by their contractions $F\mapsto F(t_i,\cdot,\dots,\cdot)$ along directions $t_1,\dots,t_u\in\mathbb F_p^r$. Directions $t:\{1..u\}\to E$ are sampled uniformly.
--
--   1. **Bad list event.** For a list $L_1,\dots,L_w$ of $h$-tuples of indices, the event that every tuple in the list is bad:
--   $$
--   \{t:\ \mathrm{bad}(t\circ L_j)\text{ for all }j\le w\}.
--   $$
--   2. **Disjoint lists.** The finite set of all lists of $w$ tuples in $\{1..u\}^h$ with pairwise disjoint supports.
--   3. **Bad samples.** For a finite family of forms $Z$ and a badness relation, a sample is bad if some form $z$ and some disjoint list $L$ have all tuples of $L$ bad for $z$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/DirectionSampling.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/DirectionSampling.lean by skeleton subtraction
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

namespace OAI

universe uU uE uJ uZ

/-!
# Counting and avoiding all disjoint zero-tuple witnesses

All ordered tuples are retained, including tuples with repeated indices.
The probability product estimate is applied only to lists whose distinct
tuple supports are pairwise disjoint. Their number is bounded by the exact
number of all ordered lists, `u ^ (h * w)`.
-/

noncomputable section

open scoped BigOperators

namespace MetricEntropyDuality.DirectionSampling

open FiniteProductCounting

section FiniteUnion

variable {U : Type uU} {E : Type uE} {J : Type uJ} [Fintype U] [DecidableEq U]
  [Fintype E] [DecidableEq E] [Nonempty E]

end FiniteUnion

section Tuples

variable {U : Type uU} {E : Type uE} [Fintype U] [DecidableEq U]
  [Fintype E] [DecidableEq E] [Nonempty E] {h w : ℕ}

/-- The event that every tuple in this particular list is bad. -/
def badListEvent (bad : (Fin h → E) → Prop) (L : Fin w → Fin h → U) :
    Finset (U → E) :=
  allEvents Finset.univ (fun j => tupleEvent bad (L j))

omit [Nonempty E] in
@[simp] theorem mem_badListEvent {bad : (Fin h → E) → Prop}
    {L : Fin w → Fin h → U} {t : U → E} :
    t ∈ badListEvent bad L ↔ ∀ j, bad (fun i => t (L j i)) := by
  classical
  simp [badListEvent, allEvents]

end Tuples

/-- Only disjoint lists are used as bad-event witnesses. -/
def disjointLists (u h w : ℕ) : Finset (Fin w → Fin h → Fin u) := by
  classical
  exact Finset.univ.filter DisjointSupports

@[simp] theorem mem_disjointLists {u h w : ℕ} {L : Fin w → Fin h → Fin u} :
    L ∈ disjointLists u h w ↔ DisjointSupports L := by
  classical
  simp [disjointLists]

section Sampling

variable {Z : Type uZ} {E : Type uE} [Fintype E] [DecidableEq E] [Nonempty E]
  {u h w : ℕ}

/-- The actual union over forms and disjoint witness lists. -/
def badSamples (forms : Finset Z) (bad : Z → (Fin h → E) → Prop) :
    Finset (Fin u → E) := by
  classical
  exact forms.biUnion fun z =>
    (disjointLists u h w).biUnion fun L => badListEvent (bad z) L

omit [Nonempty E] in
@[simp] theorem mem_badSamples {forms : Finset Z} {bad : Z → (Fin h → E) → Prop}
    {t : Fin u → E} :
    t ∈ badSamples (u := u) (w := w) forms bad ↔
      ∃ z ∈ forms, ∃ L : Fin w → Fin h → Fin u,
        DisjointSupports L ∧ ∀ j, bad z (fun i => t (L j i)) := by
  classical
  simp [badSamples]

end Sampling

end MetricEntropyDuality.DirectionSampling

end

end OAI


