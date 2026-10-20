-- Prove2me | Definitions.Def_OAI_Analysis_MetricEntropy_FiniteProductCounting
-- name    : OAI_Analysis_MetricEntropy_FiniteProductCounting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:42:23.020006+00:00
-- url     : https://prove2.me/theorems/7d88645a-309c-48e8-aa02-89d212c5453a
-- title:
--   Uniform probability on a finite product sample space
-- statement:
--   These notions belong to a counterexample to the duality conjecture for metric entropy. For every $a,b\ge1$ there are $n$ and a symmetric convex body $K\subset\mathbb R^n$ with $\log N(K,Q_n)>b\log N(Q_n^\circ,a^{-1}K^\circ)$. Here $Q_n=[-1,1]^n$ is the cube, $K^\circ=\{y:\langle x,y\rangle\le1\text{ for all }x\in K\}$ is the polar (so $Q_n^\circ$ is the $\ell_1$ ball), and $N(A,B)$ is the least number of translates of $B$ covering $A$. The sample space is the set $E^U$ of all functions $U\to E$ for finite $U$ and nonempty finite $E$.
--
--   1. **Dependence.** An event $A\subseteq E^U$ depends only on $S\subseteq U$ if any two samples agreeing on $S$ are both in $A$ or both outside it.
--   2. **Probability.** $\Pr(A)=|A|/|E|^{|U|}$, the uniform probability, with $\Pr(E^U)=1$.
--   3. **Coordinate swap.** For $S\subseteq U$ the swap exchanges two samples outside $S$ and keeps them on $S$:
--   $$
--   (\omega,\eta)\mapsto\bigl(\omega|_S\cup\eta|_{U\setminus S},\ \eta|_S\cup\omega|_{U\setminus S}\bigr).
--   $$
--   It is used to prove independence of events depending on disjoint sets.
--   4. **Joint events.** $\mathrm{all}(s,A)=\bigcap_{j\in s}A_j$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/FiniteProductCounting.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/FiniteProductCounting.lean by skeleton subtraction
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

-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

universe uU uE uJ

/-!
# Counting events on disjoint sets of coordinates

The sample space is the actual finite function space `U → E`, with uniform
probability given by cardinality divided by the cardinality of that space.
A coordinate-swap bijection proves independence of two events from their
literal disjoint supports. Finite intersections then follow by induction.
No independence hypothesis or distinctness within an individual tuple is used.
-/

namespace MetricEntropyDuality.FiniteProductCounting

open scoped BigOperators

variable {U : Type uU} {E : Type uE} [Fintype U] [DecidableEq U] [Fintype E] [DecidableEq E]

/-- Agreement on the named coordinates determines event membership. -/
def DependsOn (S : Finset U) (A : Finset (U → E)) : Prop :=
  ∀ ω η : U → E, (∀ u ∈ S, ω u = η u) → (ω ∈ A ↔ η ∈ A)

/-- Uniform probability on the complete finite product sample space. -/
noncomputable def prob (A : Finset (U → E)) : ℝ :=
  (A.card : ℝ) / (Fintype.card (U → E) : ℝ)

/-- Swap the two assignments outside `S`, retaining them on `S`. -/
def coordinateSwap (S : Finset U) (z : (U → E) × (U → E)) :
    (U → E) × (U → E) :=
  (fun u => if u ∈ S then z.1 u else z.2 u,
   fun u => if u ∈ S then z.2 u else z.1 u)

section NonemptyAlphabet

variable [Nonempty E]

omit [DecidableEq E] in
theorem sample_card_pos : (0 : ℝ) < Fintype.card (U → E) := by
  exact Nat.cast_pos.mpr (Fintype.card_pos (α := U → E))

omit [DecidableEq E] in
@[simp] theorem prob_univ : prob (Finset.univ : Finset (U → E)) = 1 := by
  simp only [prob, Finset.card_univ, div_self (ne_of_gt (sample_card_pos (U := U) (E := E)))]

end NonemptyAlphabet

/-- All indexed events hold; the index set and events are kept literally. -/
def allEvents {J : Type uJ} [DecidableEq J] (s : Finset J)
    (A : J → Finset (U → E)) : Finset (U → E) :=
  Finset.univ.filter fun ω => ∀ j ∈ s, ω ∈ A j

@[simp] theorem mem_allEvents {J : Type uJ} [DecidableEq J]
    (s : Finset J) (A : J → Finset (U → E)) (ω : U → E) :
    ω ∈ allEvents s A ↔ ∀ j ∈ s, ω ∈ A j := by
  simp [allEvents]

@[simp] theorem allEvents_empty {J : Type uJ} [DecidableEq J]
    (A : J → Finset (U → E)) : allEvents ∅ A = Finset.univ := by
  ext ω
  simp

section FiniteIntersection

variable [Nonempty E]

end FiniteIntersection

end MetricEntropyDuality.FiniteProductCounting

end OAI


