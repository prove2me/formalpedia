-- Prove2me | Definitions.Def_OAI_Analysis_MetricEntropy_FieldGraphSeparation
-- name    : OAI_Analysis_MetricEntropy_FieldGraphSeparation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:50:02.508297+00:00
-- url     : https://prove2.me/theorems/a9bfb383-415e-4fc2-bf18-552a1b4fee31
-- title:
--   Contraction labels and padded tuples
-- statement:
--   These notions belong to a counterexample to the duality conjecture for metric entropy. For every $a,b\ge1$ there are $n$ and a symmetric convex body $K\subset\mathbb R^n$ with $\log N(K,Q_n)>b\log N(Q_n^\circ,a^{-1}K^\circ)$. Here $Q_n=[-1,1]^n$ is the cube, $K^\circ=\{y:\langle x,y\rangle\le1\text{ for all }x\in K\}$ is the polar (so $Q_n^\circ$ is the $\ell_1$ ball), and $N(A,B)$ is the least number of translates of $B$ covering $A$. In the construction the rows are the symmetric $h$-linear forms on $\mathbb F_p^r$. Their coefficients are indexed by multisets of size $h$, so there are $p^D$ of them with $D=\binom{r+h-1}{h}$. They are labelled by their contractions $F\mapsto F(t_i,\cdot,\dots,\cdot)$ along directions $t_1,\dots,t_u\in\mathbb F_p^r$.
--
--   1. **Labels.** For directions $t_i\in K^r$ ($i\in\iota$), the $i$-th label of a symmetric $(j+1)$-linear form $F$ is its contraction $F_{t_i}=F(t_i,\cdot,\dots,\cdot)$. Two forms are adjacent in the partition graph for $T$ when they have equal contractions along some $t_i$, $i\in T$.
--   2. **Padding.** A $k$-tuple $a$ is padded to an $h$-tuple with a filler value:
--   $$
--   \mathrm{pad}(a)_i=\begin{cases}a_i&i\le k,\\ \text{filler}&i>k.\end{cases}
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/FieldGraphSeparation.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/FieldGraphSeparation.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_MetricEntropy_FormContraction
import Definitions.Def_OAI_Analysis_MetricEntropy_PartitionGraph

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uK uι uα uV uA

/-!
# Actual contraction labels obstruct short walks

One label is chosen for each edge of a hypothetical short walk. These labels
are padded to the full degree using one fixed member of the same set of
directions. Symmetry moves each edge's direction to the contracted slot, so
evaluation on this single tuple is constant along the walk. This contradicts
robust nonvanishing of the difference of its endpoints.
-/

noncomputable section

namespace MetricEntropyDuality

namespace SymmetricForm

variable {K : Type uK} [CommSemiring K] {r j : ℕ}

end SymmetricForm

namespace FieldGraphSeparation

variable {K : Type uK} {ι : Type uι} [CommRing K] {r j : ℕ}

/-- The partition labels are the actual symmetric coefficient contractions. -/
def labels (t : ι → (Fin r → K)) (i : ι)
    (F : SymmetricForm K r (j + 1)) : SymmetricForm K r j :=
  SymmetricForm.contract (t i) F

 def padTuple {α : Type uα} {k h : ℕ} (a : Fin k → α) (filler : α) :
    Fin h → α := fun i => if hi : i.val < k then a ⟨i.val, hi⟩ else filler

end FieldGraphSeparation
end MetricEntropyDuality

end

end OAI


