-- Prove2me | Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricIndex
-- name    : OAI_Analysis_MetricEntropy_SymmetricIndex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:36:18.018724+00:00
-- url     : https://prove2.me/theorems/331d303d-fd0c-495c-bcd9-0e9274ed363c
-- title:
--   Multiset index of a tuple of basis indices
-- statement:
--   These notions belong to a counterexample to the duality conjecture for metric entropy. For every $a,b\ge1$ there are $n$ and a symmetric convex body $K\subset\mathbb R^n$ with $\log N(K,Q_n)>b\log N(Q_n^\circ,a^{-1}K^\circ)$. Here $Q_n=[-1,1]^n$ is the cube, $K^\circ=\{y:\langle x,y\rangle\le1\text{ for all }x\in K\}$ is the polar (so $Q_n^\circ$ is the $\ell_1$ ball), and $N(A,B)$ is the least number of translates of $B$ covering $A$. In the construction the rows are the symmetric $h$-linear forms on $\mathbb F_p^r$. Their coefficients are indexed by multisets of size $h$, so there are $p^D$ of them with $D=\binom{r+h-1}{h}$. They are labelled by their contractions $F\mapsto F(t_i,\cdot,\dots,\cdot)$ along directions $t_1,\dots,t_u\in\mathbb F_p^r$.
--
--   1. **Symmetric index.** For a tuple $a=(a_1,\dots,a_j)$ of indices in $\{1,\dots,r\}$, $\mathrm{sym}(a)$ is the multiset $\{\!\{a_1,\dots,a_j\}\!\}$ of its entries, with repetitions kept. It is an element of the $j$-th symmetric power of $\{1,\dots,r\}$.
--   2. **Basic rules.** $\mathrm{sym}(c,a_1,\dots,a_j)$ is $\mathrm{sym}(a)$ with $c$ added, and
--   $$
--   \mathrm{sym}(a\circ\sigma)=\mathrm{sym}(a)
--   $$
--   for every permutation $\sigma$ of the slots.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/SymmetricIndex.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/SymmetricIndex.lean by skeleton subtraction
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

namespace OAI

/-!
# Symmetric indices of tuples

A tuple is sent to its literal multiset of entries. Repeated entries are retained.
Two tuples have the same index exactly when a permutation of their slots relates them.
-/

namespace MetricEntropyDuality

/-- The multiset of entries of a tuple, including every repetition. -/
def tupleSym {r j : ℕ} (a : Fin j → Fin r) : Sym (Fin r) j :=
  ⟨(List.ofFn a : Multiset (Fin r)), by simp⟩

@[simp]
theorem coe_tupleSym {r j : ℕ} (a : Fin j → Fin r) :
    (tupleSym a : Multiset (Fin r)) = (List.ofFn a : Multiset (Fin r)) := rfl

@[simp]
theorem tupleSym_cons {r j : ℕ} (a : Fin r) (args : Fin j → Fin r) :
    tupleSym (Fin.cons a args) = Sym.cons a (tupleSym args) := by
  apply Sym.ext
  simp only [coe_tupleSym, List.ofFn_cons, Sym.coe_cons, Multiset.cons_coe]

@[simp]
theorem tupleSym_comp_perm {r j : ℕ} (a : Fin j → Fin r)
    (σ : Equiv.Perm (Fin j)) : tupleSym (a ∘ σ) = tupleSym a := by
  apply Sym.ext
  exact Multiset.coe_eq_coe.mpr (σ.ofFn_comp_perm a)

end MetricEntropyDuality

end OAI


