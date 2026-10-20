-- Prove2me | Definitions.Def_OAI_Analysis_MetricEntropy_Parameters
-- name    : OAI_Analysis_MetricEntropy_Parameters
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:35:48.294679+00:00
-- url     : https://prove2.me/theorems/bc37fafe-5e36-483e-a935-125f790742c6
-- title:
--   Numerical parameters of the entropy-duality construction
-- statement:
--   These notions belong to a counterexample to the duality conjecture for metric entropy. For every $a,b\ge1$ there are $n$ and a symmetric convex body $K\subset\mathbb R^n$ with $\log N(K,Q_n)>b\log N(Q_n^\circ,a^{-1}K^\circ)$. Here $Q_n=[-1,1]^n$ is the cube, $K^\circ=\{y:\langle x,y\rangle\le1\text{ for all }x\in K\}$ is the polar (so $Q_n^\circ$ is the $\ell_1$ ball), and $N(A,B)$ is the least number of translates of $B$ covering $A$. All parameters below are fixed by the proposed constant $a\ge1$ and the rank $r$, before the prime $p$ is chosen.
--
--   1. **Accuracy.** $\theta(a)=\dfrac1{1000a}$.
--   2. **Pivot slots.** $s(\theta)=\lceil1/\theta\rceil$.
--   3. **Compression radius.** $h(a)=\lceil\exp(\log3/\theta(a))\rceil+1$, so that $\log3/\log(h+1)\le\theta$.
--   4. **Direction count.** $u(r,h,\theta)=\lceil 2h\,D(r,h)/\theta\rceil$, with $D(r,h)=\binom{r+h-1}{h}$.
--   5. **Encoding cost.**
--   $$
--   C(h,\theta,u)=\log u+h\,s(\theta)\,2^u\log\Bigl(1+\frac{s(\theta)\,2^u}{\theta}\Bigr),
--   $$
--   the part of the logarithm of the compression count that does not involve $p$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/Parameters.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/Parameters.lean by skeleton subtraction
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

namespace OAI

/-!
# Parameters fixed before the prime is chosen

These are the literal accuracy, pivot-slot, direction-count and encoding-cost
parameters of the construction. The radius and rank are genuinely available
for every proposed comparison constant. Their existence does not depend on
the eventual field size.
-/

noncomputable section

namespace MetricEntropyDuality

def accuracy (a : ℝ) : ℝ := 1 / (1000 * a)

def pivotSlots (θ : ℝ) : ℕ := Nat.ceil (1 / θ)

/-- A fixed positive radius satisfying the logarithmic compression condition. -/
def compressionRadius (a : ℝ) : ℕ :=
  Nat.ceil (Real.exp (Real.log 3 / accuracy a)) + 1

def directionCount (r h : ℕ) (θ : ℝ) : ℕ :=
  Nat.ceil ((h : ℝ) * (2 * (formDimension r h : ℝ)) / θ)

def encodingCost (h : ℕ) (θ : ℝ) (u : ℕ) : ℝ :=
  Real.log (u : ℝ) + (h : ℝ) * (pivotSlots θ : ℝ) * (2 : ℝ) ^ u *
    Real.log (1 + (pivotSlots θ : ℝ) * (2 : ℝ) ^ u / θ)

end MetricEntropyDuality

end

end OAI


