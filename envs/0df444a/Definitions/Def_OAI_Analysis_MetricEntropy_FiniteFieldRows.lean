-- Prove2me | Definitions.Def_OAI_Analysis_MetricEntropy_FiniteFieldRows
-- name    : OAI_Analysis_MetricEntropy_FiniteFieldRows
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:55:28.523059+00:00
-- url     : https://prove2.me/theorems/e79e1940-3618-4098-a073-e5f8a81d07b4
-- title:
--   The finite-field graph matrix of symmetric forms
-- statement:
--   These notions belong to a counterexample to the duality conjecture for metric entropy. For every $a,b\ge1$ there are $n$ and a symmetric convex body $K\subset\mathbb R^n$ with $\log N(K,Q_n)>b\log N(Q_n^\circ,a^{-1}K^\circ)$. Here $Q_n=[-1,1]^n$ is the cube, $K^\circ=\{y:\langle x,y\rangle\le1\text{ for all }x\in K\}$ is the polar (so $Q_n^\circ$ is the $\ell_1$ ball), and $N(A,B)$ is the least number of translates of $B$ covering $A$. In the construction the rows are the symmetric $h$-linear forms on $\mathbb F_p^r$. Their coefficients are indexed by multisets of size $h$, so there are $p^D$ of them with $D=\binom{r+h-1}{h}$. They are labelled by their contractions $F\mapsto F(t_i,\cdot,\dots,\cdot)$ along directions $t_1,\dots,t_u\in\mathbb F_p^r$. For a set $T$ of direction indices, two forms are adjacent in the partition graph when they have the same contraction along some $t_i$ with $i\in T$, and $d_T$ is the graph distance (infinite between components). The matrix column $(v,T)$ is $x\mapsto\varphi_h(d_T(x,v))$ with the logarithmic profile $\varphi_h(d)=\max\bigl(0,1-\log(d+1)/\log(h+1)\bigr)$ and $\varphi_h(\infty)=0$.
--
--   1. **Admissible sets.** For $\theta>0$ and $u$ directions, $T\subseteq\{1..u\}$ is admissible if $|\{1..u\}\setminus T|\le\theta u$.
--   2. **Rows and columns.** Rows are the symmetric $h$-linear forms over $\mathbb F_p$ in $r$ variables. Columns are pairs $(v,T)$ of a form and an admissible set.
--   3. **Labels.** For directions $t_1,\dots,t_u\in\mathbb F_p^r$, the $i$-th label of $F$ is the contraction $F(t_i,\cdot,\dots,\cdot)$.
--   4. **Matrix.**
--   $$
--   g\bigl((v,T),F\bigr)=\varphi_h\bigl(d_T(F,v)\bigr),
--   $$
--   the graph-profile matrix for these labels and all admissible sets.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/FiniteFieldRows.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/FiniteFieldRows.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_MetricEntropy_FieldGraphSeparation
import Definitions.Def_OAI_Analysis_MetricEntropy_LogProfile
import Definitions.Def_OAI_Analysis_MetricEntropy_GraphProfile

namespace OAI

/-!
# The finite-field graph matrix

The rows are literal symmetric forms, the labels are their actual contractions,
and every admissible set is included as a column index. The only input to the
separation theorem is the repeated-tuple nonvanishing conclusion constructed
by the robust-directions argument; graph separation is proved from it.
-/

noncomputable section

namespace MetricEntropyDuality.FiniteFieldRows

/-- All admissible subsets are fixed before a pair of rows is chosen. -/
def admissibleSets (θ : ℝ) (u : ℕ) : Finset (Finset (Fin u)) := by
  classical
  exact Finset.univ.filter (fun T => ((Finset.univ \ T).card : ℝ) ≤ θ * (u : ℝ))

@[simp] theorem mem_admissibleSets {θ : ℝ} {u : ℕ} {T : Finset (Fin u)} :
    T ∈ admissibleSets θ u ↔ ((Finset.univ \ T).card : ℝ) ≤ θ * (u : ℝ) := by
  classical
  simp [admissibleSets]

abbrev RowIndex (p r h : ℕ) := SymmetricForm (ZMod p) r h

abbrev ColumnIndex (θ : ℝ) (p r h u : ℕ) :=
  GraphProfile.Columns (RowIndex p r h) (admissibleSets θ u)

/-- The literal contraction partition maps on forms of positive degree. -/
abbrev labels {p r j u : ℕ} (t : Fin u → (Fin r → ZMod p)) :=
  FieldGraphSeparation.labels (j := j) t

/-- The actual matrix, in the column-first convention of compression. -/
def column {p r j u : ℕ} (θ : ℝ) (t : Fin u → (Fin r → ZMod p)) :
    ColumnIndex θ p r (j + 1) u → RowIndex p r (j + 1) → ℝ :=
  GraphProfile.column (labels t) (admissibleSets θ u) (j + 1)

section Separation

variable {p r j u : ℕ} [NeZero p] {θ : ℝ}
variable (t : Fin u → (Fin r → ZMod p))
variable (hrobust : ∀ Z : SymmetricForm (ZMod p) r (j + 1), Z ≠ 0 →
  ∃ T : Finset (Fin u), ((Finset.univ \ T).card : ℝ) ≤ θ * (u : ℝ) ∧
    T.Nonempty ∧ ∀ a : Fin (j + 1) → Fin u, (∀ l, a l ∈ T) →
      Z.eval (fun l => t (a l)) ≠ 0)

include hrobust

end Separation
end MetricEntropyDuality.FiniteFieldRows

end

end OAI


