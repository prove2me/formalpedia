-- Prove2me | Definitions.Def_OAI_Analysis_MetricEntropy_WeightRounding
-- name    : OAI_Analysis_MetricEntropy_WeightRounding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T22:02:58.73441+00:00
-- url     : https://prove2.me/theorems/cc5c3e3d-b848-4830-be23-341b543746b6
-- title:
--   Rounding weights down to a mesh
-- statement:
--   These notions belong to a counterexample to the duality conjecture for metric entropy. For every $a,b\ge1$ there are $n$ and a symmetric convex body $K\subset\mathbb R^n$ with $\log N(K,Q_n)>b\log N(Q_n^\circ,a^{-1}K^\circ)$. Here $Q_n=[-1,1]^n$ is the cube, $K^\circ=\{y:\langle x,y\rangle\le1\text{ for all }x\in K\}$ is the polar (so $Q_n^\circ$ is the $\ell_1$ ball), and $N(A,B)$ is the least number of translates of $B$ covering $A$. Fix a mesh $\delta>0$.
--
--   1. **Rounding.** A weight $w\in[0,1]$ is rounded down to
--   $$
--   \mathrm{round}_\delta(w)=\delta\lfloor w/\delta\rfloor .
--   $$
--   2. **Codes.** Its integer coefficient $\lfloor w/\delta\rfloor$ lies in $\{0,\dots,\lfloor1/\delta\rfloor\}$, a code set of size $\lfloor1/\delta\rfloor+1$. A code $c$ decodes to $\delta c$.
--   3. **Level mesh.** For accuracy $\theta$, $s$ pivot slots and $u$ directions, the mesh used is $\theta/(s\,2^u)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/WeightRounding.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/WeightRounding.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteFieldRows
import Definitions.Def_OAI_Analysis_MetricEntropy_GreedyPivots
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionLevels
import Definitions.Def_OAI_Analysis_MetricEntropy_ProfileMixtures
import Definitions.Def_OAI_Analysis_MetricEntropy_LabelEncoding
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionCode

namespace OAI

universe uI

/-!
# Finite codes for downward rounding of grouped weights

For a positive mesh `δ`, a weight in `[0, 1]` is rounded down to
`δ * floor (w / δ)`. Its integer coefficient is an actual element of
`Fin (floor (1 / δ) + 1)`, including the possible endpoint `w = 1`.
The error estimates apply to every indicator with values in `[0, 1]`.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators

/-- The number of possible rounded values of a weight in `[0, 1]`. -/
def weightCodeSize (δ : ℝ) : ℕ := Nat.floor (1 / δ) + 1

/-- Downward rounding to the mesh `δ`. -/
def roundWeight (δ w : ℝ) : ℝ := δ * (Nat.floor (w / δ) : ℝ)

/-- Decode an integer weight code using the fixed mesh. -/
def decodeWeight (δ : ℝ) (c : Fin (weightCodeSize δ)) : ℝ := δ * (c.val : ℝ)

/-- The integer coefficient of every rounded weight is within the finite code
range. The positivity and interval hypotheses are explicit. -/
def weightCode (δ w : ℝ) (hδ : 0 < δ) (_hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    Fin (weightCodeSize δ) :=
  ⟨Nat.floor (w / δ), Nat.lt_succ_of_le
    (Nat.floor_mono ((div_le_div_iff_of_pos_right hδ).2 hw1))⟩

@[simp] theorem weightCode_val (δ w : ℝ) (hδ : 0 < δ) (hw0 : 0 ≤ w)
    (hw1 : w ≤ 1) :
    (weightCode δ w hδ hw0 hw1).val = Nat.floor (w / δ) := rfl

@[simp] theorem decodeWeight_weightCode (δ w : ℝ) (hδ : 0 < δ) (hw0 : 0 ≤ w)
    (hw1 : w ≤ 1) :
    decodeWeight δ (weightCode δ w hδ hw0 hw1) = roundWeight δ w := rfl

@[simp] theorem roundWeight_zero (δ : ℝ) : roundWeight δ 0 = 0 := by
  simp [roundWeight]

/-- The mesh used for one level of the partition compression. -/
def roundingStep (θ : ℝ) (s u : ℕ) : ℝ := θ / ((s : ℝ) * 2 ^ u)

end MetricEntropyDuality

end

end OAI


