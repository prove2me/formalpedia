-- Prove2me | Definitions.Def_CountingMatroid_Analysis_SlotDemandRecursion
-- name    : CountingMatroid_Analysis_SlotDemandRecursion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:29:04.118052+00:00
-- url     : https://prove2.me/theorems/5156fc51-46a1-47f8-aaef-30fc61dd9c02
-- title:
--   Balanced demands and the slot-recursion interface
-- statement:
--   Let $E=\{0,\ldots,n-1\}\times\{0,1\}$, fix Boolean subset oracles $o_1,o_2$, a natural rank parameter $r$, a rational activity $q$, fixed labels $B\subseteq E$, and remaining pair indices $U$. A demand node is a pair $N=(R,h)$ with displayed holes $R\subseteq E$ and coefficients $h:E\to\mathbb R$. Write $s_i(B,R,U)$ for the slot-completion weight total, using weight $q^{n-\mathrm{pairedRank}(S)}$ on each distinct completed state $S$. A node is balanced when
--   $$
--   \sum_{i\in R}s_i(B,R,U)h(i)=0.
--   $$
--   Splitting pair $t$ with choice $c\in\{0,1\}$ replaces $R$ by $R'=R\cup\{(t,c)\}$ and $U$ by $U'=U\setminus\{t\}$, updates only the coefficient at $(t,c)$ to
--   $$
--   h'(t,c)=-\frac{\sum_{i\in R}s_i(B,R',U')h(i)}
--   {s_{(t,c)}(B,R',U')},
--   $$
--   and leaves every other coefficient unchanged. Recursing along a list of pairs concatenates the false-child and true-child leaf lists. Division is totalized, so these formulas are defined even at zero denominators.
--
--   For multipliers $W:E\to\mathbb R$, the node potential and its future term at pair $t$ are
--   $$
--   \Phi_W(N;B,U)=\sum_{i\in R}\frac{s_i(B,R,U)h(i)^2}{W(i)},
--   \qquad
--   F_t(N;B,U)=\sum_{i,j\in R}M_t(i,j)h(i)h(j),
--   $$
--   where $M_t$ is the slot future matrix. The two-hole root has $R=\{p,d\}$ and coefficients $1/s_p$ at $p$, $-1/s_d$ at $d$, and zero elsewhere, with the $p$ branch taking priority if the labels coincide.
--
--   The proposition $\operatorname{DemandRecursionControl}$ requires every root with $p\ne d$ to be balanced. It also requires a nonempty list of balanced terminal nodes preserving all initial hole coefficients and satisfying
--   $$
--   \sum_{\ell}\Phi_W(N_\ell;B,\varnothing)
--   \le\Phi_W(N;B,U)-\sum_{t\in U}\frac{F_t(N;B,U)}{W(t,0)}.
--   $$
--   This second requirement is quantified over a duplicate-free pair list with set $U$, disjoint $B,R$, both labels of every remaining pair absent from $B\cup R$, $|B|+|R|+|U|=n+1$, an initially balanced node, and multipliers satisfying $W(t,0)=W(t,1)>0$ for $t\in U$. The interface asserts existence of such leaves; it does not identify its witness list with the recursively defined list.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/SlotDemandRecursion.lean#L18-L23

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectCoefficients
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectExtractionCoefficients
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectQuadratics
import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionQuadraticConstruction
import Definitions.Def_CountingMatroid_Analysis_DefectSlotConservation
import Definitions.Def_CountingMatroid_Analysis_DefectSlotSplitSignature
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_OmittedRankWeightPolynomial
import Definitions.Def_CountingMatroid_Analysis_OmittedSlotCoefficientFormula
import Definitions.Def_CountingMatroid_Analysis_OmittedSlotQuadratic
import Definitions.Def_CountingMatroid_Analysis_OmittedTutteNormalization
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightQuadraticSignature
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_SlotBlockSignature
import Definitions.Def_CountingMatroid_Analysis_SquarefreeCoordinateHessian
import Definitions.Def_CountingMatroid_Analysis_ThreePairSignatureSchur
import Definitions.Def_CountingMatroid_Analysis_TransversalPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalProjection
import Definitions.Def_CountingMatroid_Interface_Pseudocode
import Definitions.Def_CountingMatroid_Interface_Pseudocode_Extension1
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Combinatorics.Matroid.Sum
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finsupp.Indicator
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas

namespace CountingMatroid.Analysis.SlotOmissionPatternCharacterization
end CountingMatroid.Analysis.SlotOmissionPatternCharacterization
namespace CountingMatroid.Analysis.TwoLabelDerivativeNilpotence
end CountingMatroid.Analysis.TwoLabelDerivativeNilpotence
namespace CountingMatroid.Analysis.MixedDirectionalRankWeightSignature
end CountingMatroid.Analysis.MixedDirectionalRankWeightSignature
namespace CountingMatroid.Analysis.RankWeightCoordinateLorentzian
end CountingMatroid.Analysis.RankWeightCoordinateLorentzian
namespace CountingMatroid.Analysis.RankWeightCoordinateSignature
end CountingMatroid.Analysis.RankWeightCoordinateSignature
namespace CountingMatroid.Analysis.RankWeightResidualSignature
end CountingMatroid.Analysis.RankWeightResidualSignature
namespace CountingMatroid.Analysis.RankWeightClosurePair
end CountingMatroid.Analysis.RankWeightClosurePair
namespace CountingMatroid.Analysis.ClosureClassQuadraticBound
end CountingMatroid.Analysis.ClosureClassQuadraticBound
namespace CountingMatroid.Analysis.SquarefreeFullDerivative
end CountingMatroid.Analysis.SquarefreeFullDerivative
namespace CountingMatroid.Analysis.BinaryRankWeightSignature
end CountingMatroid.Analysis.BinaryRankWeightSignature
namespace CountingMatroid.Analysis.CubicDirectionalSignature
end CountingMatroid.Analysis.CubicDirectionalSignature
namespace CountingMatroid.Analysis.CubicTensorRayleighContraction
end CountingMatroid.Analysis.CubicTensorRayleighContraction
namespace CountingMatroid.Analysis.NonnegativeContractionLimit
end CountingMatroid.Analysis.NonnegativeContractionLimit
namespace CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
end CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
namespace CountingMatroid.Analysis.ConnectedRayleighHyperplane
end CountingMatroid.Analysis.ConnectedRayleighHyperplane
namespace CountingMatroid.Analysis.ConnectedNormalizedRayleigh
end CountingMatroid.Analysis.ConnectedNormalizedRayleigh
namespace CountingMatroid.Analysis.ConnectedLaplacianKernel
end CountingMatroid.Analysis.ConnectedLaplacianKernel
namespace CountingMatroid.Analysis.RayleighFixedKernel
end CountingMatroid.Analysis.RayleighFixedKernel
namespace CountingMatroid.Analysis.QuadraticSignatureHyperplane
end CountingMatroid.Analysis.QuadraticSignatureHyperplane
namespace CountingMatroid.Analysis.CubicExchangeCut
end CountingMatroid.Analysis.CubicExchangeCut
namespace CountingMatroid.Analysis.CubicThirdDerivativeSupport
end CountingMatroid.Analysis.CubicThirdDerivativeSupport
namespace CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
end CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
namespace CountingMatroid.Analysis.LinearSubstitutionHessian
end CountingMatroid.Analysis.LinearSubstitutionHessian
namespace CountingMatroid.Analysis.LinearPolynomialChainRule
end CountingMatroid.Analysis.LinearPolynomialChainRule
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
namespace Arlib
end Arlib
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.PairedRankValue
end CountingMatroid.Analysis.PairedRankValue
namespace CountingMatroid.Analysis.SignatureOrthogonalNonpositive
end CountingMatroid.Analysis.SignatureOrthogonalNonpositive
section


set_option autoImplicit false

/-!
Demand nodes and the binary recursion from the transport proof. Splitting a
node keeps old-hole values and assigns the new hole the value that balances
its child. The recursion records all leaves in processing order.
-/

namespace CountingMatroid.Analysis.SlotDemandRecursion

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.DefectSlotSplitSignature
open scoped BigOperators

/-- INTERNAL: The displayed holes and their demand per unit weight at a
node of the analytical recursion.
TEXLINE: main.tex:516-530 -/
structure DemandNode (n : ℕ) where
  holes : PairedSet n
  values : PairedGround n → ℝ

/-- PAPER: main.tex:543-553
Keep every old-hole value and give the new hole the unique balancing value. -/
noncomputable def splitNode {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (U : Finset (Fin n))
    (node : DemandNode n) (t : Fin n) (c : Bool) : DemandNode n := by
  classical
  let R := insert (t, c) node.holes
  let s := slotTotal r o₁ o₂ q B R (U.erase t)
  exact ⟨R, Function.update node.values (t, c)
    (-(∑ i ∈ node.holes, s i * node.values i) / s (t, c))⟩

/-- INTERNAL: Demand balance is expressed using the completion totals at
the current node, before any further pair is processed.
TEXLINE: main.tex:528-530 -/
def Balanced {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (U : Finset (Fin n)) (node : DemandNode n) : Prop :=
  (∑ i ∈ node.holes, slotTotal r o₁ o₂ q B node.holes U i * node.values i) = 0





/-- PAPER: main.tex:516-520,642-665
Process the ordinary pairs in order and retain the displayed holes and
balanced demands at all terminal nodes. -/
noncomputable def leafNodes {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) : List (Fin n) → DemandNode n → List (DemandNode n)
  | [], node => [node]
  | t :: slots, node =>
    leafNodes r o₁ o₂ q B slots
      (splitNode r o₁ o₂ q B (t :: slots).toFinset node t false) ++
    leafNodes r o₁ o₂ q B slots
      (splitNode r o₁ o₂ q B (t :: slots).toFinset node t true)











/-- PAPER: main.tex:555-560
Potential of one demand node, with the current completion totals and the
multiplier of each displayed hole. -/
noncomputable def nodePotential {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (U : Finset (Fin n))
    (W : PairedGround n → ℝ) (node : DemandNode n) : ℝ :=
  ∑ i ∈ node.holes, slotTotal r o₁ o₂ q B node.holes U i * node.values i ^ 2 / W i

/-- INTERNAL: The future quadratic evaluated at a demand node.
TEXLINE: main.tex:628-641 -/
noncomputable def nodeFuture {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (U : Finset (Fin n))
    (node : DemandNode n) (s : Fin n) : ℝ :=
  ∑ i ∈ node.holes, ∑ j ∈ node.holes,
    futureMatrix r o₁ o₂ q B node.holes U s i j * node.values i * node.values j







/-- PAPER: main.tex:531
Initialize the two root holes with opposite unit total demands. -/
noncomputable def twoHoleRoot {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (U : Finset (Fin n))
    (p d : PairedGround n) : DemandNode n := by
  classical
  let R : PairedSet n := {p, d}
  let s := slotTotal r o₁ o₂ q B R U
  exact ⟨R, fun i => if i = p then 1 / s p else if i = d then -1 / s d else 0⟩



/-- INTERNAL: The proved demand-tree interface needed by leaf-flow
assembly, including balance, persistent root values, and the total cost.
TEXLINE: main.tex:516-665 -/
structure DemandRecursionControl (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) : Prop where
  root_balanced : ∀ (B : PairedSet n) (U : Finset (Fin n))
    (p d : PairedGround n), p ≠ d →
    CountingMatroid.Analysis.SlotDemandRecursion.Balanced r o₁ o₂ q B U (twoHoleRoot r o₁ o₂ q B U p d)
  tree : ∀ (B : PairedSet n) (slots : List (Fin n)), slots.Nodup →
    ∀ node : DemandNode n, Disjoint B node.holes →
    (∀ s ∈ slots, ∀ c : Bool, (s, c) ∉ B ∧ (s, c) ∉ node.holes) →
    B.card + node.holes.card + slots.toFinset.card = n + 1 →
    CountingMatroid.Analysis.SlotDemandRecursion.Balanced r o₁ o₂ q B slots.toFinset node →
    ∀ W : PairedGround n → ℝ,
    (∀ s ∈ slots, W (s, false) = W (s, true) ∧ 0 < W (s, false)) →
    ∃ leaves : List (DemandNode n),
      (∃ leaf, leaf ∈ leaves) ∧
      (∀ leaf ∈ leaves, CountingMatroid.Analysis.SlotDemandRecursion.Balanced r o₁ o₂ q B ∅ leaf) ∧
      (∀ leaf ∈ leaves, ∀ i ∈ node.holes,
        i ∈ leaf.holes ∧ leaf.values i = node.values i) ∧
      (leaves.map (nodePotential r o₁ o₂ q B ∅ W)).sum ≤
        nodePotential r o₁ o₂ q B slots.toFinset W node -
          ∑ s ∈ slots.toFinset,
            nodeFuture r o₁ o₂ q B slots.toFinset node s / W (s, false)



end CountingMatroid.Analysis.SlotDemandRecursion

end


