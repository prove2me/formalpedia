-- Prove2me | Definitions.Def_CountingMatroid_Analysis_DefectSlotSplitSignature
-- name    : CountingMatroid_Analysis_DefectSlotSplitSignature
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:25:47.308113+00:00
-- url     : https://prove2.me/theorems/2e79d46f-adcf-4561-9bd2-0f9f2307fe66
-- title:
--   Slot completions and the split-control inequality
-- statement:
--   Let $E=\{0,\ldots,n-1\}\times\{0,1\}$, let $B,R\subseteq E$, let $U$ be a set of pair indices, and let $i\in E$. A slot completion is any distinct subset
--   $$
--   S=B\cup(R\setminus\{i\})\cup\{(t,c(t)):t\in U\}
--   $$
--   for a Boolean choice function $c$. Fix a natural rank parameter $r$, arbitrary Boolean subset oracles $o_1,o_2$, and $q\in\mathbb Q$. Its slot total $s_i(B,R,U)$ is the sum of weights $q^{n-\operatorname{pairedRank}(S)}$ over all such states, cast to $\mathbb R$, with natural-number exponent subtraction.
--
--   For a pair index $t$, the matrix $M_t(i,j)$ has zero diagonal. When $i\ne j$, it sums the same weights over distinct states
--   $$
--   B\cup(R\setminus\{i,j\})\cup\{(t,0),(t,1)\}
--    \cup\{(u,c(u)):u\in U\setminus\{t\}\}.
--   $$
--   The predicate $\operatorname{SlotSplitControl}$ requires the following inequality for every configuration with $B\cap R=\varnothing$, both labels of each pair in $U$ absent from $B\cup R$, and $|B|+|R|+|U|=n+1$. For every $t\in U$ and function $h:E\to\mathbb R$, set
--   $$
--   s_0(i)=s_i(B,R\cup\{(t,0)\},U\setminus\{t\}),\quad
--   s_1(i)=s_i(B,R\cup\{(t,1)\},U\setminus\{t\}),\quad
--   u=s_0(t,0).
--   $$
--   If $\sum_{i\in R}(s_0(i)+s_1(i))h(i)=0$, it requires
--   $$
--   \frac{2\bigl(\sum_{i\in R}s_0(i)h(i)\bigr)^2}{u}
--   \le-\sum_{i,j\in R}M_t(i,j)h(i)h(j).
--   $$
--   The definition imposes no additional positivity assumption on $q$ or $u$; division is totalized.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/DefectSlotSplitSignature.lean#L30-L36

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
The omitted-element quadratic input to the recursive slot transport. The
slot totals and old-hole matrix below follow main.tex:516-601. The numerical
split estimate and the real signature-to-orthogonal-nonpositivity implication
are proved. The explicit block matrix is assembled on the old holes and two
new coordinates. The dual-matroid omitted-label extraction is constructed;
its descendant, homogeneous degree, and exact normalization to the operational
omitted-rank polynomial are proved. The surviving omitted-label patterns
are identified exactly with the operational completion totals in all four
Hessian blocks, including the zero diagonals. The imported rank-weight
signature theorem and the proved block-form calculation give nonpositivity
on the balanced hyperplane and hence the recursive split bound.
-/

namespace CountingMatroid.Analysis.DefectSlotSplitSignature

open CountingMatroid.Model CountingMatroid.Program
open scoped BigOperators
open Classical

/-- INTERNAL: A completion of fixed selected labels and displayed holes,
with one chosen label in each remaining original pair.
TEXLINE: main.tex:516-543 -/
def SlotCompletion {n : ℕ} (B R : PairedSet n) (U : Finset (Fin n))
    (hole : PairedGround n) (state : PairedSet n) : Prop :=
  ∃ choices : Fin n → Bool,
    state = B ∪ R.erase hole ∪ U.image (fun t => (t, choices t))

/-- PAPER: main.tex:522-526
The unmultiplied weight total for a displayed hole at a recursion node. -/
noncomputable def slotTotal {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B R : PairedSet n) (U : Finset (Fin n)) (hole : PairedGround n) : ℝ :=
  ∑ state : PairedSet n, if SlotCompletion B R U hole state then
    (q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val) : ℚ)
  else 0







/-- PAPER: main.tex:571-579
The old-hole quadratic matrix: two distinct displayed holes are omitted,
the next pair is doubled, and all other remaining pairs are singly occupied.
Its diagonal is zero. -/
noncomputable def futureMatrix {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B R : PairedSet n) (U : Finset (Fin n)) (t : Fin n)
    (i j : PairedGround n) : ℝ :=
  if i = j then 0 else
    ∑ state : PairedSet n,
      if (∃ choices : Fin n → Bool,
        state = B ∪ (R.erase i).erase j ∪ {(t, false), (t, true)} ∪
          (U.erase t).image (fun s => (s, choices s))) then
        (q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val) : ℚ)
      else 0





/-- INTERNAL: The split-control invariant consumed by the flow recursion.
All slot configurations retain their disjointness and size hypotheses.
TEXLINE: main.tex:531-625 -/
def SlotSplitControl (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (q : ℚ) : Prop :=
  ∀ (B R : PairedSet n) (U : Finset (Fin n)),
    Disjoint B R →
    (∀ t ∈ U, ∀ b : Bool, (t, b) ∉ B ∧ (t, b) ∉ R) →
    B.card + R.card + U.card = n + 1 →
    ∀ t ∈ U, ∀ h : PairedGround n → ℝ,
    let sₐ := fun i => slotTotal r o₁ o₂ q B (insert (t, false) R) (U.erase t) i
    let sᵦ := fun i => slotTotal r o₁ o₂ q B (insert (t, true) R) (U.erase t) i
    let u := slotTotal r o₁ o₂ q B (insert (t, false) R) (U.erase t) (t, false)
    (∑ i ∈ R, (sₐ i + sᵦ i) * h i) = 0 →
    2 * (∑ i ∈ R, sₐ i * h i) ^ 2 / u ≤
      -(∑ i ∈ R, ∑ j ∈ R, futureMatrix r o₁ o₂ q B R U t i j * h i * h j)



end CountingMatroid.Analysis.DefectSlotSplitSignature

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · closed slot_split_signature using the proved two-active-omission completion characterization; identified all four operational Hessian blocks and impossible diagonal patterns, retaining the existing signature and split-control proofs.
* 2026-10-09 · partial, dependency blocked · proved exact dual-Tutte normalization, paired rank n, complement dual-rank identity, extraction multiplicities, and the finite-state omitted-slot coefficient formula in two new support modules; the parent uses both and still needs omission-pattern/completion equivalence. Both targeted builds and the parent elaboration passed before a concurrent RankWeightQuadraticSignature edit removed its object and failed a later permitted rebuild at List.length_eq_zero.mp.
* 2026-10-09 · partial · proved the real signature-to-orthogonal-nonpositivity step and exact block-vector expansion in two support modules; the original open theorem now has only the explicit operational block-matrix sigPos bound open. Its all-slot omitted-polynomial descendant and coefficient extraction remain unavailable; no new open declaration or Prior assumption was introduced.
-/

end


