-- Prove2me | Definitions.Def_CountingMatroid_Analysis_DefectSlotConservation
-- name    : CountingMatroid_Analysis_DefectSlotConservation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:27:04.174498+00:00
-- url     : https://prove2.me/theorems/40286dce-c147-4913-b6a4-5fd297d46576
-- title:
--   Conservation contract for binary slot completions
-- statement:
--   Fix $n,r\in\mathbb N$, independence oracles $o_1,o_2$, and $q\in\mathbb Q$. A node consists of paired-label sets $B,R$ and a set $U\subseteq[n]$ of unprocessed pairs. For a displayed hole $i$, let $s_i$ be the sum of operational weights $q^{\,n-\operatorname{pairedRank}(S)}$ over distinct states
--   $$S=B\cup(R\setminus\{i\})\cup\{(v,\beta(v)):v\in U\},\qquad \beta:[n]\to\{0,1\}.$$
--   For a branching pair $t$, write $a=(t,0)$, $b=(t,1)$, $R_a=R\cup\{a\}$, $R_b=R\cup\{b\}$, and $U'=U\setminus\{t\}$. Superscripts $a,b$ denote the corresponding child totals. The proposition $\operatorname{SlotConservationControl}$ packages four universally quantified identities.
--
--   First, if $t\in U$ and neither label at $t$ lies in $B$ or $R$, then
--   $$s_i^a+s_i^b=s_i\qquad(i\in R).$$
--   Second, merely assuming $a,b\notin R$, it requires $s_a^a=s_b^b$.
--
--   For a further pair $v$, let $V_v(i,j)$ be the zero-diagonal matrix whose off-diagonal entry sums operational weights of completions with holes $i,j$ removed, both labels at $v$ inserted, and one chosen label at each pair of $U\setminus\{v\}$. Put $Q_v(h)=\sum_{i,j\in R}V_v(i,j)h_i h_j$, with analogous child forms. If $t\in U$, $t\ne v$, both labels at $t$ are absent from $B,R$, and real functions $h^a,h^b$ agree with $h$ on $R$ and satisfy $h_a^a+h_b^b=0$, the third identity is
--   $$Q_v^a(h^a)+Q_v^b(h^b)=Q_v(h).$$
--   Finally, under the same freedom condition on $t\in U$, for arbitrary real functions $W,h,h^a,h^b$ with both child functions agreeing with $h$ on $R$ and $W_a=W_b$, the potential identity is
--   $$\sum_{i\in R_a}\frac{s_i^a(h_i^a)^2}{W_i}
--   +\sum_{i\in R_b}\frac{s_i^b(h_i^b)^2}{W_i}
--   =\sum_{i\in R}\frac{s_i h_i^2}{W_i}
--   +\frac{u(h_a^a)^2+u(h_b^b)^2}{W_a},\qquad u=s_a^a.$$
--   This last field assumes neither positivity of $W$ nor a balance condition on the two new function values. Field division is total, and the structure itself supplies a contract rather than a proof of its inhabitation.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/DefectSlotConservation.lean#L377-L415

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
Binary completion identities used by the balanced-hole recursion. Processing
one ordinary pair partitions each old-hole completion into its two children.
The corresponding future-slot matrix identities give conservation of the
future quadratic forms; these identities use finite sets, not a signature
assumption.
-/

namespace CountingMatroid.Analysis.DefectSlotConservation

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.DefectSlotSplitSignature
open scoped BigOperators

























/-- INTERNAL: The operational identities consumed together by the
recursive demand construction, separated from the Hessian split bound.
TEXLINE: main.tex:535-567,628-641 -/
structure SlotConservationControl (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) : Prop where
  old_hole : ∀ (B R : PairedSet n) (U : Finset (Fin n))
    (t : Fin n), t ∈ U →
    (∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ R) →
    ∀ hole ∈ R,
      slotTotal r o₁ o₂ q B (insert (t, false) R) (U.erase t) hole +
        slotTotal r o₁ o₂ q B (insert (t, true) R) (U.erase t) hole =
          slotTotal r o₁ o₂ q B R U hole
  new_hole : ∀ (B R : PairedSet n) (U : Finset (Fin n)) (t : Fin n),
    (∀ c : Bool, (t, c) ∉ R) →
    slotTotal r o₁ o₂ q B (insert (t, false) R) (U.erase t) (t, false) =
      slotTotal r o₁ o₂ q B (insert (t, true) R) (U.erase t) (t, true)
  future_form : ∀ (B R : PairedSet n) (U : Finset (Fin n))
    (t s : Fin n), t ∈ U → t ≠ s →
    (∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ R) →
    ∀ h hₐ hᵦ : PairedGround n → ℝ,
    (∀ i ∈ R, hₐ i = h i) → (∀ i ∈ R, hᵦ i = h i) →
    hₐ (t, false) + hᵦ (t, true) = 0 →
    (∑ i ∈ insert (t, false) R, ∑ j ∈ insert (t, false) R,
      futureMatrix r o₁ o₂ q B (insert (t, false) R) (U.erase t) s i j * hₐ i * hₐ j) +
    (∑ i ∈ insert (t, true) R, ∑ j ∈ insert (t, true) R,
      futureMatrix r o₁ o₂ q B (insert (t, true) R) (U.erase t) s i j * hᵦ i * hᵦ j) =
    ∑ i ∈ R, ∑ j ∈ R, futureMatrix r o₁ o₂ q B R U s i j * h i * h j
  potential : ∀ (B R : PairedSet n) (U : Finset (Fin n)) (t : Fin n), t ∈ U →
    (∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ R) →
    ∀ W h hₐ hᵦ : PairedGround n → ℝ,
    (∀ i ∈ R, hₐ i = h i) → (∀ i ∈ R, hᵦ i = h i) →
    W (t, false) = W (t, true) →
    let sₐ := slotTotal r o₁ o₂ q B (insert (t, false) R) (U.erase t)
    let sᵦ := slotTotal r o₁ o₂ q B (insert (t, true) R) (U.erase t)
    let u := sₐ (t, false)
    (∑ i ∈ insert (t, false) R, sₐ i * hₐ i ^ 2 / W i) +
      (∑ i ∈ insert (t, true) R, sᵦ i * hᵦ i ^ 2 / W i) =
    (∑ i ∈ R, slotTotal r o₁ o₂ q B R U i * h i ^ 2 / W i) +
      (u * hₐ (t, false) ^ 2 + u * hᵦ (t, true) ^ 2) / W (t, false)



end CountingMatroid.Analysis.DefectSlotConservation

end


