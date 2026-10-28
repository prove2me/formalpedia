-- Prove2me | Definitions.Def_CountingMatroid_Analysis_OmittedSlotQuadratic
-- name    : CountingMatroid_Analysis_OmittedSlotQuadratic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:21:35.5389+00:00
-- url     : https://prove2.me/theorems/ddc20ed4-a8ac-49e4-93e7-12ca0f3fb9a8
-- title:
--   Omitted-label extraction of a slot polynomial
-- statement:
--   Let $E=\{0,\ldots,n-1\}\times\{0,1\}$, let $N$ be any matroid on $E$, let $q\in\mathbb Q$, let $B,R\subseteq E$, let $U$ be a set of pair indices, and let $t$ be a pair index. Define the fixed omitted labels by
--   $$
--   C=E\setminus\bigl(B\cup R\cup(U\times\{0,1\})\bigr).
--   $$
--   Starting with the homogenized Tutte polynomial $T_N(q;z_0,(x_e)_{e\in E})$, take $n$ derivatives in $z_0$ and then set $z_0=0$. Differentiate once in each label of $C$. The slot substitution keeps $x_e$ when $e\in R$ or $e$ belongs to pair $t$, replaces both labels of each other pair $s\in U\setminus\{t\}$ by $x_{(s,0)}$, and sends all remaining labels to zero. Write $\mathcal S$ for this substitution and $\mathcal E_e g=(\partial_{x_e}g)|_{x_e=0}$ for extraction of exponent exactly one. The resulting construction is
--   $$
--   Q=\frac{q^n}{n!}\,
--   \mathcal A\!\left[
--   \left(\prod_{s\in U\setminus\{t\}}\mathcal E_{(s,0)}\right)
--   \mathcal S\!\left[
--   \left(\prod_{e\in C}\partial_{x_e}\right)
--   \left.(\partial_{z_0}^{\,n}T_N)\right|_{z_0=0}
--   \right]\right].
--   $$
--   Here $\mathcal A$ uses separate variables indexed by $R$ and by $\{0,1\}$: $x_e$ maps to the sum of its matching $R$ variable, if any, and its matching pair-$t$ variable, if any. Thus overlapping labels contribute both variables. The operations use the source's finite-list order. The definition assumes neither disjointness nor positivity nor a degree condition; its name does not by itself establish that every such input produces a quadratic polynomial.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/OmittedSlotQuadratic.lean#L18-L21

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
import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionQuadraticConstruction
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightQuadraticSignature
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
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
import Mathlib.Algebra.MvPolynomial.PDeriv
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
section


set_option autoImplicit false

/-!
The derivative and substitution construction of the omitted-label quadratic
at a slot recursion node. Its descendant and degree properties concern a
matroid rank polynomial; they do not identify operational oracle weights.
-/

namespace CountingMatroid.Analysis.OmittedSlotQuadratic

open CountingMatroid.Model
open CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
open scoped BigOperators

/-- INTERNAL: Labels forced to be omitted at a slot node.
TEXLINE: main.tex:584-593 -/
noncomputable def fixedOmissions {n : ℕ} (B R : PairedSet n) (U : Finset (Fin n)) :
    PairedSet n := Finset.univ \ (B ∪ R ∪ U.product Finset.univ)

/-- INTERNAL: Delete the homogenizing variable, retaining omitted labels.
TEXLINE: main.tex:354-367 -/
noncomputable def omitHomogenizer {n : ℕ} :
    Option (PairedGround n) → PairedGround n → ℚ
  | none, _ => 0
  | some e, f => if e = f then 1 else 0

/-- INTERNAL: Differentiate in each fixed omitted label.
TEXLINE: main.tex:584-586 -/
noncomputable def differentiateLabels {n : ℕ} (C : PairedSet n)
    (g : MvPolynomial (PairedGround n) ℚ) : MvPolynomial (PairedGround n) ℚ :=
  C.toList.foldl (fun p e => MvPolynomial.pderiv e p) g

/-- INTERNAL: Delete fixed labels, and identify the two labels of each
ordinary slot except the next one, using its false label as representative.
TEXLINE: main.tex:586-589 -/
noncomputable def slotSubstitution {n : ℕ} (R : PairedSet n)
    (U : Finset (Fin n)) (t : Fin n) : PairedGround n → PairedGround n → ℚ :=
  fun e f => if e ∈ R ∨ e.1 = t then (if e = f then 1 else 0)
    else if e.1 ∈ U.erase t then (if (e.1, false) = f then 1 else 0) else 0

/-- INTERNAL: Extract exponent exactly one in an ordinary-slot variable.
TEXLINE: main.tex:369-373,587-589 -/
noncomputable def extractLabel {n : ℕ} (e : PairedGround n)
    (g : MvPolynomial (PairedGround n) ℚ) : MvPolynomial (PairedGround n) ℚ :=
  linearSubstitution (fun s f => if s = e then 0 else if s = f then 1 else 0)
    (MvPolynomial.pderiv e g)

/-- INTERNAL: Relabel the surviving variables by the old-hole subtype and
the two new labels.
TEXLINE: main.tex:592-601 -/
noncomputable def activeSubstitution {n : ℕ} (R : PairedSet n) (t : Fin n) :
    PairedGround n → (R ⊕ Bool) → ℚ
  | e, .inl i => if e = i then 1 else 0
  | e, .inr b => if e = (t, b) then 1 else 0

/-- INTERNAL: The actual omitted-label slot extraction, starting with the
homogenized Tutte polynomial of the dual paired matroid. The normalization
is the paper's q^n/n!.
TEXLINE: main.tex:354-367,584-601 -/
noncomputable def omittedSlotQuadratic {n : ℕ} (N : Matroid (PairedGround n))
    (q : ℚ) (B R : PairedSet n) (U : Finset (Fin n)) (t : Fin n) :
    MvPolynomial (R ⊕ Bool) ℚ := by
  classical
  let F := linearSubstitution omitHomogenizer
    ((MvPolynomial.pderiv none)^[n] (tuttePolynomial N q))
  let G := linearSubstitution (slotSubstitution R U t)
    (differentiateLabels (fixedOmissions B R U) F)
  let H := (U.erase t).toList.foldl (fun p s => extractLabel (s, false) p) G
  exact MvPolynomial.C (q ^ n / (n.factorial : ℚ)) *
    linearSubstitution (activeSubstitution R t) H







end CountingMatroid.Analysis.OmittedSlotQuadratic

end


