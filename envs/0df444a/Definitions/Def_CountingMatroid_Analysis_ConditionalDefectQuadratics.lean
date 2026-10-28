-- Prove2me | Definitions.Def_CountingMatroid_Analysis_ConditionalDefectQuadratics
-- name    : CountingMatroid_Analysis_ConditionalDefectQuadratics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:13:11.006553+00:00
-- url     : https://prove2.me/theorems/d9f26d0b-cae0-447e-902a-885522b0b0b6
-- title:
--   Conditioned pair and triple polynomial constructions
-- statement:
--   Let $M_1,M_2$ be matroids on $G=\{0,\ldots,n-1\}$, let $q\in\mathbb Q$, and let $\sigma:G\to\operatorname{Option}\{0,1\}$ be a partial assignment. Put $A_\sigma=\{i:\sigma(i)\ne\operatorname{none}\}$ and let $T$ be the homogenized Tutte polynomial of the paired matroid $M_1\oplus M_2^*$. The conditioned substitution $\mathcal S_\sigma$ sends the homogenizing variable to zero, both label variables of an assigned pair to zero, and both label variables of an unassigned pair $i$ to $y_i$. Define
--   $$
--   F_\sigma=\frac{q^n}{n!}\mathcal S_\sigma
--   \left[\left(\prod_{i\in A_\sigma}\partial_{x_{(i,\sigma(i))}}\right)
--   \partial_{z_0}^{\,n}T\right].
--   $$
--   For a retained set $D\subseteq G$, extract exponent exactly one in every unassigned coordinate outside $D$:
--   $$
--   F_{\sigma,D}=
--   \left(\prod_{s\in G\setminus(A_\sigma\cup D)}
--   \left.\partial_{y_s}\right|_{y_s=0}\right)F_\sigma.
--   $$
--   Products denote the finite-list operations in the supplied construction. The two-coordinate polynomial substitutes $y_s\mapsto [s=i]X_0+[s=j]X_1$ in $F_{\sigma,\{i,j\}}$. The three-coordinate polynomial substitutes $y_s\mapsto[s=i]X_0+[s=j]X_1+[s=k]X_2$ in $\partial_{y_k}F_{\sigma,\{i,j,k\}}$. Repeated distinguished indices therefore contribute more than one target variable. No distinctness, positivity, or unassigned-index hypotheses are imposed by these definitions, and the names alone do not assert a degree theorem for arbitrary inputs.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ConditionalDefectQuadratics.lean#L22-L25

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

namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
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
section


set_option autoImplicit false

/-!
Concrete selected-element descendants for an arbitrary partial assignment.
Differentiation fixes the selected label at each assigned pair; substitution
deletes both labels of those pairs and identifies each remaining pair.
Ordinary-pair extraction then leaves the distinguished pair variables.
The descendant and homogeneous-degree facts below do not assert identities
between polynomial coefficients and operational rank sums.
-/

namespace CountingMatroid.Analysis.ConditionalDefectQuadratics

open CountingMatroid.Model
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid.Analysis.DefectPartitionQuadraticExtraction

/-- INTERNAL: The pair indices at which a partial assignment selects a label.
TEXLINE: main.tex:403-407 -/
noncomputable def assignedPairs {n : ℕ} (σ : Assignment n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => σ i ≠ none)

/-- INTERNAL: Delete both variables of assigned pairs, and identify the two
variables in each unassigned pair, also deleting the homogenizing variable.
TEXLINE: main.tex:403-407 -/
noncomputable def conditionedPairSubstitution {n : ℕ} (σ : Assignment n) :
    Option (PairedGround n) → Fin n → ℚ
  | none, _ => 0
  | some e, j => if σ e.1 = none ∧ e.1 = j then 1 else 0

/-- INTERNAL: The paper's conditioned selected-element polynomial, before
ordinary-pair extraction, constructed from the matroid Tutte polynomial.
TEXLINE: main.tex:354-367,403-407 -/
noncomputable def conditionedPairPolynomial {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (σ : Assignment n) : MvPolynomial (Fin n) ℚ :=
  MvPolynomial.C (q ^ n / (n.factorial : ℚ)) *
    linearSubstitution (conditionedPairSubstitution σ)
      ((assignedPairs σ).toList.foldl
        (fun g i => MvPolynomial.pderiv (some (i, (σ i).getD false)) g)
        ((MvPolynomial.pderiv none)^[n] (tuttePolynomial (pairedMatroid M₁ M₂) q)))

/-- INTERNAL: Extract exactly one selected element at every unassigned pair
outside the retained set of distinguished indices.
TEXLINE: main.tex:408-417 -/
noncomputable def retainedPolynomial {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (σ : Assignment n) (retained : Finset (Fin n)) :
    MvPolynomial (Fin n) ℚ :=
  ((Finset.univ \ (assignedPairs σ ∪ retained)).toList).foldl
    (fun g i => extractOne i g) (conditionedPairPolynomial M₁ M₂ q σ)













/-- INTERNAL: Retain the two distinguished coordinates after conditioning.
TEXLINE: main.tex:408-412 -/
noncomputable def pairSubstitutionTwo {n : ℕ} (i j : Fin n) : Fin n → Fin 2 → ℚ :=
  fun s t => if s = i ∧ t = 0 then 1 else if s = j ∧ t = 1 then 1 else 0

/-- INTERNAL: The actual conditioned two-pair quadratic in the determinant
argument, rather than a matrix defined from the desired inequalities.
TEXLINE: main.tex:408-412 -/
noncomputable def conditionedPairQuadratic {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (σ : Assignment n) (i j : Fin n) : MvPolynomial (Fin 2) ℚ :=
  linearSubstitution (pairSubstitutionTwo i j) (retainedPolynomial M₁ M₂ q σ {i, j})

/-- INTERNAL: The actual conditioned three-pair quadratic, including the
last derivative at k prescribed in the paper.
TEXLINE: main.tex:412-417 -/
noncomputable def conditionedTripleQuadratic {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (σ : Assignment n) (i j k : Fin n) : MvPolynomial (Fin 3) ℚ :=
  linearSubstitution (tripleSubstitution i j k)
    (MvPolynomial.pderiv k (retainedPolynomial M₁ M₂ q σ {i, j, k}))





end CountingMatroid.Analysis.ConditionalDefectQuadratics

end


