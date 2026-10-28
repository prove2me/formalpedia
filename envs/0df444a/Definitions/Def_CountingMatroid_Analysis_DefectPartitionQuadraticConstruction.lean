-- Prove2me | Definitions.Def_CountingMatroid_Analysis_DefectPartitionQuadraticConstruction
-- name    : CountingMatroid_Analysis_DefectPartitionQuadraticConstruction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:11:33.739717+00:00
-- url     : https://prove2.me/theorems/d0d4007c-5155-4911-8fb8-facf2d7947b7
-- title:
--   Paired matroid and selected three-coordinate polynomial
-- statement:
--   For matroids $M_1,M_2$ on $G=\{0,\ldots,n-1\}$, the paired matroid is $M_1\oplus M_2^*$ relabeled on $E=G\times\{0,1\}$, with false labels carrying $M_1$ and true labels carrying the dual of $M_2$. The pair substitution sends the homogenizing variable $z_0$ to zero and both label variables $x_{(s,0)},x_{(s,1)}$ to $y_s$. For a polynomial $g$, define exponent-one extraction by
--   $$
--   \mathcal E_s g=\left.\frac{\partial g}{\partial y_s}\right|_{y_s=0}.
--   $$
--   Let $q\in\mathbb Q$ and $i,j,k\in G$. If $T$ is the homogenized Tutte polynomial of the paired matroid, put
--   $$
--   f=\mathcal S(\partial_{z_0}^{\,n}T),\qquad
--   g=\left(\prod_{s\notin\{i,j,k\}}\mathcal E_s\right)f.
--   $$
--   The extraction follows ground-set order. The selected three-coordinate construction is
--   $$
--   Q_{i,j,k}=\frac{q^n}{n!}\,
--   \mathcal T_{i,j,k}(\partial_{y_k}g),
--   \qquad
--   \mathcal T_{i,j,k}(y_s)=[s=i]X_0+[s=j]X_1+[s=k]X_2.
--   $$
--   Here brackets denote zero-one coefficients. Repeated distinguished indices can contribute several target variables. The definitions require neither distinct indices nor positive $q$; the designation as a quadratic does not by itself establish a degree statement for every input.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/DefectPartitionQuadraticConstruction.lean#L33-L39

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
The concrete selected-element quadratic used in the three-pair inequality.
It is constructed from the homogenized Tutte polynomial by the paper's
actual derivative and substitution sequence. Its membership in the allowed
closure operations is proved separately from its operational coefficients.
Its last diagonal Hessian entry is proved to vanish directly from squarefree
label exponents, without any operational coefficient identity.
The remaining coefficient identities need the paired-rank correspondence
and extraction calculation; it does not assume a signature theorem. The
existing paired-rank correspondence and extraction-calculus lemmas live in
modules that import this module. Reusing them here requires separating the
construction declarations above the operational extraction theorem from
that theorem, so those dependencies no longer import their consumer.
-/

namespace CountingMatroid.Analysis.DefectPartitionQuadraticExtraction

open CountingMatroid.Model
open CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid.Analysis.ThreePairSignatureSchur
open CountingMatroid.Analysis.TwoLabelDerivativeNilpotence

/-- PAPER: main.tex:262-272
The direct sum of the first matroid and the second matroid's dual, on the
existing paired labels; false denotes x and true denotes y. -/
noncomputable def pairedMatroid {n : ℕ} (M₁ M₂ : Matroid (Fin n)) :
    Matroid (PairedGround n) :=
  (Matroid.sum' (fun b : Bool => if b then M₂✶ else M₁)).mapEquiv
    (Equiv.prodComm Bool (Fin n))



/-- INTERNAL: Identify the two label variables of a pair and set the
homogenizing variable to zero.
TEXLINE: main.tex:354-373,403-407 -/
noncomputable def pairSubstitution {n : ℕ} : Option (PairedGround n) → Fin n → ℚ
  | none, _ => 0
  | some e, j => if e.1 = j then 1 else 0

/-- INTERNAL: Delete a variable after differentiating, extracting precisely
exponent one rather than all positive exponents.
TEXLINE: main.tex:369-373 -/
noncomputable def extractOne {n : ℕ} (j : Fin n)
    (g : MvPolynomial (Fin n) ℚ) : MvPolynomial (Fin n) ℚ :=
  linearSubstitution (fun s t => if s = j then 0 else if s = t then 1 else 0)
    (MvPolynomial.pderiv j g)

/-- INTERNAL: Retain the three distinguished pair variables, in the order
i,j,k, and delete the already extracted ordinary-pair variables.
TEXLINE: main.tex:412-417 -/
noncomputable def tripleSubstitution {n : ℕ} (i j k : Fin n) :
    Fin n → Fin 3 → ℚ := fun s t =>
  if s = i ∧ t = 0 then 1 else
    if s = j ∧ t = 1 then 1 else if s = k ∧ t = 2 then 1 else 0

/-- INTERNAL: The specific quadratic obtained by the paper's extraction
from T: n homogenizing derivatives, z₀=0 and pair identification, extraction
of all ordinary pairs, and one derivative at k, scaled by qⁿ/n!.
TEXLINE: main.tex:354-373,403-417 -/
noncomputable def selectedTripleQuadratic {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (i j k : Fin n) : MvPolynomial (Fin 3) ℚ :=
  let f := linearSubstitution pairSubstitution
    ((MvPolynomial.pderiv none)^[n] (tuttePolynomial (pairedMatroid M₁ M₂) q))
  let ordinary := (List.finRange n).filter (fun s => s ≠ i ∧ s ≠ j ∧ s ≠ k)
  let cubic := ordinary.foldl (fun g s => extractOne s g) f
  MvPolynomial.C (q ^ n / (n.factorial : ℚ)) *
    linearSubstitution (tripleSubstitution i j k) (MvPolynomial.pderiv k cubic)















end CountingMatroid.Analysis.DefectPartitionQuadraticExtraction

end


