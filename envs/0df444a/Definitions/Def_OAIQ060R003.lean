-- Prove2me | Definitions.Def_OAIQ060R003
-- name    : OAIQ060R003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T23:51:15.960956+00:00
-- url     : https://prove2.me/theorems/053c2a12-f8f3-45ad-b586-429f22a52171
-- title:
--   Definitions bundle OAIQ060R003 of the split of OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 247 declarations of OpenAI's Lean: 219 definitions, 1 inductive type or structure, 11 instances and 16 theorems. The definitions and types are `OAI.SharpRamseyFive.Marking.allWindowIDE`, `OAI.SharpRamseyFive.Marking.boundsIDE`, `OAI.SharpRamseyFive.Marking.goodVarIDE`, `OAI.SharpRamseyFive.Marking.highDomainPreIndexDE`, `OAI.SharpRamseyFive.Marking.highDomainStageIndexDE`, `OAI.SharpRamseyFive.Marking.highDomainThreeIndexDE`, `OAI.SharpRamseyFive.Marking.highFourLoss`, `OAI.SharpRamseyFive.Marking.highFourPreIndexDE`, `OAI.SharpRamseyFive.Marking.highFourSampler`, `OAI.SharpRamseyFive.Marking.highLeft`, `OAI.SharpRamseyFive.Marking.highRepresentative`, `OAI.SharpRamseyFive.Marking.highRight`, `OAI.SharpRamseyFive.Marking.highThreeLeft`, `OAI.SharpRamseyFive.Marking.highThreeRight`, `OAI.SharpRamseyFive.Marking.inputWinIDE`, `OAI.SharpRamseyFive.Marking.markingEndpointsPairDecEq`, `OAI.SharpRamseyFive.Marking.scanChoice`, `OAI.SharpRamseyFive.Marking.survRetIDE`, `OAI.SharpRamseyFive.Marking.wcdIDE`, `OAI.SharpRamseyFive.Marking.windowScoreIndexDE`, `OAI.SharpRamseyFive.NondominantOverlap.planePairs`, `OAI.SharpRamseyFive.PoissonScore.allEmptyIndicator`, `OAI.SharpRamseyFive.PoissonScore.emptyTests`, `OAI.SharpRamseyFive.PoissonScore.emptyWeight`, `OAI.SharpRamseyFive.PoissonScore.forcedHits`, `OAI.SharpRamseyFive.PoissonScore.hitIndicator`, `OAI.SharpRamseyFive.PoissonScore.internalPart`, `OAI.SharpRamseyFive.PoissonScore.maskedFactor`, `OAI.SharpRamseyFive.PoissonScore.maskedTerm`, `OAI.SharpRamseyFive.PoissonScore.otherComponents`, `OAI.SharpRamseyFive.PoissonScore.ownScore`, `OAI.SharpRamseyFive.PoissonScore.pairMean`, `OAI.SharpRamseyFive.PoissonScore.scheduleMeasure`, `OAI.SharpRamseyFive.PoissonScore.typicalScore`, `OAI.SharpRamseyFive.ProjectiveIncidence.AmbientPairMessage`, `OAI.SharpRamseyFive.ProjectiveIncidence.FiniteNodeMessage`, `OAI.SharpRamseyFive.ProjectiveIncidence.FiniteNodeTape`, `OAI.SharpRamseyFive.ProjectiveIncidence.OrientedNodeMessage`, `OAI.SharpRamseyFive.ProjectiveIncidence.OrientedNodeTape`, `OAI.SharpRamseyFive.ProjectiveIncidence.OrientedPivotMessage` and 180 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `RamseyFive_Decoding_FreshPublicValidation`, `RamseyFive_Decoding_FreshValidation`, `RamseyFive_Decoding_OffFiberPairs`, `RamseyFive_Decoding_ReverseCap`, `RamseyFive_Decoding_UniversalFresh`, `RamseyFive_Decoding_UniversalReverse`, `RamseyFive_Entropy_AllWindowCost`, `RamseyFive_Entropy_ClippedWeight`, `RamseyFive_Entropy_EmptyWeight`, `RamseyFive_Entropy_FreshPublicFamily`, `RamseyFive_Entropy_LocalNodeLaw`, `RamseyFive_Entropy_LogContractionDrop`, `RamseyFive_Entropy_Pairs`, `RamseyFive_Entropy_PrimitiveMessageWeights`, `RamseyFive_Entropy_ReciprocalLossBudget`, `RamseyFive_Entropy_Rectangle`, `RamseyFive_Entropy_SelectedRestriction`, `RamseyFive_Entropy_SubsetEncoding`, `RamseyFive_Entropy_TreeWeights`, `RamseyFive_Entropy_WindowLossAggregation`, `RamseyFive_Entropy_WindowPosterior`, `RamseyFive_Entropy_WindowTargetInputs`, `RamseyFive_Geometry_AmbientPairPublic`, `RamseyFive_Geometry_BaseCapturedLaw`, `RamseyFive_Geometry_BaseFinitePublic`, `RamseyFive_Geometry_BasePublicFamily`, `RamseyFive_Geometry_BaseSmallLaw`, `RamseyFive_Geometry_DimensionTwoOriented`, `RamseyFive_Geometry_EmptyVariableTree`, `RamseyFive_Geometry_FiniteFamily`, `RamseyFive_Geometry_FourFinitePredictor`, `RamseyFive_Geometry_GeneralReversedCode`, `RamseyFive_Geometry_GeometricRestriction`, `RamseyFive_Geometry_GuardedNodeSent`, `RamseyFive_Geometry_ModifiedRadialSchedule`, `RamseyFive_Geometry_OrientedPivotTree`, `RamseyFive_Geometry_OrientedTreeDomains`, `RamseyFive_Geometry_Outside`, `RamseyFive_Geometry_OverlapDyads`, `RamseyFive_Geometry_OwnQuery`, `RamseyFive_Geometry_PencilCount`, `RamseyFive_Geometry_PlaneExceptions`, `RamseyFive_Geometry_PlanePublicDefs`, `RamseyFive_Geometry_PredictorReverseCap`, `RamseyFive_Geometry_ProjectiveEquiv`, `RamseyFive_Geometry_PublicDecoder`, `RamseyFive_Geometry_RadialLabel`, `RamseyFive_Geometry_ReversedBasePublic`, `RamseyFive_Geometry_SampledPoints`, `RamseyFive_Geometry_ScoredMessage`, `RamseyFive_Geometry_SubspacePointsEquiv`, `RamseyFive_Geometry_ThreeCoordinateCertified`, `RamseyFive_Geometry_ThreeFiniteOriented`, `RamseyFive_Geometry_ThreeFinitePredictor`, `RamseyFive_Geometry_ThreePublic`, `RamseyFive_Geometry_ThreePublicDefs`, `RamseyFive_Geometry_TwoAmbientCaps`, `RamseyFive_Geometry_TwoFinitePublic`, `RamseyFive_Geometry_TwoPublicCaps`, `RamseyFive_Iteration_CodedWindowStage`, `RamseyFive_Iteration_HighWindowStage`, `RamseyFive_Iteration_Scale`, `RamseyFive_Iteration_StageState`, `RamseyFive_Iteration_WindowStage`, `RamseyFive_Marking_AllWindowBounds`, `RamseyFive_Marking_ChooseLevel`, `RamseyFive_Marking_GoodWindowVariation`, `RamseyFive_Marking_HighDomainEndpoints`, `RamseyFive_Marking_HighDomainPreRound`, `RamseyFive_Marking_HighFourPreRound`, `RamseyFive_Marking_HighLowConflict`, `RamseyFive_Marking_HighSampleRetention`, `RamseyFive_Marking_MarkingEndpoints`, `RamseyFive_Marking_OrderedHighConflict`, `RamseyFive_Marking_ScanChoice`, `RamseyFive_Marking_ScanRecordPresent`, `RamseyFive_Marking_State`, `RamseyFive_Marking_TwoScan`, `RamseyFive_Marking_WindowCodeDomains`, `RamseyFive_Marking_WindowDeletionCount`, `RamseyFive_Marking_WindowReciprocalScores`, `RamseyFive_Marking_WindowTargetRetention`, `RamseyFive_Probability_AllEmptyIndicator`, `RamseyFive_Probability_AmbientPublicTest`, `RamseyFive_Probability_EmptyTestsManySmall`, `RamseyFive_Probability_OwnFraction`, `RamseyFive_Probability_PublicCapLaw`, `RamseyFive_Streams_DependentPrivateStream`, `RamseyFive_Trees_HistoryPrivateStream`, `RamseyFive_Trees_PivotTree`, `SharpRamsey_Entropy_CompleteProgramWeight`, `SharpRamsey_Entropy_ExternalMass`, `SharpRamsey_Entropy_ForcedHits`, `SharpRamsey_Entropy_HighMoments`, `SharpRamsey_Entropy_IntegralTypicalScoreSq`, `SharpRamsey_Entropy_LabelledFilterCard`, `SharpRamsey_Entropy_NewEvents`, `SharpRamsey_Entropy_PoissonLaw`, `SharpRamsey_Entropy_TwoAnchorCrossCost`, `SharpRamsey_Entropy_WitnessList`.
--
--   **Imports.** It imports the bundles `OAIQ060R000` and `OAIQ060R001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ060R004`; the statements `OAI.SharpRamseyFive.AmbientEnumeration.ambient_refined_truncated_moment`, `OAI.SharpRamseyFive.AmbientEnumeration.ambient_untruncated_moment`, `OAI.SharpRamseyFive.ProjectiveIncidence.producedPairLaw_spec`, `OAI.SharpRamseyFive.ProjectiveIncidence.reverse_after_general_capture`, `OAI.SharpRamseyFive.ProjectiveRestriction.eventually_three_flat_finite_predictor`, `OAI.SharpRamseyFive.ScoreGeometry.captured_global_trunc_exp_bound`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_finite_predictor`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_high_protocol`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_high_training_score`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_low_protocol`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_low_training_score`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_global_trunc`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_three_coordinates_certified`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_three_score_integrals`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_three_small_protocol`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_three_training_score`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_law`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_oriented`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_public_complete`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_score_integrals`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_score_procedure`, `OAI.SharpRamseyFive.ScoreGeometry.literal_hyperplane_pair_moment` and `OAI.SharpRamseyFive.ScoreGeometry.score_pair_low_moment`; the proofs of `OAI.SharpRamseyFive.AmbientEnumeration.ambient_refined_truncated_moment`, `OAI.SharpRamseyFive.AmbientEnumeration.ambient_untruncated_moment`, `OAI.SharpRamseyFive.ProjectiveIncidence.producedPairLaw_spec`, `OAI.SharpRamseyFive.ProjectiveIncidence.reverse_after_general_capture`, `OAI.SharpRamseyFive.ProjectiveRestriction.eventually_three_flat_finite_predictor`, `OAI.SharpRamseyFive.ScoreGeometry.captured_global_trunc_exp_bound`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_four_finite_predictor`, `OAI_SharpRamseyFive_ScoreGeometry_eventually_four_low_score_integrals`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_high_peel_exceptions`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_exceptions`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_global_trunc`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_half_exceptions`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_three_coordinates_certified`, `OAI_SharpRamseyFive_ScoreGeometry_eventually_three_validation_tail`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_law`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_oriented`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_two_public_complete`, `OAI.SharpRamseyFive.ScoreGeometry.literal_hyperplane_pair_moment` and `OAI.SharpRamseyFive.ScoreGeometry.score_pair_low_moment`.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ060R000
import Definitions.Def_OAIQ060R001

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_ReverseCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype B]

noncomputable def cap (R : A→B→Prop) (U : Finset A) {n : ℕ} (q : ℝ) (row : Fin n→B) : Finset A :=
  U.filter fun a=>hits (neighbors R a) row < (n:ℝ)/(5*q)

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_FreshValidation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

noncomputable def rejected (R : A→B→Prop) (S : Finset A) {n : ℕ}
    (q : ℝ) (row : Fin n→B) : Finset A :=
  S.filter fun a=>(n:ℝ)/(5*q) ≤ hits (neighbors R a) row

noncomputable def validationRows (R : A→B→Prop) (S U : Finset A) (C : Finset B)
    (n : ℕ) (q M : ℝ) : Finset (Fin n→B) :=
  Finset.univ.filter fun row=>(∀i,row i∈C) ∧ ((cap R U q row).card:ℝ) ≤ M ∧
    (9:ℝ)/10*S.card ≤ (S∩cap R U q row).card

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_SubspacePointsEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

open scoped LinearAlgebra.Projectivization
open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma incident_iff (a : ℙ K V) (b : ℙ K (Module.Dual K V)) :
    Incident a b ↔ b.rep a.rep = 0 := by
  rw [Incident, Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem,
    LinearMap.mem_ker]

namespace RadialLine

instance instFinite (x : ℙ K V) [Finite V] : Finite (RadialLine x) := by
  unfold RadialLine
  infer_instance

noncomputable def through (x y : ℙ K V) (hxy : x ≠ y) : RadialLine x :=
  ⟨x.submodule ⊔ y.submodule, finrank_sup_points hxy, le_sup_left⟩

open scoped BigOperators Classical

end RadialLine

open scoped Classical

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_OffFiberPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.NondominantOverlap
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (x : ℙ K V)

noncomputable def planePairs (X : Finset {y : ℙ K V // x ≠ y}) (A : Submodule K V) :=
  offFiberPairs (fun y : {y : ℙ K V // x ≠ y} => RadialLine.through x y.val y.property) (onPlane x X A)

end SharpRamseyFive.NondominantOverlap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Pairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.WeightedOverlap
open Module ProjectiveIncidence RichPlaneGeometry NondominantOverlap ActualOverlap
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Finite K]
  (x : ℙ K V)

noncomputable def pairs (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (δ a : ℝ) :=
  (F ×ˢ F).filter fun p => p.1 ≠ p.2 ∧ a ≤ δ*(pairPoints x X p.1 p.2).card

noncomputable def neighbors (X : Finset {y : ℙ K V // x ≠ y})
    (F : Finset (Submodule K V)) (H : Submodule K V) (δ a : ℝ) :=
  F.filter fun A => H ≠ A ∧ a ≤ δ*(pairPoints x X H A).card

end SharpRamseyFive.WeightedOverlap

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_PoissonLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.StaticCertificates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section PairWitnesses

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

noncomputable def AnchorChoice.cost (rate : ι → ℝ≥0)
    {C : Finset (κ × ι)} {S : Finset ι} : AnchorChoice C S → ℝ
  | .inl _ => 1
  | .inr rd => rate rd.2.val

end PairWitnesses
end SharpRamseyFive.StaticCertificates
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_TwoAnchorCrossCost
attribute [-instance] _root_.OAI.SharpRamseyFive.CertificateCover.completePrograms_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

open scoped BigOperators

namespace SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.StaticCertificates
open SharpRamseyFive.CertificateEnumeration
open scoped BigOperators NNReal

variable {V H D B : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]

variable (lines : H → Finset D)

noncomputable def oneCost (rate : D → ℝ≥0) (denom : ℝ)
    (s : State V H D B) (c : OneChoice lines s) : ℝ :=
  c.2.2.1.cost rate / denom
noncomputable def twoCost (rate : D → ℝ≥0) (denom : ℝ)
    (s : State V H D B) (c : TwoChoice lines s) : ℝ :=
  c.2.2.2.1.cost rate * c.2.2.2.2.1.cost rate / denom
noncomputable def pairCost (rate : D → ℝ≥0) (denom : ℝ) (K : ℕ)
    (s : State V H D B) (c : PairChoice lines K s) : ℝ :=
  weight (fun p : B × D => rate p.2)
    (witnessRequirements c.2.2.2.2.1.val
      (PairDirections lines s c.2.2.1 c.2.2.2.1.val) c.2.2.2.2.2) / denom ^ 2

noncomputable def anchorBudget (_rate : D → ℝ≥0) (s : State V H D B) (mass : ℝ) : ℝ :=
  s.2.card + Fintype.card B * mass

end SharpRamseyFive.WeightedPrograms
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_NewEvents
attribute [-instance] _root_.OAI.SharpRamseyFive.CertificateCover.completePrograms_fintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
namespace SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.StaticCertificates
open SharpRamseyFive.CertificateEnumeration
open scoped BigOperators NNReal
variable {V H D B : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]
variable (lines : H → Finset D)

noncomputable def rawCost (rate : D → ℝ≥0) (denom : ℝ) (K : ℕ) (low : Bool)
    (s : State V H D B) : Action lines K s → ℝ
  | .inl _ => 1 / denom
  | .inr (.inl c) => if low then oneCost lines rate denom s c else 0
  | .inr (.inr (.inl c)) => twoCost lines rate denom s c
  | .inr (.inr (.inr c)) => pairCost lines rate denom K s c

noncomputable def programCost (rate : D → ℝ≥0) (denom : ℝ) (K : ℕ) (low : Bool)
    (s : State V H D B) (a : Action lines K s) : ℝ :=
  if s.2.card ≤ K * Fintype.card V then rawCost lines rate denom K low s a else 0

end SharpRamseyFive.WeightedPrograms

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_WitnessList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.ResidualCertificate
variable {V : Type*} [Fintype V] [DecidableEq V]

section SharedHitGeometry

open scoped Classical

variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

noncomputable def touchedToEncoded (s : V → Finset D) (hit : B → D → Prop)
    (E : Finset V) (v : V) : Finset D :=
  (s v ∩ encodedDirections s E).filter (fun d => ∃ r, hit r d)

noncomputable def survivingDirections (s : V → Finset D) (E : Finset V)
    (v : {v // v ∉ E}) : Finset D := s v.val \ encodedDirections s E

noncomputable def outsideDirections (s : V → Finset D) (E : Finset V) (v : V) : Finset D :=
  s v \ encodedDirections s E

inductive EncodingStep (s : V → Finset D) (hit : B → D → Prop)
    (anchorNumber K : ℕ) : Finset V → Finset V → Prop
  | anchor (E : Finset V) (v : V) (hv : v ∉ E)
      (ha : anchorNumber ≤ (touchedToEncoded s hit E v).card) :
      EncodingStep s hit anchorNumber K E (insert v E)
  | pair (E : Finset V) (v u : V) (hv : v ∉ E) (hu : u ∉ E) (hne : v ≠ u)
      (hp : K ≤ (sharedBatches (outsideDirections s E) hit v u).card) :
      EncodingStep s hit anchorNumber K E (insert v (insert u E))

end SharedHitGeometry
end SharpRamseyFive.ResidualCertificate
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_HighMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SharpRamseyFive.PoissonScore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

instance flat_HighMomentRecovered_1 (rate : ι → ℝ≥0) : IsProbabilityMeasure (batchMeasure rate) := by
  unfold batchMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def scheduleMeasure (rate : ι → ℝ≥0) (R : ℕ) :
    Measure (Fin R → ι → ℕ) :=
  Measure.pi (fun _ : Fin R => batchMeasure rate)

instance flat_HighMomentRecovered_2 (rate : ι → ℝ≥0) (R : ℕ) : IsProbabilityMeasure (scheduleMeasure rate R) := by
  unfold scheduleMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def pairMean (rate : ι → ℝ≥0) (s t : Finset ι) (b : ℝ) : ℝ :=
  (Real.exp (-mass rate s) - b) * (Real.exp (-mass rate t) - b) +
    Real.exp (-(mass rate s + mass rate t)) *
      (Real.exp (mass rate (s ∩ t)) - 1)

variable {κ : Type*}

noncomputable def typicalScore {R : ℕ} (H : Finset κ) (directions : κ → Finset ι)
    (b : ℝ) (own : κ → Fin R → Bool) (ω : Fin R → ι → ℕ) : ℝ :=
  ∑ h ∈ H, scoreTerm (directions h) b (own h) ω

end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_IntegralTypicalScoreSq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*}

noncomputable def maskedFactor (s : Finset ι) (b : ℝ) (own touched : Bool)
    (ω : ι → ℕ) : ℝ :=
  if own then (if touched then -b else centeredFactor s b ω) else 0

noncomputable def maskedTerm {R : ℕ} (s : Finset ι) (b : ℝ)
    (own touched : Fin R → Bool) (ω : Fin R → ι → ℕ) : ℝ :=
  ∏ r, maskedFactor s b (own r) (touched r) (ω r)

noncomputable def hitIndicator (i : ι) (ω : ι → ℕ) : ℝ :=
  1 - emptyIndicator {i} ω

noncomputable def forcedHits {R : ℕ} (i : ι) (T : Finset (Fin R))
    (ω : Fin R → ι → ℕ) : ℝ := ∏ r ∈ T, hitIndicator i (ω r)

end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_ForcedHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*}

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

section ComponentGeometry

variable {H : Type*} [Fintype H] [DecidableEq H]

noncomputable def internalPart (rate : ι → ℝ≥0) (s : H → Finset ι)
    (t : ℝ) (h : H) : Finset ι := by
  classical
  exact (s h).filter (fun i => ¬ External rate s t i)

noncomputable def otherComponents (rate : ι → ℝ≥0) (s : H → Finset ι)
    (t : ℝ) (h : H) : Finset H := by
  classical
  exact Finset.univ.filter (fun k =>
    (strongGraph rate s t).connectedComponentMk h ≠
      (strongGraph rate s t).connectedComponentMk k)

end ComponentGeometry
end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_ExternalMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SharpRamseyFive.TupleComponents
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore
open Classical
variable {D V C : Type} [Fintype D] [DecidableEq D]
  [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
variable (label : D → Option C) (R : ℕ)

variable (color : V → C) (s : V → Finset D) (b : ℝ) (own : V → Fin R → Bool)

noncomputable def strongSplit (weight rate : D → ℝ≥0) (t : ℝ) (J : ℕ) : ℝ := by
  classical
  let G := strongGraph weight s t
  let label := componentLabel weight s t
  exact ∫ z, blockTrunc label R J none z * ∏ c : G.ConnectedComponent,
    ∫ x, componentFactor label R G.connectedComponentMk s b own J c z x
      ∂batchMeasure (fun i : Block label R (some c) => rate i.1.2)
      ∂batchMeasure (fun i : Block label R none => rate i.1.2)

end SharpRamseyFive.TupleComponents
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_CompleteProgramWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.SelectionBridge
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations SharpRamseyFive.AmbientDesignations
open SharpRamseyFive.CertificateCover SharpRamseyFive.WeightedPrograms
open Classical
variable {D V H C : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype C] [DecidableEq C]

noncomputable def selectedHit (weight : D → ℝ≥0) (s : V → Finset D) (t : ℝ)
    {R : ℕ} (ω : Fin R × D → ℕ) (r : Fin R) (d : D) : Prop :=
  componentLabel weight s t d = none ∧ ω (r,d) ≠ 0

end SharpRamseyFive.SelectionBridge

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_LabelledFilterCard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.SingletonEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations SharpRamseyFive.AmbientDesignations
open SharpRamseyFive.SelectionBridge SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.ResidualElimination
open Classical
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]

noncomputable def shiftKernel (weight : D → ℝ≥0) (lines : H → Finset D) (p K : ℕ)
    (x y : H) : ℝ := min 1 (((p : ℝ) * mass weight (lines x ∩ lines y)) ^ K)

end SharpRamseyFive.SingletonEnumeration
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_Outside
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable (x : ℙ K V) [Fintype (RadialLine x)]

noncomputable def radialWeight (X : Finset {y : ℙ K V // x ≠ y})
    (δ : ℝ≥0) (l : RadialLine x) : ℝ≥0 :=
  δ * (RadialLine.trainingOnLine X l).card

noncomputable def pencilLines (F : Finset (ℙ K (Module.Dual K V)))
    (H : F) : Finset (RadialLine x) := RadialLine.inFlat (LinearMap.ker H.val.rep)

end
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_RadialLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] (x : ℙ K V) [Fintype (RadialLine x)]

noncomputable def radialLabel (X : Finset {y : ℙ K V // x ≠ y}) (y : X) : RadialLine x :=
  RadialLine.through x y.val.val y.val.property

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ProjectiveEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ProjectiveIncidence
open Module
open scoped LinearAlgebra.Projectivization Classical
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

lemma incident_mk_right (a : ℙ K V) (f : Module.Dual K V) (hf : f ≠ 0) :
    Incident a (Projectivization.mk K f hf) ↔ f a.rep = 0 := by
  obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep K f hf
  rw [incident_iff,←hc]
  simp only [LinearMap.smul_apply,Units.smul_def,smul_eq_mul,mul_eq_zero,
    Units.ne_zero,false_or]

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_Scale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreRegularity
open Module ProjectiveIncidence CellVariance
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def deviation {J : Type*} (S : Finset (ℙ K V))
    (C : J→Finset (ℙ K V)) (j : Option J) (H : ℙ K (Dual K V)) : ℝ :=
  cellMass (familyCell S C j) ((Nat.card K:ℝ)/S.card) H -
    (familyCell S C j).card/(S.card:ℝ)

noncomputable def exceptional {J : Type*} [Fintype J] (S : Finset (ℙ K V))
    (C : J→Finset (ℙ K V)) : Finset (ℙ K (Dual K V)) :=
  Finset.univ.filter fun H => ∃ j : Option J,threshold j < |deviation S C j H|

end SharpRamseyFive.ScoreRegularity

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ClippedWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreRegularity
open Module ProjectiveIncidence CellVariance
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def clippedWeight {J : Type*} [Fintype J] (S : Finset (ℙ K V))
    (C : J→Finset (ℙ K V)) : Option (Option J)→ℙ K (Dual K V)→ℝ
  | none,H => if H∈exceptional S C then 1 else 0
  | some j,H => min 1 ((deviation S C j H)^2)

end SharpRamseyFive.ScoreRegularity

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_OwnFraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreRegularity

section
open Module ProjectiveIncidence CellVariance
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable [Finite K] [Fintype (ℙ K (Dual K V))]

noncomputable def outsideMass (S O : Finset (ℙ K V)) (x : ℙ K V) (H : ℙ K (Dual K V)) : ℝ :=
  cellMass (S\(O∪{x})) ((Nat.card K:ℝ)/S.card) H

noncomputable def queryLoss (S O : Finset (ℙ K V)) (x : ℙ K V) (H : ℙ K (Dual K V)) : ℝ :=
  cellMass (S\O) ((Nat.card K:ℝ)/S.card) H-outsideMass S O x H

end

open Module ProjectiveIncidence CellVariance
open scoped BigOperators LinearAlgebra.Projectivization Classical

end SharpRamseyFive.ScoreRegularity

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OwnQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]

noncomputable def ownBitsMinus (x : ℙ K V) (S O : Finset (ℙ K V))
    (F : Finset (ℙ K (Dual K V))) {R : ℕ}
    (u : Fin R→{y : S // ownQuery x S O y}→ℕ) (H : F) (r : Fin R) : Bool :=
  decide (∀ (y : S) (hy : y.val∈O),x≠y.val → Incident y.val H.val → u r ⟨y,Or.inl hy⟩=0)

noncomputable def modifiedPointScore (x : ℙ K V) (S O : Finset (ℙ K V))
    (F : Finset (ℙ K (Dual K V))) {R : ℕ} (b : ℝ) (ω : Fin R→S→ℕ) : ℝ :=
  typicalScore Finset.univ
    (fun H : F => Finset.univ.filter fun y : outsideAt x S O => Incident y.val.val H.val)
    b (ownBitsMinus x S O F (fun r i => ω r i))
    (fun r d => ω r ((outsideEquiv x S O).symm d).val)

end

open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]

noncomputable def pointScore (S O : Finset (ℙ K V))
    (F : Finset (ℙ K (Dual K V))) {R : ℕ} (b : ℝ) (ω : Fin R→S→ℕ) : ℝ :=
  ∑ H : F, ∏ r, (if (∀ y : S,y.val∈O → Incident y.val H.val → ω r y=0) then 1 else 0)*
    ((if (∀ y : S,y.val∉O → Incident y.val H.val → ω r y=0) then 1 else 0)-b)

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_AllEmptyIndicator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

variable {ι H : Type*} [Fintype ι]

noncomputable def allEmptyIndicator {R : ℕ} (s : Finset ι) (ω : Fin R→ι→ℕ) : ℝ :=
  ∏ r,emptyIndicator s (ω r)

noncomputable def emptyTests {R : ℕ} (E : Finset H) (lines : H→Finset ι)
    (ω : Fin R→ι→ℕ) : Finset H := E.filter fun h => ∀r,ω r∈emptyEvent (lines h)

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_EmptyWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι H : Type*} [Fintype ι]

noncomputable def emptyWeight {R : ℕ} (E : Finset H) (lines : H→Finset ι)
    (w : H→ℝ) (ω : Fin R→ι→ℕ) : ℝ :=
  ∑h∈E,w h*allEmptyIndicator (lines h) ω

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_EmptyTestsManySmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

variable {ι H : Type*} [DecidableEq ι]

noncomputable def ownScore {R : ℕ} (s o : Finset ι) (b : ℝ) (ω : Fin R→ι→ℕ) : ℝ :=
  ∏r,emptyIndicator (s∩o) (ω r)*(emptyIndicator (s\o) (ω r)-b)

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PencilCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence CellVariance ScoreRegularity
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def pencilCount (Z : Finset (ℙ K (Dual K V))) (x : ℙ K V) : ℝ :=
  (Z.filter fun H => Incident x H).card

end

open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]

noncomputable def hyperplaneSupport (S : Finset (ℙ K V)) (H : ℙ K (Dual K V)) : Finset S :=
  Finset.univ.filter fun y => Incident y.val H

variable [Fintype (ℙ K (Dual K V))]
noncomputable def pencil (x : ℙ K V) : Finset (ℙ K (Dual K V)) :=
  Finset.univ.filter fun H => Incident x H

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_SampledPoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore ScoreAcceptance
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def decoded (U S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (b : ℙ K V→ℝ) (z : ℕ) {R : ℕ} (ω : Fin R→S→ℕ) : Finset (ℙ K V) :=
  accepted U (sampledPoints S ω) (fun x => pointScore S (O x) (pencil x) (b x) ω)
    ((z:ℝ)/(2*(Nat.card K:ℝ)))

noncomputable def typicalFailures (U S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (E : Finset (ℙ K (Dual K V))) (b : ℙ K V→ℝ) (t : ℝ) {R : ℕ}
    (ω : Fin R→S→ℕ) : Finset (ℙ K V) :=
  U.filter fun x => Unsampled x S ω ∧ t < |pointScore S (O x) (pencil x\E) (b x) ω|

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PublicDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore ScoreAcceptance
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def publicScore (O : Finset (ℙ K V)) (F : Finset (ℙ K (Dual K V)))
    {R : ℕ} (b : ℝ) (ω : Fin R→ℙ K V→ℕ) : ℝ :=
  ∑ H : F, ∏ r, (if (∀ y,y∈O → Incident y H.val → ω r y=0) then 1 else 0)*
    ((if (∀ y,y∉O → Incident y H.val → ω r y=0) then 1 else 0)-b)

noncomputable def publicDecoded (U : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (b : ℙ K V→ℝ) (z : ℕ) {R : ℕ} (ω : Fin R→ℙ K V→ℕ) : Finset (ℙ K V) :=
  accepted U (publicSamples U ω) (fun x=>publicScore (O x) (pencil x) (b x) ω)
    ((z:ℝ)/(2*(Nat.card K:ℝ)))

end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore ScoreAcceptance MeasurePublicTable
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def trueScoreSuccess (U S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (b : ℙ K V→ℝ) (E : Finset (ℙ K (Dual K V))) (R : ℕ) (s M c : ℝ) : Set (Fin R→S→ℕ) :=
  {ω | let W := decoded U S O b (emptyTests E (hyperplaneSupport S) ω).card ω
    (sampleCount ω:ℝ)≤ s ∧ (W.card:ℝ)≤ M ∧ c≤((W∩S).card:ℝ)}

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_PublicCapLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

noncomputable def publicCapLaw (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hW : W.Nonempty) (n : ℕ) (q M : ℝ) : Law (Option (Finset A)) :=
  map (map (iid (iid (uniformOn W hW) (Fin n)) (Fin (uniformCutoff q C W n)))
    (firstAccepted (validationRows R S U C n q M)))
    (Option.map (cap R U q))

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_AmbientPublicTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

noncomputable def ambientCapLaw (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hW : W.Nonempty) (n : ℕ) (q M : ℝ) : Law (Option (Finset A)) :=
  map (map (iid (iid (uniformOn W hW) (Fin n)) (Fin (uniformCutoff q C W n)))
    (firstAccepted (validationRows R S U C n q M)))
    (Option.map (cap R Finset.univ q))

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_FreshPublicFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

noncomputable def freshTapeLaw (W : Finset B) (hW : W.Nonempty) (n : ℕ) (q : ℝ) :
    Law (FreshTape W n q) :=
  piLaw fun m : Fin (W.card+1)=>iid (iid (uniformOn W hW) (Fin n)) (Fin (cardCutoff q m W.card n))

noncomputable def freshDecoded (R : A→B→Prop) (W : Finset B) (n : ℕ) (q : ℝ)
    (t : FreshTape W n q) (m : FreshMessage W n q) : Finset A :=
  cap R Finset.univ q (t m.1 m.2)

noncomputable def freshEncoded (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (n : ℕ) (q M : ℝ) (t : FreshTape W n q) :
    Option (FreshMessage W n q) :=
  let m : Fin (W.card+1) := ⟨C.card,Nat.lt_succ_of_le (Finset.card_le_card hCW)⟩
  Option.map (fun i=>⟨m,i⟩) (acceptedIndex (validationRows R S U C n q M) (t m))

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OverlapDyads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

open Module ProjectiveIncidence PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

noncomputable def offRow (X : Finset {y : ℙ K V // x≠y}) (δ : ℝ≥0)
    (F : Finset (ℙ K (Dual K V))) (H H' : F) : ℝ :=
  if H=H' then 0 else mass (radialWeight x X δ) (pencilLines x F H ∩ pencilLines x F H')

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ModifiedRadialSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] (x : ℙ K V) [Fintype (RadialLine x)]

noncomputable def modifiedRadialSchedule (S O : Finset (ℙ K V)) {R : ℕ}
    (ω : Fin R→S→ℕ) : Fin R→RadialLine x→ℕ :=
  fun r => aggregate (radialLabel x (outsideAt x S O))
    (fun d => ω r ((outsideEquiv x S O).symm d).val)

end

open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PlaneExceptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

noncomputable def radialInventory {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype (ℙ K V)] [∀x : ℙ K V,Fintype (RadialLine x)] :
    Finset (Submodule K V) := Finset.univ.biUnion fun x : ℙ K V =>
      Finset.univ.image fun l : RadialLine x => l.val

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PredictorReverseCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def lowIncidence (C : Finset (ℙ K (Dual K V))) : Finset (ℙ K V) :=
  Finset.univ.filter fun x=>((C.filter (Incident x)).card:ℝ) ≤ (C.card:ℝ)/(2*Nat.card K)

noncomputable def lowPencil (C : Finset (ℙ K V)) : Finset (ℙ K (Dual K V)) :=
  Finset.univ.filter fun y=>((C.filter fun x=>Incident x y).card:ℝ) ≤ (C.card:ℝ)/(2*Nat.card K)

end
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization BigOperators

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_FreshPublicValidation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def generalNextCapLaw (S U : Finset (ℙ K V))
    (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty)
    (c : ℝ) (hc : 0 < c) (n : ℕ) (q M MT : ℝ)
    (Y : Option (Finset (ℙ K (Dual K V)))) : Law (Option (Finset (ℙ K V))) :=
  match Y with
  | none => pureLaw none
  | some W => if hW : CaptureBound T UT c MT W then
      publicCapLaw Incident S U (T∩W) W
        ((hW.nonempty hT hc).mono Finset.inter_subset_right) n q M
    else pureLaw none

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_UniversalFresh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

noncomputable def universalFreshLaw (B : Type*) [Fintype B] (H : ℕ) (q : ℝ) :
    Law (UniversalFresh B H q) :=
  piLaw fun i : FreshIndex B H=>freshTapeLaw i.1.1 i.1.2 i.2 q

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TwoPublicCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def nextCapLaw (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty)
    (nA : ℕ) (q MA MB : ℝ) (Y : Option (Finset (ℙ K (Dual K V)))) :
    Law (Option (Finset (ℙ K V))) :=
  match Y with
  | none => pureLaw none
  | some Y => if hY : ValidCap B UB MB Y then
      publicCapLaw Incident A UA (B∩Y) Y
        ((hY.source_nonempty hB).mono Finset.inter_subset_right) nA q MA
    else pureLaw none

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_UniversalReverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

noncomputable def universalFreshDecoded (R : A→B→Prop) (W : Finset B)
    (H : ℕ) (q : ℝ) (t : UniversalFresh B H q) (m : UniversalFreshMessage W H q) : Finset A :=
  if hW : W.Nonempty then
    freshDecoded R W m.1 q (t (⟨W,hW⟩,m.1)) m.2
  else ∅

noncomputable def universalFreshEncoded (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (H : ℕ) (n : Fin (H+1)) (q M : ℝ)
    (t : UniversalFresh B H q) : Option (UniversalFreshMessage W H q) :=
  if hW : W.Nonempty then
    (freshEncoded R S U C W hCW n q M (t (⟨W,hW⟩,n))).map (fun m=>⟨n,m⟩)
  else none

end SharpRamseyFive.ReverseCap

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def publicReverseResult (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (_ : B.Nonempty)
    (H : ℕ) (n : Fin (H+1)) (q MA MB : ℝ)
    (Y : Option (Finset (ℙ K (Dual K V)))) (t : UniversalFresh (ℙ K (Dual K V)) H q) :
    Option (Finset (ℙ K V)) :=
  match Y with
  | none => none
  | some W => if _hW : ValidCap B UB MB W then
      (universalFreshEncoded Incident A UA (B∩W) W Finset.inter_subset_right H n q MA t).map
        (fun m=>UA∩universalFreshDecoded Incident W H q t m)
    else none

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_SubsetEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence SubsetEncoding
open scoped Classical LinearAlgebra.Projectivization BigOperators NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def baseDecoded (U : Finset (ℙ K V)) (n : ℕ) (P τ : ℝ) (L₀ : ℝ≥0)
    {R : ℕ} (t : Fin (sizeScoreCutoff U n P τ) → Fin R → ℙ K V → ℕ)
    (m : baseAlphabet U n P τ) : Finset (ℙ K V) := by
  classical
  exact if h : (n:ℝ)≤100*(Nat.card K:ℝ)*P then
    decode U n (cast (by simp only [baseAlphabet,h,ite_true]) m)
  else
    let m' : Fin (sizeScoreCutoff U n P τ) × Fin (Fintype.card (ℙ K (Dual K V))+1) :=
      cast (by simp only [baseAlphabet,h,ite_false]) m
    publicDecoded U (fun _=>∅) (fun _=>Real.exp (-(L₀:ℝ))) m'.2 (t m'.1)

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_BasePublicFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence SubsetEncoding
open MeasureTheory ProbabilityTheory PoissonScore
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def baseRowMeasure (U : Finset (ℙ K V)) (n : ℕ) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :=
  Measure.pi (fun _ : Fin (sizeScoreCutoff U n P τ) => scheduleMeasure
    (fun x=>if x∈U then (L₀*(Nat.card K:ℝ≥0))/(U.card:ℝ≥0) else 0) R)

noncomputable def baseTapeMeasure (U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    Measure (BaseTape U P τ R) :=
  Measure.pi (fun n : Fin (Fintype.card (ℙ K V)+1) => baseRowMeasure U n P τ R L₀)

instance instIsProbabilityMeasureForallFinSizeScoreCutoffForallForallProjectivizationNatBaseRowMeasure (U : Finset (ℙ K V)) (n : ℕ) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    IsProbabilityMeasure (baseRowMeasure U n P τ R L₀) := by
  unfold baseRowMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance instIsProbabilityMeasureBaseTapeBaseTapeMeasure (U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    IsProbabilityMeasure (baseTapeMeasure U P τ R L₀) := by
  unfold baseTapeMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def baseMessageDecoded (U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (t : BaseTape U P τ R)
    (m : (n : Fin (Fintype.card (ℙ K V)+1)) × baseAlphabet U n P τ) : Finset (ℙ K V) :=
  baseDecoded U m.1 P τ L₀ (t m.1) m.2

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ScoredMessage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence Metadata FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization NNReal BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def scoredMessageDecoded (U : Finset (ℙ K V)) (σ P τ : ℝ)
    (R : ℕ) (L₀ : ℝ≥0) (t : BaseTape U P τ R) (m : ScoredMessage U σ P τ) :
    Finset (ℙ K V) :=
  publicDecoded U (messageOwn m.2.1) (messageBase m.2.1 L₀) m.2.2.2 (t m.1 m.2.2.1)

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_BaseCapturedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence FiniteEntropy
open MeasureTheory
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def baseOutcome (S U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (t : BaseTape U P τ R) : Option (Finset (ℙ K V)) :=
  let n : Fin (Fintype.card (ℙ K V)+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
  let dec := fun m : baseAlphabet U S.card P τ=>baseMessageDecoded U P τ R L₀ t ⟨n,m⟩
  (chooseMessage (fun (u : BaseTape U P τ R) (m : baseAlphabet U S.card P τ) =>
    let W := baseMessageDecoded U P τ R L₀ u ⟨n,m⟩
    W⊆U ∧ (W.card:ℝ)≤(S.card:ℝ)*Real.exp (2*P) ∧ (9/10:ℝ)*S.card≤((W∩S).card:ℝ)) t).map dec

noncomputable def baseCaptureLaw (S U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    Law (Option (Finset (ℙ K V))) :=
  finiteImageLaw (baseTapeMeasure U P τ R L₀) (baseOutcome S U P τ R L₀)

end

section
open Module ProjectiveIncidence FiniteEntropy MeasureTheory
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def scoredOutcome (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (Own : ℙ K V→Finset (ℙ K V))
    (Base : ℙ K V→ℝ) (P τ c a : ℝ) (R : ℕ) (t : BaseTape U P τ R) :
    Option (Finset (ℙ K V)) :=
  let dec := fun m : Fin (sizeScoreCutoff U n P τ) × Fin (Fintype.card (ℙ K (Dual K V))+1) =>
    publicDecoded U Own Base m.2 (t n m.1)
  (chooseMessage (fun (u : BaseTape U P τ R)
      (m : Fin (sizeScoreCutoff U n P τ) × Fin (Fintype.card (ℙ K (Dual K V))+1)) =>
    let W := publicDecoded U Own Base m.2 (u n m.1)
    W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (a*P) ∧ c*X.card≤((W∩X).card:ℝ)) t).map dec

noncomputable def scoredCaptureLaw (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (Own : ℙ K V→Finset (ℙ K V))
    (Base : ℙ K V→ℝ) (P τ c a : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    Law (Option (Finset (ℙ K V))) :=
  finiteImageLaw (baseTapeMeasure U P τ R L₀) (scoredOutcome X U n Own Base P τ c a R)

end

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy MeasurePublicTable Metadata
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_BaseSmallLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

lemma incident_mk_pair (v : V) (hv : v≠0) (a : Dual K V) (ha : a≠0) :
    Incident (Projectivization.mk K v hv) (Projectivization.mk K a ha) ↔ a v=0 := by
  rw [incident_mk_right]
  obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  rw [←hc]
  simp only [LinearMap.map_smul_of_tower,Units.smul_def,smul_eq_mul,mul_eq_zero,Units.ne_zero,false_or]

end

open Module
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma incident_bidual (x : ℙ K V) (f : ℙ K (Dual K V)) :
    Incident f (bidualPoint x) ↔ Incident x f := by
  induction x using Projectivization.ind with | h v hv =>
  induction f using Projectivization.ind with | h a ha =>
  change Incident (Projectivization.mk K a ha)
    (Projectivization.map (Module.evalEquiv K V).toLinearMap (Module.evalEquiv K V).injective
      (Projectivization.mk K v hv)) ↔ _
  rw [Projectivization.map_mk,incident_mk_pair,incident_mk_pair]
  rfl

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_DimensionTwoOriented
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

noncomputable def twoOrientedLaw (S U : Finset (ℙ K V))
    (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty)
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) : Law (Option (Finset (ℙ K V))) :=
  if S.card≤T.card then baseCaptureLaw S U P τ R L₀ else
    optionCompose (baseCaptureLaw T UT P τ R L₀)
      (nextCapLaw S U T UT hT (reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card)))
        (Nat.card K) ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^3/T.card)
        ((T.card:ℝ)*Real.exp (2*P)))

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_GeometricRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveRestriction

section
open Module
open scoped LinearAlgebra.Projectivization Classical
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

noncomputable def image (f : V→ₗ[K]W) (p : Domain f) : ℙ K W :=
  Projectivization.mk K (f p.val.rep) p.property

lemma image_eq_iff (f : V→ₗ[K]W) (p : Domain f) (b : ℙ K W) :
    image f p=b ↔ ∃ a : Kˣ,a • f p.val.rep=b.rep := by
  change Projectivization.mk K (f p.val.rep) p.property=b ↔ _
  conv_lhs => rw [←b.mk_rep,eq_comm,Projectivization.mk_eq_mk_iff]

noncomputable def normalized (f : V→ₗ[K]W) (b : ℙ K W)
    (p : {p : Domain f // image f p=b}) : {v : V // f v=b.rep} :=
  ⟨(image_eq_iff f p.val b |>.mp p.property).choose • p.val.val.rep,by
    rw [LinearMap.map_smul_of_tower]
    exact (image_eq_iff f p.val b |>.mp p.property).choose_spec⟩

lemma normalized_nonzero (f : V→ₗ[K]W) (b : ℙ K W)
    (p : {p : Domain f // image f p=b}) : (normalized f b p).val≠0 := by
  intro h
  have hh := (normalized f b p).property
  rw [h,map_zero] at hh
  exact b.rep_nonzero hh.symm

end

open Module ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators

end SharpRamseyFive.ProjectiveRestriction

namespace SharpRamseyFive.ProjectiveRestriction

section
open Module ProjectiveIncidence DyadicLifts
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def flatDegree (U : Submodule K V) (S : Finset (ℙ K U))
    (p : ℙ K (Dual K V)) : ℕ :=
  (S.filter fun x=>Incident (Projectivization.map U.subtype U.injective_subtype x) p).card

noncomputable def goodLifts (U : Submodule K V) (S : Finset (ℙ K U))
    (T : Finset (ℙ K (Dual K V))) (κ : ℝ) : Finset (ℙ K (Dual K V)) :=
  T.filter fun p=>(flatDegree U S p:ℝ) ≤ κ*S.card

noncomputable def nonzeroLifts (U : Submodule K V) (T : Finset (ℙ K (Dual K V))) :
    Finset (Domain U.dualRestrict) := T.subtype fun p : ℙ K (Dual K V)=>U.dualRestrict p.rep≠0

end

open Module ProjectiveIncidence DyadicLifts
open scoped Classical LinearAlgebra.Projectivization BigOperators

end SharpRamseyFive.ProjectiveRestriction

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TwoAmbientCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def nextAmbientCapLaw (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty)
    (nA : ℕ) (q MA MB : ℝ) (Y : Option (Finset (ℙ K (Dual K V)))) :
    Law (Option (Finset (ℙ K V))) :=
  match Y with
  | none => pureLaw none
  | some Y => if hY : ValidCap B UB MB (UB∩Y) then
      ambientCapLaw Incident A UA (B∩(UB∩Y)) (UB∩Y)
        ((hY.source_nonempty hB).mono Finset.inter_subset_right) nA q MA
    else pureLaw none

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_LocalNodeLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def producedPairLaw (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty) (c : ℝ)
    (out : Option (Finset (ℙ K V))) :
    Law (Option (Finset (ℙ K (Dual K V))×Finset (ℙ K V))) :=
  match out with
  | none => pureLaw none
  | some W => if hW : W.Nonempty then
      let nA := reverseLength (Nat.card K) (Real.log ((UA.card:ℝ)/A.card))
      let nB := reverseLength (Nat.card K) (Real.log ((UB.card:ℝ)/B.card))
      let MA := (320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card
      let MB := (320/c+320)*(Nat.card K:ℝ)^5/A.card
      let firstCap := ambientCapLaw (fun b a=>Incident a b) B UB (A∩W) W hW nB (Nat.card K) MB
      map (adaptiveLaw firstCap (nextAmbientCapLaw A UA B UB hB nA (Nat.card K) MA MB)) pairOptions
    else pureLaw none

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_AmbientPairPublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def publicAmbientSecond (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V)))
    (H : ℕ) (n : Fin (H+1)) (q MA MB : ℝ)
    (Y : Option (Finset (ℙ K (Dual K V)))) (t : UniversalFresh (ℙ K (Dual K V)) H q) :
    Option (Finset (ℙ K V)) :=
  match Y with
  | none => none
  | some W => if _hW : ValidCap B UB MB (UB∩W) then
      (universalFreshEncoded Incident A UA (B∩(UB∩W)) (UB∩W) Finset.inter_subset_right H n q MA t).map
        (universalFreshDecoded Incident (UB∩W) H q t)
    else none
noncomputable def ambientPairTapeLaw (H : ℕ) (q : ℝ) : Law (AmbientPairTape K V H q) :=
  adaptiveLaw (universalFreshLaw (ℙ K V) H q) (fun _=>universalFreshLaw (ℙ K (Dual K V)) H q)
abbrev AmbientPairMessage (UB : Finset (ℙ K (Dual K V))) (W : Finset (ℙ K V))
    (H : ℕ) (q : ℝ) (t : AmbientPairTape K V H q) :=
  (m : UniversalFreshMessage W H q) × UniversalFreshMessage
    (UB∩universalFreshDecoded (fun b a=>Incident a b) W H q t.1 m) H q
noncomputable def ambientPairDecoded (UB : Finset (ℙ K (Dual K V))) (W : Finset (ℙ K V))
    (H : ℕ) (q : ℝ) (t : AmbientPairTape K V H q) (m : AmbientPairMessage UB W H q t) :
    Finset (ℙ K (Dual K V)) × Finset (ℙ K V) :=
  let Y := universalFreshDecoded (fun b a=>Incident a b) W H q t.1 m.1
  (Y,universalFreshDecoded Incident (UB∩Y) H q t.2 m.2)
noncomputable def ambientPairEncoded (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (W : Finset (ℙ K V))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB : ℝ) (t : AmbientPairTape K V H q) :
    Option (AmbientPairMessage UB W H q t) :=
  (universalFreshEncoded (fun b a=>Incident a b) B UB (A∩W) W Finset.inter_subset_right H nB q MB t.1).bind
    fun f=>let Y := universalFreshDecoded (fun b a=>Incident a b) W H q t.1 f
      if _hv : ValidCap B UB MB (UB∩Y) then
        (universalFreshEncoded Incident A UA (B∩(UB∩Y)) (UB∩Y) Finset.inter_subset_right H nA q MA t.2).map
          (fun g=>⟨f,g⟩)
      else none
noncomputable def ambientPairCost (UB : Finset (ℙ K (Dual K V))) (W : Finset (ℙ K V))
    (H : ℕ) (q : ℝ) (t : AmbientPairTape K V H q) (m : AmbientPairMessage UB W H q t) : ℝ :=
  universalFreshCost W H q m.1+
    universalFreshCost (UB∩universalFreshDecoded (fun b a=>Incident a b) W H q t.1 m.1) H q m.2

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_BaseFinitePublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def baseTableLaw (U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    Law (BaseTable U P τ) :=
  publicTableLaw (α:=BaseMessage U P τ) (β:=Finset (ℙ K V))
    (Ω:=BaseTape U P τ R) (baseTapeMeasure U P τ R L₀) (baseMessageDecoded U P τ R L₀)

noncomputable def baseTableEncoded (S U : Finset (ℙ K V)) (P τ : ℝ)
    (t : BaseTable U P τ) : Option (baseAlphabet U S.card P τ) :=
  let n : Fin (Fintype.card (ℙ K V)+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
  chooseMessage (fun (u : BaseTable U P τ) m=>
    let W := u ⟨n,m⟩
    W⊆U ∧ (W.card:ℝ)≤(S.card:ℝ)*Real.exp (2*P) ∧ (9/10:ℝ)*S.card≤((W∩S).card:ℝ)) t

noncomputable def baseFiniteEncoded (S U : Finset (ℙ K V)) (P τ : ℝ)
    (t : BaseTable U P τ) : Option (BaseMessage U P τ) :=
  let n : Fin (Fintype.card (ℙ K V)+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
  (baseTableEncoded S U P τ t).map (fun m=>⟨n,m⟩)

end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence Metadata FiniteEntropy MeasureTheory
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def scoredEncoded (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (σ P τ c a : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (code : TrainingCode V (listCap σ) (productCap σ) (Nat.card V))
    (t : BaseTape U P τ R) : Option (ScoredMessage U σ P τ) :=
  (chooseMessage (fun (u : BaseTape U P τ R)
      (m : Fin (sizeScoreCutoff U n P τ) × Fin (Fintype.card (ℙ K (Dual K V))+1)) =>
    let W := publicDecoded U (messageOwn code) (messageBase code L₀) m.2 (u n m.1)
    W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (a*P) ∧ c*X.card≤((W∩X).card:ℝ)) t).map
      (fun m=>⟨n,code,m⟩)

end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy Metadata
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def scoreTableLaw (U : Finset (ℙ K V)) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    Law (ScoreTable U σ P τ) :=
  publicTableLaw (Ω:=BaseTape U P τ R) (α:=ScoredMessage U σ P τ) (β:=Finset (ℙ K V))
    (baseTapeMeasure U P τ R L₀) (scoredMessageDecoded U σ P τ R L₀)

noncomputable def scoreFiniteEncoded (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (σ P τ c a : ℝ)
    (code : TrainingCode V (listCap σ) (productCap σ) (Nat.card V))
    (t : ScoreTable U σ P τ) : Option (ScoredMessage U σ P τ) :=
  (chooseMessage (fun (u : ScoreTable U σ P τ)
      (m : Fin (sizeScoreCutoff U n P τ) × Fin (Fintype.card (ℙ K (Dual K V))+1)) =>
    let W := u ⟨n,code,m⟩
    W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (a*P) ∧ c*X.card≤((W∩X).card:ℝ)) t).map
      (fun m=>⟨n,code,m⟩)

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ReversedBasePublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

noncomputable def reversedBaseDecoded (U : Finset (ℙ K V))
    (UT : Finset (ℙ K (Dual K V))) (P τ : ℝ) (H : ℕ) (q : ℝ)
    (t : ReversedBaseTape UT P τ H q) (m : ReversedBaseMessage UT P τ H q t) : Finset (ℙ K V) :=
  U∩universalFreshDecoded Incident (t.1 m.1) H q t.2 m.2

noncomputable def reversedBaseEncoded (S U : Finset (ℙ K V))
    (T UT : Finset (ℙ K (Dual K V))) (P τ : ℝ) (H : ℕ) (n : Fin (H+1)) (q MA MB : ℝ)
    (t : ReversedBaseTape UT P τ H q) : Option (ReversedBaseMessage UT P τ H q t) :=
  (baseFiniteEncoded T UT P τ t.1).bind fun m=>
    if _hv : ValidCap T UT MB (t.1 m) then
      (universalFreshEncoded Incident S U (T∩t.1 m) (t.1 m) Finset.inter_subset_right H n q MA t.2).map
        (fun f=>⟨m,f⟩)
    else none

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TwoFinitePublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

noncomputable def twoPublicLaw (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) (H : ℕ) (q : ℝ) : Law (TwoPublicTape U UT P τ H q) :=
  adaptiveLaw (baseTableLaw U P τ R L₀) (fun _=>
    adaptiveLaw (baseTableLaw UT P τ R L₀) (fun _=>universalFreshLaw (ℙ K (Dual K V)) H q))
noncomputable def twoPublicDecoded (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (H : ℕ) (q : ℝ) (t : TwoPublicTape U UT P τ H q) :
    TwoPublicMessage U UT P τ H q t→Finset (ℙ K V)
  | Sum.inl m => t.1 m
  | Sum.inr m => reversedBaseDecoded U UT P τ H q t.2 m
noncomputable def twoPublicEncoded (S U : Finset (ℙ K V))
    (T UT : Finset (ℙ K (Dual K V))) (P τ : ℝ) (H : ℕ) (n : Fin (H+1)) (q MA MB : ℝ)
    (t : TwoPublicTape U UT P τ H q) : Option (TwoPublicMessage U UT P τ H q t) :=
  if S.card≤T.card then (baseFiniteEncoded S U P τ t.1).map Sum.inl else
    (reversedBaseEncoded S U T UT P τ H n q MA MB t.2).map Sum.inr

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PlanePublicDefs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ProjectiveRestriction
open Module ProjectiveIncidence ProjectiveTraining ScoreGeometry FiniteEntropy
open DyadicLifts ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)]
variable (A : Submodule K V) [Fintype (ℙ K A)] [Fintype (ℙ K (Dual K A))]
  [Fintype (ℙ K (Dual K (Dual K A)))]
noncomputable def planeHidden (X : Finset (ℙ K V)) (T : Finset (ℙ K (Dual K V))) (τ : ℝ) (k : ℕ) :=
  restrictions (image A.dualRestrict)
    (nonzeroLifts A (goodLifts A (flatSection A X) T (Real.sqrt τ/Nat.card K))) k
noncomputable def planeEnclosure (UT : Finset (ℙ K (Dual K V))) (k : ℕ) :=
  enclosure (image A.dualRestrict) (nonzeroLifts A UT) (2^k)
abbrev PlanePublicTape (UX : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V))) (P τ : ℝ) (k : ℕ) :=
  TwoPublicTape (flatSection A UX) (planeEnclosure A UT k) P (Real.sqrt τ) (1000*(Nat.card K)^2) (Nat.card K)
abbrev PlanePublicMessage (UX : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V))) (P τ : ℝ) (k : ℕ)
    (t : PlanePublicTape A UX UT P τ k) :=
  TwoPublicMessage (flatSection A UX) (planeEnclosure A UT k) P (Real.sqrt τ) (1000*(Nat.card K)^2) (Nat.card K) t
noncomputable def planePublicLaw (UX : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) (k : ℕ) : Law (PlanePublicTape A UX UT P τ k) :=
  twoPublicLaw (flatSection A UX) (planeEnclosure A UT k) P (Real.sqrt τ) R L₀ (1000*(Nat.card K)^2) (Nat.card K)
noncomputable def planePublicDecoded (UX : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (k : ℕ) (t : PlanePublicTape A UX UT P τ k) (m : PlanePublicMessage A UX UT P τ k t) : Finset (ℙ K V) :=
  (twoPublicDecoded (flatSection A UX) (planeEnclosure A UT k) P (Real.sqrt τ) (1000*(Nat.card K)^2) (Nat.card K) t m).map (flatEmbedding A)
noncomputable def planePublicEncoded (X UX : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (k : ℕ) (t : PlanePublicTape A UX UT P τ k) : Option (PlanePublicMessage A UX UT P τ k t) :=
  let n := reverseLength (Nat.card K) (Real.log (((flatSection A UX).card:ℝ)/(flatSection A X).card))
  if hn : n≤1000*(Nat.card K)^2 then
    twoPublicEncoded (flatSection A X) (flatSection A UX) (planeHidden A X T τ k) (planeEnclosure A UT k)
      P (Real.sqrt τ) (1000*(Nat.card K)^2) ⟨n,Nat.lt_succ_of_le hn⟩ (Nat.card K)
      ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^3/(planeHidden A X T τ k).card)
      (((planeHidden A X T τ k).card:ℝ)*Real.exp (2*P)) t
  else none
noncomputable def planePublicCost (UX : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (k : ℕ) (t : PlanePublicTape A UX UT P τ k) (m : PlanePublicMessage A UX UT P τ k t) : ℝ :=
  twoPublicCost (flatSection A UX) (planeEnclosure A UT k) P (Real.sqrt τ) (1000*(Nat.card K)^2) (Nat.card K) t m

end SharpRamseyFive.ProjectiveRestriction

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ThreePublicDefs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining ProjectiveRestriction
open Metadata FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K : Type} [Field K] [Finite K] [Fintype K]
  [Fintype (ℙ K (Fin 4→K))] [Fintype (ℙ K (Dual K (Fin 4→K)))]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K A)]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K A))]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K (Dual K A)))]

noncomputable def ThreeLocalTape (U : Finset (ℙ K (Fin 4→K)))
    (UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) : ThreePublicIndex K σ→Type _
  | .inl _ => BaseTable U P τ
  | .inr (.inl _) => ScoreTable U σ P τ
  | .inr (.inr a) => PlanePublicTape (flatEnumeration a.1.1) U UT P τ a.2
noncomputable instance instFintypeThreeLocalTape (U : Finset (ℙ K (Fin 4→K)))
    (UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) (br : ThreePublicIndex K σ) :
    Fintype (ThreeLocalTape U UT σ P τ br) := by
  rcases br with b|b
  · dsimp only [ThreeLocalTape];infer_instance
  · rcases b with b|b <;> dsimp only [ThreeLocalTape] <;> infer_instance

noncomputable def ThreeLocalMessage (U : Finset (ℙ K (Fin 4→K)))
    (UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) :
    (br : ThreePublicIndex K σ)→ThreeLocalTape U UT σ P τ br→Type _
  | .inl _,_ => BaseMessage U P τ
  | .inr (.inl _),_ => ScoredMessage U σ P τ
  | .inr (.inr a),t => PlanePublicMessage (flatEnumeration a.1.1) U UT P τ a.2 t

noncomputable def threeLocalLaw (U : Finset (ℙ K (Fin 4→K)))
    (UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    (br : ThreePublicIndex K σ)→Law (ThreeLocalTape U UT σ P τ br)
  | .inl _ => baseTableLaw U P τ R L₀
  | .inr (.inl _) => scoreTableLaw U σ P τ R L₀
  | .inr (.inr a) => planePublicLaw (flatEnumeration a.1.1) U UT P τ R L₀ a.2

noncomputable def threeLocalDecoded (U : Finset (ℙ K (Fin 4→K)))
    (UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) :
    (br : ThreePublicIndex K σ)→(t : ThreeLocalTape U UT σ P τ br)→
      ThreeLocalMessage U UT σ P τ br t→Finset (ℙ K (Fin 4→K))
  | .inl _,t,m => t m
  | .inr (.inl _),t,m => t m
  | .inr (.inr a),t,m => planePublicDecoded (flatEnumeration a.1.1) U UT P τ a.2 t m

noncomputable def threeLocalEncoded (X U : Finset (ℙ K (Fin 4→K)))
    (T UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) :
    (br : ThreePublicIndex K σ)→(t : ThreeLocalTape U UT σ P τ br)→
      Option (ThreeLocalMessage U UT σ P τ br t)
  | .inl _,t => baseFiniteEncoded X U P τ t
  | .inr (.inl c),t => scoreFiniteEncoded X U c.1 σ P τ (9/20) 10 c.2 t
  | .inr (.inr a),t => planePublicEncoded (flatEnumeration a.1.1) X U T UT P τ a.2 t

noncomputable def threeLocalCost (U : Finset (ℙ K (Fin 4→K)))
    (UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) :
    (br : ThreePublicIndex K σ)→(t : ThreeLocalTape U UT σ P τ br)→
      ThreeLocalMessage U UT σ P τ br t→ℝ
  | .inl _,_,m => baseFiniteCost U P τ m
  | .inr (.inl _),_,m => scoreFiniteCost U σ P τ m
  | .inr (.inr a),t,m => planePublicCost (flatEnumeration a.1.1) U UT P τ a.2 t m

abbrev ThreePublicTape (U : Finset (ℙ K (Fin 4→K)))
    (UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) :=
  (br : ThreePublicIndex K σ)→ThreeLocalTape U UT σ P τ br
noncomputable def threePublicLaw (U : Finset (ℙ K (Fin 4→K)))
    (UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    Law (ThreePublicTape U UT σ P τ) := piLaw (threeLocalLaw U UT σ P τ R L₀)
abbrev ThreePublicMessage (U : Finset (ℙ K (Fin 4→K)))
    (UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) (t : ThreePublicTape U UT σ P τ) :=
  (br : ThreePublicIndex K σ)×ThreeLocalMessage U UT σ P τ br (t br)
noncomputable def threePublicEncoded (X U : Finset (ℙ K (Fin 4→K)))
    (T UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) (br : ThreePublicIndex K σ)
    (t : ThreePublicTape U UT σ P τ) : Option (ThreePublicMessage U UT σ P τ t) :=
  branchEncoded br (threeLocalEncoded X U T UT σ P τ br) t
noncomputable def threePublicDecoded (U : Finset (ℙ K (Fin 4→K)))
    (UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ)
    (t : ThreePublicTape U UT σ P τ) (m : ThreePublicMessage U UT σ P τ t) : Finset (ℙ K (Fin 4→K)) :=
  branchDecoded (threeLocalDecoded U UT σ P τ) t m
noncomputable def threePublicCost (U : Finset (ℙ K (Fin 4→K)))
    (UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ)
    (t : ThreePublicTape U UT σ P τ) (m : ThreePublicMessage U UT σ P τ t) : ℝ :=
  Real.log (Fintype.card (ThreePublicIndex K σ):ℝ)+threeLocalCost U UT σ P τ m.1 (t m.1) m.2

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ThreePublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining Metadata FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K : Type} [Field K] [Finite K] [Fintype K]
  [Fintype (ℙ K (Fin 4→K))] [Fintype (ℙ K (Dual K (Fin 4→K)))]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K A)]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K A))]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K (Dual K A)))]

def ThreeCertified (X U : Finset (ℙ K (Fin 4→K)))
    (T UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (br : ThreePublicIndex K σ) : Prop :=
  let p := map (threePublicLaw U UT σ P τ R L₀)
    (fun t=>(threePublicEncoded X U T UT σ P τ br t).map (threePublicDecoded U UT σ P τ t))
  p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
  (∀W,0<p (some W)→W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P) ∧
    (9/1000:ℝ)*X.card≤(W∩X).card) ∧
  (∀t m,threePublicEncoded X U T UT σ P τ br t=some m →
    threePublicCost U UT σ P τ t m≤
    4100*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P))

noncomputable def threeCertifiedBranch (X U : Finset (ℙ K (Fin 4→K)))
    (T UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) : ThreePublicIndex K σ :=
  if h : ∃br,ThreeCertified X U T UT σ P τ R L₀ br then h.choose else .inl ()

noncomputable def threeCertifiedEncoded (X U : Finset (ℙ K (Fin 4→K)))
    (T UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (t : ThreePublicTape U UT σ P τ) : Option (ThreePublicMessage U UT σ P τ t) :=
  threePublicEncoded X U T UT σ P τ (threeCertifiedBranch X U T UT σ P τ R L₀) t
noncomputable def threeCertifiedLaw (X U : Finset (ℙ K (Fin 4→K)))
    (T UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) : Law (Option (Finset (ℙ K (Fin 4→K)))) :=
  map (threePublicLaw U UT σ P τ R L₀)
    (fun t=>(threeCertifiedEncoded X U T UT σ P τ R L₀ t).map (threePublicDecoded U UT σ P τ t))
end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ThreeCoordinateCertified
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining Metadata Filter ParameterHierarchy FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [Fintype K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Fin 4→K))] [Fintype (ℙ K (Dual K (Fin 4→K)))]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K A)]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K A))]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K (Dual K A)))]

abbrev ThreeCoordinateTape (e : V≃ₗ[K](Fin 4→K))
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V))) (σ P τ : ℝ) :=
  ThreePublicTape (U.map (projectiveEquiv e).toEmbedding)
    (UT.map (projectiveEquiv e.symm.dualMap).toEmbedding) σ P τ
abbrev ThreeCoordinateMessage (e : V≃ₗ[K](Fin 4→K))
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V))) (σ P τ : ℝ)
    (t : ThreeCoordinateTape e U UT σ P τ) :=
  ThreePublicMessage (U.map (projectiveEquiv e).toEmbedding)
    (UT.map (projectiveEquiv e.symm.dualMap).toEmbedding) σ P τ t
noncomputable def threeCoordinatePublicLaw (e : V≃ₗ[K](Fin 4→K))
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    Law (ThreeCoordinateTape e U UT σ P τ) :=
  threePublicLaw (U.map (projectiveEquiv e).toEmbedding)
    (UT.map (projectiveEquiv e.symm.dualMap).toEmbedding) σ P τ R L₀
noncomputable def threeCoordinateEncoded (e : V≃ₗ[K](Fin 4→K))
    (X U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (t : ThreeCoordinateTape e U UT σ P τ) : Option (ThreeCoordinateMessage e U UT σ P τ t) :=
  threeCertifiedEncoded (X.map (projectiveEquiv e).toEmbedding) (U.map (projectiveEquiv e).toEmbedding)
    (T.map (projectiveEquiv e.symm.dualMap).toEmbedding) (UT.map (projectiveEquiv e.symm.dualMap).toEmbedding)
    σ P τ R L₀ t
noncomputable def threeCoordinateDecoded (e : V≃ₗ[K](Fin 4→K))
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V))) (σ P τ : ℝ)
    (t : ThreeCoordinateTape e U UT σ P τ) (m : ThreeCoordinateMessage e U UT σ P τ t) : Finset (ℙ K V) :=
  (threePublicDecoded (U.map (projectiveEquiv e).toEmbedding)
    (UT.map (projectiveEquiv e.symm.dualMap).toEmbedding) σ P τ t m).map (projectiveEquiv e).symm.toEmbedding
noncomputable def threeCoordinateCost (e : V≃ₗ[K](Fin 4→K))
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V))) (σ P τ : ℝ)
    (t : ThreeCoordinateTape e U UT σ P τ) (m : ThreeCoordinateMessage e U UT σ P τ t) : ℝ :=
  threePublicCost (U.map (projectiveEquiv e).toEmbedding)
    (UT.map (projectiveEquiv e.symm.dualMap).toEmbedding) σ P τ t m
noncomputable def threeCoordinateCertifiedLaw (e : V≃ₗ[K](Fin 4→K)) (σ : ℝ)
    (X U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) : Law (Option (Finset (ℙ K V))) :=
  map (threeCoordinatePublicLaw e U UT σ P τ R L₀)
    (fun t=>(threeCoordinateEncoded e X U T UT σ P τ R L₀ t).map (threeCoordinateDecoded e U UT σ P τ t))
end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def publicGeneralReverseResult (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (_hB : B.Nonempty)
    (H : ℕ) (n : Fin (H+1)) (q MA MB c : ℝ) (_hc : 0 < c)
    (Y : Option (Finset (ℙ K (Dual K V)))) (t : UniversalFresh (ℙ K (Dual K V)) H q) :
    Option (Finset (ℙ K V)) :=
  match Y with
  | none => none
  | some W => if _hW : CaptureBound B UB c MB W then
      (universalFreshEncoded Incident A UA (B∩W) W Finset.inter_subset_right H n q MA t).map
        (fun m=>UA∩universalFreshDecoded Incident W H q t m)
    else none

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_GeneralReversedCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V Ω : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] [Fintype Ω]

noncomputable def generalReversedDecoded (M : Ω→Type*) (dec : ∀t,M t→Finset (ℙ K (Dual K V)))
    (U : Finset (ℙ K V)) (H : ℕ) (q : ℝ) (t : GeneralReversedTape Ω K V H q)
    (m : GeneralReversedMessage M dec H q t) : Finset (ℙ K V) :=
  U∩universalFreshDecoded Incident (dec t.1 m.1) H q t.2 m.2
noncomputable def generalReversedEncoded (M : Ω→Type*) (dec : ∀t,M t→Finset (ℙ K (Dual K V)))
    (enc : ∀t,Option (M t)) (S U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V)))
    (H : ℕ) (n : Fin (H+1)) (q MA MB c : ℝ) (t : GeneralReversedTape Ω K V H q) :
    Option (GeneralReversedMessage M dec H q t) :=
  (enc t.1).bind fun m=>if _hv : CaptureBound T UT c MB (dec t.1 m) then
    (universalFreshEncoded Incident S U (T∩dec t.1 m) (dec t.1 m) Finset.inter_subset_right H n q MA t.2).map
      (fun f=>⟨m,f⟩) else none
end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining Metadata FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal

attribute [instance] FinitePredictor.tapeFintype FinitePredictor.messageFintype

noncomputable def FinitePredictor.output {A B : Type} [Fintype A] [Fintype B]
    (p : FinitePredictor A B) (S : Finset A) (T : Finset B) : Law (Option (Finset A)) :=
  map p.tapeLaw (fun t=>(p.encoded S T t).map (p.decoded t))

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable instance instFintypeThreeLocalMessage {K : Type} [Field K] [Finite K] [Fintype K]
    [Fintype (ℙ K (Fin 4→K))] [Fintype (ℙ K (Dual K (Fin 4→K)))]
    [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K A)]
    [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K A))]
    [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K (Dual K A)))]
    (U : Finset (ℙ K (Fin 4→K))) (UT : Finset (ℙ K (Dual K (Fin 4→K))))
    (σ P τ : ℝ) (br : ThreePublicIndex K σ) (t : ThreeLocalTape U UT σ P τ br) :
    Fintype (ThreeLocalMessage U UT σ P τ br t) := by
  rcases br with b|b
  · dsimp only [ThreeLocalMessage];infer_instance
  · rcases b with b|b <;> dsimp only [ThreeLocalMessage] <;> infer_instance

noncomputable def threeFinitePredictor (hd : finrank K V=4) (σ : ℝ)
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) : FinitePredictor (ℙ K V) (ℙ K (Dual K V)) := by
  letI : Fintype K := Fintype.ofFinite _
  letI : Finite (Dual K (Fin 4→K)) := Module.finite_of_finite K
  letI : Fintype (ℙ K (Fin 4→K)) := Fintype.ofFinite _
  letI : Fintype (ℙ K (Dual K (Fin 4→K))) := Fintype.ofFinite _
  letI (A : Submodule K (Fin 4→K)) : Finite (Dual K A) := Module.finite_of_finite K
  letI (A : Submodule K (Fin 4→K)) : Finite (Dual K (Dual K A)) := Module.finite_of_finite K
  letI (A : Submodule K (Fin 4→K)) : Fintype (ℙ K A) := Fintype.ofFinite _
  letI (A : Submodule K (Fin 4→K)) : Fintype (ℙ K (Dual K A)) := Fintype.ofFinite _
  letI (A : Submodule K (Fin 4→K)) : Fintype (ℙ K (Dual K (Dual K A))) := Fintype.ofFinite _
  let e := LinearEquiv.ofFinrankEq V (Fin 4→K) (by rw [Module.finrank_pi,Fintype.card_fin,hd])
  exact {
    Tape := ThreeCoordinateTape e U UT σ P τ
    tapeFintype := inferInstance
    Message := ThreeCoordinateMessage e U UT σ P τ
    messageFintype := fun _=>inferInstance
    tapeLaw := threeCoordinatePublicLaw e U UT σ P τ R L₀
    decoded := threeCoordinateDecoded e U UT σ P τ
    encoded := fun S T=>threeCoordinateEncoded e S U T UT σ P τ R L₀
    cost := threeCoordinateCost e U UT σ P τ }
end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ThreeFinitePredictor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

noncomputable def orientedFinitePredictor
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (d H : ℕ) (q P c B : ℝ) : FinitePredictor (ℙ K V) (ℙ K (Dual K V)) where
  Tape := f.Tape × GeneralReversedTape r.Tape K V H q
  tapeFintype := inferInstance
  Message := fun t=>f.Message t.1 ⊕ GeneralReversedMessage r.Message r.decoded H q t.2
  messageFintype := fun _=>inferInstance
  tapeLaw := adaptiveLaw f.tapeLaw (fun _=>adaptiveLaw r.tapeLaw (fun _=>universalFreshLaw (ℙ K (Dual K V)) H q))
  decoded := fun t m=>match m with
    | .inl m=>f.decoded t.1 m
    | .inr m=>generalReversedDecoded r.Message r.decoded U H q t.2 m
  encoded := fun S T t=>if S.card≤T.card then (f.encoded S T t.1).map Sum.inl else
    if hn : reverseLength q (Real.log ((U.card:ℝ)/S.card))≤H then
      (generalReversedEncoded r.Message r.decoded (r.encoded T (S.map bidualPoint.toEmbedding)) S U T UT H
        ⟨_,Nat.lt_succ_of_le hn⟩ q ((320/c+320)*q^d/T.card) ((T.card:ℝ)*Real.exp (B*P)) c t.2).map Sum.inr
    else none
  cost := fun t m=>Real.log 2 + match m with
    | .inl m=>f.cost t.1 m
    | .inr m=>generalReversedCost r.Message r.decoded r.cost H q t.2 m

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ThreeFiniteOriented
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

noncomputable def threeOrientedFinitePredictor (hd : finrank K V=4) (σ : ℝ)
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) : FinitePredictor (ℙ K V) (ℙ K (Dual K V)) :=
  orientedFinitePredictor (threeFinitePredictor hd σ U UT P τ R L₀)
    (threeFinitePredictor (Subspace.dual_finrank_eq.trans hd) σ UT
      (U.map bidualPoint.toEmbedding) P τ R L₀)
    U UT 4 (1000*(Nat.card K)^2) (Nat.card K) P (9/1000) 10

end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open FiniteEntropy
open scoped Classical
variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
noncomputable def FinitePredictor.transform (p : FinitePredictor A B) (e : A↪C)
    (inputs : Finset C→Finset D→Finset A×Finset B) : FinitePredictor C D where
  Tape := p.Tape
  tapeFintype := p.tapeFintype
  Message := p.Message
  messageFintype := p.messageFintype
  tapeLaw := p.tapeLaw
  decoded := fun t m=>(p.decoded t m).map e
  encoded := fun S T=>p.encoded (inputs S T).1 (inputs S T).2
  cost := p.cost
end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ProjectiveRestriction
open Module ProjectiveIncidence ProjectiveTraining ScoreGeometry FiniteEntropy
open DyadicLifts ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def threeFlatFinitePredictor (A : Submodule K V) (hA : finrank K A=4) (σ : ℝ)
    (UX : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (τ P : ℝ) (R : ℕ) (L₀ : ℝ≥0) (k : ℕ) : FinitePredictor (ℙ K V) (ℙ K (Dual K V)) := by
  letI : Finite A := Module.finite_of_finite K
  letI : Finite (Dual K A) := Module.finite_of_finite K
  letI : Finite (Dual K (Dual K A)) := Module.finite_of_finite K
  letI : Fintype (ℙ K A) := Fintype.ofFinite _
  letI : Fintype (ℙ K (Dual K A)) := Fintype.ofFinite _
  letI : Fintype (ℙ K (Dual K (Dual K A))) := Fintype.ofFinite _
  exact (threeOrientedFinitePredictor hA σ (flatSection A UX) (planeEnclosure A UT k)
    P (Real.sqrt τ) R L₀).transform (flatEmbedding A)
      (fun X T=>(flatSection A X,planeHidden A X T τ k))

end SharpRamseyFive.ProjectiveRestriction

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FiniteFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open FiniteEntropy
open scoped Classical
variable {A B I : Type} [Fintype A] [Fintype B] [Fintype I]
noncomputable def FinitePredictor.family (p : I→FinitePredictor A B)
    (choose : Finset A→Finset B→I) : FinitePredictor A B where
  Tape := ∀i,(p i).Tape
  tapeFintype := inferInstance
  Message := fun t=>(i : I)×(p i).Message (t i)
  messageFintype := fun _=>inferInstance
  tapeLaw := piLaw (fun i=>(p i).tapeLaw)
  decoded := branchDecoded (fun i=>(p i).decoded)
  encoded := fun S T=>branchEncoded (choose S T) ((p (choose S T)).encoded S T)
  cost := fun t m=>Real.log (Fintype.card I:ℝ)+(p m.1).cost (t m.1) m.2
end

section
open Module ProjectiveIncidence ProjectiveTraining ProjectiveRestriction
open Metadata FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K : Type} [Field K] [Finite K] [Fintype K]
  [Fintype (ℙ K (Fin 5→K))] [Fintype (ℙ K (Dual K (Fin 5→K)))]
  [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K A)]
  [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K (Dual K A))]
  [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K (Dual K (Dual K A)))]

noncomputable def fourLocalPredictor (U : Finset (ℙ K (Fin 5→K)))
    (UT : Finset (ℙ K (Dual K (Fin 5→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    FourPublicIndex K σ→FinitePredictor (ℙ K (Fin 5→K)) (ℙ K (Dual K (Fin 5→K)))
  | .inl _ => {
      Tape := BaseTable U P τ
      tapeFintype := inferInstance
      Message := fun _=>BaseMessage U P τ
      messageFintype := fun _=>inferInstance
      tapeLaw := baseTableLaw U P τ R L₀
      decoded := fun t=>t
      encoded := fun X _=>baseFiniteEncoded X U P τ
      cost := fun _=>baseFiniteCost U P τ }
  | .inr (.inl c) => {
      Tape := ScoreTable U σ P τ
      tapeFintype := inferInstance
      Message := fun _=>ScoredMessage U σ P τ
      messageFintype := fun _=>inferInstance
      tapeLaw := scoreTableLaw U σ P τ R L₀
      decoded := fun t=>t
      encoded := fun X _=>scoreFiniteEncoded X U c.2.1 σ P τ (if c.1 then 9/20 else 9/40) 10 c.2.2
      cost := fun _=>scoreFiniteCost U σ P τ }
  | .inr (.inr (.inl a)) => {
      Tape := PlanePublicTape (flatEnumeration a.1.1) U UT P τ a.2
      tapeFintype := inferInstance
      Message := PlanePublicMessage (flatEnumeration a.1.1) U UT P τ a.2
      messageFintype := fun _=>inferInstance
      tapeLaw := planePublicLaw (flatEnumeration a.1.1) U UT P τ R L₀ a.2
      decoded := planePublicDecoded (flatEnumeration a.1.1) U UT P τ a.2
      encoded := fun X T=>planePublicEncoded (flatEnumeration a.1.1) X U T UT P τ a.2
      cost := planePublicCost (flatEnumeration a.1.1) U UT P τ a.2 }
  | .inr (.inr (.inr a)) => threeFlatFinitePredictor (flatEnumeration a.1.1)
      (flatIndices_rank 4 a.1.1 a.1.2) σ U UT τ P R L₀ a.2
end

section
open Module ProjectiveIncidence ProjectiveTraining Metadata FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K : Type} [Field K] [Finite K] [Fintype K]
  [Fintype (ℙ K (Fin 5→K))] [Fintype (ℙ K (Dual K (Fin 5→K)))]
  [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K A)]
  [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K (Dual K A))]
  [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K (Dual K (Dual K A)))]

def FourCertified (X U : Finset (ℙ K (Fin 5→K)))
    (T UT : Finset (ℙ K (Dual K (Fin 5→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (br : FourPublicIndex K σ) : Prop :=
  let pred := fourLocalPredictor U UT σ P τ R L₀ br
  let p := pred.output X T
  p none≤3*Real.exp (-(Nat.card K:ℝ)) ∧
  (∀W,0<p (some W)→W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P) ∧
    (9/100000:ℝ)*X.card≤(W∩X).card) ∧
  (∀t m,pred.encoded X T t=some m→pred.cost t m≤
    30000*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P))
noncomputable def fourCertifiedBranch (X U : Finset (ℙ K (Fin 5→K)))
    (T UT : Finset (ℙ K (Dual K (Fin 5→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) : FourPublicIndex K σ :=
  if h : ∃br,FourCertified X U T UT σ P τ R L₀ br then h.choose else .inl ()
noncomputable def fourCertifiedPredictor (U : Finset (ℙ K (Fin 5→K)))
    (UT : Finset (ℙ K (Dual K (Fin 5→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    FinitePredictor (ℙ K (Fin 5→K)) (ℙ K (Dual K (Fin 5→K))) :=
  FinitePredictor.family (fourLocalPredictor U UT σ P τ R L₀)
    (fun X T=>fourCertifiedBranch X U T UT σ P τ R L₀)
end

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy MeasurePublicTable Metadata FiniteEntropy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FourFinitePredictor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining Metadata Filter ParameterHierarchy FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def fourFinitePredictor (hd : finrank K V=5) (σ : ℝ)
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) : FinitePredictor (ℙ K V) (ℙ K (Dual K V)) := by
  letI : Fintype K := Fintype.ofFinite _
  letI : Finite (Dual K (Fin 5→K)) := Module.finite_of_finite K
  letI : Fintype (ℙ K (Fin 5→K)) := Fintype.ofFinite _
  letI : Fintype (ℙ K (Dual K (Fin 5→K))) := Fintype.ofFinite _
  letI (A : Submodule K (Fin 5→K)) : Finite (Dual K A) := Module.finite_of_finite K
  letI (A : Submodule K (Fin 5→K)) : Finite (Dual K (Dual K A)) := Module.finite_of_finite K
  letI (A : Submodule K (Fin 5→K)) : Fintype (ℙ K A) := Fintype.ofFinite _
  letI (A : Submodule K (Fin 5→K)) : Fintype (ℙ K (Dual K A)) := Fintype.ofFinite _
  letI (A : Submodule K (Fin 5→K)) : Fintype (ℙ K (Dual K (Dual K A))) := Fintype.ofFinite _
  let e := LinearEquiv.ofFinrankEq V (Fin 5→K) (by rw [Module.finrank_pi,Fintype.card_fin,hd])
  exact (fourCertifiedPredictor (U.map (projectiveEquiv e).toEmbedding)
    (UT.map (projectiveEquiv e.symm.dualMap).toEmbedding) σ P τ R L₀).transform
      (projectiveEquiv e).symm.toEmbedding
      (fun X T=>(X.map (projectiveEquiv e).toEmbedding,T.map (projectiveEquiv e.symm.dualMap).toEmbedding))

end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

abbrev FiniteNodeTape (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V))) (H : ℕ) (q : ℝ) :=
  pred.Tape × AmbientPairTape K V H q
noncomputable def finiteNodeTapeLaw (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V))) (H : ℕ) (q : ℝ) :
    Law (FiniteNodeTape pred H q) :=
  adaptiveLaw pred.tapeLaw (fun _=>ambientPairTapeLaw H q)
abbrev FiniteNodeMessage (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (UB : Finset (ℙ K (Dual K V))) (H : ℕ) (q : ℝ) (t : FiniteNodeTape pred H q) :=
  (m : pred.Message t.1) × AmbientPairMessage UB (pred.decoded t.1 m) H q t.2
noncomputable def finiteNodeDecoded (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (UB : Finset (ℙ K (Dual K V))) (H : ℕ) (q : ℝ) (t : FiniteNodeTape pred H q)
    (m : FiniteNodeMessage pred UB H q t) : Finset (ℙ K (Dual K V)) × Finset (ℙ K V) :=
  ambientPairDecoded UB (pred.decoded t.1 m.1) H q t.2 m.2
noncomputable def finiteNodeEncoded (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB c M : ℝ) (t : FiniteNodeTape pred H q) :
    Option (FiniteNodeMessage pred UB H q t) :=
  (pred.encoded A B t.1).bind fun m=>
    if _hc : CaptureBound A UA c M (pred.decoded t.1 m) then
      (ambientPairEncoded A UA B UB (pred.decoded t.1 m) H nA nB q MA MB t.2).map (fun f=>⟨m,f⟩)
    else none
noncomputable def finiteNodeCost (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (UB : Finset (ℙ K (Dual K V))) (H : ℕ) (q : ℝ) (t : FiniteNodeTape pred H q)
    (m : FiniteNodeMessage pred UB H q t) : ℝ :=
  pred.cost t.1 m.1+ambientPairCost UB (pred.decoded t.1 m.1) H q t.2 m.2
noncomputable def finiteNodeNextOut (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB c M : ℝ)
    (W : Option (Finset (ℙ K V))) (t : AmbientPairTape K V H q) :
    Option (Finset (ℙ K (Dual K V))×Finset (ℙ K V)) :=
  W.bind fun W=>if _hc : CaptureBound A UA c M W then
    (ambientPairEncoded A UA B UB W H nA nB q MA MB t).map (ambientPairDecoded UB W H q t)
    else none
noncomputable def finiteNodeNextLaw (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB c M : ℝ)
    (W : Option (Finset (ℙ K V))) : Law (Option (Finset (ℙ K (Dual K V))×Finset (ℙ K V))) :=
  map (ambientPairTapeLaw H q) (finiteNodeNextOut A UA B UB H nA nB q MA MB c M W)
noncomputable def finiteNodeOutput (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB c M : ℝ) :
    Law (Option (Finset (ℙ K (Dual K V))×Finset (ℙ K V))) :=
  map (finiteNodeTapeLaw pred H q) (fun t=>
    (finiteNodeEncoded pred A UA B UB H nA nB q MA MB c M t).map (finiteNodeDecoded pred UB H q t))

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_GuardedNodeSent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

abbrev OrientedNodeTape
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V)))) (H : ℕ) (q : ℝ) :=
  FiniteNodeTape f H q × FiniteNodeTape r H q
noncomputable instance orientedNodeTapeFintype
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V)))) (H : ℕ) (q : ℝ) :
    Fintype (OrientedNodeTape f r H q) := by
  exact @instFintypeProd (FiniteNodeTape f H q) (FiniteNodeTape r H q) inferInstance inferInstance
abbrev OrientedNodeMessage
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (UA : Finset (ℙ K V)) (UB : Finset (ℙ K (Dual K V))) (H : ℕ) (q : ℝ)
    (t : OrientedNodeTape f r H q) :=
  FiniteNodeMessage f UB H q t.1 ⊕ FiniteNodeMessage r (UA.map bidualPoint.toEmbedding) H q t.2
noncomputable def orientedNodeTapeLaw
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V)))) (H : ℕ) (q : ℝ) :
    Law (OrientedNodeTape f r H q) :=
  adaptiveLaw (finiteNodeTapeLaw f H q) (fun _=>finiteNodeTapeLaw r H q)
noncomputable def reverseNodePair
    (out : Finset (ℙ K (Dual K (Dual K V)))×Finset (ℙ K (Dual K V))) :
    Finset (ℙ K (Dual K V))×Finset (ℙ K V) :=
  (out.2,out.1.map bidualPoint.symm.toEmbedding)
noncomputable def orientedNodeDecoded
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (UA : Finset (ℙ K V)) (UB : Finset (ℙ K (Dual K V))) (H : ℕ) (q : ℝ)
    (t : OrientedNodeTape f r H q) (m : OrientedNodeMessage f r UA UB H q t) :
    Finset (ℙ K (Dual K V))×Finset (ℙ K V) := match m with
  | .inl m=>finiteNodeDecoded f UB H q t.1 m
  | .inr m=>reverseNodePair (finiteNodeDecoded r (UA.map bidualPoint.toEmbedding) H q t.2 m)
noncomputable def orientedNodeCost
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (UA : Finset (ℙ K V)) (UB : Finset (ℙ K (Dual K V))) (H : ℕ) (q : ℝ)
    (t : OrientedNodeTape f r H q) (m : OrientedNodeMessage f r UA UB H q t) : ℝ :=
  Real.log 2 + match m with
    | .inl m=>finiteNodeCost f UB H q t.1 m
    | .inr m=>finiteNodeCost r (UA.map bidualPoint.toEmbedding) H q t.2 m

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_PrimitiveMessageWeights
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedNodeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveRestriction ReverseCap
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal

def FinitePredictor.Normalized {A B : Type} [Fintype A] [Fintype B]
    (p : FinitePredictor A B) : Prop :=
  ∀t,(∑m : p.Message t,Real.exp (-p.cost t m))≤1

end SharpRamseyFive.ScoreGeometry
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_PivotTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.TreeCodec
open FiniteEntropy BinaryTree
open scoped Classical
universe u v w z
variable {A : Type u} {C : Type v} [Fintype C]
  (Ω : A→C→Type w) (M : ∀a c,Ω a c→Type z)

variable (left right : ∀a c t,M a c t→C)

noncomputable def tapeLaw [∀a c,Fintype (Ω a c)] (p : ∀a c,Law (Ω a c)) :
    (b : BinaryTree A)→Law (Tape Ω b)
  | .nil => pureLaw PUnit.unit
  | .node a l r => adaptiveLaw (piLaw (p a)) (fun _=>
      adaptiveLaw (tapeLaw p l) (fun _=>tapeLaw p r))
end SharpRamseyFive.TreeCodec

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OrientedPivotTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))

abbrev OrientedPivotTape (C : PivotContext K V) :=
  OrientedNodeTape (f C) (r C) (1000*(Nat.card K)^2) (Nat.card K)
abbrev OrientedPivotMessage (C : PivotContext K V) (ω : OrientedPivotTape f r C) :=
  OrientedNodeMessage (f C) (r C) C.1 C.2 (1000*(Nat.card K)^2) (Nat.card K) ω
noncomputable instance orientedPivotMessageFintype (C : PivotContext K V) (ω : OrientedPivotTape f r C) :
    Fintype (OrientedPivotMessage f r C ω) := by
  exact @instFintypeSum
    (FiniteNodeMessage (f C) C.2 (1000*(Nat.card K)^2) (Nat.card K) ω.1)
    (FiniteNodeMessage (r C) (C.1.map bidualPoint.toEmbedding) (1000*(Nat.card K)^2) (Nat.card K) ω.2)
    inferInstance inferInstance
noncomputable def orientedPivotLeft (C : PivotContext K V)
    (ω : OrientedPivotTape f r C) (m : OrientedPivotMessage f r C ω) : PivotContext K V :=
  (C.1∩(orientedNodeDecoded (f C) (r C) C.1 C.2 (1000*(Nat.card K)^2) (Nat.card K) ω m).2,C.2)
noncomputable def orientedPivotRight (C : PivotContext K V)
    (ω : OrientedPivotTape f r C) (m : OrientedPivotMessage f r C ω) : PivotContext K V :=
  (C.1,C.2∩(orientedNodeDecoded (f C) (r C) C.1 C.2 (1000*(Nat.card K)^2) (Nat.card K) ω m).1)

variable {ι : Type}
abbrev OrientedPivotTreeTape (b : BinaryTree ι) := TreeCodec.Tape (fun _ : ι=>OrientedPivotTape f r) b
abbrev OrientedPivotTreeMessage (b : BinaryTree ι) (ω : OrientedPivotTreeTape f r b)
    (C : PivotContext K V) :=
  TreeCodec.Message (fun _ : ι=>OrientedPivotTape f r) (fun _ : ι=>OrientedPivotMessage f r)
    (fun _ : ι=>orientedPivotLeft f r) (fun _ : ι=>orientedPivotRight f r) b ω C
noncomputable instance orientedPivotTreeTapeFintype (b : BinaryTree ι) :
    Fintype (OrientedPivotTreeTape f r b) := by
  exact @TreeCodec.tapeFintype ι (PivotContext K V) inferInstance
    (fun _ : ι=>OrientedPivotTape f r) (fun _ _=>orientedNodeTapeFintype _ _ _ _) b
noncomputable instance orientedPivotTreeMessageFintype (b : BinaryTree ι)
    (ω : OrientedPivotTreeTape f r b) (C : PivotContext K V) :
    Fintype (OrientedPivotTreeMessage f r b ω C) := by
  letI : ∀(_ : ι) C ω,Fintype (OrientedPivotMessage f r C ω) := fun _ _ _=>inferInstance
  exact TreeCodec.messageFintype (fun _ : ι=>OrientedPivotTape f r) (fun _ : ι=>OrientedPivotMessage f r)
    (fun _ : ι=>orientedPivotLeft f r) (fun _ : ι=>orientedPivotRight f r) b ω C
noncomputable def orientedPivotTreeLaw (b : BinaryTree ι) : Law (OrientedPivotTreeTape f r b) := by
  exact @TreeCodec.tapeLaw ι (PivotContext K V) inferInstance
    (fun _ : ι=>OrientedPivotTape f r) (fun _ _=>orientedNodeTapeFintype _ _ _ _)
    (fun _ C=>orientedNodeTapeLaw (f C) (r C) (1000*(Nat.card K)^2) (Nat.card K)) b

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_TreeWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
variable [Fintype (ℙ K (Dual K (Dual K V)))]
variable {ι : Type}
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
noncomputable def orientedPivotSlotCost (b : BinaryTree ι) (ω : OrientedPivotTreeTape f r b)
    (C : PivotContext K V) (m : OrientedPivotTreeMessage f r b ω C) : ℝ :=
  TreeCodec.slotCost (fun _ : ι=>OrientedPivotTape f r) (fun _ : ι=>OrientedPivotMessage f r)
    (fun _ : ι=>orientedPivotLeft f r) (fun _ : ι=>orientedPivotRight f r)
    (fun _ C t m=>orientedNodeCost (f C) (r C) C.1 C.2 (1000*(Nat.card K)^2) (Nat.card K) t m)
    b ω C m
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OrientedTreeDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
variable {I : Type}

def flagRectangle (A : Finset (ℙ K V)) (B : Finset (ℙ K (Dual K V))) :
    Finset ((ℙ K V)×(ℙ K (Dual K V))) := (A×ˢB).filter fun z=>Incident z.1 z.2

def orientedNodeDomain (C : PivotContext K V) (t : OrientedPivotTape f r C)
    (m : OrientedPivotMessage f r C t) :=
  let d:=orientedNodeDecoded (f C) (r C) C.1 C.2 (1000*(Nat.card K)^2) (Nat.card K) t m
  flagRectangle (C.1∩d.2) (C.2∩d.1)

def orientedPublicDomain (tree : BinaryTree I) (ω : OrientedPivotTreeTape f r tree)
    (C : PivotContext K V) (m : OrientedPivotTreeMessage f r tree ω C) (j : Address tree) :=
  (decodedAt (fun _ : I=>OrientedPivotTape f r) (fun _ : I=>OrientedPivotMessage f r)
    (fun _=>orientedPivotLeft f r) (fun _=>orientedPivotRight f r)
    (fun _=>orientedNodeDomain f r) tree ω C m j).getD ∅

end
end

open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))

abbrev VariableTreeTape (w : ℕ) := ∀ m : Fin (w+1),OrientedPivotTreeTape f r (finiteBalanced m.val)

def variableTreeLaw (w : ℕ) : Law (VariableTreeTape f r w) :=
  piLaw (fun m : Fin (w+1)=>orientedPivotTreeLaw f r (finiteBalanced m.val))

abbrev VariableTreeMessage {w : ℕ} (t : VariableTreeTape f r w) (C : PivotContext K V) :=
  (m : Fin (w+1)) × OrientedPivotTreeMessage f r (finiteBalanced m.val) (t m) C

def variableTreeCost {w : ℕ} (t : VariableTreeTape f r w) (C : PivotContext K V)
    (a : VariableTreeMessage f r t C) : ℝ :=
  Real.log (w+1)+orientedPivotSlotCost f r (finiteBalanced a.1.val) (t a.1) C a.2

def variableTreeDomain {w : ℕ} (t : VariableTreeTape f r w) (C : PivotContext K V)
    (a : VariableTreeMessage f r t C) (j : Fin (w+1)) : Finset ((ℙ K V)×(ℙ K (Dual K V))) :=
  if h : j.val<a.1.val then
    orientedPublicDomain f r (finiteBalanced a.1.val) (t a.1) C a.2
      ((finiteRankEquiv a.1.val).symm ⟨j.val,h⟩)
  else ∅

end

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_EmptyVariableTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
def emptyTreeMessage {I : Type} (b : BinaryTree I) (h : b=.nil)
    (t : OrientedPivotTreeTape f r b) (C : PivotContext K V) : OrientedPivotTreeMessage f r b t C := by
  subst b
  exact PUnit.unit

def variableTreeEmpty {w : ℕ} (t : VariableTreeTape f r w) (C : PivotContext K V) :
    VariableTreeMessage f r t C :=
  ⟨⟨0,Nat.zero_lt_succ w⟩,emptyTreeMessage f r (finiteBalanced 0)
    (by simp [finiteBalanced,balanced,BinaryTree.map]) _ C⟩
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_LogContractionDrop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open scoped BigOperators Classical

theorem finite_scan_bound {Y : Type*} [DecidableEq Y]
    (S : ℕ → Fin 5 → Finset Y) (chosen : ℕ → Option (Fin 5))
    (N : ℕ) (δ : ℝ) (hδ : 0<δ)
    (hmono : ∀ i<N,∀ j,S (i+1) j⊆S i j)
    (hchosen : ∀ i<N,∀ j,chosen i=some j →
      (S i j).Nonempty ∧ ((S (i+1) j).card:ℝ)≤(1-δ)*(S i j).card) :
    (((Finset.range N).filter fun i => (chosen i).isSome).card:ℝ)*(δ/2)≤
      ∑ j:Fin 5,Real.log (1+(S 0 j).card) := by
  let Φ : ℕ → ℝ:=fun i => ∑ j:Fin 5,Real.log (1+(S i j).card)
  let e : ℕ → ℝ:=fun i => if (chosen i).isSome then δ/2 else 0
  have hd : ∀ i<N,Φ (i+1)≤Φ i-e i := by
    intro i hi
    have hj (j : Fin 5) : Real.log (1+(S (i+1) j).card)≤Real.log (1+(S i j).card) := by
      apply Real.log_le_log (by positivity)
      have hh : ((S (i+1) j).card:ℝ)≤(S i j).card := by exact_mod_cast Finset.card_le_card (hmono i hi j)
      linarith
    cases hc : chosen i with
    | none =>
      simp only [e,hc,Option.isSome_none,Bool.false_eq_true,ite_false,sub_zero]
      exact Finset.sum_le_sum fun j _ => hj j
    | some j =>
      have hcol:=hchosen i hi j hc
      have hx : (1:ℝ)≤(S i j).card := by exact_mod_cast Finset.card_pos.mpr hcol.1
      have hdrop:=log_contraction_drop (S i j).card (S (i+1) j).card δ hx (by positivity) hδ.le hcol.2
      have hs : (∑ k:Fin 5,Real.log (1+(S (i+1) k).card))≤
          ∑ k:Fin 5,(Real.log (1+(S i k).card)-(if k=j then δ/2 else 0)) := by
        apply Finset.sum_le_sum
        intro k _
        by_cases hk : k=j
        · subst k; simpa using hdrop
        · simpa only [ite_eq_right hk,sub_zero] using hj k
      simpa [Φ,e,hc,Finset.sum_sub_distrib] using hs
  have hf:=telescoping_drop Φ e N hd
  have hnonneg : 0≤Φ N := Finset.sum_nonneg fun j _ => Real.log_nonneg (by
    have h : (0:ℝ)≤(S N j).card := by positivity
    linarith)
  have he : (∑ i∈Finset.range N,e i)=
      (((Finset.range N).filter fun i => (chosen i).isSome).card:ℝ)*(δ/2) := by
    simp only [e,←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  rw [he] at hf
  change _≤Φ 0
  linarith

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_State
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma state_mono (a : ι → ℙ K V) (b : ι → ℙ K (Dual K V))
    {E F : Finset ι} (hEF : E⊆F) (y : ℙ K (Dual K V)) :
    state a b E y≤ state a b F y := by
  apply iSup₂_le
  intro i hi
  exact le_iSup_of_le i (le_iSup_of_le (hEF hi) le_rfl)

end

open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ChooseLevel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))]

omit [FiniteDimensional K V] in
lemma scanSet_mono (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V)) (q : ℝ) (n : ℕ) :
    scanSet a b q n⊆scanSet a b q (n+1) := by
  rw [scanSet]
  split_ifs
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

omit [FiniteDimensional K V] in
lemma scanState_mono (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V))
    (q : ℝ) (n : ℕ) (y : ℙ K (Dual K V)) :
    scanState a b q n y≤ scanState a b q (n+1) y :=
  state_mono a b (scanSet_mono a b q n) y

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ScanChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))]

noncomputable def scanChoice (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V))
    (q : ℝ) (n : ℕ) : Option (Fin 5) :=
  if Expensive (scanState a b q n) (a n) (b n) q then
    if h : chooseLevel (scanState a b q n) (finrank K (scanState a b q n (b n)))<5
      then some ⟨_,h⟩ else none
  else none

end

open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ScanRecordPresent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section

variable {β : Type*} [Nonempty β] {N : ℕ}

attribute [local instance] OAI.SharpRamseyFive.Marking.finiteMarkingDecEq
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]

omit [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma tupleConsistent_extend {f : Fin N → FlagPair K V} (h : TupleConsistent f) :
    ∀ i j,i<j → j<N → Incident (tupleFirst f i) (tupleSecond f j) →
      Incident (tupleFirst f j) (tupleSecond f i) := by
  intro i j hij hj
  have hi : i<N := hij.trans hj
  simpa only [tupleFirst,tupleSecond,extendTuple,dite_eq_left hi,dite_eq_left hj] using
    (h ⟨i,hi⟩ ⟨j,hj⟩ hij)

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_TwoScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
attribute [local instance] OAI.SharpRamseyFive.Marking.twoScanDecEq
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

lemma reverseTuple_consistent {f : Fin N → FlagPair K V} (hf : TupleConsistent f) :
    TupleConsistent (reverseTuple f) := by
  intro i j hij hh
  simp only [reverseTuple,swapFlag_apply,incident_bidual] at hh ⊢
  exact hf j.rev i.rev (by simpa using hij) hh

lemma reverseTuple_incident {f : Fin N → FlagPair K V} (hf : TupleIncident f) :
    TupleIncident (reverseTuple f) := by
  intro i
  simpa only [reverseTuple,swapFlag_apply,incident_bidual] using hf i.rev

variable [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))]

omit [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] [Nonempty (ℙ K V)] in
lemma reverseExpensive_card (f : Fin N → FlagPair K V) (q : ℝ) :
    (reverseExpensive f q).card=(expensiveSet (reverseTuple f) q).card := by
  exact Finset.card_image_of_injective _ (fun _ _ h=>by simpa using congrArg Fin.rev h)

end

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators

end SharpRamseyFive.Marking

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_MarkingEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
local instance markingEndpointsPairDecEq : DecidableEq (FlagPair K V) := Classical.decEq _

end

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators

end SharpRamseyFive.Marking

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_WindowReciprocalScores
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Windows
open scoped Classical
noncomputable section
variable {w r : ℕ}
def middleSlot (v : Fin w) (t : Fin (2*r)) : Slots w r := Sum.inr (v,t)
end
end SharpRamseyFive.Windows
namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  {w r : ℕ} [Nonempty (Fin r)]
local instance windowScoreIndexDE : DecidableEq (Slots w r) := Classical.decEq _

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_WindowLossAggregation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
noncomputable local instance origWindowIDE (w n : ℕ) : DecidableEq (Windows.Slots w n) := Classical.decEq _
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree Windows Marking
open scoped Classical BigOperators LinearAlgebra.Projectivization
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_WindowDeletionCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
local instance allWindowIDE (w n : ℕ) : DecidableEq (Slots w n) := Classical.decEq _
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_AllWindowCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree Marking Windows
open ParameterHierarchy Filter
open scoped Classical BigOperators LinearAlgebra.Projectivization Topology NNReal
noncomputable section
local instance costIDE (w n : ℕ) : DecidableEq (Slots w n) := Classical.decEq _

end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_StageState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open scoped Classical BigOperators
open FiniteEntropy
noncomputable section
variable {α β γ Ω κ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype Ω] [Fintype κ]

namespace SelectedStream
variable {N n : ℕ} {admissible : (Fin N→α)→Prop}

def augment (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible) (q : Ω→Law κ) :
    SelectedStream (Ω:=Ω×κ) (β:=β) N n admissible where
  law := adaptiveLaw S.law q
  stream := fun z=>S.stream z.1
  tuple := fun z=>S.tuple z.1
  reverse := S.reverse
  view := S.view
  selected := by
    intro z hz
    have hp : 0<S.law z.1 := by
      change 0<S.law z.1*q z.1 z.2 at hz
      exact (mul_pos_iff.mp hz).resolve_right (fun h=>(S.law.nonneg _).not_gt h.1) |>.1
    exact S.selected _ hp
  good := by
    intro z hz
    have hp : 0<S.law z.1 := by
      change 0<S.law z.1*q z.1 z.2 at hz
      exact (mul_pos_iff.mp hz).resolve_right (fun h=>(S.law.nonneg _).not_gt h.1) |>.1
    exact S.good _ hp
  density := S.density
  density_nonneg := S.density_nonneg
  density_bound := by intro s; rw [adaptive_stream]; exact S.density_bound s

def changeOrientation (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible)
    (swap : β→γ) (back : γ→β) (hinv : Function.LeftInverse back swap) :
    SelectedStream (Ω:=Ω) (β:=γ) N n admissible where
  law := S.law
  stream := S.stream
  tuple := fun a i=>swap (S.tuple a i.rev)
  reverse := !S.reverse
  view := S.view ∘ back
  selected := by
    intro a ha
    have hh : sourceSequence (!S.reverse) (S.view ∘ back)
      (fun i=>swap (S.tuple a i.rev))=sourceSequence S.reverse S.view (S.tuple a) := by
      funext i
      cases h:S.reverse <;> simp only [sourceSequence,Bool.not_false,Bool.not_true,
        Bool.false_eq_true,ite_false,ite_true,Fin.rev_rev,Function.comp_apply] <;>
        exact congrArg S.view (hinv _)
    rw [hh]
    exact S.selected a ha
  good := S.good
  density := S.density
  density_nonneg := S.density_nonneg
  density_bound := S.density_bound

end SelectedStream
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Streams_DependentPrivateStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.SelectedTuple.SelectedStream
open FiniteEntropy
open scoped Classical
variable {Ω β α : Type*} [Fintype Ω] [Fintype β] [Fintype α]
  {Γ : Ω→Type*} [∀a,Fintype (Γ a)] {N n : ℕ} {admissible : (Fin N→α)→Prop}

def augmentSigma (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible) (q : ∀a,Law (Γ a)) :
    SelectedStream (Ω:=Sigma Γ) (β:=β) N n admissible where
  law:=sigmaLaw S.law q
  stream:=fun z=>S.stream z.1
  tuple:=fun z=>S.tuple z.1
  reverse:=S.reverse
  view:=S.view
  selected:=fun z hz=>S.selected z.1 (sigmaLaw_positive S.law q z hz).1
  good:=fun z hz=>S.good z.1 (sigmaLaw_positive S.law q z hz).1
  density:=S.density
  density_nonneg:=S.density_nonneg
  density_bound:=by intro s;rw [sigma_stream];exact S.density_bound s
end SharpRamseyFive.SelectedTuple.SelectedStream

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_HistoryPrivateStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking
open scoped Classical LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype Ω] [Fintype κ] [Fintype α]
  {N w n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}
local instance hpsIDE : DecidableEq (Slots w n) := Classical.decEq _

attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.hpsBDE
local instance hpsTDE_rc2b3a2_1 : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
abbrev WindowLiftSample (Ω K V : Type) [Field K] [AddCommGroup V] [Module K V]
    (w n steps : ℕ) := Ω×(BlockHistory (Fin w×Bool) (Fin n) (Fin w×Fin (2*n)) (FlagPair K V) steps×
      (Fin w×Bool→Fin n))

end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_WindowPosterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking CoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype Ω] [Fintype κ] [Fintype α] {N w n : ℕ} [Nonempty (Fin n)]
  {admissible : (Fin N→α)→Prop}
local instance wpSDE : DecidableEq (Slots w n) := Classical.decEq _
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_SelectedRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {Ω κ α β : Type} [Fintype Ω] [Fintype κ] [Fintype α] [Fintype β]
  {N n l : ℕ} {admissible : (Fin N→α)→Prop}
attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.srFinDE
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
omit [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma reverseTuple_injective : Function.Injective (reverseTuple (K:=K) (V:=V) (N:=n)) := by
  intro x y h
  funext i
  have H:=congrFun h i.rev
  simp only [reverseTuple,Fin.rev_rev] at H
  exact swapFlag.injective H
lemma changeOrientation_deficit (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (J : ℝ) :
    let T:=S.changeOrientation swapFlag swapFlag.symm swapFlag.symm_apply_apply
    mean (first (pair T.law ctx T.tuple)) (fun c=>(n:ℝ)*J-entropy (fiber (pair T.law ctx T.tuple) c))=
    mean (first (pair S.law ctx S.tuple)) (fun c=>(n:ℝ)*J-entropy (fiber (pair S.law ctx S.tuple) c)) := by
  exact mean_fiber_entropy_injective S.law ctx S.tuple reverseTuple reverseTuple_injective _
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_HighLowConflict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.CoreGeometry
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  {n : ℕ}

def highThreeLeft (p : Law (FlagPair K V)) (s : ℝ) : Finset (ℙ K V) :=
  highGoodFirst p (32*(Nat.card K:ℝ)^3) ((Nat.card K:ℝ)^4) ((Nat.card K:ℝ)^3) s
def highThreeRight (p : Law (FlagPair K V)) (s : ℝ) : Finset (ℙ K (Dual K V)) :=
  highGoodFirst (swap p) (32*(Nat.card K:ℝ)^3) ((Nat.card K:ℝ)^4) ((Nat.card K:ℝ)^3) s
end
end

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_HighSampleRetention
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.HighSamples
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

attribute [local instance] OAI.SharpRamseyFive.Marking.highRepDE
attribute [local instance] OAI.SharpRamseyFive.Marking.highRepDualDE
def highLeft (p : Law (FlagPair K V)) (r' : ℕ) (s : ℝ) : Finset (ℙ K V) :=
  highGoodFirst p (32*(Nat.card K:ℝ)^r') ((Nat.card K:ℝ)^4) ((Nat.card K:ℝ)^r') s
def highRight (p : Law (FlagPair K V)) (r : ℕ) (s : ℝ) : Finset (ℙ K (Dual K V)) :=
  highGoodFirst (swap p) (32*(Nat.card K:ℝ)^r) ((Nat.card K:ℝ)^4) ((Nat.card K:ℝ)^r) s

def highRepresentative (p : Law (FlagPair K V)) (r r' : ℕ) (s : ℝ) : Law (FlagPair K V) :=
  if h : 0<eventMass p (highLeft p r' s×ˢhighRight p r s) then
    conditionOn p (highLeft p r' s×ˢhighRight p r s) h else p

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_HighFourPreRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.HighSamples SharpRamseyFive.Windows
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] {N r : ℕ} [Nonempty (Fin r)]
local instance highFourPreBlockDE_rc2b3a2_1 : DecidableEq (Fin 1×Bool) := Classical.decEq _
local instance highFourPreIndexDE : DecidableEq (Slots 1 r) := Classical.decEq _

def highFourLoss (q : ℕ) (r' h : ℕ) (s d ε : ℝ) : ℝ :=
  highBadMass s d 153+64*(q:ℝ)^5*(2*Real.exp s/(q:ℝ)^r')*
    (Real.exp s/(q:ℝ)^4)+3*(1-1/(5*(q:ℝ)))^h+12*h*ε

def highFourSampler {κ : Type} [Fintype κ] {n : ℕ}
    (p : κ→Law (Slots 1 r→FlagPair K V)) (r' : ℕ) (s : ℝ) (h : ℕ)
    (z : (κ×BlockHistory (Fin 1×Bool) (Fin r) (Fin 1×Fin (2*r)) (FlagPair K V) n)×
      ((Fin 1×Bool)→Fin r)) : Law (Fin 3→Fin h→FlagPair K V) :=
  iid (iid (highRepresentative (map (historyPosterior (p z.1.1) z.1.2)
    (fun x=>x (Sum.inl ((0,false),z.2 (0,false))))) 4 r' s) (Fin h)) (Fin 3)

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ReciprocalLossBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization
noncomputable section
variable {K V α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype α]
  {N n : ℕ} {admissible : (Fin N→α)→Prop} {d Λ J M d' Λ' J' : ℝ}
def CodedStream.mono (S : CodedStream (K:=K) (V:=V) N n admissible d Λ J M)
    (hd : d≤d') (hΛ : Λ≤Λ') (hJ : J≤J') :
    CodedStream (K:=K) (V:=V) N n admissible d' Λ' J' M where
  sample:=S.sample
  stream:=S.stream
  code:=S.code
  description:=S.description.mono hΛ hJ
  density_bound:=S.density_bound.trans hd
  geometric:=S.geometric
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Rectangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.RectangleGeometry
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence
  SharpRamseyFive.CoreGeometry
open scoped LinearAlgebra.Projectivization BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

abbrev Flag := {ab : ℙ K V × ℙ K (Module.Dual K V) // Incident ab.1 ab.2}

noncomputable def rectangle (U : Submodule K (Module.Dual K V)) : Finset (Flag (K := K) (V := V)) :=
  Finset.univ.filter fun ab => ab.val.1.submodule≤U.dualCoannihilator ∧ ab.val.2.submodule≤U

end SharpRamseyFive.RectangleGeometry

namespace SharpRamseyFive.RectangleGeometry
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.CoreGeometry
open scoped LinearAlgebra.Projectivization BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]
  [Fintype (Submodule K (Module.Dual K V))]

noncomputable local instance instDecidableEqFlag : DecidableEq (Flag (K := K) (V := V)) := Classical.decEq _

end SharpRamseyFive.RectangleGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_WindowTargetInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  {w r : ℕ} [Nonempty (Fin r)]
local instance inputWinIDE : DecidableEq (Slots w r) := Classical.decEq _

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_WindowStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking PivotTree ReverseCap ScoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N w n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}
local instance awsIDE : DecidableEq (Slots w n) := Classical.decEq _
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_CodedWindowStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking PivotTree ReverseCap ScoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N w n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}
local instance cwsIDE : DecidableEq (Slots w n) := Classical.decEq _
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_HighWindowStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking HighSamples
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}
attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.hwsBDE
local instance hwsTDE_rc2b3a2_1 : DecidableEq (Fin 1×Fin (2*n)) := Classical.decEq _
local instance hwsIDE : DecidableEq (Slots 1 n) := Classical.decEq _

end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_AllWindowBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
local instance boundsIDE (w n : ℕ) : DecidableEq (Slots w n) := Classical.decEq _
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_GoodWindowVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  {w r : ℕ} [Nonempty (Fin r)]
local instance goodVarIDE : DecidableEq (Slots w r) := Classical.decEq _

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_HighDomainEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.HighSamples SharpRamseyFive.Windows
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] {N w r : ℕ} [Nonempty (Fin r)]
local instance highDomainStageIndexDE : DecidableEq (Slots w r) := Classical.decEq _

end

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_HighDomainPreRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.HighSamples SharpRamseyFive.Windows
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] {N r : ℕ} [Nonempty (Fin r)]
local instance highDomainPreBlockDE_rc2b3a2_1 : DecidableEq (Fin 1×Bool) := Classical.decEq _
local instance highDomainPreIndexDE : DecidableEq (Slots 1 r) := Classical.decEq _

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_OrderedHighConflict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.Windows
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] {N w r : ℕ} [Nonempty (Fin r)]
local instance highDomainThreeIndexDE : DecidableEq (Slots w r) := Classical.decEq _

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_WindowCodeDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy Windows ReverseCap ScoreGeometry PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
local instance wcdIDE (w n : ℕ) : DecidableEq (Slots w n) := Classical.decEq _
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_WindowTargetRetention
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal Topology
noncomputable section
local instance survRetIDE (w n : ℕ) : DecidableEq (Slots w n) := Classical.decEq _

end

end SharpRamseyFive.Marking

end OAI
end


