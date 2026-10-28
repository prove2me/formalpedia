-- Prove2me | Definitions.Def_OAIQ076M027
-- name    : OAIQ076M027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:22:25.096492+00:00
-- url     : https://prove2.me/theorems/d86155ff-7375-4251-97c9-2b47f90886af
-- title:
--   Definitions bundle OAIQ076M027 of the split of OpenAI, Constant-factor hardness of Min-UnCut (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinUncut.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of Min-UnCut (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 225 declarations of OpenAI's Lean: 56 definitions, 8 instances and 161 theorems. The definitions and types are `OAI.MinUncut.Preprocess.Alphabet.ambient`, `OAI.MinUncut.Preprocess.Alphabet.arrays`, `OAI.MinUncut.Preprocess.Alphabet.forms`, `OAI.MinUncut.Preprocess.Alphabet.formsEquiv`, `OAI.MinUncut.Preprocess.Alphabet.labelEquiv`, `OAI.MinUncut.Preprocess.Alphabet.labels`, `OAI.MinUncut.Preprocess.Alphabet.rhs`, `OAI.MinUncut.Preprocess.Alphabet.signatures`, `OAI.MinUncut.Preprocess.Alphabet.triples`, `OAI.MinUncut.Preprocess.DemandBody.bodyQuery`, `OAI.MinUncut.Preprocess.DemandOrder.Body`, `OAI.MinUncut.Preprocess.DemandOrder.bodyExpr`, `OAI.MinUncut.Preprocess.DemandOrder.bodyRepetitions`, `OAI.MinUncut.Preprocess.DemandOrder.indexEquiv`, `OAI.MinUncut.Preprocess.Face.codeEquiv`, `OAI.MinUncut.Preprocess.Face.codeGood`, `OAI.MinUncut.Preprocess.Face.codes`, `OAI.MinUncut.Preprocess.Grid.cells`, `OAI.MinUncut.Preprocess.Grid.coordinates`, `OAI.MinUncut.Preprocess.Grid.indices`, `OAI.MinUncut.Preprocess.Grid.samples`, `OAI.MinUncut.Preprocess.Queries.queries`, `OAI.MinUncut.Preprocess.Queries.queryEquiv`, `OAI.MinUncut.Preprocess.Queries.table`, `OAI.MinUncut.Preprocess.Source.context`, `OAI.MinUncut.Preprocess.Source.coordinates`, `OAI.MinUncut.Preprocess.Source.equalities`, `OAI.MinUncut.Preprocess.Source.polarities`, `OAI.MinUncut.Preprocess.Source.signatures`, `OAI.MinUncut.Preprocess.Source.sigs`, `OAI.MinUncut.Preprocess.Source.slotContexts`, `OAI.MinUncut.Preprocess.Source.slots`, `OAI.MinUncut.Preprocess.Source.sls`, `OAI.MinUncut.Preprocess.Syntax.sourceArgs`, `OAI.MinUncut.Preprocess.UEncoding.field`, `OAI.MinUncut.Preprocess.Weights.localSamples`, `OAI.MinUncut.Preprocess.chosenError`, `OAI.MinUncut.Preprocess.chosenNoise`, `OAI.MinUncut.Preprocess.gridExtract`, `OAI.MinUncut.Preprocess.gridPredicate` and 16 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MinUncut_Analysis_UniformCube`, `MinUncut_Estimates_Bridge`, `MinUncut_Estimates_ExpressionEffectivity`, `MinUncut_Estimates_LocalBodyEffectivity`, `MinUncut_Estimates_SelectedSyntax`, `MinUncut_Estimates_TemplateExpressions`, `MinUncut_Estimates_UniformAlgebra`, `MinUncut_Estimates_UniformEquation`, `MinUncut_Estimates_UniformEquationOutput`, `MinUncut_Estimates_UniformFaceArray`, `MinUncut_Estimates_UniformGrid`, `MinUncut_Graphs_CompleteGraphProgram`, `MinUncut_Graphs_DemandExpressions`, `MinUncut_Graphs_DemandOrder`, `MinUncut_Graphs_DemandQueryEffectivity`, `MinUncut_Graphs_DemandStageEffectivity`, `MinUncut_Machines_MachineExpanderTableProgram`, `MinUncut_Machines_MachineRegularOriginalBody`, `MinUncut_Machines_UniformAlphabet`, `MinUncut_Machines_UniformDemandAlphabet`, `MinUncut_PCP_ExpanderFamily`, `MinUncut_PCP_GraphTableComplexity`, `MinUncut_PCP_InitialGraph`, `MinUncut_PCP_PoweringOpinionTables`, `MinUncut_PCP_PoweringReturn`, `MinUncut_PCP_PoweringTableSemantics`, `MinUncut_PCP_PreprocessingRegularTables`, `MinUncut_PCP_PreprocessingTableSpectral`, `MinUncut_PCP_SpectralCut`, `MinUncut_PCP_TableIteration`, `MinUncut_Search_ArithmeticTactic`, `MinUncut_Search_FiniteQueryFamily`, `MinUncut_Search_UniformFiniteSum`.
--
--   **Imports.** It imports the bundles `OAIQ076M014`, `OAIQ076M015`, `OAIQ076M017`, `OAIQ076M019`, `OAIQ076M020` and `OAIQ076M021` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ076M030`.
-- source:
--   OpenAI, Constant-factor hardness of Min-UnCut (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ076M014
import Definitions.Def_OAIQ076M015
import Definitions.Def_OAIQ076M017
import Definitions.Def_OAIQ076M019
import Definitions.Def_OAIQ076M020
import Definitions.Def_OAIQ076M021

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_FiniteQueryFamily
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteProof
attribute [local instance] Classical.propDecidable
variable {Name I : Type*} [Fintype I]

instance familyAlphabetFintype (q : FamilyQuestion Name I) : Fintype (FamilyAlphabet q) := by
  cases q <;> unfold FamilyAlphabet <;> infer_instance

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ExpanderFamily
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.ExpanderTables

open PoweringWalks SpectralReturn

theorem step_certificate {v d : Nat} [NeZero v] [NeZero d]
    (G : Table v (d * d)) (H : Table ((d * d) * (d * d)) d)
    (hG : SpectralCertificate (graph G) (1 / 2 : ℝ))
    (hH : SpectralCertificate (graph H) (1 / 100 : ℝ)) :
    SpectralCertificate (graph (step G H)) (1 / 2 : ℝ) := by
  rw [step, graph_ofGraph]
  apply GraphTransport.reindex_spectralCertificate
  apply ZigzagSpectral.square_zigzag_halfCertificate
  · exact hG
  · exact GraphTransport.reindex_spectralCertificate _ _ _ _ hH

theorem initial_certificate (d : Nat) :
    SpectralCertificate (graph (initial d)) (1 / 2 : ℝ) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro f hf
  have hfun : f = fun _ => f 0 := funext (fun x => congrArg f (Subsingleton.elim x 0))
  have hm : mean f = f 0 := (congrArg mean hfun).trans (mean_const _)
  have hz : f 0 = 0 := hm.symm.trans hf
  rw [hfun, hz]
  simp [energy, mean, averagingOperator]

theorem family_certificate {d : Nat} [NeZero d]
    (H : Table ((d * d) * (d * d)) d)
    (hH : SpectralCertificate (graph H) (1 / 100 : ℝ)) (n : Nat) :
    SpectralCertificate (graph (family H n)) (1 / 2 : ℝ) := by
  induction n with
  | zero => exact initial_certificate d
  | succ n ih =>
    let : NeZero (vertexCount (d * d) n) :=
      ⟨Nat.ne_of_gt (vertexCount_positive (Nat.mul_pos (NeZero.pos d) (NeZero.pos d)) n)⟩
    exact step_certificate _ _ ih hH

end MinUncutGames.Foundations.PCP.ExpanderTables

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PreprocessingRegularTables
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncutGames.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.PreprocessingRegularTables

open scoped BigOperators
open PoweringWalks DegreeReplacement

theorem rejectionCount_ofCloudTables (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (labels : Fin (vertexCount t padding) → GraphTables.Label) :
    (PortTables.baseGraph (ofCloudTables t padding tables)).rejectionCount labels =
      (sourceGraph t padding tables).rejectionCount
        (fun z => labels (vertexOrder t padding z)) := by
  classical
  unfold ConstraintGraph.rejectionCount
  symm
  apply Finset.card_equiv (Equiv.prodCongr (vertexOrder t padding) (portOrder q))
  rintro ⟨v, p⟩
  simp only [ConstraintGraph.mem_rejectedDarts, Equiv.prodCongr_apply,
    Prod.map_apply, edgeSatisfied_ofCloudTables]

end MinUncutGames.Foundations.PCP.PreprocessingRegularTables

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_SpectralCut
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.PreprocessingRegularSoundness

open PoweringWalks DegreeReplacement SpectralReturn PreprocessingRegularTables

theorem resizeTable_certificate {n m q : Nat} (h : n = m)
    (table : ExpanderTables.Table n q) (lambda : ℝ)
    (certificate : SpectralCertificate (ExpanderTables.graph table) lambda) :
    SpectralCertificate (ExpanderTables.graph (resizeTable h table)) lambda := by
  cases h
  exact certificate

noncomputable def roundLabels (t : GraphTables.Table)
    (labels : Fin (vertexCount t (padding t)) → GraphTables.Label) :
    Fin t.vertices → GraphTables.Label :=
  CloudRounding.roundLabels
    (paddedGraph (GraphTables.semantics t) (fun v => Fin (padding t v)))
    (fun z => labels (vertexOrder t (padding t) z))

end MinUncutGames.Foundations.PCP.PreprocessingRegularSoundness

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PreprocessingTableSpectral
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncutGames.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PreprocessingTableSpectral

open PoweringWalks SpectralReturn

theorem materialize_portGraph {n d : Nat} {D : Type*}
    (G : ConstraintGraph (Fin n) (Fin n × D) PortTables.Label)
    (ports : D ≃ Fin d) :
    PortTables.portGraph (PreprocessingOverlayTables.materialize G ports) =
      GraphTransport.reindex (Overlay.originalPortGraph G) (Equiv.refl _) ports := by
  apply portGraph_ext
  intro x
  rw [PortTables.portGraph_rot, PreprocessingOverlayTables.rotation_materialize]
  rfl

theorem overlay_portGraph {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) :
    PortTables.portGraph (PreprocessingOverlayTables.overlay G H) =
      GraphTransport.reindex
        (Overlay.portGraph (PortTables.portGraph G) (ExpanderTables.graph H))
        (Equiv.refl _) (PreprocessingOverlayTables.overlayPorts d e) := by
  unfold PreprocessingOverlayTables.overlay
  rw [materialize_portGraph]
  rfl

theorem lazy_portGraph {n d : Nat} (G : PortTables.Table n d) :
    PortTables.portGraph (PreprocessingOverlayTables.lazy G) =
      GraphTransport.reindex (lazyGraph (PortTables.portGraph G))
        (Equiv.refl _) (PreprocessingOverlayTables.lazyPorts d) := by
  unfold PreprocessingOverlayTables.lazy
  rw [materialize_portGraph]
  rfl

theorem overlay_certificate_seven_eighths {n d e : Nat}
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (hn : 0 < n) (hdegree : d = e + 1) (he : 8 ≤ e)
    (hH : SpectralCertificate (ExpanderTables.graph H) (1 / 2 : ℝ)) :
    SpectralCertificate (PortTables.portGraph (PreprocessingOverlayTables.overlay G H))
      (7 / 8 : ℝ) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [overlay_portGraph]
  apply GraphTransport.reindex_spectralCertificate
  apply Overlay.spectralCertificate_seven_eighths
    (PortTables.portGraph G) (ExpanderTables.graph H)
  · simpa only [Fintype.card_fin] using hdegree
  · simp only [Fintype.card_fin]
    omega
  · exact hH

end MinUncutGames.Foundations.PCP.PreprocessingTableSpectral

end
section
noncomputable section

namespace MinUncutGames.Foundations.PCP.PreprocessingGuarantees

open PoweringWalks SpectralReturn PreprocessingTables
open PreprocessingRegularTables (internalDegree )

variable {n d e : Nat}

def restrictedLabel (t : GraphTables.Table)
    (labels : Fin (vertices t) → GraphTables.Label) :
    Fin (regularVertices t) → GraphTables.Label :=
  fun v => labels (v.castLE (PreprocessingLevels.le_paddedSize (regularVertices t)))

def roundLabels (t : GraphTables.Table)
    (labels : Fin (vertices t) → GraphTables.Label) : Fin t.vertices → GraphTables.Label :=
  PreprocessingRegularSoundness.roundLabels t (restrictedLabel t labels)

end MinUncutGames.Foundations.PCP.PreprocessingGuarantees

end
end
section
namespace MinUncutGames.Foundations.PCP.PoweringLabels

open PoweringWalks
open scoped BigOperators

variable {V D A : Type*}

instance finiteBall [Finite D] (G : PortGraph V D) (t : Nat) (v : V) :
    Finite (Ball G t v) :=
  Finite.of_surjective (wordToBall G t v) (wordToBall_surjective G t v)

end MinUncutGames.Foundations.PCP.PoweringLabels

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PoweringReturn
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PoweringTest

open PoweringWalks PoweringLabels PoweringReach PoweringOpinions

variable {V D A : Type*}

theorem rejection_mean_eq_path_mean [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) :
    SpectralReturn.mean (fun d : Dart V D n => PoweringMoment.bit
      ((poweredGraph G accepts n selectors).edgeSatisfied labels d = false)) =
      SpectralReturn.mean (fun w : Walk V D (n + 1) => PoweringMoment.bit
        (pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) = false)) := by
  rw [SpectralReturn.mean_prod]
  simp only [poweredGraph_edgeSatisfied, SpectralReturn.mean_const]

theorem witness_implies_path_rejection (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (assignment : V → A) (w : Walk V D (n + 1)) (k : Fin (n + 1))
    (h : witness G accepts n selectors labels fallback assignment w k) :
    pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) = false := by
  obtain ⟨hBad, hTail, hHead⟩ := h
  have hTailDecode :
      decode (selectors w.1) (labels w.1) (tailFromStart G n w k) =
        assignment (edgeAt G n w k).1 :=
    (opinionAt_eq_decode G (n + 1) selectors labels fallback w.1
      (tailFromStart G n w k)).symm.trans hTail
  have hHeadDecode :
      decode (selectors (endpoint G w)) (labels (endpoint G w))
          (headFromEnd G n w k) = assignment (G.rot (edgeAt G n w k)).1 :=
    (opinionAt_eq_decode G (n + 1) selectors labels fallback (endpoint G w)
      (headFromEnd G n w k)).symm.trans hHead
  have hFalse := (decodedBad_eq_true_iff G accepts assignment (edgeAt G n w k)).1 hBad
  cases hPath : pathAccepts G accepts n selectors w
      (labels w.1) (labels (endpoint G w)) with
  | false => rfl
  | true =>
      have hChecked := (pathAccepts_eq_true_iff G accepts n selectors w _ _).1 hPath k
      rw [hTailDecode, hHeadDecode, hFalse] at hChecked
      exact False.elim (Bool.noConfusion hChecked)

end MinUncutGames.Foundations.PCP.PoweringTest

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PoweringOpinionTables
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PoweringCounting

open PoweringWalks PoweringLabels PoweringTest
open scoped BigOperators

variable {V D A E : Type*}

theorem edgeDensity_eq_bit_mean [Fintype V] [Fintype D]
    (bad : Edge V D → Bool) :
    SpectralReturn.edgeDensity bad =
      SpectralReturn.mean (fun e : Edge V D => PoweringMoment.bit (bad e = true)) := by
  convert (SpectralReturn.mean_prod
    (fun e : Edge V D => PoweringMoment.bit (bad e = true))).symm using 1
  all_goals try with_reducible_and_instances rfl
  change SpectralReturn.mean (fun v => SpectralReturn.mean
    (fun d => if bad (v, d) then (1 : ℝ) else 0)) = _
  apply congrArg SpectralReturn.mean
  funext v
  apply congrArg SpectralReturn.mean
  funext d
  cases bad (v, d) <;> simp [PoweringMoment.bit]

theorem base_edgeDensity_eq_rejection_count [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (assignment : V → A) :
    SpectralReturn.edgeDensity (decodedBad G accepts assignment) =
      ((baseGraph G accepts reverse_accepts).rejectionCount assignment : ℝ) /
        (Fintype.card (Edge V D) : ℝ) := by
  calc
    _ = SpectralReturn.mean (fun e : Edge V D => PoweringMoment.bit
        (decodedBad G accepts assignment e = true)) := edgeDensity_eq_bit_mean _
    _ = SpectralReturn.mean (fun e : Edge V D => PoweringMoment.bit
        ((baseGraph G accepts reverse_accepts).edgeSatisfied assignment e = false)) := by
      apply congrArg SpectralReturn.mean
      funext e
      exact congrArg PoweringMoment.bit
        (propext (decodedBad_eq_true_iff G accepts assignment e))
    _ = _ := constraint_rejection_mean_eq_count _ _

theorem base_count_lower_to_density [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (assignment : V → A) (hcard : 0 < Fintype.card (Edge V D)) (ε : ℝ)
    (hcount : ε * (Fintype.card (Edge V D) : ℝ) ≤
      ((baseGraph G accepts reverse_accepts).rejectionCount assignment : ℝ)) :
    ε ≤ SpectralReturn.edgeDensity (decodedBad G accepts assignment) := by
  rw [base_edgeDensity_eq_rejection_count G accepts reverse_accepts assignment]
  exact (le_div_iff₀ (Nat.cast_pos.mpr hcard)).2 hcount

end MinUncutGames.Foundations.PCP.PoweringCounting

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PoweringTableSemantics
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.PoweringTableSemantics

open PoweringWalks PoweringLabels PoweringAddresses PoweringEnumeration PoweringTables

theorem card_darts_eq_table {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) = (table input n).darts := by
  change Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) =
    2 * vertices * d ^ (n + 1)
  simpa only [Fintype.card_fin] using Fintype.card_congr (dartEquiv vertices d n)

end MinUncutGames.Foundations.PCP.PoweringTableSemantics

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineExpanderTableProgram
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineExpanderTable

open _root_.Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

instance alphabetFintype (tape : Tape) : Fintype (Alphabet tape) := by
  cases tape <;> exact inferInstanceAs (Fintype Bool)

end MinUncutGames.Foundations.Complexity.MachineExpanderTable

namespace MinUncutGames.Foundations.Complexity.MachineExpanderFamily

open _root_.Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

instance alphabetFintype (tape : Tape) : Fintype (Alphabet tape) := by
  rw [alphabet_eq]
  exact inferInstanceAs (Fintype Bool)

open _root_.Turing

open _root_.Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

end MinUncutGames.Foundations.Complexity.MachineExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegularOriginalBody
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineRegularOwnerCleanup

open _root_.Turing MachineComposition

variable {LabelType : Type}

instance tapeFintype : Fintype Tape := by
  change Fintype
    ((Fin 27 ⊕ (MachineRegularMetadata.Extra ⊕
      (((MachineExpanderRow.Tape ⊕ MachineExpanderTable.ExtraTape) ⊕
        MachineExpanderFamily.ExtraTape) ⊕ MachineCeilingPower.Tape))) ⊕ Fin 2)
  infer_instance

end MinUncutGames.Foundations.Complexity.MachineRegularOwnerCleanup

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_InitialGraph
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.InitialGraph

open Target

instance vertexNonempty (F : Formula) : Nonempty (Vertex F) := ⟨dummyVertex F⟩

end MinUncutGames.Foundations.PCP.InitialGraph

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_GraphTableComplexity
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PoweringWitness

open PoweringWalks SpectralReturn PoweringReturn PoweringLazy
open PoweringMoment (bit)

variable {V D : Type*}

theorem iterate_mul_const [Fintype D] (G : PortGraph V D)
    (n : Nat) (c : ℝ) (h : V → ℝ) :
    iterateOperator G n (fun x => c * h x) =
      fun x => c * iterateOperator G n h x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change averagingOperator G (iterateOperator G n (fun x => c * h x)) =
      fun x => c * averagingOperator G (iterateOperator G n h) x
    rw [ih]
    funext v
    exact mean_mul_left c (fun d => iterateOperator G n h (G.rot (v, d)).1)

noncomputable def endpointWitness (G : PortGraph V D) (bad : Edge V D → Bool)
    (φ ψ : Edge V D → V → ℝ) (n : Nat) (k : Fin (n + 1))
    (w : Walk V D (n + 1)) : ℝ :=
  bit (bad (edgeAt G n w k) = true) *
    φ (edgeAt G n w k) w.1 * ψ (edgeAt G n w k) (endpoint G w)

noncomputable def vertexWitness (G : PortGraph V D) (bad : Edge V D → Bool)
    (f : V → V → ℝ) (n : Nat) (k : Fin (n + 1)) :
    Walk V D (n + 1) → ℝ :=
  endpointWitness G bad (fun e => f e.1) (fun e => f (next G e.1 e.2)) n k

theorem endpoint_lower_bound [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (n : Nat) (k : Fin (n + 1)) (bad : Edge V D → Bool)
    (φ ψ : Edge V D → V → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hL : ∀ e, bad e = true → a ≤ iterateOperator G k.val (φ e) e.1)
    (hR : ∀ e, bad e = true →
      a ≤ iterateOperator G (n - k.val) (ψ e) (next G e.1 e.2)) :
    edgeDensity bad * a ^ 2 ≤ mean (endpointWitness G bad φ ψ n k) := by
  have hfactor : mean (endpointWitness G bad φ ψ n k) =
      mean (fun e : Edge V D =>
        (bit (bad e = true) * iterateOperator G k.val (φ e) e.1) *
          iterateOperator G (n - k.val) (ψ e) (next G e.1 e.2)) := by
    unfold endpointWitness
    rw [mean_edge_endpoints G n k (fun e x => bit (bad e = true) * φ e x) ψ]
    simp_rw [iterate_mul_const]
  have hbitMean : mean (fun e : Edge V D => bit (bad e = true)) = edgeDensity bad := by
    calc
      _ = mean (fun v : V => mean (fun d : D => bit (bad (v, d) = true))) :=
        mean_prod (A := V) (B := D) (fun e => bit (bad e = true))
      _ = edgeDensity bad := by simp only [mean_edge_bit, edgeDensity]
  calc
    edgeDensity bad * a ^ 2 =
        mean (fun e : Edge V D => bit (bad e = true) * a ^ 2) := by
      rw [mean_mul_right, hbitMean]
    _ ≤ mean (fun e : Edge V D =>
        (bit (bad e = true) * iterateOperator G k.val (φ e) e.1) *
          iterateOperator G (n - k.val) (ψ e) (next G e.1 e.2)) := by
      apply mean_mono
      intro e
      cases hb : bad e with
      | false => simp [bit]
      | true =>
        have hprod := mul_le_mul (hL e hb) (hR e hb) ha (ha.trans (hL e hb))
        simpa [bit, hb, pow_two] using hprod
    _ = mean (endpointWitness G bad φ ψ n k) := hfactor.symm

theorem lazy_middle_witness_mean [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (q M : Nat) (hq : 1 ≤ q) (hM : 1 ≤ M)
    (k : Fin (2 * (4 * q * M) ^ 2 + 1))
    (hlo : (4 * q * M) ^ 2 - M ≤ k.val)
    (hhi : k.val ≤ (4 * q * M) ^ 2 + M)
    (bad : Edge V (Bool × D) → Bool) (f : V → V → ℝ)
    (hf : ∀ u w, f u w ∈ Set.Icc (0 : ℝ) 1)
    (hmodal : ∀ u, 1 / (q : ℝ) ≤
      iterateOperator (lazyGraph G) ((4 * q * M) ^ 2) (f u) u) :
    edgeDensity bad / (4 * (q : ℝ) ^ 2) ≤
      mean (vertexWitness (lazyGraph G) bad f (2 * (4 * q * M) ^ 2) k) := by
  have hk : k.val ≤ 2 * (4 * q * M) ^ 2 := Nat.le_of_lt_succ k.isLt
  have hslo : (4 * q * M) ^ 2 - M ≤ 2 * (4 * q * M) ^ 2 - k.val := by omega
  have hshi : 2 * (4 * q * M) ^ 2 - k.val ≤ (4 * q * M) ^ 2 + M := by omega
  have ha : (0 : ℝ) ≤ 1 / (2 * (q : ℝ)) := by positivity
  have hbound := endpoint_lower_bound (lazyGraph G) (2 * (4 * q * M) ^ 2) k bad
    (fun e => f e.1) (fun e => f (next (lazyGraph G) e.1 e.2))
    (1 / (2 * (q : ℝ))) ha
    (by
      intro e _
      exact lazy_endpoint_modal_transfer G q M k.val hq hM hlo hhi
        (f e.1) (hf e.1) e.1 (hmodal e.1))
    (by
      intro e _
      exact lazy_endpoint_modal_transfer G q M (2 * (4 * q * M) ^ 2 - k.val)
        hq hM hslo hshi (f (next (lazyGraph G) e.1 e.2))
        (hf (next (lazyGraph G) e.1 e.2)) (next (lazyGraph G) e.1 e.2)
        (hmodal (next (lazyGraph G) e.1 e.2)))
  have hscale : edgeDensity bad * (1 / (2 * (q : ℝ))) ^ 2 =
      edgeDensity bad / (4 * (q : ℝ) ^ 2) := by ring
  simpa only [vertexWitness, hscale] using hbound

end MinUncutGames.Foundations.PCP.PoweringWitness

end
section
namespace MinUncutGames.Foundations.PCP.PoweringMomentBound

open scoped BigOperators
open PoweringWalks SpectralReturn PoweringReturn
open PoweringMoment (bit hits)

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]

def windowEvent (G : PortGraph V D) (bad : V × D → Bool)
    (n start m : Nat) (h : start + m ≤ n + 1) (i : Fin m) (w : Walk V D (n + 1)) : Prop :=
  bad (edgeAt G n w (windowIndex n start m h i)) = true

theorem window_second_moment_eq (G : PortGraph V D) (bad : V × D → Bool)
    (n start m : Nat) (h : start + m ≤ n + 1) :
    mean (fun w => hits (windowEvent G bad n start m h) w ^ 2) =
      (m : ℝ) * edgeDensity bad +
        2 * ∑ j ∈ Finset.range m, ∑ gap ∈ Finset.range j, returnMass G bad gap := by
  rw [show mean (fun w => hits (windowEvent G bad n start m h) w ^ 2) =
      ∑ i, ∑ j, mean (fun w => bit (windowEvent G bad n start m h i w ∧
        windowEvent G bad n start m h j w)) from
    PoweringMoment.second_moment_eq (windowEvent G bad n start m h)]
  apply symmetric_gap_matrix_sum
  · intro i j
    congr 1
    funext w
    simp only [and_comm]
  · intro i
    simp only [and_self]
    exact hit_mean G bad n (windowIndex n start m h i)
  · intro i j hij
    have hwin : windowIndex n start m h i < windowIndex n start m h j :=
      Nat.add_lt_add_left hij start
    have hp := pair_event_mean G bad n (windowIndex n start m h i)
      (windowIndex n start m h j) hwin
    simpa only [windowEvent, windowIndex, Nat.add_sub_add_left] using hp

theorem window_second_moment_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e)
    (n start m : Nat) (h : start + m ≤ n + 1) :
    mean (fun w => hits (windowEvent G bad n start m h) w ^ 2) ≤
      (m : ℝ) * edgeDensity bad *
        (1 + 2 / (1 - lambda) + ((m : ℝ) - 1) * edgeDensity bad) := by
  rw [window_second_moment_eq]
  exact secondMoment_return_envelope G lambda certificate bad reversal m

end MinUncutGames.Foundations.PCP.PoweringMomentBound

end
section
noncomputable section

namespace MinUncutGames.Foundations.PCP.PoweringSoundness

open scoped BigOperators
open PoweringWalks PoweringLabels PoweringOpinions PoweringTest
open SpectralReturn PoweringWitness PoweringMomentBound
open PoweringMoment (bit hits)

variable {V D A : Type*}

variable [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
  [Fintype A] [Nonempty A]

def decodedError (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n N : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A) : ℝ :=
  edgeDensity (decodedBad G accepts (decoded G (n + 1) N selectors labels fallback))

def poweredRejection (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) : ℝ :=
  mean (fun d : Dart V D n => bit ((poweredGraph G accepts n selectors).edgeSatisfied labels d = false))

omit [Fintype V] [Nonempty V] [Nonempty D] in
theorem witness_bit_eq (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n N : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (w : Walk V D (n + 1)) (k : Fin (n + 1)) :
    bit (witness G accepts n selectors labels fallback
      (decoded G (n + 1) N selectors labels fallback) w k) =
      vertexWitness G
        (decodedBad G accepts (decoded G (n + 1) N selectors labels fallback))
        (matchFn G (n + 1) N selectors labels fallback) n k w := by
  simp only [witness, vertexWitness, endpointWitness, matchFn,
    PoweringMoment.bit_mul, next, and_assoc]

omit [Nonempty V] in
theorem modal_witness_mean (G : PortGraph V D) (M : Nat) (hM : 1 ≤ M)
    (accepts : Edge V (Bool × D) → A → A → Bool)
    (selectors : ∀ v, AddressSelector (lazyGraph G) (2 * center (Fintype.card A) M + 1) v)
    (labels : V → PaddedLabel (Bool × D) (2 * center (Fintype.card A) M + 1) A)
    (fallback : A) (k : Fin (2 * center (Fintype.card A) M + 1))
    (hlo : center (Fintype.card A) M - M ≤ k.val)
    (hhi : k.val ≤ center (Fintype.card A) M + M) :
    decodedError (lazyGraph G) accepts (2 * center (Fintype.card A) M)
      (center (Fintype.card A) M) selectors labels fallback / (4 * (Fintype.card A : ℝ) ^ 2) ≤
      mean (fun w => bit (witness (lazyGraph G) accepts (2 * center (Fintype.card A) M)
        selectors labels fallback (decoded (lazyGraph G) (2 * center (Fintype.card A) M + 1)
          (center (Fintype.card A) M) selectors labels fallback) w k)) := by
  have h := lazy_middle_witness_mean G (Fintype.card A) M Fintype.card_pos hM k hlo hhi
    (decodedBad (lazyGraph G) accepts
      (decoded (lazyGraph G) (2 * center (Fintype.card A) M + 1)
        (center (Fintype.card A) M) selectors labels fallback))
    (matchFn (lazyGraph G) (2 * center (Fintype.card A) M + 1)
      (center (Fintype.card A) M) selectors labels fallback)
    (matchFn_mem_Icc (lazyGraph G) (2 * center (Fintype.card A) M + 1)
      (center (Fintype.card A) M) selectors labels fallback)
    (decoded_modal_baseline (lazyGraph G) (2 * center (Fintype.card A) M + 1)
      (center (Fintype.card A) M) selectors labels fallback)
  simp_rw [witness_bit_eq]
  convert h using 1 <;> rfl

theorem rejection_lower_bound (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate (lazyGraph G) lambda)
    (accepts : Edge V (Bool × D) → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts ((lazyGraph G).rot e) b a = accepts e a b)
    (M : Nat) (hM : 1 ≤ M)
    (selectors : ∀ v, AddressSelector (lazyGraph G) (2 * center (Fintype.card A) M + 1) v)
    (labels : V → PaddedLabel (Bool × D) (2 * center (Fintype.card A) M + 1) A)
    (fallback : A)
    (hε : 0 < decodedError (lazyGraph G) accepts (2 * center (Fintype.card A) M)
      (center (Fintype.card A) M) selectors labels fallback) :
    gain (Fintype.card A) M lambda *
        min (decodedError (lazyGraph G) accepts (2 * center (Fintype.card A) M)
          (center (Fintype.card A) M) selectors labels fallback)
          (1 / ((2 * center (Fintype.card A) M + 1 : Nat) : ℝ)) ≤
      poweredRejection (lazyGraph G) accepts (2 * center (Fintype.card A) M) selectors labels := by
  let q := Fintype.card A
  let N := center q M
  let n := 2 * N
  let m := 2 * M + 1
  let start := N - M
  let L := lazyGraph G
  let assignment := decoded L (n + 1) N selectors labels fallback
  let bad := decodedBad L accepts assignment
  let ε := edgeDensity bad
  let α : ℝ := 1 / (2 * (q : ℝ))
  let C : ℝ := 1 + 2 / (1 - lambda)
  have hNM : M ≤ N := le_center q M Fintype.card_pos hM
  have hw : start + m ≤ n + 1 := by dsimp [start, m, n]; omega
  let E := windowEvent L bad n start m hw
  let W : Fin m → Walk V (Bool × D) (n + 1) → Prop := fun i w =>
    witness L accepts n selectors labels fallback assignment w (windowIndex n start m hw i)
  let R : Walk V (Bool × D) (n + 1) → Prop := fun w =>
    pathAccepts L accepts n selectors w (labels w.1) (labels (endpoint L w)) = false
  have hWE : ∀ i w, W i w → E i w := by
    intro i w h
    exact h.1
  have hWR : ∀ i w, W i w → R w := by
    intro i w h
    exact witness_implies_path_rejection L accepts n selectors labels fallback assignment w
      (windowIndex n start m hw i) h
  have hpoint (i : Fin m) : ε / (4 * (q : ℝ) ^ 2) ≤ mean (fun w => bit (W i w)) := by
    have hlo : N - M ≤ (windowIndex n start m hw i).val := by
      dsimp [windowIndex, start]
      omega
    have hhi : (windowIndex n start m hw i).val ≤ N + M := by
      have hi := i.isLt
      dsimp [windowIndex, start]
      dsimp [m] at hi
      omega
    exact modal_witness_mean G M hM accepts selectors labels fallback
      (windowIndex n start m hw i) hlo hhi
  have hfirst : α ^ 2 * (m : ℝ) * ε ≤ mean (hits W) := by
    change α ^ 2 * (m : ℝ) * ε ≤ PoweringMoment.mean (hits W)
    rw [PoweringMoment.mean_hits]
    calc
      _ = ∑ _i : Fin m, ε / (4 * (q : ℝ) ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        dsimp [α]
        ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hpoint i)
  have hsecond : mean (fun w => hits E w ^ 2) ≤
      (m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε) :=
    window_second_moment_le L lambda certificate bad
      (decodedBad_rot L accepts reverse_accepts assignment) n start m hw
  have hε' : 0 < ε := hε
  have hm : 0 < m := by dsimp [m]; omega
  have hmReal : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hqReal : (0 : ℝ) < q := Nat.cast_pos.mpr Fintype.card_pos
  have hden : 0 < 1 - lambda := sub_pos.mpr certificate.lt_one
  have hC : 0 < C := by dsimp [C]; positivity
  have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hα : 0 < α := by dsimp [α]; positivity
  have ha : 0 < α ^ 2 * (m : ℝ) * ε := by positivity
  have hb : 0 < (m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε) := by
    have hdiff : 0 ≤ (m : ℝ) - 1 := sub_nonneg.mpr hmOne
    positivity
  have hCS := PoweringMoment.rejection_lower_bound E W R hWE hWR
    (α ^ 2 * (m : ℝ) * ε) ((m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε))
    ha hb hfirst hsecond
  have ht : (0 : ℝ) < ((n + 1 : Nat) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have hmn : m ≤ n + 1 := by dsimp [m, n]; omega
  have hmt : (m : ℝ) - 1 ≤ ((n + 1 : Nat) : ℝ) := by
    have hmnReal : (m : ℝ) ≤ ((n + 1 : Nat) : ℝ) := by exact_mod_cast hmn
    linarith
  have hratio := PoweringNumeric.count_moment_ratio_lower α ε C ((n + 1 : Nat) : ℝ)
    m hm hε' hC ht hmt
  change (α ^ 4 * (m : ℝ) / (C + 1)) * min ε (1 / ((n + 1 : Nat) : ℝ)) ≤ _
  change _ ≤ mean (fun d : Dart V (Bool × D) n =>
    bit ((poweredGraph L accepts n selectors).edgeSatisfied labels d = false))
  rw [rejection_mean_eq_path_mean]
  exact hratio.trans hCS

end MinUncutGames.Foundations.PCP.PoweringSoundness

end
end
section
namespace MinUncutGames.Foundations.PCP.PoweringGap

open PoweringWalks PoweringLabels PoweringOpinions PoweringTest
open SpectralReturn PoweringSoundness PoweringCounting

variable {V D A : Type*}

variable [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
  [Fintype A] [Nonempty A]

theorem uniform_count_gap (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate (lazyGraph G) lambda)
    (accepts : Edge V (Bool × D) → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts ((lazyGraph G).rot e) b a = accepts e a b)
    (M : Nat) (hM : 1 ≤ M)
    (selectors : ∀ v, AddressSelector (lazyGraph G)
      (2 * center (Fintype.card A) M + 1) v)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hgap : ∀ assignment : V → A,
      epsilon * (Fintype.card (Edge V (Bool × D)) : ℝ) ≤
        ((baseGraph (lazyGraph G) accepts reverse_accepts).rejectionCount assignment : ℝ))
    (labels : V → PaddedLabel (Bool × D) (2 * center (Fintype.card A) M + 1) A) :
    (gain (Fintype.card A) M lambda *
      min epsilon (1 / ((2 * center (Fintype.card A) M + 1 : Nat) : ℝ))) *
        (Fintype.card (Dart V (Bool × D) (2 * center (Fintype.card A) M)) : ℝ) ≤
      ((poweredGraph (lazyGraph G) accepts (2 * center (Fintype.card A) M)
        selectors).rejectionCount labels : ℝ) := by
  classical
  let L := lazyGraph G
  let N := center (Fintype.card A) M
  let n := 2 * N
  let H := poweredGraph L accepts n selectors
  change (gain (Fintype.card A) M lambda *
      min epsilon (1 / ((n + 1 : Nat) : ℝ))) *
        (Fintype.card (Dart V (Bool × D) n) : ℝ) ≤
      (H.rejectionCount labels : ℝ)
  rcases eq_or_lt_of_le hepsilon with hzero | hpositive
  · rw [← hzero]
    have hcap : (0 : ℝ) ≤ 1 / ((n + 1 : Nat) : ℝ) := by positivity
    rw [min_eq_left hcap, mul_zero, zero_mul]
    exact Nat.cast_nonneg _
  · let fallback : A := Classical.choice (inferInstance : Nonempty A)
    let assignment := decoded L (n + 1) N selectors labels fallback
    have hdecoded : epsilon ≤ decodedError L accepts n N selectors labels fallback := by
      change epsilon ≤ edgeDensity (decodedBad L accepts assignment)
      exact base_count_lower_to_density L accepts reverse_accepts assignment
        Fintype.card_pos epsilon (hgap assignment)
    have herror : 0 < decodedError L accepts n N selectors labels fallback :=
      hpositive.trans_le hdecoded
    have hsound := PoweringSoundness.rejection_lower_bound G lambda certificate
      accepts reverse_accepts M hM selectors labels fallback herror
    have hgain : 0 ≤ gain (Fintype.card A) M lambda :=
      gain_nonneg (Fintype.card A) M lambda certificate.lt_one
    have hmin : min epsilon (1 / ((n + 1 : Nat) : ℝ)) ≤
        min (decodedError L accepts n N selectors labels fallback)
          (1 / ((n + 1 : Nat) : ℝ)) :=
      min_le_min hdecoded (le_refl _)
    have hlower : gain (Fintype.card A) M lambda *
        min epsilon (1 / ((n + 1 : Nat) : ℝ)) ≤
        poweredRejection L accepts n selectors labels :=
      (mul_le_mul_of_nonneg_left hmin hgain).trans hsound
    exact (constraint_rejection_lower_iff H labels Fintype.card_pos
      (gain (Fintype.card A) M lambda *
        min epsilon (1 / ((n + 1 : Nat) : ℝ)))).mp hlower

end MinUncutGames.Foundations.PCP.PoweringGap

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_TableIteration
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MinUncutGames.Foundations.PCP.PoweringPortReindex
open PoweringWalks PoweringLabels PoweringReach PoweringTest
open SpectralReturn PoweringSoundness

variable {V D E A : Type*}

def walkEquiv (ports : D ≃ E) (n : Nat) : Walk V D n ≃ Walk V E n :=
  Equiv.prodCongr (Equiv.refl V) (wordEquiv ports n)

def addressEquiv (ports : D ≃ E) (t : Nat) : PortWords D t ≃ PortWords E t where
  toFun w := ⟨w.1, wordEquiv ports w.1.val w.2⟩
  invFun w := ⟨w.1, (wordEquiv ports w.1.val).symm w.2⟩
  left_inv w := by rcases w with ⟨n,p⟩; simp
  right_inv w := by rcases w with ⟨n,p⟩; simp

def labelEquiv (ports : D ≃ E) (t : Nat) : PaddedLabel E t A ≃ PaddedLabel D t A where
  toFun a := fun w => a (addressEquiv ports t w)
  invFun a := fun w => a ((addressEquiv ports t).symm w)
  left_inv a := by funext w; simp
  right_inv a := by funext w; simp

variable (G : PortGraph V D) (H : PortGraph V E) (ports : D ≃ E)
variable (rotation : ∀ v d, H.rot (v, ports d) =
  ((G.rot (v,d)).1, ports (G.rot (v,d)).2))

include rotation

theorem wordEnd_map (n : Nat) (v : V) (p : Fin n → D) :
    wordEnd H n v (wordEquiv ports n p) = wordEnd G n v p := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    simp only [wordEnd, next, wordEquiv, Equiv.coe_fn_mk, rotation]
    exact ih _ _

theorem endpoint_map (n : Nat) (w : Walk V D n) :
    endpoint H (walkEquiv ports n w) = endpoint G w :=
  wordEnd_map G H ports rotation n w.1 w.2

theorem reach_iff (t : Nat) (v u : V) :
    (∃ n, n ≤ t ∧ ∃ p : Fin n → D, wordEnd G n v p = u) ↔
    (∃ n, n ≤ t ∧ ∃ p : Fin n → E, wordEnd H n v p = u) := by
  constructor
  · rintro ⟨n,hn,p,hp⟩
    exact ⟨n,hn,wordEquiv ports n p,(wordEnd_map G H ports rotation n v p).trans hp⟩
  · rintro ⟨n,hn,p,hp⟩
    refine ⟨n,hn,(wordEquiv ports n).symm p,?_⟩
    rw [← wordEnd_map G H ports rotation, Equiv.apply_symm_apply]
    exact hp

def ballEquiv (t : Nat) (v : V) : Ball G t v ≃ Ball H t v where
  toFun u := ⟨u.val,(reach_iff G H ports rotation t v u.val).mp u.property⟩
  invFun u := ⟨u.val,(reach_iff G H ports rotation t v u.val).mpr u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem wordToBall_map (t : Nat) (v : V) (w : PortWords D t) :
    wordToBall H t v (addressEquiv ports t w) =
      ballEquiv G H ports rotation t v (wordToBall G t v w) := by
  apply Subtype.ext
  exact wordEnd_map G H ports rotation w.1.val v w.2

def pullSelector {t : Nat} {v : V} (S : AddressSelector H t v) :
    AddressSelector G t v where
  address u := (addressEquiv ports t).symm
    (S.address (ballEquiv G H ports rotation t v u))
  correct u := by
    apply (ballEquiv G H ports rotation t v).injective
    rw [← wordToBall_map, Equiv.apply_symm_apply, S.correct]

theorem decode_pullSelector {t : Nat} {v : V} (S : AddressSelector H t v)
    (a : PaddedLabel E t A) (u : Ball G t v) :
    decode (pullSelector G H ports rotation S) (labelEquiv ports t a) u =
      decode S a (ballEquiv G H ports rotation t v u) := by
  simp [decode, pullSelector, labelEquiv]

theorem decode_transport {t : Nat} (selectors : ∀v, AddressSelector H t v)
    (a : PaddedLabel E t A) {v w : V} (hvw : v = w)
    (u : Ball G t v) (u' : Ball H t w) (hu : u.val = u'.val) :
    decode (pullSelector G H ports rotation (selectors v)) (labelEquiv ports t a) u =
      decode (selectors w) a u' := by
  subst w
  rw [decode_pullSelector]
  congr 1
  exact Subtype.ext hu

theorem advanceTail_map (n : Nat) (w : Walk V D (n+1)) :
    advanceTail H (walkEquiv ports (n+1) w) =
      walkEquiv ports n (advanceTail G w) := by
  apply Prod.ext
  · change (H.rot (w.1, ports (w.2 0))).1 = (G.rot (w.1,w.2 0)).1
    rw [rotation]
  · rfl

theorem edgeAt_map (n : Nat) (w : Walk V D (n+1)) (k : Fin (n+1)) :
    edgeAt H n (walkEquiv ports (n+1) w) k =
      ((edgeAt G n w k).1, ports (edgeAt G n w k).2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    induction k using Fin.cases with
    | zero => rfl
    | succ k =>
      simp only [edgeAt, Fin.cases_succ]
      rw [advanceTail_map G H ports rotation]
      exact ih _ _

variable (accepts : Edge V E → A → A → Bool)

def dartEquiv (n : Nat) : Dart V D n ≃ Dart V E n :=
  Equiv.prodCongr (Equiv.refl Bool) (walkEquiv ports (n+1))

end MinUncutGames.Foundations.PCP.PoweringPortReindex

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Bridge
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.SourceBridge
open MinUncut.Inner MinUncut.Outer
open MinUncutGames.Reduction
attribute [local instance] Classical.propDecidable

def fieldBool (x : F₂) : Bool := decide (x=1)

lemma boolField_fieldBool (x : F₂) : boolField (fieldBool x)=x := by
  fin_cases x <;> rfl

lemma satisfied_equation {N : Type} (e : CloneGap.Equation N) (b : N → Bool) :
    Satisfied (fun x => boolField (b x)) (equation e) ↔ CloneGap.satisfied e b=true := by
  change boolField (b e.first)+boolField (b e.second)+boolField (b e.third)=boolField e.rhs ↔
    ((b e.first ^^ b e.second ^^ b e.third)==e.rhs)=true
  cases e.rhs <;> cases b e.first <;> cases b e.second <;> cases b e.third <;> decide

lemma sum_satisfied (input : SourceEncoding.Input) (bits : Fin input.«variables» → Bool) :
    (∑ i : Fin input.equations.length,
      if Satisfied (fun x => boolField (bits x)) (equations input i) then (1:ℝ) else 0)=
      (input.equations.countP (fun e => CloneGap.satisfied e bits):ℝ) := by
  simp_rw [equations,satisfied_equation]
  exact sum_list_count input.equations (fun e => CloneGap.satisfied e bits)

end MinUncut.SourceBridge

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ExpressionEffectivity
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess.Syntax
open MinUncut.Costed MinUncut.CodeEffective Turing.ToPartrec
variable {P : Type} [Primcodable P]
lemma C.const {f : P → ℕ} (hf : Computable f) : C (fun p=>.const (f p)) := p_constCode.to_comp.comp hf
lemma C.add {a b : P → AExpr} (ha : C a) (hb : C b) : C (fun p=>.add (a p) (b p)) :=
  (p_bin PolyProgram.add.code).to_comp.comp ha hb
lemma C.mul {a b : P → AExpr} (ha : C a) (hb : C b) : C (fun p=>.mul (a p) (b p)) :=
  (p_bin PolyProgram.mul.code).to_comp.comp ha hb
lemma C.div {a b : P → AExpr} (ha : C a) (hb : C b) : C (fun p=>.div (a p) (b p)) :=
  (p_bin Division.quotient.code).to_comp.comp ha hb
attribute [local irreducible] PolyProgram.add PolyProgram.sub PolyProgram.mul
lemma C.pow {a : P → AExpr} {n : P → ℕ} (ha : C a) (hn : Computable n) : C (fun p=>(a p).pow (n p)) := by
  have hh := Computable.nat_rec (σ:=Code) hn (Computable.const (AExpr.const 1).program.code)
    ((p_bin PolyProgram.mul.code).to_comp.comp (Computable.snd.comp Computable.snd)
      (ha.comp Computable.fst)).to₂
  exact hh.of_eq (fun p=>powCode_eq (a p) (n p))

end MinUncut.Preprocess.Syntax

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_TemplateExpressions
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess.Syntax
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open MinUncut.FiniteProof MinUncut.Costed MinUncut.CodeEffective Turing.ToPartrec UEncoding
variable {P : Type} [Primcodable P] {A B : P → Type} {c : UEncoding P A}
lemma O.functionExpr {b : UEncoding P B} {base : P → ℕ} (hb : Computable base)
    {f : ∀p,A p × B p → AExpr} (hf : O (c.prod b) f) :
    O c (fun p x=>MinUncut.SourceTemplate.functionExpr (b.enc p) (base p) (fun y=>f p (x,y))) := by
  have hpow : (c.prod b).Out (fun p x=>base p ^ ((b.enc p).code x.2).val) :=
    (out_const _ hb).map₂ (out_code b).second (ca_pow Computable.fst Computable.snd)
  apply (hf.mul (O.const hpow)).sum_enum.ofEq
  intro p x
  simp only [MinUncut.SourceTemplate.functionExpr,Encoding.enumerate,List.map_ofFn,Function.comp_def,Equiv.apply_symm_apply]
end MinUncut.Preprocess.Syntax

end
end
section
namespace MinUncut.Preprocess.Source
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncut.SourceTemplate UEncoding

def slots : UEncoding ℕ (fun _=>Slot) := fixed slotEncoding
def coordinates : UEncoding ℕ (fun u=>Fin u × Slot) := positions.prod slots
def polarities : UEncoding ℕ (fun u=>Fin u → Slot → Bool) := positions.function (slots.function bool)
def equalities : UEncoding ℕ (fun u=>(Fin u × Slot) → (Fin u × Slot) → Bool) :=
  coordinates.function (coordinates.function bool)
def signatures : UEncoding ℕ Signature := (polarities.prod equalities).ofEquiv signatureEquiv

lemma map_positive : signatures.Map polarities (fun _ s=>s.positive) := by
  change ((polarities.prod equalities).ofEquiv signatureEquiv).Map polarities (fun u s=>(signatureEquiv u s).1)
  exact map_comp (map_to (polarities.prod equalities) signatureEquiv) (map_fst polarities equalities)
lemma map_same : signatures.Map equalities (fun _ s=>s.same) := by
  change ((polarities.prod equalities).ofEquiv signatureEquiv).Map equalities (fun u s=>(signatureEquiv u s).2)
  exact map_comp (map_to (polarities.prod equalities) signatureEquiv) (map_snd polarities equalities)

variable {Γ : ℕ → Type} {g : UEncoding ℕ Γ}
lemma map_satisfies {s : ∀u,Γ u → Signature u} {j : ∀u,Γ u → J u} {t : ∀u,Γ u → Fin u}
    (hs : g.Map signatures s) (hj : g.Map rights j) (ht : g.Map positions t) :
    g.Map bool (fun u x=>(s u x).satisfies (j u x) (t u x)) := by
  exact map_binary (slotEncoding.function Encoding.bool) clauseAnswerEncoding Encoding.bool
    (fun p a=>(literalValue (p .first) a.first || literalValue (p .second) a.second) ||
      literalValue (p .third) a.third)
    (map_apply (map_comp hs map_positive) ht) (map_apply hj ht)

lemma map_same_at {s : ∀u,Γ u → Signature u} {a b : ∀u,Γ u → Fin u × Slot}
    (hs : g.Map signatures s) (ha : g.Map coordinates a) (hb : g.Map coordinates b) :
    g.Map bool (fun u x=>(s u x).same (a u x) (b u x)) :=
  map_apply (map_apply (map_comp hs map_same) ha) hb
lemma map_answer_at {j : ∀u,Γ u → J u} {a : ∀u,Γ u → Fin u × Slot}
    (hj : g.Map rights j) (ha : g.Map coordinates a) :
    g.Map bool (fun u x=>answerAt (j u x (a u x).1) (a u x).2) :=
  map_binary clauseAnswerEncoding slotEncoding Encoding.bool answerAt
    (map_apply hj (map_comp ha (map_fst _ _))) (map_comp ha (map_snd _ _))

lemma map_consistent {s : ∀u,Γ u → Signature u} {j : ∀u,Γ u → J u}
    {a b : ∀u,Γ u → Fin u × Slot}
    (hs : g.Map signatures s) (hj : g.Map rights j)
    (ha : g.Map coordinates a) (hb : g.Map coordinates b) :
    g.Map bool (fun u x=>decide ((s u x).same (a u x) (b u x)=true →
      answerAt (j u x (a u x).1) (a u x).2=answerAt (j u x (b u x).1) (b u x).2)) := by
  apply (map_or (map_not (map_same_at hs ha hb))
    (map_bool_eq (map_answer_at hj ha) (map_answer_at hj hb))).ofEq
  intro u x
  by_cases h:(s u x).same (a u x) (b u x)=true <;> simp [h]

lemma map_valid : (signatures.prod rights).Map bool (fun _ x=>x.1.valid x.2) := by
  classical
  have hs : ((signatures.prod rights).prod positions).Map bool
      (fun u x=>x.1.1.satisfies x.1.2 x.2) :=
    map_satisfies (map_fst signatures rights).first (map_snd signatures rights).first (map_snd _ _)
  have hc : (((signatures.prod rights).prod coordinates).prod coordinates).Map bool
      (fun u x=>decide (x.1.1.1.same x.1.2 x.2=true →
        answerAt (x.1.1.2 x.1.2.1) x.1.2.2=answerAt (x.1.1.2 x.2.1) x.2.2)) :=
    map_consistent (map_fst signatures rights).first.first (map_snd signatures rights).first.first
      (map_snd (signatures.prod rights) coordinates).first (map_snd _ _)
  apply (map_and (map_forall hs) (map_forall (map_forall hc))).ofEq
  intro u x
  simp only [Signature.valid,Bool.decide_and,decide_eq_true_eq]
  congr 1
  apply decide_eq_decide.mpr
  simp only [Prod.forall]
  constructor
  · intro h t t' s s' he
    exact h t s t' s' he
  · intro h t s t' s' he
    exact h t t' s s' he

end MinUncut.Preprocess.Source

end
section
namespace MinUncut.Preprocess.Source
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncut.SourceTemplate UEncoding

def slotContexts : UEncoding ℕ SlotContext := positions.function slots

variable {Γ : ℕ → Type} {g : UEncoding ℕ Γ}
lemma map_slot {s : ∀u,Γ u → Signature u} {r : ∀u,Γ u → SlotContext u} {t : ∀u,Γ u → Fin u}
    (hs : g.Map signatures s) (hr : g.Map slotContexts r) (ht : g.Map positions t) :
    g.Map slots (fun u x=>(s u x).slot (r u x) (t u x)) := by
  exact map_binary Encoding.bool Encoding.bool slotEncoding
    (fun b c=>if b then .first else if c then .second else .third)
    (map_same_at hs (map_pair ht (map_const (Computable.const 0))) (map_pair ht (map_apply hr ht)))
    (map_same_at hs (map_pair ht (map_const (Computable.const 1))) (map_pair ht (map_apply hr ht)))

lemma map_project {s : ∀u,Γ u → Signature u} {r : ∀u,Γ u → SlotContext u} {j : ∀u,Γ u → J u}
    (hs : g.Map signatures s) (hr : g.Map slotContexts r) (hj : g.Map rights j) :
    g.Map lefts (fun u x=>(s u x).project (r u x) (j u x)) := by
  exact map_lambda (map_binary clauseAnswerEncoding slotEncoding Encoding.bool answerAt
    (map_apply hj.first (map_snd g positions))
    (map_slot hs.first hr.first (map_snd g positions)))

end MinUncut.Preprocess.Source

end
section
namespace MinUncut.SourceTemplate
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncutGames.Reduction.CloneGap

lemma rawLocal_eq {u D : ℕ} (valid : J u → Bool) (π : J u → I u)
    (t : SourceTape.TestTape (I u) (J u) D) :
    rawLocal valid π t.1 t.2.2 (MinUncutGames.Reduction.FiniteNoise.realizedNoise t.2.1)=
      localEquation valid π t := by
  rw [rawLocal,←findValid_map,←firstValid]
  unfold localEquation
  cases hh:firstValid (jEncoding u) valid with
  | none => rfl
  | some j₀ =>
    dsimp only [Option.map_some,Option.elim_some,mapEquation,FoldedEquation.conditionedEquation,
      FoldedEquation.equation,foldedLocal,canonicalInput]
    rw [extend_representative]
    have he : thirdQuery (fun j:{j : J u // valid j=true}=>π j.val) t.1
        (restrictQuery valid t.2.2)
        (restrictQuery valid (MinUncutGames.Reduction.FiniteNoise.realizedNoise t.2.1))=
        restrictQuery valid (thirdQuery π t.1 t.2.2
          (MinUncutGames.Reduction.FiniteNoise.realizedNoise t.2.1)) := rfl
    rw [he,extend_representative]
    rfl
end MinUncut.SourceTemplate

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_UniformCube
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess.UEncoding
open MinUncutGames.Foundations.Hastad MinUncutGames.Foundations.Hastad.SourceOccurrences
open MinUncutGames.Reduction.CloneGap
variable {P : Type} [Primcodable P] {A B Γ : P → Type}

lemma map_padded {g : UEncoding P Γ} {a : UEncoding P A}
    {v f : ∀p,Γ p → A p → Bool} {i : ∀p,Γ p → A p}
    (hv : g.Map (a.function bool) v) (hf : g.Map (a.function bool) f) (hi : g.Map a i) :
    g.Map (a.function bool) (fun p x j=>if v p x j then representative (i p x) (f p x) j else false) :=
  map_lambda (map_cond (map_apply hv.first (map_snd g a))
    (map_apply (map_representative hf hi).first (map_snd g a)) (map_false _))

end MinUncut.Preprocess.UEncoding

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformAlgebra
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open scoped BigOperators
variable {P X : Type} [Primcodable P] [Primcodable X] [AddCommMonoid X]

namespace UEncoding
variable {A B Γ : P → Type}

instance primcodableF₂ : Primcodable MinUncut.Inner.F₂ :=
  Primcodable.ofEquiv (Fin 2) MinUncut.Outer.fieldEncoding.code

abbrev field (P : Type) [Primcodable P] := fixed (P:=P) MinUncut.Outer.fieldEncoding

lemma out_field (a : UEncoding P A) {f : ∀p,A p → MinUncut.Inner.F₂}
    (hf : a.Map (field P) f) : a.Out f := hf.out 0
lemma map_field_add {a : UEncoding P A} {f g : ∀p,A p → MinUncut.Inner.F₂}
    (hf : a.Map (field P) f) (hg : a.Map (field P) g) :
    a.Map (field P) (fun p x=>f p x+g p x) :=
  ((out_field a hf).map₂ (out_field a hg) (Primrec.dom_finite _).to_comp).toFixed
lemma map_field_mul {a : UEncoding P A} {f g : ∀p,A p → MinUncut.Inner.F₂}
    (hf : a.Map (field P) f) (hg : a.Map (field P) g) :
    a.Map (field P) (fun p x=>f p x*g p x) :=
  ((out_field a hf).map₂ (out_field a hg) (Primrec.dom_finite _).to_comp).toFixed
lemma map_field_sum {g : UEncoding P Γ} {a : UEncoding P A} [∀p,Fintype (A p)]
    {f : ∀p,Γ p × A p → MinUncut.Inner.F₂} (hf : (g.prod a).Map (field P) f) :
    g.Map (field P) (fun p s=>∑x,f p (s,x)) :=
  (out_sum (out_field _ hf) (Primrec.dom_finite _).to_comp).toFixed
end UEncoding
end MinUncut.Preprocess

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformEquation
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Preprocess.Source
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncutGames.Reduction.CloneGap
open MinUncut.SourceTemplate UEncoding

variable {Γ : Par → Type} {e : UEncoding Par Γ}
lemma map_rawLocal {v : ∀p,Γ p → J p.1 → Bool} {π : ∀p,Γ p → J p.1 → I p.1}
    {f : ∀p,Γ p → Cube (I p.1)} {g μ : ∀p,Γ p → Cube (J p.1)}
    (hv : e.Map gc v) (hπ : e.Map (rs.function ls) π)
    (hf : e.Map fc f) (hg : e.Map gc g) (hμ : e.Map gc μ) :
    e.Map keys.equation (fun p x=>rawLocal (v p x) (π p x) (f p x) (g p x) (μ p x)) := by
  have ha : e.Map ls (fun p _=>leftAnchor p.1) :=
    map_lambda (map_false (e.prod (up positions)))
  have hfirst := map_comp (map_representative hf ha) (map_inl fc (gc.sum (fixed Encoding.unit)))
  have hdummy : e.Map keys (fun _ _=>Sum.inr (Sum.inr ())) :=
    map_comp (map_comp (map_const (Computable.const 0)) (map_inr gc (fixed Encoding.unit)))
      (map_inr fc (gc.sum (fixed Encoding.unit)))
  have hnone : e.Map keys.equation (fun p x=>
      ⟨.inl (representative (leftAnchor p.1) (f p x)),.inr (.inr ()),.inr (.inr ()),f p x (leftAnchor p.1)⟩) :=
    map_equation hfirst hdummy hdummy (map_apply hf ha)
  have hright (h : e.Map gc g) : (e.prod rs).Map keys
      (fun p x=>.inr (.inl (paddedRep (v p x.1) x.2 (g p x.1)))) :=
    map_comp (map_comp (map_padded hv.first h.first (map_snd e rs))
      (map_inl gc (fixed Encoding.unit))) (map_inr fc (gc.sum (fixed Encoding.unit)))
  have hthird := map_thirdQuery hπ hf hg hμ
  have hsome : (e.prod rs).Map keys.equation (fun p x=>
      ⟨.inl (representative (leftAnchor p.1) (f p x.1)),
       .inr (.inl (paddedRep (v p x.1) x.2 (g p x.1))),
       .inr (.inl (paddedRep (v p x.1) x.2 (thirdQuery (π p x.1) (f p x.1) (g p x.1) (μ p x.1)))),
       f p x.1 (leftAnchor p.1) ^^ f p x.1 (π p x.1 x.2) ^^ μ p x.1 x.2⟩) := by
    exact map_equation hfirst.first (hright hg)
      (map_comp (map_comp (map_padded hv.first hthird.first (map_snd e rs))
        (map_inl gc (fixed Encoding.unit))) (map_inr fc (gc.sum (fixed Encoding.unit))))
      (map_xor (map_xor (map_apply hf ha).first
         (map_apply hf.first (map_apply hπ.first (map_snd e rs))))
         (map_apply hμ.first (map_snd e rs)))
  apply (map_comp (map_pair (map_id e) (map_find_apply hv)) (map_option_elim hnone hsome)).ofEq
  intro p x
  rfl

def sigs := up signatures
def sls := up slotContexts
def context := (sigs.prod sls).prod tapes

lemma map_context_signature : context.Map sigs (fun _ x=>x.1.1) :=
  (map_fst sigs sls).first
lemma map_context_slot : context.Map sls (fun _ x=>x.1.2) :=
  (map_snd sigs sls).first
lemma map_context_first : context.Map fc (fun _ x=>x.2.1) :=
  map_comp (map_snd _ _) (map_fst _ _)
lemma map_context_last : context.Map gc (fun _ x=>x.2.2.2) :=
  ((map_snd (rs.function ds) gc).second (c:=fc)).second (c:=sigs.prod sls)
lemma map_context_noiseTape : context.Map (rs.function ds) (fun _ x=>x.2.2.1) :=
  ((map_fst (rs.function ds) gc).second (c:=fc)).second (c:=sigs.prod sls)
lemma map_context_valid : context.Map gc (fun _ x=>x.1.1.valid) :=
  map_lambda (map_comp (map_pair map_context_signature.first (map_snd context rs))
    (map_valid.pullback Computable.fst))
lemma map_context_project : context.Map (rs.function ls) (fun _ x=>x.1.1.project x.1.2) := by
  have hh := (map_project (g:=((signatures.prod slotContexts).prod rights))
    (map_fst signatures slotContexts).first
    (map_snd signatures slotContexts).first (map_snd _ _)).pullback
    (f:=(Prod.fst : Par → ℕ)) Computable.fst
  exact map_lambda (map_comp
    (map_pair (map_pair map_context_signature.first map_context_slot.first) (map_snd context rs)) hh)
lemma map_context_noise : context.Map gc
    (fun _ x=>MinUncutGames.Reduction.FiniteNoise.realizedNoise x.2.2.1) :=
  map_lambda (map_value_zero (map_apply map_context_noiseTape.first (map_snd context rs)))
lemma map_localEquation : context.Map keys.equation
    (fun _ x=>x.1.1.equation x.1.2 x.2) := by
  apply (map_rawLocal map_context_valid map_context_project map_context_first
    map_context_last map_context_noise).ofEq
  intro p x
  exact rawLocal_eq x.1.1.valid (x.1.1.project x.1.2) x.2
end MinUncut.Preprocess.Source

noncomputable section
namespace MinUncut.Preprocess.Syntax
open MinUncutGames.Foundations.PCP
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open MinUncutGames.Foundations.Hastad.SourceContexts
open MinUncut.Costed MinUncut.SourceTemplate UEncoding
variable {P Q : Type} [Primcodable P] [Primcodable Q] {A : P → Type} {c : UEncoding P A}
lemma O.tupleDigit {i : ∀p,A p → ℕ} (hi : c.Out i) : O c (fun p x=>tupleDigit (i p x)) :=
  ((O.fixed (.reg 0)).div ((O.fixed (.reg 2)).pow hi)).mod (O.fixed (.reg 2))
lemma O.slotWord {i j : ∀p,A p → ℕ} {s : ∀p,A p → Slot}
    (hi : c.Out i) (hs : c.Map (UEncoding.fixed slotEncoding) s) (hj : c.Out j) :
    O c (fun p x=>slotWord (i p x) (s p x) (j p x)) := by
  have hn := (out_code (UEncoding.fixed (P:=P) slotEncoding)).comp hs
  have hc := (out_const c (Computable.const 2)).map₂ hn (ca_mul Computable.fst Computable.snd)
  have hb := hc.map₂ hj (ca_add Computable.fst Computable.snd)
  exact ((O.fixed (.const 3)).add ((O.fixed (.const 6)).mul (O.tupleDigit hi))).add (.const hb) |>.at

lemma c_positiveExpr : C positiveExpr := by
  have hi : ((unitN.prod Source.positions).prod Source.slots).Out (fun _ x=>x.1.2.val) :=
    (out_code Source.positions).second.first
  have hs := map_snd (unitN.prod Source.positions) Source.slots
  have hw := O.slotWord hi hs (out_const _ (Computable.const 1))
  exact (hw.functionExpr (Computable.const 2) |>.functionExpr (Computable.const (2^3))).toC
lemma c_sameExpr : C sameExpr := by
  let c := (unitN.prod Source.coordinates).prod Source.coordinates
  have ha : c.Map Source.coordinates (fun _ x=>x.1.2) := (map_snd unitN Source.coordinates).first
  have hb : c.Map Source.coordinates (fun _ x=>x.2) := map_snd _ _
  have hai := (out_code Source.positions).comp (map_comp ha (map_fst _ _))
  have hbi := (out_code Source.positions).comp (map_comp hb (map_fst _ _))
  have has := map_comp ha (map_snd _ _)
  have hbs := map_comp hb (map_snd _ _)
  have hzero := out_const c (Computable.const 0)
  have hw := (O.slotWord hai has hzero).eq (O.slotWord hbi hbs hzero)
  exact (hw.functionExpr (Computable.const 2) |>.functionExpr
    (ca_pow (Computable.const 2) (ca_mul Computable.id (Computable.const 3)))).toC
lemma c_signatureExpr : C signatureExpr := by
  have hconst := C.const (ca_pow (ca_pow (Computable.const 2)
    (ca_mul Computable.id (Computable.const 3))) (ca_mul Computable.id (Computable.const 3)))
  exact c_sameExpr.add (hconst.mul c_positiveExpr)
lemma O.sourceLookup {u : P → ℕ} (hu : Computable u)
    {f : ∀p,A p × Signature (u p) → ℕ}
    (hf : (c.prod (Source.signatures.pullback u hu)).Out f) :
    O c (fun p x=>signatureLookup (fun s=>f p (x,s))) :=
  (O.fromC (c_signatureExpr.precomp hu)).lookup (out_constantTable hf)
lemma map_sourceSlot {u : P → ℕ} (hu : Computable u) {s : ∀p,A p → SlotContext (u p)}
    (hs : c.Map (Source.slotContexts.pullback u hu) s) :
    (c.prod (fin u hu)).Map (fixed slotEncoding) (fun p x=>s p x.1 x.2) := by
  have ht : c.Map ((fin u hu).function (fixed slotEncoding)) s := hs
  exact map_apply ht.first (map_snd c (fin u hu))
lemma O.sourceSampled {u : P → ℕ} (hu : Computable u) {s : ∀p,A p → SlotContext (u p)}
    (hs : c.Map (Source.slotContexts.pullback u hu) s) : O c (fun p x=>sampledExpr (s p x)) := by
  let d := c.prod (fin u hu)
  have hi : d.Out (fun _ x=>x.2.val) := (out_code (fin u hu)).second
  have hx := map_sourceSlot hu hs
  have hw : O d (fun p x=>MinUncut.SourceTemplate.slotWord x.2.val (s p x.1 x.2) 0) :=
    O.slotWord hi hx (out_const d (Computable.const 0))
  have hp : O d (fun _ x=>(AExpr.reg 1).pow x.2.val) := (O.fixed (.reg 1)).pow hi
  have hh : O d (fun p x=>.mul (MinUncut.SourceTemplate.slotWord x.2.val (s p x.1 x.2) 0) ((AExpr.reg 1).pow x.2.val)) := hw.mul hp
  exact hh.sum_fin hu
end MinUncut.Preprocess.Syntax

namespace MinUncut.Preprocess.Face
open MinUncut.Inner MinUncut.FiniteProof
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open UEncoding
open scoped BigOperators
variable {P : Type} [Primcodable P]
variable (m n : P → ℕ) (hm : Computable m) (hn : Computable n) (hnpos : ∀p,0<n p)

lemma map_faceSum : ((rows m n hm hn hnpos).function (field P)).Map
    ((points m n hm hn).function (field P)) (fun p x=>faceSum (m p) (n p) x) := by
  let r:=rows m n hm hn hnpos
  let v:=points m n hm hn
  let ax:=axes m hm
  let c:=(r.function (field P)).prod v
  have hx : (c.prod ax).Map v (fun _ x=>x.1.2) := (map_snd _ _).first
  have hi : (c.prod ax).Map ax (fun _ x=>x.2) := map_snd _ _
  have hr : (c.prod ax).Map r (fun _ x=>⟨x.2,face x.1.2 x.2⟩) :=
    map_comp (map_pair hx hi) (map_faceRow m n hm hn hnpos)
  have hf : (c.prod ax).Map (r.function (field P)) (fun _ x=>x.1.1) := (map_fst _ _).first
  exact map_lambda (map_field_sum (map_apply hf hr))

def codeGood (p : P) (x : Point (m p) (n p) → F₂) : Bool :=
  decide (∃f:Row (m p) (n p) → F₂,faceSum (m p) (n p) f=x)
include hnpos in
lemma map_codeGood : ((points m n hm hn).function (field P)).Map bool (codeGood m n) := by
  let r:=(rows m n hm hn hnpos).function (field P)
  let v:=(points m n hm hn).function (field P)
  have hh:=map_exists (map_bool_eq
    ((map_faceSum m n hm hn hnpos).second (c:=v)) (map_fst v r))
  apply hh.ofEq
  intro p x
  simp only [codeGood,decide_eq_true_eq]

def codeEquiv (p : P) : Code (m p) (n p) ≃
    {x:Point (m p) (n p) → F₂ // codeGood m n p x=true} where
  toFun x := ⟨x.val,by simpa only [codeGood,decide_eq_true_eq] using (LinearMap.mem_range.mp x.property)⟩
  invFun x := ⟨x.val,LinearMap.mem_range.mpr (by simpa only [codeGood,decide_eq_true_eq] using x.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def codes : UEncoding P (fun p=>Code (m p) (n p)) :=
  (((points m n hm hn).function (field P)).restrict (codeGood m n)
    (map_codeGood m n hm hn hnpos)).ofEquiv (codeEquiv m n)
lemma map_codeVal : (codes m n hm hn hnpos).Map ((points m n hm hn).function (field P))
    (fun _ x=>x.val) := by
  have hh := map_comp (map_to (((points m n hm hn).function (field P)).restrict (codeGood m n)
    (map_codeGood m n hm hn hnpos)) (codeEquiv m n))
    (map_restrict_val ((points m n hm hn).function (field P)) (codeGood m n)
      (map_codeGood m n hm hn hnpos))
  exact hh.ofEq (by intros; rfl)
lemma map_codeMk {Γ : P → Type} {g : UEncoding P Γ}
    {f : ∀p,Γ p → Point (m p) (n p) → F₂}
    (hf : g.Map ((points m n hm hn).function (field P)) f)
    (h : ∀p x,∃a:Row (m p) (n p) → F₂,faceSum (m p) (n p) a=f p x) :
    g.Map (codes m n hm hn hnpos) (fun p x=>⟨f p x,LinearMap.mem_range.mpr (h p x)⟩) := by
  have hh:=map_restrict_mk (map_codeGood m n hm hn hnpos) hf
    (by intro p x; simp only [codeGood,decide_eq_true_eq]; exact h p x)
  exact map_comp hh (map_from _ (codeEquiv m n))

end MinUncut.Preprocess.Face

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_UniformAlphabet
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess.Alphabet
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open UEncoding
open scoped BigOperators
variable {P : Type} [Primcodable P]
variable (t : P → ℕ) (ht : Computable t) (h : ∀p,Fin (t p) → Bool)
variable (hc : Computable (fun p=>(((Encoding.fin (t p)).function Encoding.bool).code (h p)).val))
def labelEquiv (p : P) : LocalTemplate.Alphabet (h p) ≃ (Slot t h p → F₂) where
  toFun x := fun j=>x j.1 j.2
  invFun x := fun j k=>x ⟨j,k⟩
  left_inv _ := rfl
  right_inv _ := rfl

def labels : UEncoding P (fun p=>LocalTemplate.Alphabet (h p)) :=
  ((slots t ht h hc).function (field P)).ofEquiv (labelEquiv t h)
def formsEquiv (p : P) : Forms (LocalTemplate.Alphabet (h p)) ≃ F₂ × (Slot t h p → F₂) :=
  (SampleEnumeration.formsCurryEquiv (Fin (t p)) (fun j=>Fin (width (h p j)))).trans
    (SampleEnumeration.formsPiEquiv (Slot t h p))
def forms : UEncoding P (fun p=>Forms (LocalTemplate.Alphabet (h p))) :=
  ((field P).prod ((slots t ht h hc).function (field P))).ofEquiv (formsEquiv t h)

omit [Primcodable P] in
lemma forms_apply (p : P) (f : Forms (LocalTemplate.Alphabet (h p))) (x : LocalTemplate.Alphabet (h p)) :
    f x=(formsEquiv t h p f).1+∑j:Slot t h p,(formsEquiv t h p f).2 j*labelEquiv t h p x j := by
  let e:=SampleEnumeration.formsCurryEquiv (Fin (t p)) (fun j=>Fin (width (h p j)))
  let f':=e f
  have he : f x=f' (labelEquiv t h p x) := rfl
  rw [he]
  change f' (labelEquiv t h p x)=f' 0+∑j:Slot t h p,
    (LinearEquiv.piRing F₂ F₂ (Slot t h p) F₂ f'.linear) j*labelEquiv t h p x j
  have hl := congrArg (fun L : (Slot t h p → F₂) →ₗ[F₂] F₂=>L (labelEquiv t h p x))
    ((LinearEquiv.piRing F₂ F₂ (Slot t h p) F₂).symm_apply_apply f'.linear)
  rw [LinearEquiv.piRing_symm_apply] at hl
  have hd:=congrFun f'.decomp (labelEquiv t h p x)
  change f' (labelEquiv t h p x)=f'.linear (labelEquiv t h p x)+f' 0 at hd
  rw [hd,←hl]
  simp only [smul_eq_mul,mul_comm]
  exact add_comm _ _

lemma map_forms_apply : ((forms t ht h hc).prod (labels t ht h hc)).Map (field P)
    (fun _ x=>x.1 x.2) := by
  let s:=slots t ht h hc
  let f:=forms t ht h hc
  let a:=labels t ht h hc
  let c:=f.prod a
  have hf : c.Map ((field P).prod (s.function (field P))) (fun p x=>formsEquiv t h p x.1) :=
    (map_to _ (formsEquiv t h)).first
  have ha : c.Map (s.function (field P)) (fun p x=>labelEquiv t h p x.2) :=
    (map_to _ (labelEquiv t h)).second
  have hcoef:=map_comp hf (map_snd _ _)
  have hv:=map_snd c s
  have hs:=map_field_sum (map_field_mul (map_apply hcoef.first hv) (map_apply ha.first hv))
  apply (map_field_add (map_comp hf (map_fst _ _)) hs).ofEq
  intro p x
  exact (forms_apply t h p x.1 x.2).symm
end MinUncut.Preprocess.Alphabet

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformFaceArray
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess.Alphabet
open MinUncut.Inner MinUncut.FiniteProof MinUncut.Outer
open UEncoding
variable {P : Type} [Primcodable P]
variable (t : P → ℕ) (ht : Computable t) (h : ∀p,Fin (t p) → Bool)
variable (hc : Computable (fun p=>(((MinUncutGames.Foundations.Hastad.SourceOccurrences.Encoding.fin (t p)).function
  MinUncutGames.Foundations.Hastad.SourceOccurrences.Encoding.bool).code (h p)).val))
variable (m n : P → ℕ) (hm : Computable m) (hn : Computable n) (hnpos : ∀p,0<n p)
def arrays : UEncoding P (fun p=>FaceArray (LocalTemplate.Alphabet (h p)) (m p) (n p)) :=
  (Face.rows m n hm hn hnpos).function (forms t ht h hc)
lemma map_labelCode : ((arrays t ht h hc m n hm hn hnpos).prod (labels t ht h hc)).Map
    (Face.codes m n hm hn hnpos) (fun _ x=>labelCode x.1 x.2) := by
  let r:=Face.rows m n hm hn hnpos
  let a:=arrays t ht h hc m n hm hn hnpos
  let l:=labels t ht h hc
  let c:=a.prod l
  have hb : (c.prod r).Map a (fun _ x=>x.1.1) := (map_fst _ _).first
  have hx : (c.prod r).Map l (fun _ x=>x.1.2) := (map_snd _ _).first
  have he : c.Map (r.function (field P)) (fun _ x r=>(x.1 r) x.2) :=
    map_lambda (map_comp (map_pair (map_apply hb (map_snd _ _)) hx) (map_forms_apply t ht h hc))
  exact Face.map_codeMk m n hm hn hnpos
    (map_comp he (Face.map_faceSum m n hm hn hnpos)) (by intro p x; exact ⟨_,rfl⟩)
end MinUncut.Preprocess.Alphabet

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_UniformDemandAlphabet
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess.Alphabet
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate MinUncut.FiniteProof
open MinUncutGames.Foundations.Hastad.SourceOccurrences UEncoding
attribute [local instance] Classical.propDecidable
variable {P : Type} [Primcodable P]
variable (t : P → ℕ) (ht : Computable t) (h : ∀p,Fin (t p) → Bool)
variable (hc : Computable (fun p=>(((Encoding.fin (t p)).function Encoding.bool).code (h p)).val))
def triples : UEncoding P (fun _=>Triple) := (positions (P:=P)).function (field P)
def ambient := (axes t ht).function (triples (P:=P))
def rhs := (axes t ht).function (field P)
def signatures : UEncoding P (fun p=>Signature (Fin (t p))) :=
  ((rhs t ht).prod (equalities t ht)).ofEquiv (fun p=>signatureEquiv (t p))
lemma map_rhs : (signatures t ht).Map (rhs t ht) (fun _ s=>s.rhs) := by
  have hh := map_comp (map_to ((rhs t ht).prod (equalities t ht)) (fun p=>signatureEquiv (t p)))
    (map_fst (rhs t ht) (equalities t ht))
  exact hh
lemma map_same : (signatures t ht).Map (equalities t ht) (fun _ s=>s.same) := by
  have hh := map_comp (map_to ((rhs t ht).prod (equalities t ht)) (fun p=>signatureEquiv (t p)))
    (map_snd (rhs t ht) (equalities t ht))
  exact hh
lemma map_origin : (signatures t ht).Map (ambient t ht) (fun _ s=>s.origin) := by
  let c:=signatures t ht
  let ax:=axes t ht
  let po:=positions (P:=P)
  have hh : ((c.prod ax).prod po).Map (field P) (fun _ x=>x.1.1.rhs x.1.2) :=
    map_apply (map_rhs t ht).first.first (map_snd c ax).first
  exact map_lambda (map_lambda hh)
lemma map_zeroLabel : (fixed (P:=P) Encoding.unit).Map (labels t ht h hc) (fun _ _=>0) := by
  let s:=slots t ht h hc
  have hf : (fixed (P:=P) Encoding.unit).Map (s.function (field P)) (fun _ _ _=>0) :=
    map_lambda (map_const (Computable.const 0))
  have hh := map_comp hf (map_from (s.function (field P)) (labelEquiv t h))
  exact hh
lemma projectSlot_apply (b : Bool) (pos : Fin 3) (x : Triple) (k : Fin (width b))
    (hk : k.val<3) : projectSlot b pos x k = if b then x pos else x ⟨k.val,hk⟩ := by
  cases b <;> rfl
lemma map_projectEval : (((positionsList t ht).prod (ambient t ht)).prod (slots t ht h hc)).Map
    (field P) (fun p x=>project (h p) x.1.1 x.1.2 x.2.1 x.2.2) := by
  let c:=(positionsList t ht).prod (ambient t ht)
  let sl:=slots t ht h hc
  let ax:=axes t ht
  let po:=positions (P:=P)
  have hi : (c.prod sl).Map ax (fun _ x=>x.2.1) := (map_slotAxis t ht h hc).second
  have hk : (c.prod sl).Map po (fun p x=>(slotEquiv t h p x.2).val.2) := (map_slotPosition t ht h hc).second
  have hpos : (c.prod sl).Map po (fun _ x=>x.1.1 x.2.1) :=
    map_apply (map_fst _ _).first hi
  have hm : (c.prod sl).Map (ax.function bool) (fun p _=>h p) := map_const hc
  have hh : (c.prod sl).Map bool (fun p x=>h p x.2.1) := map_apply hm hi
  have hx : (c.prod sl).Map (triples (P:=P)) (fun _ x=>x.1.2 x.2.1) :=
    map_apply (map_snd _ _).first hi
  apply (map_cond hh (map_apply hx hpos) (map_apply hx hk)).ofEq
  intro p x
  exact (projectSlot_apply _ _ _ _ _).symm
lemma map_project : ((positionsList t ht).prod (ambient t ht)).Map (labels t ht h hc)
    (fun p x=>project (h p) x.1 x.2) := by
  let c:=(positionsList t ht).prod (ambient t ht)
  let sl:=slots t ht h hc
  have hl : c.Map (sl.function (field P)) (fun p x y=>project (h p) x.1 x.2 y.1 y.2) :=
    map_lambda (map_projectEval t ht h hc)
  have hout := map_comp hl (map_from (sl.function (field P)) (labelEquiv t h))
  exact hout.ofEq (by intro p x; rfl)
lemma map_decode : (ambient t ht).Map (labels t ht h hc) (fun p x=>decode (h p) x) := by
  have hz : (ambient t ht).Map (positionsList t ht) (fun _ _ _=>0) :=
    map_lambda (map_const (Computable.const 0))
  have hh := map_comp (map_pair hz (map_id _)) (map_project t ht h hc)
  exact hh
lemma map_valid : ((signatures t ht).prod (ambient t ht)).Map bool
    (fun _ x=>decide (x.1.Valid x.2)) := by
  classical
  let c:=(signatures t ht).prod (ambient t ht)
  let ax:=axes t ht
  let po:=positions (P:=P)
  let tr:=triples (P:=P)
  have hx : (c.prod ax).Map tr (fun _ x=>x.1.2 x.2) :=
    map_apply (map_snd _ _).first (map_snd c ax)
  have hr : (c.prod ax).Map (field P) (fun _ x=>x.1.1.rhs x.2) :=
    map_apply (map_rhs t ht).first.first (map_snd c ax)
  have hpar : (c.prod ax).Map (field P) (fun _ x=>parity (x.1.2 x.2)) :=
    map_fixed_apply ((Encoding.fin 3).function fieldEncoding) fieldEncoding parity hx
  have hsame : (((c.prod ax).prod po).prod po).Map bool
      (fun _ x=>x.1.1.1.1.same x.1.1.2 x.1.2 x.2) :=
    map_apply (map_apply (map_apply (map_same t ht).first.first.first.first
      (map_snd c ax).first.first) (map_snd (c.prod ax) po).first) (map_snd _ _)
  have hp : (((c.prod ax).prod po).prod po).Map (field P)
      (fun _ x=>x.1.1.1.2 x.1.1.2 x.1.2) :=
    map_apply hx.first.first (map_snd (c.prod ax) po).first
  have hq : (((c.prod ax).prod po).prod po).Map (field P)
      (fun _ x=>x.1.1.1.2 x.1.1.2 x.2) :=
    map_apply hx.first.first (map_snd _ _)
  have he:=map_forall (map_forall (map_or (map_not hsame) (map_bool_eq hp hq)))
  apply (map_forall (map_and (map_bool_eq hpar hr) he)).ofEq
  intro p x
  simp only [Signature.Valid,decide_eq_true_eq]
  apply decide_eq_decide.mpr
  simp only [Bool.and_eq_true, Bool.not_eq_true',Bool.or_eq_true,decide_eq_true_eq]
  constructor
  · intro H i
    refine ⟨(H i).1,?_⟩
    intro j k hj
    rcases (H i).2 j k with h|h
    · simp [hj] at h
    · exact h
  · intro H i
    refine ⟨(H i).1,?_⟩
    intro j k
    by_cases hj:x.1.same i j k=true
    · exact Or.inr ((H i).2 j k hj)
    · exact Or.inl (Bool.eq_false_iff.mpr hj)
end MinUncut.Preprocess.Alphabet

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformGrid
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MinUncut.Preprocess
open MinUncut.FiniteGaussian
open scoped BigOperators
attribute [local irreducible] endpoint qIntegral primitive
lemma c_rawCellWeight : Computable (fun p : GridData × ℕ=>
    qIntegral p.1.r (endpoint p.1.T p.1.L p.2) (endpoint p.1.T p.1.L (p.2+1)) /
      qIntegral p.1.r (-p.1.T) p.1.T) := by
  have hr:=c_gridData_r.comp (Computable.fst (α:=GridData) (β:=ℕ))
  have ht:=ca_ratCast (c_gridData_T.comp (Computable.fst (α:=GridData) (β:=ℕ)))
  have hl:=c_gridData_L.comp (Computable.fst (α:=GridData) (β:=ℕ))
  have he : Computable (fun p : GridData × ℕ=>endpoint p.1.T p.1.L p.2) :=
    ca_endpoint ht hl Computable.snd
  have he' : Computable (fun p : GridData × ℕ=>endpoint p.1.T p.1.L (p.2+1)) :=
    ca_endpoint ht hl (ca_add Computable.snd (ca_const 1))
  have ha : Computable (fun p : GridData × ℕ=>qIntegral p.1.r
      (endpoint p.1.T p.1.L p.2) (endpoint p.1.T p.1.L (p.2+1))) :=
    ca_qIntegral hr he he'
  have hb : Computable (fun p : GridData × ℕ=>qIntegral p.1.r (-p.1.T) p.1.T) :=
    ca_qIntegral hr (computable_ratNeg.comp ht) ht
  exact ca_ratDiv ha hb

namespace Grid
open UEncoding MinUncut.Inner
variable {P : Type} [Primcodable P]
variable (m n : P → ℕ) (hm : Computable m) (hn : Computable n) (hnpos : ∀p,0<n p)
variable (g : P → GridData) (hg : Computable g)
def coordinates : UEncoding P (fun p=>TestCoordinates (m p) (n p)) :=
  (Face.points m n hm hn).sum ((Face.points m n hm hn).sum (Face.codes m n hm hn hnpos))
def cells := fin (fun p=>(g p).L) (c_gridData_L.comp hg)
def samples := (coordinates m n hm hn hnpos).function (cells g hg)
lemma out_midpoint : (cells g hg).Out (fun p i=>midpoint (g p).T (g p).L i.val) :=
  ((out_const _ (ca_ratCast (c_gridData_T.comp hg))).pair
    ((out_const _ (c_gridData_L.comp hg)).pair (out_code (cells g hg)))).map c_midpoint
lemma out_cellWeight : (cells g hg).Out (fun p i=>cellWeight (g p).r (g p).T (g p).L i) :=
  ((out_const _ hg).pair (out_code (cells g hg))).map c_rawCellWeight
lemma out_gridWeight : (samples m n hm hn hnpos g hg).Out (fun p q=>gridWeight (g p) q) := by
  let a:=samples m n hm hn hnpos g hg
  let i:=coordinates m n hm hn hnpos
  exact out_prod ((out_cellWeight g hg).comp (map_apply (map_fst a i) (map_snd a i))) computable_ratMul
end Grid
end MinUncut.Preprocess

namespace MinUncut.Preprocess.Grid
open MinUncut.Inner MinUncut.FiniteGaussian UEncoding
variable {P : Type} [Primcodable P]
variable (m n : P → ℕ) (hm : Computable m) (hn : Computable n) (hnpos : ∀p,0<n p)
variable (g : P → GridData) (hg : Computable g)
def indices := bool.prod (Face.codes m n hm hn hnpos)
variable {Γ : P → Type} {c : UEncoding P Γ}
lemma out_coord {q : ∀p,Γ p → TestCoordinates (m p) (n p) → Fin (g p).L}
    {i : ∀p,Γ p → TestCoordinates (m p) (n p)}
    (hq : c.Map (samples m n hm hn hnpos g hg) q)
    (hi : c.Map (coordinates m n hm hn hnpos) i) :
    c.Out (fun p x=>midpoint (g p).T (g p).L (q p x (i p x))) :=
  (out_midpoint g hg).comp (map_apply hq hi)
lemma out_sign {z : ∀p,Γ p → Code (m p) (n p)} {i : ∀p,Γ p → Point (m p) (n p)}
    (hz : c.Map (Face.codes m n hm hn hnpos) z) (hi : c.Map (Face.points m n hm hn) i) :
    c.Out (fun p x=>qSign ((z p x).val (i p x))) :=
  (out_field c (map_apply (map_comp hz (Face.map_codeVal m n hm hn hnpos)) hi)).map
    (Primrec.dom_finite qSign).to_comp
lemma out_scoreSummand (σ : P → ℚ) (hσ : Computable σ) :
    (((samples m n hm hn hnpos g hg).prod (indices m n hm hn hnpos)).prod (Face.points m n hm hn)).Out
      (fun p x=>(midpoint (g p).T (g p).L (x.1.1 (.inl x.2))+
        (if x.1.2.1 then σ p else 0)*midpoint (g p).T (g p).L (x.1.1 (.inr (.inl x.2))))*
        qSign (x.1.2.2.val x.2)) := by
  let s:=samples m n hm hn hnpos g hg
  let z:=indices m n hm hn hnpos
  let pt:=Face.points m n hm hn
  let c:=(s.prod z).prod pt
  have hq : c.Map s (fun _ x=>x.1.1) := (map_fst _ _).first
  have hz : c.Map z (fun _ x=>x.1.2) := (map_snd _ _).first
  have hi : c.Map pt (fun _ x=>x.2) := map_snd _ _
  have hx := out_coord m n hm hn hnpos g hg hq
    (map_comp hi (map_inl pt (pt.sum (Face.codes m n hm hn hnpos))))
  have hy := out_coord m n hm hn hnpos g hg hq
    (map_comp (map_comp hi (map_inl pt (Face.codes m n hm hn hnpos)))
      (map_inr pt (pt.sum (Face.codes m n hm hn hnpos))))
  have hs : c.Out (fun p x=>if x.1.2.1 then σ p else 0) :=
    Out.cond (map_comp hz (map_fst _ _)) (out_const _ hσ) (out_const _ (ca_const 0))
  exact (hx.ratAdd (hs.ratMul hy)).ratMul
    (out_sign m n hm hn hnpos (map_comp hz (map_snd _ _)) hi)
lemma map_scoreTable (σ η : P → ℚ) (hσ : Computable σ) (hη : Computable η) :
    ((samples m n hm hn hnpos g hg).prod (indices m n hm hn hnpos)).Map bool
      (fun p x=>rationalScoreTable (σ p) (η p)
        (fun i=>midpoint (g p).T (g p).L (x.1 i)) x.2) := by
  let s:=samples m n hm hn hnpos g hg
  let z:=indices m n hm hn hnpos
  let pt:=Face.points m n hm hn
  let co:=Face.codes m n hm hn hnpos
  let c:=s.prod z
  have hq : c.Map s (fun _ x=>x.1) := map_fst _ _
  have hz : c.Map z (fun _ x=>x.2) := map_snd _ _
  have hc : c.Map co (fun _ x=>x.2.2) := map_comp hz (map_snd _ _)
  have hy := out_coord m n hm hn hnpos g hg hq
    (map_comp (map_comp hc (map_inr pt co)) (map_inr pt (pt.sum co)))
  have he : c.Out (fun p x=>if x.2.1 then η p else 0) :=
    Out.cond (map_comp hz (map_fst _ _)) (out_const _ hη) (out_const _ (ca_const 0))
  exact (out_sum (out_scoreSummand m n hm hn hnpos g hg σ hσ) computable_ratAdd).algebraicNonneg
    (he.ratMul hy) (out_const _ (ca_pow hn hm))
end MinUncut.Preprocess.Grid

namespace MinUncut.Preprocess
open MinUncut.Inner MinUncut.FiniteProof MinUncut.FiniteGaussian MinUncut.Outer
open MinUncutGames.Foundations.Hastad.SourceOccurrences UEncoding
open scoped BigOperators
attribute [local irreducible] gridWeight
namespace Weights
variable {P : Type} [Primcodable P]
variable (t : P → ℕ) (ht : Computable t) (h : ∀p,Fin (t p) → Bool)
variable (hc : Computable (fun p=>(((Encoding.fin (t p)).function Encoding.bool).code (h p)).val))
variable (m n : P → ℕ) (hm : Computable m) (hn : Computable n) (hnpos : ∀p,0<n p)
variable (g : P → GridData) (hg : Computable g)
def localSamples := (Alphabet.arrays t ht h hc m n hm hn hnpos).prod
  ((Alphabet.arrays t ht h hc m n hm hn hnpos).prod ((Face.codes m n hm hn hnpos).prod
    (Grid.samples m n hm hn hnpos g hg)))
lemma out_rationalRowDensity (a : P → ℚ) (ha : Computable a) :
    ((Alphabet.forms t ht h hc).prod (Alphabet.forms t ht h hc)).Out
      (fun p x=>RowNoise.rationalRowDensity (a p) x.1 x.2) := by
  classical
  let c:=(Alphabet.forms t ht h hc).prod (Alphabet.forms t ht h hc)
  have hc' : Computable (fun p=>Fintype.card (Forms (LocalTemplate.Alphabet (h p)))) :=
    computableCard (Alphabet.forms t ht h hc)
  have hi : c.Out (fun p x=>if x.2=x.1 then (Fintype.card (Forms (LocalTemplate.Alphabet (h p))):ℚ) else 0) := by
    apply (Out.cond (map_bool_eq (map_snd _ _) (map_fst _ _))
      (out_const c (ca_ratCast hc')) (out_const c (ca_const 0))).ofEq
    intro p x
    simp only [decide_eq_true_eq]
  exact ((out_const c (ca_const 1)).ratSub (out_const c ha)).ratMul hi |>.ratAdd (out_const c ha)
lemma out_rationalDensity (a : P → ℚ) (ha : Computable a) :
    ((Alphabet.arrays t ht h hc m n hm hn hnpos).prod (Alphabet.arrays t ht h hc m n hm hn hnpos)).Out
      (fun p x=>RowNoise.rationalDensity (a p) x.1 x.2) := by
  let ar:=Alphabet.arrays t ht h hc m n hm hn hnpos
  let ro:=Face.rows m n hm hn hnpos
  have hb : ((ar.prod ar).prod ro).Map ar (fun _ x=>x.1.1) := (map_fst _ _).first
  have hc' : ((ar.prod ar).prod ro).Map ar (fun _ x=>x.1.2) := (map_snd _ _).first
  have hr : ((ar.prod ar).prod ro).Map ro (fun _ x=>x.2) := map_snd _ _
  exact out_prod ((out_rationalRowDensity t ht h hc a ha).comp
    (map_pair (map_apply hb hr) (map_apply hc' hr))) computable_ratMul
end Weights
namespace Denominator
variable {P : Type} [Primcodable P]
variable (t m n : P → ℕ) (ht : Computable t) (hm : Computable m) (hn : Computable n) (hnpos : ∀p,0<n p)
variable (g : P → GridData) (hg : Computable g)
include hm hn hnpos hg in
lemma c_gridDenominator : Computable (fun p=>gridDenominator (m p) (n p) (g p)) := by
  let a : UEncoding P (fun p=>TestCoordinates (m p) (n p) → Fin (g p).L) :=
    Grid.samples m n hm hn hnpos g hg
  have hw : a.Out (fun p q=>(gridWeight (g p) q).den) :=
    (Grid.out_gridWeight m n hm hn hnpos g hg).map primrec_ratDen.to_comp
  have hh := @computable_prod P ℕ _ _ (fun p=>TestCoordinates (m p) (n p) → Fin (g p).L)
    _ a (fun _=>inferInstance) _ hw Primrec.nat_mul.to_comp
  apply hh.of_eq
  intro p
  unfold gridDenominator
  apply Finset.prod_congr (by ext; simp)
  intro q _
  rfl
end Denominator

open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate MinUncut.FiniteProof MinUncut.FiniteGaussian
open MinUncutGames.Foundations.Hastad.SourceOccurrences UEncoding
namespace Queries
variable {P : Type} [Primcodable P]
variable (t : P → ℕ) (ht : Computable t) (h : ∀p,Fin (t p) → Bool)
variable (hc : Computable (fun p=>(((Encoding.fin (t p)).function Encoding.bool).code (h p)).val))
variable (m n : P → ℕ) (hm : Computable m) (hn : Computable n) (hnpos : ∀p,0<n p)
def table := (Alphabet.labels t ht h hc).function (bool (P:=P))
def queryEquiv (p : P) : Query (h p) ≃ Bool × (Alphabet (h p) → Bool) × (Alphabet (h p) → Bool) where
  toFun q := (q.first,q.left,q.right)
  invFun q := ⟨q.1,q.2.1,q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
def queries : UEncoding P (fun p=>Query (h p)) :=
  (bool.prod ((table t ht h hc).prod (table t ht h hc))).ofEquiv (queryEquiv t h)
lemma map_first : (queries t ht h hc).Map bool (fun _ q=>q.first) := by
  have hh:=map_comp (map_to (bool.prod ((table t ht h hc).prod (table t ht h hc))) (queryEquiv t h)) (map_fst _ _)
  exact hh
lemma map_left : (queries t ht h hc).Map (table t ht h hc) (fun _ q=>q.left) := by
  have hh:=map_comp (map_comp (map_to (bool.prod ((table t ht h hc).prod (table t ht h hc))) (queryEquiv t h)) (map_snd _ _)) (map_fst _ _)
  exact hh
lemma map_right : (queries t ht h hc).Map (table t ht h hc) (fun _ q=>q.right) := by
  have hh:=map_comp (map_comp (map_to (bool.prod ((table t ht h hc).prod (table t ht h hc))) (queryEquiv t h)) (map_snd _ _)) (map_snd _ _)
  exact hh

end Queries
end MinUncut.Preprocess

namespace MinUncut.Preprocess.Queries
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate MinUncut.FiniteProof MinUncut.FiniteGaussian
open MinUncutGames.Foundations.Hastad.SourceOccurrences UEncoding
variable {P : Type} [Primcodable P]
variable (t : P → ℕ) (ht : Computable t) (h : ∀p,Fin (t p) → Bool)
variable (hc : Computable (fun p=>(((Encoding.fin (t p)).function Encoding.bool).code (h p)).val))
variable {Γ : P → Type} {c : UEncoding P Γ}
variable {Q : ∀p,Γ p → Query (h p)} {pos : ∀p,Γ p → Fin (t p) → Fin 3}
variable {sig : ∀p,Γ p → Signature (Fin (t p))} {x : ∀p,Γ p → Fin (t p) → Triple}
variable (hQ : c.Map (queries t ht h hc) Q) (hp : c.Map (Alphabet.positionsList t ht) pos)
variable (hs : c.Map (Alphabet.signatures t ht) sig)
lemma zero_map : c.Map (Alphabet.labels t ht h hc) (fun _ _=>0) := by
  have hunit : c.Map (fixed Encoding.unit) (fun _ _=>()) := map_const (Computable.const 0)
  have hh := map_comp hunit (Alphabet.map_zeroLabel t ht h hc)
  exact hh
include hQ hp hs in
lemma map_leftBase : c.Map bool (fun p a=>(Q p a).leftBase (pos p a) (sig p a)) := by
  have hf:=map_comp hQ (map_first t ht h hc)
  have hl:=map_comp hQ (map_left t ht h hc)
  have ho:=map_comp hs (Alphabet.map_origin t ht)
  have hz:=map_comp (map_pair hp ho) (Alphabet.map_project t ht h hc)
  exact map_cond hf (map_apply hl hz) (map_apply hl (zero_map t ht h hc))
include hQ hp hs in
lemma map_leftTableEval (hx : c.Map (Alphabet.ambient t ht) x) :
    c.Map bool (fun p a=>(Q p a).leftTable (pos p a) (sig p a) (x p a)) := by
  have hf:=map_comp hQ (map_first t ht h hc)
  have hl:=map_comp hQ (map_left t ht h hc)
  have hv:=map_comp (map_pair hs hx) (Alphabet.map_valid t ht)
  have hproj:=map_comp (map_pair hp hx) (Alphabet.map_project t ht h hc)
  have hd:=map_comp hx (Alphabet.map_decode t ht h hc)
  have hfalse : c.Map bool (fun _ _=>false) := map_const (Computable.const 0)
  have hbase:=map_leftBase t ht h hc hQ hp hs
  have hzero:=map_apply hl (zero_map t ht h hc)
  apply (map_cond hf (map_cond hv (map_bool_eq hbase (map_apply hl hproj)) hfalse)
    (map_bool_eq hzero (map_apply hl hd))).ofEq
  intro p a
  simp only [Query.leftTable, Bool.beq_eq_decide_eq]
  split_ifs <;> simp_all only [decide_eq_true_eq, ite_true, ite_false]
include hQ in
lemma map_rightTableEval (hx : c.Map (Alphabet.ambient t ht) x) :
    c.Map bool (fun p a=>(Q p a).rightTable (x p a)) := by
  have hr:=map_comp hQ (map_right t ht h hc)
  have hd:=map_comp hx (Alphabet.map_decode t ht h hc)
  apply (map_bool_eq (map_apply hr (zero_map t ht h hc)) (map_apply hr hd)).ofEq
  intro p a
  simp only [Query.rightTable, Bool.beq_eq_decide_eq]
include hQ hp hs in
lemma map_localSign : c.Map bool (fun p a=>(Q p a).localSign (pos p a) (sig p a)) := by
  have hr:=map_comp hQ (map_right t ht h hc)
  apply (map_bool_eq (map_leftBase t ht h hc hQ hp hs) (map_apply hr (zero_map t ht h hc))).ofEq
  intro p a
  simp only [Query.localSign, Bool.beq_eq_decide_eq]
include hQ hp hs in
lemma map_leftTable : c.Map ((Alphabet.ambient t ht).function bool)
    (fun p a=>(Q p a).leftTable (pos p a) (sig p a)) :=
  map_lambda (map_leftTableEval t ht h hc hQ.first hp.first hs.first (map_snd _ _))
include hQ in
lemma map_rightTable : c.Map ((Alphabet.ambient t ht).function bool)
    (fun p a=>(Q p a).rightTable) :=
  map_lambda (map_rightTableEval t ht h hc hQ.first (map_snd _ _))
end MinUncut.Preprocess.Queries

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_DemandExpressions
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MinUncut.Preprocess.Syntax
open MinUncut.Costed MinUncut.Costed.SourceWords
open MinUncut.Outer MinUncut.Outer.LocalTemplate UEncoding
variable {P : Type} [Primcodable P] {A : P → Type} {c : UEncoding P A}
lemma O.demandLookup {t : P → ℕ} (ht : Computable t)
    {f : ∀p,A p × Signature (Fin (t p)) → ℕ}
    (hf : (c.prod (Alphabet.signatures t ht)).Out f) :
    O c (fun p x=>MinUncut.Costed.SourceWords.signatureLookup (fun s=>f p (x,s))) :=
  (O.fromC (c_demandSignatureExpr.precomp ht)).lookup (out_constantTable hf)
end MinUncut.Preprocess.Syntax

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_DemandQueryEffectivity
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess.Syntax
open MinUncut.Costed MinUncut.Costed.SourceWords
open MinUncut.Outer MinUncut.Outer.LocalTemplate UEncoding
open MinUncutGames.Foundations.Hastad.SourceOccurrences
variable {P : Type} [Primcodable P] {A : P → Type} {c : UEncoding P A}
variable (t : P → ℕ) (ht : Computable t) (h : ∀p,Fin (t p) → Bool)
variable (hc : Computable (fun p=>(((Encoding.fin (t p)).function Encoding.bool).code (h p)).val))
variable {Q : ∀p,A p → Query (h p)} {pos : ∀p,A p → Fin (t p) → Fin 3}
variable (hQ : c.Map (Queries.queries t ht h hc) Q)
variable (hp : c.Map (Alphabet.positionsList t ht) pos)
include hQ hp in
lemma O.leftExpr : O c (fun p x=>leftExpr (Q p x) (pos p x)) := by
  let s:=Alphabet.signatures t ht
  have htab:=Queries.map_leftTable t ht h hc hQ.first hp.first (map_snd c s)
  have hnum : (c.prod s).Out (fun p x=>tableNumber ((Q p x.1).leftTable (pos p x.1) x.2)) :=
    (out_code ((Alphabet.ambient t ht).function bool)).comp htab
  have hl:=O.demandLookup ht hnum
  have hf:=map_comp hQ (Queries.map_first t ht h hc)
  have hfirst := O.fromC (c_firstExpr.precomp ht) (c:=c)
  have hsecond:=O.secondAddress t ht h hc hp
  exact hl.add ((O.const (out_const c (ca_pow (Computable.const 2)
    (ca_pow (Computable.const (2^3)) ht)))).mul (O.choose hf hfirst hsecond))
include hQ hp in
lemma O.rightExpr : O c (fun p x=>rightExpr (Q p x) (pos p x)) := by
  have htab:=Queries.map_rightTable t ht h hc hQ
  have hnum : c.Out (fun p x=>tableNumber (Q p x).rightTable) :=
    (out_code ((Alphabet.ambient t ht).function bool)).comp htab
  exact (O.const hnum).add ((O.const (out_const c (ca_pow (Computable.const 2)
    (ca_pow (Computable.const (2^3)) ht)))).mul (O.secondAddress t ht h hc hp))
include hQ hp in
lemma O.signExpr : O c (fun p x=>signExpr (Q p x) (pos p x)) := by
  let s:=Alphabet.signatures t ht
  have hs:=Queries.map_localSign t ht h hc hQ.first hp.first (map_snd c s)
  exact O.demandLookup ht (out_boolNat hs)
include hQ hp in
lemma out_queryExpressions : c.Out (fun p x=>
    ([leftExpr (Q p x) (pos p x),rightExpr (Q p x) (pos p x),signExpr (Q p x) (pos p x)]).map
      (fun e=>e.program.code)) :=
  (O.leftExpr t ht h hc hQ hp).cons ((O.rightExpr t ht h hc hQ hp).cons
    ((O.signExpr t ht h hc hQ hp).cons (out_const c (Computable.const []))))
end MinUncut.Preprocess.Syntax

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_LocalBodyEffectivity
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate MinUncut.FiniteGaussian
open MinUncutGames.Foundations.Hastad.SourceOccurrences UEncoding
open MinUncut.Costed MinUncut.Costed.SourceWords MinUncut.FiniteProof
attribute [local irreducible] rationalScoreTable MinUncut.FiniteGaussian.midpoint
namespace DemandBody
variable {P : Type} [Primcodable P] {p : P}
variable (t : P → ℕ) (ht : Computable t) (h : ∀p,Fin (t p) → Bool)
variable (hc : Computable (fun p=>(((Encoding.fin (t p)).function Encoding.bool).code (h p)).val))
variable (m n : P → ℕ) (hm : Computable m) (hn : Computable n) (hnpos : ∀p,0<n p)
variable (g : P → GridData) (hg : Computable g)
def bodyQuery (σ η : ℚ) (x : (LocalSample (Alphabet (h p)) (m p) (n p) (g p) × Test) × (Fin (t p) → Fin 3)) :=
  query (h p) x.1.1.1 x.1.1.2.1 x.1.1.2.2.1
    (rationalScoreTable σ η (fun i=>midpoint (g p).T (g p).L (x.1.1.2.2.2 i))) x.1.2
end DemandBody
end MinUncut.Preprocess

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformEquationOutput
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess.UEncoding
open MinUncutGames.Foundations.Hastad.SourceOccurrences MinUncutGames.Reduction.CloneGap
variable {P : Type} [Primcodable P] {A B : P → Type} {X : Type} [Primcodable X]
lemma map_eqTuple (a : UEncoding P A) : a.equation.Map (a.prod (a.prod (a.prod bool)))
    (fun p e=>equationEquiv (A p) e) := map_to _ (fun p=>equationEquiv (A p))
lemma map_eqFirst (a : UEncoding P A) : a.equation.Map a (fun _ e=>e.first) := by
  have hh := map_comp (map_eqTuple a) (map_fst a (a.prod (a.prod bool)))
  exact hh
lemma map_eqSecond (a : UEncoding P A) : a.equation.Map a (fun _ e=>e.second) := by
  have hh := map_comp (map_eqTuple a) (map_snd a (a.prod (a.prod bool)))
  have hh := map_comp hh (map_fst a (a.prod bool))
  exact hh
lemma map_eqThird (a : UEncoding P A) : a.equation.Map a (fun _ e=>e.third) := by
  have hh := map_comp (map_eqTuple a) (map_snd a (a.prod (a.prod bool)))
  have hh := map_comp hh (map_snd a (a.prod bool))
  have hh := map_comp hh (map_fst a bool)
  exact hh
lemma map_eqRhs (a : UEncoding P A) : a.equation.Map bool (fun _ e=>e.rhs) := by
  have hh := map_comp (map_eqTuple a) (map_snd a (a.prod (a.prod bool)))
  have hh := map_comp hh (map_snd a (a.prod bool))
  have hh := map_comp hh (map_snd a bool)
  exact hh
end MinUncut.Preprocess.UEncoding

end

noncomputable section
namespace MinUncut.Preprocess.Syntax
open MinUncutGames.Foundations.PCP
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open MinUncutGames.Foundations.Hastad.SourceContexts
open MinUncut.Costed MinUncut.SourceTemplate UEncoding
variable {P : Type} [Primcodable P] {A : P → Type} {c : UEncoding P A}
lemma O.sourceAddress {u : P → ℕ} (hu : Computable u) {s : ∀p,A p → SlotContext (u p)}
    (hs : c.Map (Source.slotContexts.pullback u hu) s)
    {f : ∀p,A p × Signature (u p) → LocalKey (u p)}
    (hf : (c.prod (Source.signatures.pullback u hu)).Map
      (Source.keys.pullback (fun p=>(u p,0)) (hu.pair (Computable.const 0))) f) :
    O c (fun p x=>addressExpr (s p x) (fun S=>f p (x,S))) := by
  have hp := hu.pair (Computable.const 0)
  have tag := O.sourceLookup hu ((Source.out_keyTag.pullback hp).comp hf)
  have tab := O.sourceLookup hu ((Source.out_keyTable.pullback hp).comp hf)
  have reg1 : O c (fun p _=>(AExpr.reg 1).pow (u p)) := (O.fixed (.reg 1)).pow (out_const c hu)
  have reg2 : O c (fun p _=>(AExpr.reg 2).pow (u p)) := (O.fixed (.reg 2)).pow (out_const c hu)
  have b2 := ca_pow (Computable.const 2) (ca_pow (Computable.const 2) hu)
  have b8 := ca_pow (Computable.const 2) (ca_pow (Computable.const 8) hu)
  have left := reg1.mul (O.const (out_const c b2))
  have ha := left.add (reg2.mul (O.const (out_const c b8)))
  have hb := left.add (tab.add ((O.const (out_const c b8)).mul (O.fixed (.reg 0))))
  have hc := tab.add ((O.const (out_const c b2)).mul (O.sourceSampled hu hs))
  exact (tag.eq (O.fixed (.const 0))).cond ((tag.eq (O.fixed (.const 1))).cond ha hb) hc

abbrev sourceArgs := Source.sls.prod Source.tapes
lemma map_sourceContext : (sourceArgs.prod Source.sigs).Map Source.context
    (fun _ x=>((x.2,x.1.1),x.1.2)) :=
  map_pair (map_pair (map_snd _ _) ((map_fst _ _).first)) ((map_snd _ _).first)
lemma out_sourceEquationExpressions : sourceArgs.Out
    (fun _ x=>(equationExpressions x.1 x.2).map (fun e=>e.program.code)) := by
  have hs := map_fst Source.sls Source.tapes
  have he := map_comp map_sourceContext Source.map_localEquation
  have h1 := map_comp he (map_eqFirst Source.keys)
  have h2 := map_comp he (map_eqSecond Source.keys)
  have h3 := map_comp he (map_eqThird Source.keys)
  have hb := (out_boolNat (map_comp he (map_eqRhs Source.keys)))
  have a := O.sourceAddress (c:=sourceArgs) Computable.fst hs h1
  have b := O.sourceAddress (c:=sourceArgs) Computable.fst hs h2
  have d := O.sourceAddress (c:=sourceArgs) Computable.fst hs h3
  have e := O.sourceLookup (c:=sourceArgs) Computable.fst hb
  exact a.cons (b.cons (d.cons (e.cons (out_const sourceArgs (Computable.const [])))))
lemma c_sourceExpressions : Computable (fun p : Source.Par=>
    (sourceExpressions p.1 p.2).map (fun e=>e.program.code)) := by
  have h := (out_list out_sourceEquationExpressions).enumerate
  apply (Primrec.list_flatten.to_comp.comp (Primrec.list_flatten.to_comp.comp h)).of_eq
  intro p
  simp only [sourceExpressions,List.flatMap_def,List.map_flatten,List.flatten_flatten,List.map_map,Function.comp_def]
  rfl

open MinUncut.Costed MinUncut.SourceTemplate MinUncut.CodeEffective
lemma c_sourceVariableExpr : C sourceVariableExpr := by
  exact ((C.fixed (.reg 0)).pow Computable.id |>.mul (C.const
      (ca_pow (Computable.const 2) (ca_pow (Computable.const 2) Computable.id)))).add
    (((C.fixed (.reg 1)).pow Computable.id |>.mul (C.const
      (ca_pow (Computable.const 2) (ca_pow (Computable.const 8) Computable.id)))).add (C.fixed (.const 1)))
lemma c_sourceCountExpr : C (fun p : Source.Par=>sourceCountExpr p.1 p.2) := by
  have hl : Computable (fun p : Source.Par=>(sourceExpressions p.1 p.2).length) :=
    (Computable.list_length.comp c_sourceExpressions).of_eq (fun p=>List.length_map ..)
  exact (((C.fixed (.reg 1)).pow Computable.fst).mul (C.const hl)).div (C.fixed (.const 4))
lemma c_sourceStageCode : Computable (fun p : Source.Par=>(sourceStageProgram p.1 p.2).code) := by
  have hf := p_forwardCode.to_comp.comp c_sourceExpressions ((C.fixed (.reg 1)).pow Computable.fst)
  have hh := computable_cons.comp (c_sourceVariableExpr.precomp Computable.fst)
    (computable_cons.comp c_sourceCountExpr hf)
  apply hh.of_eq
  intro p
  rw [forwardCode_eq]
  rfl
end MinUncut.Preprocess.Syntax

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_DemandOrder
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MinUncut.Preprocess.DemandOrder
open MinUncut.OuterSmoothness MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate MinUncut.FiniteGaussian MinUncut.FiniteProof
open MinUncutGames.Foundations.Hastad.SourceOccurrences UEncoding
open MinUncut.Costed MinUncut.Costed.SourceWords
attribute [local irreducible] localWeight MinUncut.FiniteProof.multiplicity innerDenominator rationalScoreTable MinUncut.FiniteGaussian.midpoint
abbrev Body (t : ℕ) (h : Fin t → Bool) (m n : ℕ) (g : GridData) :=
  (LocalSample (Alphabet h) m n g × Test) × (Fin t → Fin 3)

def bodyExpr {t m n : ℕ} {h : Fin t → Bool} {g : GridData} (σ η : ℚ) (x : Body t h m n g) : List AExpr :=
  let Q:=query h x.1.1.1 x.1.1.2.1 x.1.1.2.2.1
    (rationalScoreTable σ η (fun i=>midpoint g.T g.L (x.1.1.2.2.2 i))) x.1.2
  [leftExpr Q x.2,rightExpr Q x.2,signExpr Q x.2]
def bodyRepetitions {t m n : ℕ} {h : Fin t → Bool} {g : GridData} (a : ℚ) (b : Test → ℚ) (x : Body t h m n g) :=
  multiplicity (innerDenominator t m n g a b) (localWeight g a (b x.1.2) x.1.2 x.1.1)
def indexEquiv (t k m n : ℕ) (g : GridData) :
    (ΣH:FixedSets (Fin t) k,Body t (hiddenSet H.val) m n g) ≃ Index (Fin t) k m n g where
  toFun x := (x.2.1.2,⟨x.1,x.2.2,x.2.1.1⟩)
  invFun x := ⟨x.2.1,((x.2.2.2,x.1),x.2.2.1)⟩
  left_inv _ := rfl
  right_inv _ := rfl

open MinUncut.Inner MinUncut.Outer MinUncut.FiniteGaussian MinUncut.Costed MinUncut.Costed.SourceWords UEncoding
end MinUncut.Preprocess.DemandOrder

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_DemandStageEffectivity
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess.Syntax
open MinUncut.Costed MinUncut.Costed.SourceWords MinUncut.CodeEffective
lemma c_tupleCountExpr : C tupleCountExpr := (C.fixed (.reg 1)).pow Computable.id
lemma c_variableCountExpr : C variableCountExpr := by
  exact ((((C.fixed (.reg 0)).pow (ca_const 3)).mul (C.fixed (.const 2))).pow Computable.id |>.add
    (((C.fixed (.reg 0)).add (((C.fixed (.reg 0)).pow (ca_const 3)).mul
      (C.fixed (.const 2)))).pow Computable.id)).mul
      (C.const (ca_pow (ca_const 2) (ca_pow (ca_const (2^3)) Computable.id)))
lemma c_demandStageCode {P : Type} [Primcodable P] (es : P → List AExpr)
    (he : Computable (fun p=>(es p).map (fun e=>e.program.code)))
    (t D : P → ℕ) (ht : Computable t) (hD : Computable D) :
    Computable (fun p=>(demandStageProgram (es p) (t p) (D p)).code) := by
  have hl : Computable (fun p=>(es p).length) :=
    (Computable.list_length.comp he).of_eq (fun p=>List.length_map ..)
  have hv := c_variableCountExpr.precomp ht
  have hu : C (fun p=>unitCountExpr (es p) (t p)) :=
    ((c_tupleCountExpr.precomp ht).mul (C.const hl)).div (C.fixed (.const 3))
  have hk : C (fun p=>thresholdExpr (t p) (D p)) :=
    (C.const (ca_mul (ca_const 5) hD)).mul (c_tupleCountExpr.precomp ht)
  have hf := p_forwardCode.to_comp.comp he (c_tupleCountExpr.precomp ht)
  apply (computable_cons.comp hv (computable_cons.comp hu (computable_cons.comp hk hf))).of_eq
  intro p
  rw [forwardCode_eq]
  rfl
end MinUncut.Preprocess.Syntax

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_UniformFiniteSum
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess.UEncoding
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open scoped BigOperators
variable {P X : Type} [Primcodable P] [Primcodable X] [AddCommMonoid X]
  {A : P → Type} [∀p,Fintype (A p)]
lemma computable_sum {a : UEncoding P A} {f : ∀p,A p → X} (hf : a.Out f)
    (hadd : Computable₂ (fun x y : X=>x+y)) : Computable (fun p=>∑x,f p x) := by
  have hh:=out_sum (g:=fixed Encoding.unit) hf.second hadd
  obtain ⟨h,hr,he⟩:=hh
  exact (hr.comp (Computable.id.pair (Computable.const 0))).of_eq (fun p=>he p ())
end MinUncut.Preprocess.UEncoding

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_ArithmeticTactic
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.LocalTemplate.indexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

set_option maxHeartbeats 1000000
section
namespace MinUncut.Preprocess
open MinUncut.Inner MinUncut.Outer MinUncut.FiniteGaussian
attribute [fun_prop] c_listBound c_radicand
attribute [fun_prop] c_qError
@[fun_prop] lemma c_gT : Computable (fun p : ℕ × ℕ × ℚ × ℚ × GridData=>p.2.2.2.2.T) :=
  c_gridData_T.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
@[fun_prop] lemma c_gL : Computable (fun p : ℕ × ℕ × ℚ × ℚ × GridData=>p.2.2.2.2.L) :=
  c_gridData_L.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
@[fun_prop] lemma c_gr : Computable (fun p : ℕ × ℕ × ℚ × ℚ × GridData=>p.2.2.2.2.r) :=
  c_gridData_r.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
@[fun_prop] lemma c_gE : Computable (fun p : ℕ × ℕ × ℚ × ℚ × GridData=>p.2.2.2.1) :=
  Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
lemma grid_check_0 : ComputablePred (fun p : ℕ × ℕ × ℚ × ℚ × GridData=>1 ≤ p.2.2.2.2.T) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)
lemma grid_check_1 : ComputablePred (fun p : ℕ × ℕ × ℚ × ℚ × GridData=>1 ≤ p.2.2.2.2.L) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)
lemma grid_check_2 : ComputablePred (fun p : ℕ × ℕ × ℚ × ℚ × GridData=>(p.1:ℚ)/(p.2.2.2.2.T:ℚ)^2 < p.2.2.2.1/4) :=
  ca_ratLt (ca_ratDiv (ca_ratCast Computable.fst) (ca_ratPow (ca_ratCast c_gT) (ca_const 2)))
    (ca_ratDiv c_gE (ca_const 4))
lemma grid_check_3 : ComputablePred (fun p : ℕ × ℕ × ℚ × ℚ × GridData=>2*(p.2.1:ℚ)*p.2.2.1*p.2.2.2.2.T/p.2.2.2.2.L < p.2.2.2.1/4) :=
  ca_ratLt (ca_ratDiv (ca_ratMul (ca_ratMul
    (ca_ratMul (ca_const 2) (ca_ratCast (Computable.fst.comp Computable.snd)))
    (Computable.fst.comp (Computable.snd.comp Computable.snd))) (ca_ratCast c_gT)) (ca_ratCast c_gL))
    (ca_ratDiv c_gE (ca_const 4))
lemma c_gErrorArg : Computable (fun p : ℕ × ℕ × ℚ × ℚ × GridData=>((p.2.2.2.2.T:ℚ)^2/2)) :=
  ca_ratDiv (ca_ratPow (ca_ratCast c_gT) (ca_const 2)) (ca_const 2)
lemma c_gError : Computable (fun p : ℕ × ℕ × ℚ × ℚ × GridData=>qError p.2.2.2.2.r ((p.2.2.2.2.T:ℚ)^2/2)) :=
  (c_qError.comp (c_gr.pair c_gErrorArg)).of_eq (by intro p; rfl)
lemma c_gCoef : Computable (fun p : ℕ × ℕ × ℚ × ℚ × GridData=>2*(p.1:ℚ)*p.2.2.2.2.T) :=
  ca_ratMul (ca_ratMul (ca_const 2) (ca_ratCast Computable.fst)) (ca_ratCast c_gT)
lemma grid_check_4 : ComputablePred (fun p : ℕ × ℕ × ℚ × ℚ × GridData=>2*(p.1:ℚ)*p.2.2.2.2.T*qError p.2.2.2.2.r ((p.2.2.2.2.T:ℚ)^2/2) < p.2.2.2.1/4) :=
  ca_ratLt (ca_ratMul c_gCoef c_gError) (ca_ratDiv c_gE (ca_const 4))
lemma grid_check_computable : ComputablePred (fun p : ℕ × ℕ × ℚ × ℚ × GridData=>p.2.2.2.2.Check p.1 p.2.1 p.2.2.1 p.2.2.2.1) :=
  ca_and grid_check_0 (ca_and grid_check_1 (ca_and grid_check_2 (ca_and grid_check_3 (grid_check_4))))
end MinUncut.Preprocess

end
section
namespace MinUncut.Preprocess
open MinUncut.FiniteGaussian

def gridExtract (n : ℕ) : GridData :=
  ⟨gridField (gridTail n),gridField (gridTail (gridTail n)),
    gridField (gridTail (gridTail (gridTail n)))⟩
lemma gridExtract_encode (g : GridData) : gridExtract (oldGridEncode g)=g := by
  simp only [oldGridEncode_eq,gridExtract,gridTail,gridField,Nat.unpair_pair,Nat.add_sub_cancel_right]
lemma gridDecode_eq (n : ℕ) : oldGridDecode n =
    if oldGridEncode (gridExtract n)=n then some (gridExtract n) else none := by
  cases h : oldGridDecode n with
  | none =>
    split
    · next he =>
        have hk := @Encodable.encodek GridData instEncodableGridData (gridExtract n)
        change oldGridDecode (oldGridEncode (gridExtract n))=some (gridExtract n) at hk
        rw [he,h] at hk
        cases hk
    · rfl
  | some g =>
    have he := oldGridDecode_canonical n g h
    have hx : gridExtract n=g := by rw [←he,gridExtract_encode]
    simp only [hx,he,ite_true]

lemma c_gridMk : Computable gridDataEquiv.symm :=
  (Primrec.of_equiv_symm (e:=gridDataEquiv)).to_comp
lemma gridExtract_eq : gridExtract = fun n => gridDataEquiv.symm
    (gridField (gridTail n),gridField (gridTail (gridTail n)),
      gridField (gridTail (gridTail (gridTail n)))) := by
  funext n
  simp only [gridExtract,gridDataEquiv,Equiv.coe_fn_symm_mk]
lemma c_gridExtract : Computable gridExtract := by
  rw [gridExtract_eq]
  exact c_gridMk.comp c_gridExtractPair
lemma c_oldGridEncode : Computable oldGridEncode := by
  have hp : Computable₂ Nat.pair := Primrec₂.natPair.to_comp
  rw [show oldGridEncode=(fun g : GridData=>Nat.pair (Nat.pair 0 0+1)
    (Nat.pair (Nat.pair 0 g.T+1) (Nat.pair (Nat.pair 0 g.L+1)
      (Nat.pair (Nat.pair 0 g.r+1) (Nat.pair 0 0))))) from funext oldGridEncode_eq]
  exact hp.comp (ca_const _) (hp.comp (ca_add (hp.comp (ca_const 0) c_gridData_T) (ca_const 1))
    (hp.comp (ca_add (hp.comp (ca_const 0) c_gridData_L) (ca_const 1))
      (hp.comp (ca_add (hp.comp (ca_const 0) c_gridData_r) (ca_const 1)) (ca_const _))))
lemma c_oldGridDecode : Computable oldGridDecode := by
  have he : ComputablePred (fun n=>oldGridEncode (gridExtract n)=n) :=
    (Primrec.eq.computablePred.decide.comp ((c_oldGridEncode.comp c_gridExtract).pair Computable.id)).computablePred
  exact (Computable.cond he.decide (Computable.option_some.comp c_gridExtract) (ca_const none)).of_eq
    (by intro n; simp only [Bool.cond_decide]; exact (gridDecode_eq n).symm)
end MinUncut.Preprocess

end
section
namespace MinUncut.Preprocess
open MinUncut.Inner MinUncut.Outer MinUncut.FiniteGaussian

attribute [local irreducible] selectedInner

def gridPredicate (x : ℕ × ℕ × ℚ × ℚ) (g : GridData) : Prop :=
  if 0≤x.2.2.1 ∧ 0<x.2.2.2 then g.Check x.1 x.2.1 x.2.2.1 x.2.2.2 else g=⟨0,0,0⟩
instance instDecidableRelProdNatRatGridDataGridPredicate : DecidableRel gridPredicate := fun _ _=>by unfold gridPredicate; infer_instance
lemma grid_exists (x : ℕ × ℕ × ℚ × ℚ) : ∃g,gridPredicate x g := by
  unfold gridPredicate
  split_ifs with h
  · exact GridData.exists_check x.1 x.2.1 h.1 h.2
  · exact ⟨_,rfl⟩
noncomputable def selectedGrid (x : ℕ × ℕ × ℚ × ℚ) : GridData :=
  searchWith instEncodableGridData grid_exists x
lemma selectedGrid_eq (d S : ℕ) (A ε : ℚ) (hA : 0≤A) (hε : 0<ε) :
    selectedGrid (d,S,A,ε)=GridData.select d S A ε hA hε := by
  unfold selectedGrid searchWith GridData.select
  congr 1
  funext g
  simp only [gridPredicate,hA,hε,and_self,ite_true]
lemma c_grid_valid : ComputablePred (fun x : ℕ × ℕ × ℚ × ℚ=>0≤x.2.2.1 ∧ 0<x.2.2.2) :=
  ca_and (ca_ratLe (ca_const 0) (Computable.fst.comp (Computable.snd.comp Computable.snd)))
    (ca_ratLt (ca_const 0) (Computable.snd.comp (Computable.snd.comp Computable.snd)))
lemma c_grid_pred : ComputablePred (fun p : (ℕ × ℕ × ℚ × ℚ) × GridData=>gridPredicate p.1 p.2) := by
  have hc := grid_check_computable.decide.comp (Computable.fst.comp Computable.fst |>.pair
    ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
      ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))).pair
        ((Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))).pair Computable.snd))))
  have he : Computable (fun p : (ℕ × ℕ × ℚ × ℚ) × GridData=>decide (p.2=⟨0,0,0⟩)) :=
    ComputablePred.decide ((Primrec.eq.computablePred.decide.comp
      (Computable.snd.pair (ca_const (⟨0,0,0⟩ : GridData)))).computablePred)
  have hh := Computable.cond (c_grid_valid.decide.comp Computable.fst) hc he
  exact ⟨inferInstance,hh.of_eq (by
    intro p
    simp only [gridPredicate,Bool.cond_decide]
    split_ifs <;> rfl)⟩
lemma c_selectedGrid : Computable selectedGrid :=
  computable_searchWith instEncodableGridData c_oldGridDecode c_grid_pred grid_exists ⟨0,0,0⟩
end MinUncut.Preprocess

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_CompleteGraphProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MinUncut.Preprocess
open MinUncut.Inner MinUncut.Outer MinUncut.FiniteGaussian UEncoding
open MinUncutGames.Foundations.Hastad.SourceOccurrences MinUncut.OuterSmoothness.Density
attribute [local irreducible] selectedInner selectedOuter
open MinUncut.Costed MinUncut.Costed.SourceWords MinUncut.SourceTemplate MinUncut.OuterSmoothness

lemma c_chosenRate : Computable (fun K=>rationalRate (parameterJ K) (selectedInner K)) :=
  ca_ratDiv (ca_ratPow (c_eta.comp c_parameterJ) (ca_const 2)) (ca_ratCast c_chosenM)
lemma c_fixedSetCard : Computable (fun K=>Fintype.card (FixedSets (Fin (chosenT K)) (chosenL K))) := by
  let a:=sets chosenT c_chosenT
  let d:∀K,Finset (Fin (chosenT K))→Bool:=fun K S=>decide (S.card=chosenL K)
  have hd : a.Map bool d := ((out_setCard chosenT c_chosenT).pair (out_const a c_chosenL)).map Primrec.eq.computablePred.decide |>.toBool
  have hc := computableCard (a.restrict d hd)
  apply hc.of_eq
  intro K
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun S=>by simp [d]))

end MinUncut.Preprocess

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_SelectedSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Preprocess
attribute [local irreducible] selectedInner selectedOuter
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncutGames.Foundations MinUncutGames.Foundations.Hastad
open MinUncutGames.Integration.SourceParameters MinUncut.Costed.SourceWords MinUncut.SourceTemplate
def chosenError (K : ℕ) := (selectedParameters K).sourceError
def chosenNoise (K : ℕ) := SourceNoiseParameter.noiseDenominator (chosenError K)
lemma c_chosenError : Computable chosenError := by
  have hd := ca_ratDiv (c_outerData_b4.comp c_selectedOuter) (ca_ratCast c_chosenT)
  have hp:=ca_ratLe (ca_const (1/2:ℚ)) hd
  exact (Computable.cond hp.decide (ca_const (1/2:ℚ)) hd).of_eq (by intro K; simp [chosenError,Outer.Parameters.sourceError,min_def,selectedParameters,chosenT])
lemma c_chosenNoise : Computable chosenNoise := by
  exact ca_add (primrec_ratDen.to_comp.comp c_chosenError) (ca_const 2)
attribute [local irreducible] chosenNoise sourceStageProgram
end MinUncut.Preprocess

end
end

end OAI
end


