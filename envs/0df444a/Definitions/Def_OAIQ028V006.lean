-- Prove2me | Definitions.Def_OAIQ028V006
-- name    : OAIQ028V006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T00:13:57.884083+00:00
-- url     : https://prove2.me/theorems/2d617946-4a1e-4ab5-84c2-57f136817333
-- title:
--   Definitions bundle OAIQ028V006 of the split of OpenAI, The Factor-Two Hardness Threshold for Vertex Cover (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.VertexCover.explicit_cover_gap` and `OAI.VertexCover.every_fixed_factor_below_two`, carved from OpenAI's openai/math development (OpenAI, *The Factor-Two Hardness Threshold for Vertex Cover (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 362 declarations of OpenAI's Lean: 106 definitions, 2 instances and 254 theorems. The definitions and types are `OAI.UniqueGames.Foundations.PCP.PoweringLabels.encode`, `OAI.UniqueGames.Foundations.PCP.PoweringMomentBound.windowEvent`, `OAI.UniqueGames.Foundations.PCP.PoweringOpinions.decoded`, `OAI.UniqueGames.Foundations.PCP.PoweringOpinions.honestLabels`, `OAI.UniqueGames.Foundations.PCP.PoweringOpinions.matchFn`, `OAI.UniqueGames.Foundations.PCP.PoweringOpinions.opinionAt`, `OAI.UniqueGames.Foundations.PCP.PoweringOpinions.sampleOpinion`, `OAI.UniqueGames.Foundations.PCP.PoweringPortReindex.ballEquiv`, `OAI.UniqueGames.Foundations.PCP.PoweringPortReindex.dartEquiv`, `OAI.UniqueGames.Foundations.PCP.PoweringPortReindex.labelEquiv`, `OAI.UniqueGames.Foundations.PCP.PoweringPortReindex.pullAccepts`, `OAI.UniqueGames.Foundations.PCP.PoweringPortReindex.pullSelector`, `OAI.UniqueGames.Foundations.PCP.PoweringSoundness.decodedError`, `OAI.UniqueGames.Foundations.PCP.PoweringSoundness.poweredRejection`, `OAI.UniqueGames.Foundations.PCP.PoweringTableSemantics.EncodedLabeling`, `OAI.UniqueGames.Foundations.PCP.PoweringTableSemantics.RawLabeling`, `OAI.UniqueGames.Foundations.PCP.PoweringTableSemantics.decodeLabeling`, `OAI.UniqueGames.Foundations.PCP.PoweringTableSemantics.encodeLabeling`, `OAI.UniqueGames.Foundations.PCP.PoweringTables.mathematicalGraph`, `OAI.UniqueGames.Foundations.PCP.PoweringTables.table`, `OAI.UniqueGames.Foundations.PCP.PoweringTest.baseGraph`, `OAI.UniqueGames.Foundations.PCP.PoweringTest.decodedBad`, `OAI.UniqueGames.Foundations.PCP.PoweringTest.witness`, `OAI.UniqueGames.Foundations.PCP.PoweringWalks.rightFromPivot`, `OAI.UniqueGames.Foundations.PCP.PoweringWitness.endpointWitness`, `OAI.UniqueGames.Foundations.PCP.PoweringWitness.vertexWitness`, `OAI.UniqueGames.Foundations.PCP.PreprocessingGuarantees.roundLabels`, `OAI.UniqueGames.Foundations.PCP.PreprocessingRegularSoundness.roundLabels`, `OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.familyCloudTable`, `OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.regularize`, `OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.regularizeInput`, `OAI.UniqueGames.Foundations.PCP.PreprocessingTables.output`, `OAI.UniqueGames.Foundations.PCP.PreprocessingTables.overlayFamily`, `OAI.UniqueGames.Foundations.PCP.PreprocessingTables.padded`, `OAI.UniqueGames.Foundations.PCP.PreprocessingTables.preprocess`, `OAI.UniqueGames.Foundations.PCP.RawInitialTables.dartOrder`, `OAI.UniqueGames.Foundations.PCP.RawInitialTables.eventOrder`, `OAI.UniqueGames.Foundations.PCP.RawInitialTables.labelOrder`, `OAI.UniqueGames.Foundations.PCP.RawInitialTables.raw64`, `OAI.UniqueGames.Foundations.PCP.RawInitialTables.slotOrder` and 66 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `VertexCover_PCP_PoweringCounting`, `VertexCover_PCP_PoweringFinalConstants`, `VertexCover_PCP_PoweringGap`, `VertexCover_PCP_PoweringLabels`, `VertexCover_PCP_PoweringLazy`, `VertexCover_PCP_PoweringMomentBound`, `VertexCover_PCP_PoweringOpinions`, `VertexCover_PCP_PoweringPortReindex`, `VertexCover_PCP_PoweringReturn`, `VertexCover_PCP_PoweringSoundness`, `VertexCover_PCP_PoweringTableSemantics`, `VertexCover_PCP_PoweringTables`, `VertexCover_PCP_PoweringTest`, `VertexCover_PCP_PoweringWalks`, `VertexCover_PCP_PoweringWitness`, `VertexCover_PCP_PreprocessingCloudIndex`, `VertexCover_PCP_PreprocessingGuarantees`, `VertexCover_PCP_PreprocessingLevels`, `VertexCover_PCP_PreprocessingPaddingTables`, `VertexCover_PCP_PreprocessingRegularSoundness`, `VertexCover_PCP_PreprocessingRegularTables`, `VertexCover_PCP_PreprocessingTableSpectral`, `VertexCover_PCP_PreprocessingTables`, `VertexCover_PCP_RawInitialTables`, `VertexCover_PCP_RoundGap`, `VertexCover_PCP_RoundTableGap`, `VertexCover_PCP_RoundTables`, `VertexCover_PCP_SpectralCut`, `VertexCover_PCP_SpectralReturn`, `VertexCover_PCP_TableGapReduction`, `VertexCover_PCP_TableIteration`, `VertexCover_Repetition_AlphabetBudget`, `VertexCover_Repetition_CompletedSampling`, `VertexCover_Repetition_Completion`, `VertexCover_Repetition_LocalSimulation`, `VertexCover_Repetition_MaskedVariation`, `VertexCover_Repetition_PartialReveal`, `VertexCover_Repetition_ProfileBounds`, `VertexCover_Repetition_ProfileCorrection`, `VertexCover_Repetition_QuestionMarginal`, `VertexCover_Repetition_Reveal`, `VertexCover_Repetition_RightProfileBounds`, `VertexCover_Repetition_SelectedCommon`, `VertexCover_Repetition_SelectedCommonMarginal`, `VertexCover_Repetition_SelectedInformation`, `VertexCover_Repetition_SelectedJoint`, `VertexCover_Repetition_SelectedJointGame`, `VertexCover_Repetition_SelectedMarginal`, `VertexCover_Repetition_SelectedProfileBudget`, `VertexCover_Repetition_SelectedProfiles`, `VertexCover_Repetition_SelectionSequence`, `VertexCover_Repetition_SharedSampling`.
--
--   **Imports.** It imports the bundles `OAIQ028V003` and `OAIQ028V004` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ028V008`.
-- source:
--   OpenAI, The Factor-Two Hardness Threshold for Vertex Cover (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Factor-Two-Hardness-Threshold-for-Vertex-Cover-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ028V003
import Definitions.Def_OAIQ028V004

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringWalks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                      

namespace UniqueGames.Foundations.PCP.PoweringWalks

variable {V D : Type*}

theorem pivotEquiv_fst (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      (pivotEquiv G n k w).1 = edgeAt G n w k := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · change (pivotEquiv G n j (advanceTail G w)).1 =
        edgeAt G n (advanceTail G w) j
      exact ih j (advanceTail G w)

theorem pivotEquiv_succ_apply (G : PortGraph V D)
    (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 2)) :
    pivotEquiv G (n + 1) k.succ w =
      ((pivotEquiv G n k (advanceTail G w)).1,
       Fin.cases (G.rot (w.1, w.2 0)).2
         (pivotEquiv G n k (advanceTail G w)).2) := rfl

def rightFromPivot (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) → Edge V D → (Fin n → D) → V
  | 0, _, e, _ => next G e.1 e.2
  | n + 1, k, e, r => Fin.cases
      (wordEnd G (n + 1) (next G e.1 e.2) r)
      (fun j => rightFromPivot G n j e (fun m => r m.succ)) k

theorem leftFromPivot_actual (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      leftFromPivot G n k (pivotEquiv G n k w).1.1 (pivotEquiv G n k w).2 = w.1 := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · rw [pivotEquiv_succ_apply]
      change next G
        (leftFromPivot G n j (pivotEquiv G n j (advanceTail G w)).1.1
          (pivotEquiv G n j (advanceTail G w)).2)
        (G.rot (w.1, w.2 0)).2 = w.1
      rw [ih j (advanceTail G w)]
      change (G.rot ((G.rot (w.1, w.2 0)).1, (G.rot (w.1, w.2 0)).2)).1 = w.1
      exact congrArg Prod.fst (rot_rot G (w.1, w.2 0))

theorem rightFromPivot_actual (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      rightFromPivot G n k (pivotEquiv G n k w).1 (pivotEquiv G n k w).2 =
        endpoint G w := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · rw [pivotEquiv_succ_apply]
      change rightFromPivot G n j (pivotEquiv G n j (advanceTail G w)).1
        (pivotEquiv G n j (advanceTail G w)).2 = endpoint G w
      rw [ih j (advanceTail G w)]
      rfl

end UniqueGames.Foundations.PCP.PoweringWalks

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.PoweringLabels

open PoweringWalks
open scoped BigOperators

variable {V D A : Type*}

instance finiteBall [Finite D] (G : PortGraph V D) (t : Nat) (v : V) :
    Finite (Ball G t v) :=
  Finite.of_surjective (wordToBall G t v) (wordToBall_surjective G t v)

def encode (G : PortGraph V D) (t : Nat) (v : V) (ℓ : Ball G t v → A) :
    PaddedLabel D t A := fun w => ℓ (wordToBall G t v w)

theorem decode_encode {G : PortGraph V D} {t : Nat} {v : V}
    (S : AddressSelector G t v) (ℓ : Ball G t v → A) :
    decode S (encode G t v ℓ) = ℓ := by
  funext u
  change ℓ (wordToBall G t v (S.address u)) = ℓ u
  rw [S.correct]

end UniqueGames.Foundations.PCP.PoweringLabels

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_SpectralReturn
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.PoweringLabels.finiteBall _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_rot _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.lookup_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GraphTransport.reindex_rot _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGames.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.PortTables.rotation_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PoweringReach.headFromEnd_val _root_.OAI.UniqueGames.Foundations.PCP.PoweringReach.tailFromStart_val _root_.OAI.UniqueGames.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringTest.poweredGraph_tail_true _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_true _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_next _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_rot_apply _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.zigzag_rot_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.SpectralReturn

open PoweringWalks
open scoped BigOperators

noncomputable section

section Averages

variable {A B : Type*} [Fintype A] [Fintype B]

theorem correlation_sub_const [Nonempty A] (f g : A → ℝ) («c» d : ℝ) :
    correlation (fun x => f x - «c») (fun x => g x - d) =
      correlation f g - d * mean f - «c» * mean g + «c» * d := by
  have h : (fun x => (f x - «c») * (g x - d)) =
      (fun x => f x * g x - d * f x - «c» * g x + «c» * d) := by
    funext x
    ring
  unfold correlation
  rw [h, mean_add, mean_sub, mean_sub, mean_mul_left, mean_mul_left, mean_const]

end Averages

section Graph

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
  (G : PortGraph V D)

omit [Fintype V] [Nonempty V] in
theorem operator_sub_const (f : V → ℝ) («c» : ℝ) :
    averagingOperator G (fun v => f v - «c») = fun v => averagingOperator G f v - «c» := by
  funext v
  change mean (fun d => f (G.rot (v, d)).1 - «c») = _
  rw [mean_sub, mean_const]
  rfl

omit [Nonempty V] in
theorem mean_iterate (n : Nat) (f : V → ℝ) : mean (iterateOperator G n f) = mean f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterateOperator, mean_operator, ih]

omit [Fintype V] [Nonempty V] in
theorem iterate_sub_const (n : Nat) (f : V → ℝ) («c» : ℝ) :
    iterateOperator G n (fun v => f v - «c») = fun v => iterateOperator G n f v - «c» := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterateOperator, ih, operator_sub_const]; rfl

omit [Nonempty V] [Nonempty D] in

theorem mean_markedStep (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (f : V → ℝ) :
    mean (markedStep G bad f) = correlation (edgeProfile bad) f := by
  calc
    mean (markedStep G bad f) =
        mean (fun e : V × D => if bad e then f (G.rot e).1 else 0) := by
      exact (mean_prod (fun e : V × D => if bad e then f (G.rot e).1 else 0)).symm
    _ = mean (fun e : V × D => if bad (G.rot e)
          then f (G.rot (G.rot e)).1 else 0) :=
      (mean_equiv G.rot (fun e : V × D => if bad e then f (G.rot e).1 else 0)).symm
    _ = mean (fun e : V × D => if bad e then f e.1 else 0) := by
      congr 1
      funext e
      rw [reversal e, G.rot_involutive e]
    _ = mean (fun v => mean (fun d => if bad (v, d) then f v else 0)) :=
      mean_prod (fun e : V × D => if bad e then f e.1 else 0)
    _ = correlation (edgeProfile bad) f := by
      unfold correlation
      congr 1
      funext v
      have h : (fun d => if bad (v, d) then f v else 0) =
          (fun d => (if bad (v, d) then (1 : ℝ) else 0) * f v) := by
        funext d
        cases bad (v, d) <;> simp
      rw [h, mean_mul_right]
      rfl

omit [Nonempty V] [Nonempty D] in
theorem returnMass_eq_correlation (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (gap : Nat) :
    returnMass G bad gap = correlation (edgeProfile bad)
      (iterateOperator G gap (edgeProfile bad)) :=
  mean_markedStep G bad reversal _

omit [Nonempty V] in
theorem iterate_energy_bound (lambda : ℝ) (certificate : SpectralCertificate G lambda)
    (f : V → ℝ) (hf : mean f = 0) (n : Nat) :
    energy (iterateOperator G n f) ≤ (lambda ^ n) ^ 2 * energy f := by
  induction n with
  | zero => simp [iterateOperator]
  | succ n ih =>
      calc
        energy (iterateOperator G (n + 1) f) ≤
            lambda ^ 2 * energy (iterateOperator G n f) :=
          certificate.contraction _ ((mean_iterate G n f).trans hf)
        _ ≤ lambda ^ 2 * ((lambda ^ n) ^ 2 * energy f) :=
          mul_le_mul_of_nonneg_left ih (sq_nonneg lambda)
        _ = (lambda ^ (n + 1)) ^ 2 * energy f := by rw [pow_succ]; ring

omit [Nonempty V] in
theorem zero_mean_correlation_bound (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (f : V → ℝ)
    (hf : mean f = 0) (n : Nat) :
    correlation f (iterateOperator G n f) ≤ lambda ^ n * energy f := by
  have hsq : correlation f (iterateOperator G n f) ^ 2 ≤
      (lambda ^ n * energy f) ^ 2 := by
    calc
      _ ≤ energy f * energy (iterateOperator G n f) := correlation_sq_le _ _
      _ ≤ energy f * ((lambda ^ n) ^ 2 * energy f) :=
        mul_le_mul_of_nonneg_left (iterate_energy_bound G lambda certificate f hf n)
          (energy_nonnegative f)
      _ = _ := by ring
  exact le_of_sq_le_sq hsq
    (mul_nonneg (pow_nonneg certificate.nonnegative n) (energy_nonnegative f))

theorem correlation_centered (f : V → ℝ) (n : Nat) :
    correlation f (iterateOperator G n f) = mean f ^ 2 +
      correlation (fun v => f v - mean f)
        (iterateOperator G n (fun v => f v - mean f)) := by
  rw [iterate_sub_const, correlation_sub_const, mean_iterate]
  ring

end Graph

section Profiles

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]

omit [Fintype V] [Nonempty V] [Nonempty D] in
theorem edgeProfile_nonnegative (bad : V × D → Bool) (v : V) : 0 ≤ edgeProfile bad v :=
  mean_nonnegative _ (fun d => by cases bad (v, d) <;> norm_num)

omit [Fintype V] [Nonempty V] in
theorem edgeProfile_le_one (bad : V × D → Bool) (v : V) : edgeProfile bad v ≤ 1 := by
  change mean (fun d => if bad (v, d) then (1 : ℝ) else 0) ≤ 1
  calc
    _ ≤ mean (fun _ : D => (1 : ℝ)) := mean_mono (fun d => by
      cases bad (v, d) <;> norm_num)
    _ = 1 := mean_const _

omit [Nonempty V] [Nonempty D] in
theorem edgeDensity_nonnegative (bad : V × D → Bool) : 0 ≤ edgeDensity bad :=
  mean_nonnegative _ (edgeProfile_nonnegative bad)

omit [Nonempty V] in
theorem edgeProfile_energy_le_density (bad : V × D → Bool) :
    energy (edgeProfile bad) ≤ edgeDensity bad :=
  mean_mono (fun v => by
    have h0 := edgeProfile_nonnegative bad v
    have h1 := edgeProfile_le_one bad v
    nlinarith)

theorem edgeProfile_centered_energy (bad : V × D → Bool) :
    energy (fun v => edgeProfile bad v - edgeDensity bad) ≤
      edgeDensity bad * (1 - edgeDensity bad) := by
  rw [energy_sub_const]
  have h := edgeProfile_energy_le_density bad
  change energy (edgeProfile bad) - 2 * edgeDensity bad * edgeDensity bad +
    edgeDensity bad ^ 2 ≤ _
  nlinarith

theorem returnMass_le_sharp (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (gap : Nat) :
    returnMass G bad gap ≤ edgeDensity bad ^ 2 +
      lambda ^ gap * (edgeDensity bad * (1 - edgeDensity bad)) := by
  rw [returnMass_eq_correlation G bad reversal, correlation_centered]
  have hzero : mean (fun v => edgeProfile bad v - edgeDensity bad) = 0 := by
    rw [mean_sub, mean_const]
    simp only [edgeDensity, sub_self]
  have hc := zero_mean_correlation_bound G lambda certificate
    (fun v => edgeProfile bad v - edgeDensity bad) hzero gap
  have hv := mul_le_mul_of_nonneg_left (edgeProfile_centered_energy bad)
    (pow_nonneg certificate.nonnegative gap)
  change edgeDensity bad ^ 2 + _ ≤ _
  exact add_le_add (le_refl _) (hc.trans hv)

theorem returnMass_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (gap : Nat) :
    returnMass G bad gap ≤ edgeDensity bad ^ 2 + edgeDensity bad * lambda ^ gap := by
  have h := returnMass_le_sharp G lambda certificate bad reversal gap
  have hvar : edgeDensity bad * (1 - edgeDensity bad) ≤ edgeDensity bad := by
    nlinarith [sq_nonneg (edgeDensity bad)]
  have hm := mul_le_mul_of_nonneg_left hvar (pow_nonneg certificate.nonnegative gap)
  nlinarith

end Profiles

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]

theorem sum_returnMass_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (n : Nat) :
    (∑ gap ∈ Finset.range n, returnMass G bad gap) ≤
      (n : ℝ) * edgeDensity bad ^ 2 + edgeDensity bad / (1 - lambda) := by
  calc
    _ ≤ ∑ gap ∈ Finset.range n,
        (edgeDensity bad ^ 2 + edgeDensity bad * lambda ^ gap) :=
      Finset.sum_le_sum (fun gap _ => returnMass_le G lambda certificate bad reversal gap)
    _ = (n : ℝ) * edgeDensity bad ^ 2 +
        edgeDensity bad * (∑ gap ∈ Finset.range n, lambda ^ gap) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (n : ℝ) * edgeDensity bad ^ 2 + edgeDensity bad * (1 / (1 - lambda)) :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left
          (geometric_sum_le lambda certificate.nonnegative certificate.lt_one n)
          (edgeDensity_nonnegative bad))
    _ = _ := by ring

theorem triangular_returnMass_sum_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (n : Nat) :
    (∑ j ∈ Finset.range n, ∑ gap ∈ Finset.range j, returnMass G bad gap) ≤
      ((n : ℝ) * ((n : ℝ) - 1) / 2) * edgeDensity bad ^ 2 +
        (n : ℝ) * (edgeDensity bad / (1 - lambda)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hrow := sum_returnMass_le G lambda certificate bad reversal n
      have h := add_le_add ih hrow
      calc
        _ ≤ ((n : ℝ) * ((n : ℝ) - 1) / 2) * edgeDensity bad ^ 2 +
            (n : ℝ) * (edgeDensity bad / (1 - lambda)) +
            ((n : ℝ) * edgeDensity bad ^ 2 + edgeDensity bad / (1 - lambda)) := h
        _ = _ := by simp only [Nat.cast_add, Nat.cast_one]; ring

theorem secondMoment_return_envelope (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (n : Nat) :
    (n : ℝ) * edgeDensity bad +
        2 * (∑ j ∈ Finset.range n, ∑ gap ∈ Finset.range j, returnMass G bad gap) ≤
      (n : ℝ) * edgeDensity bad *
        (1 + 2 / (1 - lambda) + ((n : ℝ) - 1) * edgeDensity bad) := by
  calc
    _ ≤ (n : ℝ) * edgeDensity bad +
        2 * (((n : ℝ) * ((n : ℝ) - 1) / 2) * edgeDensity bad ^ 2 +
          (n : ℝ) * (edgeDensity bad / (1 - lambda))) :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left
          (triangular_returnMass_sum_le G lambda certificate bad reversal n) (by norm_num))
    _ = _ := by ring

end

end UniqueGames.Foundations.PCP.SpectralReturn

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringLazy
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.PoweringLabels.finiteBall _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.averagingOperator_cayleyGraph _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_rot _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.lookup_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GraphTransport.reindex_rot _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGames.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.PortTables.rotation_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PoweringReach.headFromEnd_val _root_.OAI.UniqueGames.Foundations.PCP.PoweringReach.tailFromStart_val _root_.OAI.UniqueGames.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringTest.poweredGraph_tail_true _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_next _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_rot_apply _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.zigzag_rot_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace UniqueGames.Foundations.PCP.PoweringLazy

open PoweringWalks SpectralReturn

variable {V D : Type*}

theorem iterate_lazy_eq_binomialMean [Fintype D] [Nonempty D]
    (G : PortGraph V D) (n : Nat) (f : V → ℝ) :
    iterateOperator (lazyGraph G) n f =
      fun v => LazySmoothing.binomialMean n (fun k => iterateOperator G k f v) := by
  induction n with
  | zero =>
    funext v
    simp [iterateOperator]
  | succ n ih =>
    funext v
    change averagingOperator (lazyGraph G) (iterateOperator (lazyGraph G) n f) v = _
    rw [ih, averagingOperator_lazy, operator_binomialMean, LazySmoothing.mean_succ]
    rfl

theorem iterate_mem_Icc [Fintype D] [Nonempty D]
    (G : PortGraph V D) (f : V → ℝ) (hf : ∀ w, f w ∈ Set.Icc (0 : ℝ) 1)
    (n : Nat) (v : V) : iterateOperator G n f v ∈ Set.Icc (0 : ℝ) 1 := by
  induction n generalizing v with
  | zero => exact hf v
  | succ n ih =>
    change mean (fun d : D => iterateOperator G n f (G.rot (v, d)).1) ∈ Set.Icc (0 : ℝ) 1
    constructor
    · exact mean_nonnegative _ (fun d => (ih ((G.rot (v, d)).1)).1)
    · calc
        mean (fun d : D => iterateOperator G n f (G.rot (v, d)).1) ≤
            mean (fun _ : D => (1 : ℝ)) :=
          mean_mono (fun d => (ih ((G.rot (v, d)).1)).2)
        _ = 1 := mean_const _

theorem lazy_endpoint_modal_transfer [Fintype D] [Nonempty D]
    (G : PortGraph V D) (q M m : Nat) (hq : 1 ≤ q) (hM : 1 ≤ M)
    (hlo : (4 * q * M) ^ 2 - M ≤ m) (hhi : m ≤ (4 * q * M) ^ 2 + M)
    (f : V → ℝ) (hf : ∀ w, f w ∈ Set.Icc (0 : ℝ) 1) (v : V)
    (hmodal : 1 / (q : ℝ) ≤ iterateOperator (lazyGraph G) ((4 * q * M) ^ 2) f v) :
    1 / (2 * (q : ℝ)) ≤ iterateOperator (lazyGraph G) m f v := by
  rw [iterate_lazy_eq_binomialMean] at hmodal ⊢
  exact LazySmoothing.modal_transfer q M m hq hM hlo hhi
    (fun k => iterateOperator G k f v) (fun k => iterate_mem_Icc G f hf k v) hmodal

end UniqueGames.Foundations.PCP.PoweringLazy

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringReturn
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.dartNonempty _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGames.Foundations.PCP.PoweringLabels.finiteBall _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_rot _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.lookup_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GraphTransport.reindex_rot _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGames.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.PortTables.rotation_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PoweringReach.headFromEnd_val _root_.OAI.UniqueGames.Foundations.PCP.PoweringReach.tailFromStart_val _root_.OAI.UniqueGames.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringTest.poweredGraph_tail_true _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_true _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_next _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_rot_apply _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.zigzag_rot_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.PoweringReturn

open PoweringWalks SpectralReturn
open PoweringMoment (bit)

variable {V D : Type*}

theorem mean_word_cons_head [Fintype D] (n : Nat)
    (F : (Fin (n + 1) → D) → ℝ) :
    mean F = mean (fun d : D => mean (fun r : Fin n → D => F (Fin.cases d r))) := by
  calc
    mean F = mean (fun z : D × (Fin n → D) => F (Fin.cases z.1 z.2)) :=
      (mean_equiv (portConsEquiv D n) F).symm
    _ = _ := mean_prod _

theorem mean_word_cons_tail [Fintype D] (n : Nat)
    (F : (Fin (n + 1) → D) → ℝ) :
    mean F = mean (fun r : Fin n → D => mean (fun d : D => F (Fin.cases d r))) := by
  calc
    mean F = mean (fun z : (Fin n → D) × D => F (Fin.cases z.2 z.1)) :=
      (mean_equiv ((Equiv.prodComm (Fin n → D) D).trans (portConsEquiv D n)) F).symm
    _ = _ := mean_prod _

theorem mean_wordEnd [Fintype D] [Nonempty D] (G : PortGraph V D) :
    ∀ (n : Nat) (v : V) (f : V → ℝ),
      mean (fun r : Fin n → D => f (wordEnd G n v r)) = iterateOperator G n f v := by
  intro n
  induction n with
  | zero =>
    intro v f
    change mean (fun _ : Fin 0 → D => f v) = f v
    exact mean_const _
  | succ n ih =>
    intro v f
    rw [mean_word_cons_head]
    change mean (fun d : D => mean (fun r : Fin n → D =>
      f (wordEnd G n (next G v d) r))) = _
    calc
      _ = mean (fun d : D => iterateOperator G n f (next G v d)) := by
        congr 1
        funext d
        exact ih (next G v d) f
      _ = iterateOperator G (n + 1) f v := rfl

theorem mean_pivot_endpoints [Fintype D] [Nonempty D] (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (e : Edge V D) (φ ψ : V → ℝ),
      mean (fun r : Fin n → D =>
        φ (leftFromPivot G n k e.1 r) * ψ (rightFromPivot G n k e r)) =
        iterateOperator G k.val φ e.1 *
          iterateOperator G (n - k.val) ψ (next G e.1 e.2) := by
  intro n
  induction n with
  | zero =>
    intro k e φ ψ
    have hk : k = 0 := Fin.eq_zero k
    subst k
    change mean (fun _ : Fin 0 → D => φ e.1 * ψ (next G e.1 e.2)) =
      φ e.1 * ψ (next G e.1 e.2)
    exact mean_const _
  | succ n ih =>
    intro k e φ ψ
    refine Fin.cases ?_ (fun j => ?_) k
    · change mean (fun r : Fin (n + 1) → D =>
        φ e.1 * ψ (wordEnd G (n + 1) (next G e.1 e.2) r)) =
          φ e.1 * iterateOperator G (n + 1) ψ (next G e.1 e.2)
      rw [mean_mul_left, mean_wordEnd]
    · simp only [Fin.val_succ, Nat.add_sub_add_right]
      rw [mean_word_cons_tail]
      change mean (fun r : Fin n → D => mean (fun d : D =>
        φ (next G (leftFromPivot G n j e.1 r) d) *
          ψ (rightFromPivot G n j e r))) =
        iterateOperator G (j.val + 1) φ e.1 *
          iterateOperator G (n - j.val) ψ (next G e.1 e.2)
      calc
        _ = mean (fun r : Fin n → D =>
            averagingOperator G φ (leftFromPivot G n j e.1 r) *
              ψ (rightFromPivot G n j e r)) := by
          congr 1
          funext r
          rw [mean_mul_right]
          rfl
        _ = iterateOperator G j.val (averagingOperator G φ) e.1 *
            iterateOperator G (n - j.val) ψ (next G e.1 e.2) :=
          ih j e (averagingOperator G φ) ψ
        _ = _ := by rw [iterateOperator_succ_right]

theorem mean_edge_endpoints [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (n : Nat) (k : Fin (n + 1)) (φ ψ : Edge V D → V → ℝ) :
    mean (fun w : Walk V D (n + 1) =>
      φ (edgeAt G n w k) w.1 * ψ (edgeAt G n w k) (endpoint G w)) =
      mean (fun e : Edge V D =>
        iterateOperator G k.val (φ e) e.1 *
          iterateOperator G (n - k.val) (ψ e) (next G e.1 e.2)) := by
  let F : Edge V D × (Fin n → D) → ℝ := fun z =>
    φ z.1 (leftFromPivot G n k z.1.1 z.2) *
      ψ z.1 (rightFromPivot G n k z.1 z.2)
  calc
    _ = mean (fun w => F (pivotEquiv G n k w)) := by
      congr 1
      funext w
      dsimp [F]
      rw [leftFromPivot_actual, rightFromPivot_actual, pivotEquiv_fst]
    _ = mean F := mean_equiv (pivotEquiv G n k) F
    _ = mean (fun e : Edge V D => mean (fun r : Fin n → D =>
        φ e (leftFromPivot G n k e.1 r) * ψ e (rightFromPivot G n k e r))) := mean_prod F
    _ = _ := by
      congr 1
      funext e
      exact mean_pivot_endpoints G n k e (φ e) (ψ e)

theorem edgeAt_zero (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    edgeAt G n w 0 = (w.1, w.2 0) := by
  cases n <;> rfl

theorem word_first_hit_mean [Fintype D] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) (n : Nat) (v : V) :
    mean (fun p : Fin (n + 1) → D => bit (bad (edgeAt G n (v, p) 0) = true)) =
      edgeProfile bad v := by
  rw [mean_word_cons_head]
  simp_rw [edgeAt_zero]
  change mean (fun d : D => mean (fun _ : Fin n → D => bit (bad (v, d) = true))) = _
  calc
    _ = mean (fun d : D => bit (bad (v, d) = true)) := by simp only [mean_const]
    _ = edgeProfile bad v := mean_edge_bit bad v

theorem word_hit_mean [Fintype D] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) :
    ∀ (n : Nat) (v : V) (k : Fin (n + 1)),
      mean (fun p : Fin (n + 1) → D => bit (bad (edgeAt G n (v, p) k) = true)) =
        iterateOperator G k.val (edgeProfile bad) v := by
  intro n
  induction n with
  | zero =>
    intro v k
    have hk : k = 0 := Fin.eq_zero k
    subst k
    exact word_first_hit_mean G bad 0 v
  | succ n ih =>
    intro v k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact word_first_hit_mean G bad (n + 1) v
    · rw [mean_word_cons_head]
      change mean (fun d : D => mean (fun p : Fin (n + 1) → D =>
        bit (bad (edgeAt G n (next G v d, p) j) = true))) =
          averagingOperator G (iterateOperator G j.val (edgeProfile bad)) v
      calc
        _ = mean (fun d : D => iterateOperator G j.val (edgeProfile bad) (next G v d)) := by
          congr 1
          funext d
          exact ih (next G v d) j
        _ = _ := rfl

theorem word_pair_hit_mean [Fintype D] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) :
    ∀ (n : Nat) (v : V) (i j : Fin (n + 1)), i < j →
      mean (fun p : Fin (n + 1) → D =>
        bit (bad (edgeAt G n (v, p) i) = true) *
          bit (bad (edgeAt G n (v, p) j) = true)) =
        iterateOperator G i.val (markedStep G bad
          (iterateOperator G (j.val - i.val - 1) (edgeProfile bad))) v := by
  intro n
  induction n with
  | zero =>
    intro v i j hij
    have hi : i = 0 := Fin.eq_zero i
    have hj : j = 0 := Fin.eq_zero j
    subst i
    subst j
    exact ((lt_irrefl _) hij).elim
  | succ n ih =>
    intro v i
    refine Fin.cases ?_ (fun a => ?_) i
    · intro j
      refine Fin.cases ?_ (fun b => ?_) j
      · intro hij
        exact ((lt_irrefl _) hij).elim
      · intro _hij
        simp only [Fin.val_zero, Fin.val_succ, Nat.sub_zero, Nat.add_sub_cancel]
        rw [mean_word_cons_head]
        change mean (fun d : D => mean (fun p : Fin (n + 1) → D =>
          bit (bad (v, d) = true) * bit (bad (edgeAt G n (next G v d, p) b) = true))) =
          markedStep G bad (iterateOperator G b.val (edgeProfile bad)) v
        calc
          _ = mean (fun d : D => bit (bad (v, d) = true) *
              iterateOperator G b.val (edgeProfile bad) (next G v d)) := by
            congr 1
            funext d
            rw [mean_mul_left, word_hit_mean]
          _ = _ := mean_marked_bit G bad _ v
    · intro j
      refine Fin.cases ?_ (fun b => ?_) j
      · intro hij
        exact (Nat.not_lt_zero _ hij).elim
      · intro hij
        have hab : a < b := Nat.lt_of_succ_lt_succ hij
        simp only [Fin.val_succ, Nat.add_sub_add_right]
        rw [mean_word_cons_head]
        change mean (fun d : D => mean (fun p : Fin (n + 1) → D =>
          bit (bad (edgeAt G n (next G v d, p) a) = true) *
            bit (bad (edgeAt G n (next G v d, p) b) = true))) =
          averagingOperator G (iterateOperator G a.val (markedStep G bad
            (iterateOperator G (b.val - a.val - 1) (edgeProfile bad)))) v
        calc
          _ = mean (fun d : D => iterateOperator G a.val (markedStep G bad
              (iterateOperator G (b.val - a.val - 1) (edgeProfile bad))) (next G v d)) := by
            congr 1
            funext d
            exact ih (next G v d) a b hab
          _ = _ := rfl

theorem hit_mean [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) (n : Nat) (k : Fin (n + 1)) :
    mean (fun w : Walk V D (n + 1) => bit (bad (edgeAt G n w k) = true)) =
      edgeDensity bad := by
  calc
    _ = mean (fun v : V => mean (fun p : Fin (n + 1) → D =>
        bit (bad (edgeAt G n (v, p) k) = true))) :=
      mean_prod (A := V) (B := Fin (n + 1) → D)
        (fun w => bit (bad (edgeAt G n w k) = true))
    _ = mean (iterateOperator G k.val (edgeProfile bad)) := by
      congr 1
      funext v
      exact word_hit_mean G bad n v k
    _ = mean (edgeProfile bad) := mean_iterate G k.val _
    _ = _ := rfl

theorem pair_hit_mean [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) (n : Nat)
    (i j : Fin (n + 1)) (hij : i < j) :
    mean (fun w : Walk V D (n + 1) => bit (bad (edgeAt G n w i) = true) *
      bit (bad (edgeAt G n w j) = true)) = returnMass G bad (j.val - i.val - 1) := by
  calc
    _ = mean (fun v : V => mean (fun p : Fin (n + 1) → D =>
        bit (bad (edgeAt G n (v, p) i) = true) *
          bit (bad (edgeAt G n (v, p) j) = true))) :=
      mean_prod (A := V) (B := Fin (n + 1) → D)
        (fun w => bit (bad (edgeAt G n w i) = true) *
          bit (bad (edgeAt G n w j) = true))
    _ = mean (iterateOperator G i.val (markedStep G bad
        (iterateOperator G (j.val - i.val - 1) (edgeProfile bad)))) := by
      congr 1
      funext v
      exact word_pair_hit_mean G bad n v i j hij
    _ = mean (markedStep G bad
        (iterateOperator G (j.val - i.val - 1) (edgeProfile bad))) := mean_iterate G i.val _
    _ = _ := rfl

theorem pair_event_mean [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) (n : Nat)
    (i j : Fin (n + 1)) (hij : i < j) :
    mean (fun w : Walk V D (n + 1) =>
      bit (bad (edgeAt G n w i) = true ∧ bad (edgeAt G n w j) = true)) =
        returnMass G bad (j.val - i.val - 1) := by
  simpa only [PoweringMoment.bit_mul] using pair_hit_mean G bad n i j hij

end UniqueGames.Foundations.PCP.PoweringReturn

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringOpinions
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.dartNonempty _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_rot _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.lookup_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GraphTransport.reindex_rot _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGames.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.PortTables.rotation_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PoweringEnumeration.decodeLabel_encodeLabel _root_.OAI.UniqueGames.Foundations.PCP.PoweringReach.headFromEnd_val _root_.OAI.UniqueGames.Foundations.PCP.PoweringReach.tailFromStart_val _root_.OAI.UniqueGames.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringTest.poweredGraph_tail_true _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_next _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_rot_apply _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.zigzag_rot_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                         

noncomputable section

namespace UniqueGames.Foundations.PCP.PoweringOpinions

open PoweringWalks PoweringLabels SpectralReturn
open PoweringMoment (bit)

variable {V D A : Type*}

def opinionAt (G : PortGraph V D) (t : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u v : V) : A := by
  classical
  exact if h : ∃ n, n ≤ t ∧ ∃ p : Fin n → D, wordEnd G n v p = u then
    decode (selectors v) (labels v) ⟨u, h⟩ else fallback

theorem opinionAt_eq_decode (G : PortGraph V D) (t : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (v : V) (u : Ball G t v) :
    opinionAt G t selectors labels fallback u.val v = decode (selectors v) (labels v) u := by
  classical
  simp [opinionAt, u.property]
  rfl

def honestLabels (G : PortGraph V D) (t : Nat) (assignment : V → A) :
    V → PaddedLabel D t A := fun v => encode G t v (fun u => assignment u.val)

variable [Fintype D] [Nonempty D] [Fintype A] [Nonempty A]

def sampleOpinion (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u : V) (p : Fin N → D) : A :=
  opinionAt G t selectors labels fallback u (wordEnd G N u p)

def decoded (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u : V) : A :=
  PoweringDecoding.mode (sampleOpinion G t N selectors labels fallback u)

def matchFn (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u v : V) : ℝ :=
  bit (opinionAt G t selectors labels fallback u v = decoded G t N selectors labels fallback u)

omit [Nonempty D] in
theorem matchFn_mem_Icc (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u v : V) :
    matchFn G t N selectors labels fallback u v ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  constructor
  · exact PoweringMoment.bit_nonneg _
  · unfold matchFn bit
    split <;> simp

theorem decoded_modal_baseline (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u : V) :
    1 / (Fintype.card A : ℝ) ≤
      iterateOperator G N (matchFn G t N selectors labels fallback u) u := by
  have h := PoweringDecoding.mode_mass_lower (sampleOpinion G t N selectors labels fallback u)
  change 1 / (Fintype.card A : ℝ) ≤ mean (fun p : Fin N → D =>
    matchFn G t N selectors labels fallback u (wordEnd G N u p)) at h
  rwa [PoweringReturn.mean_wordEnd] at h

end UniqueGames.Foundations.PCP.PoweringOpinions
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringTest
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_rot _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.lookup_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GraphTransport.reindex_rot _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGames.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.PortTables.rotation_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PoweringEnumeration.decodeLabel_encodeLabel _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_next _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_rot_apply _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.zigzag_rot_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                     

namespace UniqueGames.Foundations.PCP.PoweringTest

open PoweringWalks PoweringLabels PoweringReach PoweringOpinions

variable {V D A : Type*}

def baseGraph (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b) :
    ConstraintGraph V (Edge V D) A where
  reverse := G.rot
  reverse_involutive := G.rot_involutive
  tail := Prod.fst
  accepts := accepts
  reverse_accepts := reverse_accepts

theorem pathAccepts_eq_true_iff (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (w : Walk V D (n + 1)) (a b : PaddedLabel D (n + 1) A) :
    pathAccepts G accepts n selectors w a b = true ↔
      ∀ k : Fin (n + 1),
        accepts (edgeAt G n w k)
          (decode (selectors w.1) a (tailFromStart G n w k))
          (decode (selectors (endpoint G w)) b (headFromEnd G n w k)) = true := by
  simp [pathAccepts]

theorem poweredGraph_edgeSatisfied (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A)
    (direction : Bool) (w : Walk V D (n + 1)) :
    (poweredGraph G accepts n selectors).edgeSatisfied labels (direction, w) =
      pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) := by
  cases direction <;> rfl

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

theorem pathAccepts_honest (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (assignment : V → A)
    (satisfies : ∀ e, accepts e (assignment e.1) (assignment (G.rot e).1) = true)
    (w : Walk V D (n + 1)) :
    pathAccepts G accepts n selectors w
      (honestLabels G (n + 1) assignment w.1)
      (honestLabels G (n + 1) assignment (endpoint G w)) = true := by
  apply (pathAccepts_eq_true_iff G accepts n selectors w _ _).2
  intro k
  simpa only [honestLabels, decode_encode, tailFromStart_val, headFromEnd_val] using
    satisfies (edgeAt G n w k)

theorem perfect_completeness (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (assignment : V → A)
    (satisfies : ∀ e, accepts e (assignment e.1) (assignment (G.rot e).1) = true) :
    ∀ d, (poweredGraph G accepts n selectors).edgeSatisfied
      (honestLabels G (n + 1) assignment) d = true := by
  rintro ⟨direction, w⟩
  rw [poweredGraph_edgeSatisfied]
  exact pathAccepts_honest G accepts n selectors assignment satisfies w

theorem preserves_satisfiability (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (h : (baseGraph G accepts reverse_accepts).Satisfiable) :
    (poweredGraph G accepts n selectors).Satisfiable := by
  obtain ⟨assignment, satisfies⟩ := h
  refine ⟨honestLabels G (n + 1) assignment, ?_⟩
  apply perfect_completeness G accepts n selectors assignment
  intro e
  exact satisfies e

def decodedBad (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (assignment : V → A) (e : Edge V D) : Bool :=
  !(accepts e (assignment e.1) (assignment (G.rot e).1))

theorem decodedBad_eq_true_iff (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (assignment : V → A) (e : Edge V D) :
    decodedBad G accepts assignment e = true ↔
      accepts e (assignment e.1) (assignment (G.rot e).1) = false := by
  simp [decodedBad]

theorem decodedBad_rot (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (assignment : V → A) (e : Edge V D) :
    decodedBad G accepts assignment (G.rot e) = decodedBad G accepts assignment e := by
  have h := congrArg Bool.not
    (reverse_accepts e (assignment e.1) (assignment (G.rot e).1))
  simpa only [decodedBad, G.rot_involutive e] using h

noncomputable def witness (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (assignment : V → A) (w : Walk V D (n + 1)) (k : Fin (n + 1)) : Prop :=
  decodedBad G accepts assignment (edgeAt G n w k) = true ∧
    opinionAt G (n + 1) selectors labels fallback (edgeAt G n w k).1 w.1 =
      assignment (edgeAt G n w k).1 ∧
    opinionAt G (n + 1) selectors labels fallback
      (G.rot (edgeAt G n w k)).1 (endpoint G w) =
        assignment (G.rot (edgeAt G n w k)).1

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

end UniqueGames.Foundations.PCP.PoweringTest

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringCounting
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGames.Foundations.PCP.AlphabetRetraction.edgeSatisfied_pullback _root_.OAI.UniqueGames.Foundations.PCP.AlphabetRetraction.rejectionCount_pullback _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.FiniteGraph.Bundle.ofGraph_graph _root_.OAI.UniqueGames.Foundations.PCP.FiniteGraph.Bundle.ofGraph_rejectionCount _root_.OAI.UniqueGames.Foundations.PCP.FiniteGraph.Bundle.ofGraph_size _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.acceptsAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.reverseAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_accepts _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_reverse _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_tail _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.acceptsAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.reverseAt_graphRows _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_accepts _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_ofGraph_accepts _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_ofGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_ofGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_reverse _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.PortTables.baseGraph_accepts _root_.OAI.UniqueGames.Foundations.PCP.PortTables.baseGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.PortTables.baseGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudRank_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingOverlayTables.accepts_materialize _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.accepts_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.baseGraph_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_new _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_old _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.rotation_pad _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.Regularization.graph_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.paddedG_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                         

namespace UniqueGames.Foundations.PCP.PoweringCounting

open PoweringWalks PoweringLabels PoweringTest
open scoped BigOperators

variable {V D A E : Type*}

theorem constraint_rejection_mean_eq_count [Fintype E]
    (H : ConstraintGraph V E A) (labels : V → A) :
    SpectralReturn.mean (fun e : E => PoweringMoment.bit
      (H.edgeSatisfied labels e = false)) =
      (H.rejectionCount labels : ℝ) / (Fintype.card E : ℝ) := by
  classical
  rw [SpectralReturn.mean_eq_sum_div_card]
  simp only [PoweringMoment.bit, ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts]
  apply congrArg (fun x : ℝ => x / (Fintype.card E : ℝ))
  convert (Finset.sum_boole (R := ℝ)
    (fun e => H.edgeSatisfied labels e = false) Finset.univ) using 1 ; try rfl
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : H.edgeSatisfied labels e = false <;> simp [h]

theorem constraint_rejection_lower_iff [Fintype E]
    (H : ConstraintGraph V E A) (labels : V → A)
    (hcard : 0 < Fintype.card E) (ε : ℝ) :
    ε ≤ SpectralReturn.mean (fun e : E => PoweringMoment.bit
      (H.edgeSatisfied labels e = false)) ↔
      ε * (Fintype.card E : ℝ) ≤ (H.rejectionCount labels : ℝ) := by
  rw [constraint_rejection_mean_eq_count]
  exact le_div_iff₀ (Nat.cast_pos.mpr hcard)

theorem edgeDensity_eq_bit_mean [Fintype V] [Fintype D]
    (bad : Edge V D → Bool) :
    SpectralReturn.edgeDensity bad =
      SpectralReturn.mean (fun e : Edge V D => PoweringMoment.bit (bad e = true)) := by
  convert (SpectralReturn.mean_prod
    (fun e : Edge V D => PoweringMoment.bit (bad e = true))).symm using 1 ; try rfl
  change SpectralReturn.mean (fun v => SpectralReturn.mean
    (fun d => if bad (v, d) then (1 : ℝ) else 0)) = _
  apply congrArg SpectralReturn.mean
  funext v
  apply congrArg SpectralReturn.mean
  funext d
  cases h : bad (v, d) <;> simp [PoweringMoment.bit]

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

end UniqueGames.Foundations.PCP.PoweringCounting

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_SpectralCut
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.PoweringLabels.finiteBall _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.averagingOperator_cayleyGraph _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_rot _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.lookup_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GraphTransport.reindex_rot _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGames.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.PortTables.rotation_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PoweringReach.headFromEnd_val _root_.OAI.UniqueGames.Foundations.PCP.PoweringReach.tailFromStart_val _root_.OAI.UniqueGames.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringTest.poweredGraph_tail_true _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringWalks.lazyGraph_rot_true _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_next _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_rot_apply _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.zigzag_rot_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                    

noncomputable section
namespace UniqueGames.Foundations.PCP.SpectralCut

open scoped BigOperators
open PoweringWalks SpectralReturn

section Indicators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mean_indicator (S : Finset V) :
    mean (indicator S) = (S.card : ℝ) / (Fintype.card V : ℝ) := by
  have hf : Finset.univ.filter (fun v : V => v ∈ S) = S := by
    ext v
    simp
  rw [mean_eq_sum_div_card]
  simp only [indicator, Finset.sum_boole, hf]

end Indicators

variable {V D : Type*} [Fintype V] [Fintype D] [DecidableEq V]

section Nonempty
variable [Nonempty V] [Nonempty D] (G : PortGraph V D)

omit [Nonempty V] in
                                                                           
theorem cut_density_eq (S : Finset V) :
    ((cut G S).card : ℝ) / (Fintype.card (V × D) : ℝ) =
      mean (indicator S) - correlation (indicator S) (averagingOperator G (indicator S)) := by
  classical
  calc
    _ = mean (indicator (cut G S)) := (mean_indicator (cut G S)).symm
    _ = mean (fun e : V × D => indicator S e.1 -
        indicator S e.1 * indicator S (G.rot e).1) := by
      congr 1
      funext e
      by_cases hv : e.1 ∈ S <;> by_cases hw : (G.rot e).1 ∈ S <;>
        simp [indicator, cut, hv, hw]
    _ = mean (fun v => mean (fun d : D => indicator S v -
        indicator S v * indicator S (G.rot (v,d)).1)) := mean_prod _
    _ = mean (fun v => indicator S v -
        indicator S v * averagingOperator G (indicator S) v) := by
      congr 1
      funext v
      rw [mean_sub, mean_const, mean_mul_left]
      rfl
    _ = _ := mean_sub _ _

theorem cut_density_ge_variance
    (certificate : SpectralCertificate G (1/2)) (S : Finset V) :
    (1/2:ℝ) * mean (indicator S) * (1 - mean (indicator S)) ≤
      ((cut G S).card : ℝ) / (Fintype.card (V × D) : ℝ) := by
  let f := indicator S
  have hz : mean (fun v => f v - mean f) = 0 := by
    rw [mean_sub, mean_const, sub_self]
  have he : energy (fun v => f v - mean f) = mean f - mean f ^ 2 := by
    rw [energy_sub_const, energy_indicator]
    ring
  have hb := zero_mean_correlation_bound G (1/2) certificate
    (fun v => f v - mean f) hz 1
  have hc := correlation_centered G f 1
  simp only [iterateOperator, pow_one, he] at hb hc
  rw [cut_density_eq]
  change (1/2:ℝ) * mean f * (1 - mean f) ≤
    mean f - correlation f (averagingOperator G f)
  nlinarith

theorem cut_density_ge_quarter
    (certificate : SpectralCertificate G (1/2)) (S : Finset V)
    (hsmall : 2 * S.card ≤ Fintype.card V) :
    mean (indicator S) / 4 ≤
      ((cut G S).card : ℝ) / (Fintype.card (V × D) : ℝ) := by
  have hN : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hp0 : 0 ≤ mean (indicator S) := mean_nonnegative _ (indicator_nonnegative S)
  have hp : mean (indicator S) ≤ (1/2:ℝ) := by
    rw [mean_indicator]
    apply (div_le_iff₀ hN).mpr
    have hs : (2:ℝ) * (S.card : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hsmall
    nlinarith
  have hv := cut_density_ge_variance G certificate S
  have hprod := mul_nonneg hp0 (sub_nonneg.mpr hp)
  nlinarith

theorem cut_card_ge_quarter_degree
    (certificate : SpectralCertificate G (1/2)) (S : Finset V)
    (hsmall : 2 * S.card ≤ Fintype.card V) :
    (Fintype.card D : ℝ) * (S.card : ℝ) / 4 ≤ ((cut G S).card : ℝ) := by
  have hN : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hD : (0:ℝ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  have h := cut_density_ge_quarter G certificate S hsmall
  rw [Fintype.card_prod, Nat.cast_mul] at h
  have hh := (le_div_iff₀ (mul_pos hN hD)).mp h
  have he : mean (indicator S) / 4 *
      ((Fintype.card V : ℝ) * (Fintype.card D : ℝ)) =
        (Fintype.card D : ℝ) * (S.card : ℝ) / 4 := by
    rw [mean_indicator]
    field_simp [ne_of_gt hN]

  rw [he] at hh
  exact hh

theorem degree_mul_card_le_four_cut
    (certificate : SpectralCertificate G (1/2)) (S : Finset V)
    (hsmall : 2 * S.card ≤ Fintype.card V) :
    Fintype.card D * S.card ≤ 4 * (cut G S).card := by
  have h := cut_card_ge_quarter_degree G certificate S hsmall
  have hr : (Fintype.card D : ℝ) * (S.card : ℝ) ≤ 4 * ((cut G S).card : ℝ) := by
    linarith
  exact_mod_cast hr

end Nonempty

theorem cut_card_ge_twice (G : PortGraph V D)
    (certificate : SpectralCertificate G (1/2)) (hdegree : 8 ≤ Fintype.card D)
    (S : Finset V) (hsmall : 2 * S.card ≤ Fintype.card V) :
    2 * S.card ≤ (cut G S).card := by
  let : Nonempty D := Fintype.card_pos_iff.mp (by omega)
  rcases isEmpty_or_nonempty V with hV | hV
  · let := hV
    have hzero : Fintype.card V = 0 := Fintype.card_eq_zero
    have hs : S.card = 0 := by omega
    simp only [hs, mul_zero, Nat.zero_le]
  · let := hV
    have h := degree_mul_card_le_four_cut G certificate S hsmall
    have hdeg := Nat.mul_le_mul_right S.card hdegree
    omega

end UniqueGames.Foundations.PCP.SpectralCut
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringMomentBound
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.PoweringLabels.finiteBall _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                            

namespace UniqueGames.Foundations.PCP.PoweringMomentBound

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

end UniqueGames.Foundations.PCP.PoweringMomentBound

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringWitness
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.dartNonempty _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGames.Foundations.PCP.PoweringLabels.finiteBall _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_rot _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.lookup_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GraphTransport.reindex_rot _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGames.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.PortTables.rotation_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PoweringReach.headFromEnd_val _root_.OAI.UniqueGames.Foundations.PCP.PoweringReach.tailFromStart_val _root_.OAI.UniqueGames.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGames.Foundations.PCP.PoweringTest.poweredGraph_tail_true _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_next _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_rot_apply _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.zigzag_rot_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                        

namespace UniqueGames.Foundations.PCP.PoweringWitness

open PoweringWalks SpectralReturn PoweringReturn PoweringLazy
open PoweringMoment (bit)

variable {V D : Type*}

theorem iterate_mul_const [Fintype D] (G : PortGraph V D)
    (n : Nat) («c» : ℝ) (h : V → ℝ) :
    iterateOperator G n (fun x => «c» * h x) =
      fun x => «c» * iterateOperator G n h x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change averagingOperator G (iterateOperator G n (fun x => «c» * h x)) =
      fun x => «c» * averagingOperator G (iterateOperator G n h) x
    rw [ih]
    funext v
    exact mean_mul_left «c» (fun d => iterateOperator G n h (G.rot (v, d)).1)

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

end UniqueGames.Foundations.PCP.PoweringWitness

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringSoundness
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.dartNonempty _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.AlphabetRetraction.edgeSatisfied_pullback _root_.OAI.UniqueGames.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.padded_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.graph_rot _root_.OAI.UniqueGames.Foundations.PCP.ExpanderTables.lookup_ofGraph _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGames.Foundations.PCP.GraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGames.Foundations.PCP.GraphTransport.reindex_rot _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGames.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGames.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGames.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGames.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGames.Foundations.PCP.PortTables.rotation_ofPortGraph _root_.OAI.UniqueGames.Foundations.PCP.PoweringEnumeration.decodeLabel_encodeLabel _root_.OAI.UniqueGames.Foundations.PCP.Preprocessing.graph_reverse _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_new _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_old _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGames.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_next _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.square_rot_apply _root_.OAI.UniqueGames.Foundations.PCP.ZigzagGraphs.zigzag_rot_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                          

noncomputable section

namespace UniqueGames.Foundations.PCP.PoweringSoundness

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

omit [Fintype V] [Nonempty V] in
omit [Nonempty D] in
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

end UniqueGames.Foundations.PCP.PoweringSoundness
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringFinalConstants
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                               

namespace UniqueGames.Foundations.PCP.PoweringFinalConstants

theorem center_eq :
    PoweringSoundness.center (Fintype.card Alphabet) FinalConstants.windowHalf =
      FinalConstants.endpointLength := by
  rw [card_alphabet]
  rfl

theorem walkLength_eq :
    2 * PoweringSoundness.center (Fintype.card Alphabet) FinalConstants.windowHalf + 1 =
      FinalConstants.walkLength := by
  rw [center_eq]
  rfl

theorem gain_eq :
    PoweringSoundness.gain 64 FinalConstants.windowHalf (31 / 32) / 12288 =
      FinalConstants.gain := by
  change
    (1 / (2 * (FinalConstants.alphabet : ℝ))) ^ 4 *
        (FinalConstants.windowSize : ℝ) /
        ((1 + 2 / (1 - (31 / 32 : ℝ))) + 1) /
        (FinalConstants.compositionLoss : ℝ) =
      (FinalConstants.windowSize : ℝ) / (FinalConstants.denominator : ℝ)
  rw [spectral_denominator_eq]
  have hden : (FinalConstants.denominator : ℝ) =
      16 * (FinalConstants.alphabet : ℝ) ^ 4 * 66 *
        (FinalConstants.compositionLoss : ℝ) := by
    simp only [FinalConstants.denominator, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [hden]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem gain_card_eq :
    PoweringSoundness.gain (Fintype.card Alphabet) FinalConstants.windowHalf (31 / 32) /
        12288 = FinalConstants.gain := by
  rw [card_alphabet]
  exact gain_eq

theorem scaled_bound_eq (ε : ℝ) :
    (PoweringSoundness.gain (Fintype.card Alphabet) FinalConstants.windowHalf (31 / 32) *
        min ε
          (1 / ((2 * PoweringSoundness.center (Fintype.card Alphabet)
            FinalConstants.windowHalf + 1 : Nat) : ℝ))) / 12288 =
      FinalConstants.gain * min ε FinalConstants.cap := by
  rw [walkLength_eq]
  rw [mul_div_right_comm, gain_card_eq]
  rfl

theorem composed_scaled_gap (ε : ℝ) (hε : 0 ≤ ε) :
    min (2 * ε) FinalConstants.cap ≤
      (PoweringSoundness.gain (Fintype.card Alphabet) FinalConstants.windowHalf (31 / 32) *
        min (ε / (Preprocessing.sizeFactor : ℝ))
          (1 / ((2 * PoweringSoundness.center (Fintype.card Alphabet)
            FinalConstants.windowHalf + 1 : Nat) : ℝ))) / 12288 := by
  rw [scaled_bound_eq]
  exact FinalConstants.composed_gap ε hε

end UniqueGames.Foundations.PCP.PoweringFinalConstants

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringGap
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.dartNonempty _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                    

namespace UniqueGames.Foundations.PCP.PoweringGap

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

end UniqueGames.Foundations.PCP.PoweringGap

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PreprocessingPaddingTables
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                                   

namespace UniqueGames.Foundations.PCP.PreprocessingPaddingTables

open PoweringWalks PortTables

variable {n m d : Nat}

theorem pad_rejectionCount (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) :
    (baseGraph (pad table h)).rejectionCount labeling =
      (baseGraph table).rejectionCount (fun v => labeling (v.castLE h)) := by
  classical
  calc
    (baseGraph (pad table h)).rejectionCount labeling =
        (sumGraph table m).rejectionCount (fun v => labeling (vertexEquiv h v)) := by
      unfold ConstraintGraph.rejectionCount
      symm
      apply Finset.card_equiv (dartEquiv h)
      intro e
      simp only [ConstraintGraph.mem_rejectedDarts, edgeSatisfied_pad_equiv]
    _ = (baseGraph table).rejectionCount (fun v => labeling (v.castLE h)) := by
      simpa only [sumGraph, vertexEquiv_inl] using
        VertexPadding.pad_rejectionCount (baseGraph table) rfl (m - n)
          (fun v => labeling (vertexEquiv h v))

theorem pad_satisfiable_iff (table : Table n d) (h : n ≤ m) :
    (baseGraph (pad table h)).Satisfiable ↔ (baseGraph table).Satisfiable := by
  constructor
  · rintro ⟨labeling, hs⟩
    exact ⟨fun v => labeling (v.castLE h), (pad_labeling_satisfies_iff table h labeling).1 hs⟩
  · rintro ⟨labeling, hs⟩
    refine ⟨extendLabeling h labeling, (pad_labeling_satisfies_iff table h _).2 ?_⟩
    simpa only [extendLabeling_old] using hs

end UniqueGames.Foundations.PCP.PreprocessingPaddingTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PreprocessingCloudIndex
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                                

namespace UniqueGames.Foundations.PCP.PreprocessingCloudIndex

open scoped BigOperators
open GraphTables DegreeReplacement

theorem sum_cloudSize (t : Table) : (∑ v, cloudSize t v) = t.darts := by
  calc
    _ = ∑ v, Fintype.card (Cloud (semantics t) v) := by
      apply Finset.sum_congr rfl
      intro v _
      exact cloudSize_eq_card_cloud t v
    _ = Fintype.card (Fin t.darts) := CloudPadding.sum_card_cloud (semantics t)
    _ = t.darts := Fintype.card_fin t.darts

end UniqueGames.Foundations.PCP.PreprocessingCloudIndex

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PreprocessingLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                            

namespace UniqueGames.Foundations.PCP.PreprocessingLevels

theorem paddedSize_bounds {k : Nat} (hk : 0 < k) :
    k ≤ paddedSize k ∧ paddedSize k ≤ ExpanderFamily.growth * k := by
  rw [paddedSize_eq_size]
  exact ⟨ExpanderFamily.le_size k, ExpanderFamily.size_le_mul hk⟩

theorem cloudPaddedSize_bounds (k : Nat) :
    k ≤ cloudPaddedSize k ∧ cloudPaddedSize k ≤ ExpanderFamily.growth * k := by
  by_cases hk : k = 0
  · subst k
    simp only [cloudPaddedSize_zero, Nat.mul_zero, le_refl, and_self]
  · rw [cloudPaddedSize_of_pos (Nat.pos_of_ne_zero hk)]
    exact paddedSize_bounds (Nat.pos_of_ne_zero hk)

end UniqueGames.Foundations.PCP.PreprocessingLevels

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PreprocessingRegularTables
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                                   

namespace UniqueGames.Foundations.PCP.PreprocessingRegularTables

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

theorem cloudSize_add_padding (t : GraphTables.Table) (v : Fin t.vertices) :
    PreprocessingCloudIndex.cloudSize t v + padding t v =
      PreprocessingLevels.cloudPaddedSize (PreprocessingCloudIndex.cloudSize t v) :=
  Nat.add_sub_of_le (PreprocessingLevels.cloudPaddedSize_bounds _).1

theorem vertexCount_eq_sum_cloudPaddedSize (t : GraphTables.Table) :
    vertexCount t (padding t) = ∑ v,
      PreprocessingLevels.cloudPaddedSize (PreprocessingCloudIndex.cloudSize t v) := by
  unfold vertexCount
  rw [← PreprocessingCloudIndex.sum_cloudSize t, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun v _ => cloudSize_add_padding t v)

theorem vertexCount_le (t : GraphTables.Table) :
    vertexCount t (padding t) ≤ ExpanderFamily.growth * t.darts := by
  rw [vertexCount_eq_sum_cloudPaddedSize, ← PreprocessingCloudIndex.sum_cloudSize t,
    Finset.mul_sum]
  exact Finset.sum_le_sum (fun v _ => (PreprocessingLevels.cloudPaddedSize_bounds _).2)

def familyCloudTable (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices) :
    ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + padding t v)
      internalDegree :=
  if hk : PreprocessingCloudIndex.cloudSize t v = 0 then
    resizeTable (by rw [cloudSize_add_padding, hk]; rfl) (emptyTable internalDegree)
  else
    resizeTable (by
      rw [cloudSize_add_padding,
        PreprocessingLevels.cloudPaddedSize_of_pos (Nat.pos_of_ne_zero hk)]
      exact PreprocessingLevels.table_vertexCount_eq_paddedSize _)
      (ExpanderTables.family H
        (PreprocessingLevels.boundedLevel (PreprocessingCloudIndex.cloudSize t v)))

def regularize (H : BaseTable) (t : GraphTables.Table) :
    PortTables.Table (vertexCount t (padding t)) (internalDegree + 1) :=
  ofCloudTables t (padding t) (familyCloudTable H t)

def regularizeInput (H : BaseTable) (t : GraphTables.Table) :
    PortTables.Input (internalDegree + 1) :=
  ⟨vertexCount t (padding t), regularize H t⟩

end UniqueGames.Foundations.PCP.PreprocessingRegularTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PreprocessingTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                            

namespace UniqueGames.Foundations.PCP.PreprocessingTables

open PreprocessingRegularTables

theorem degree_eq : degree = Preprocessing.degree := by
  unfold degree internalDegree Preprocessing.degree
  rw [pow_two]
  omega

def padded (H : BaseTable) (t : GraphTables.Table) :
    PortTables.Table (vertices t) (internalDegree + 1) :=
  PreprocessingPaddingTables.pad (regularize H t)
    (PreprocessingLevels.le_paddedSize (regularVertices t))

def overlayFamily (H : BaseTable) (t : GraphTables.Table) :
    ExpanderTables.Table (vertices t) internalDegree :=
  resizeTable (PreprocessingLevels.table_vertexCount_eq_paddedSize (regularVertices t))
    (ExpanderTables.family H (PreprocessingLevels.boundedLevel (regularVertices t)))

def preprocess (H : BaseTable) (t : GraphTables.Table) :
    PortTables.Table (vertices t) degree :=
  PreprocessingOverlayTables.lazy
    (PreprocessingOverlayTables.overlay (padded H t) (overlayFamily H t))

def output (H : BaseTable) (t : GraphTables.Table) : PortTables.Input degree :=
  ⟨vertices t, preprocess H t⟩

theorem regularVertices_le (t : GraphTables.Table) :
    regularVertices t ≤ ExpanderFamily.growth * t.darts := vertexCount_le t

theorem vertices_le_of_positive (t : GraphTables.Table) (ht : 0 < t.darts) :
    vertices t ≤ ExpanderFamily.growth ^ 2 * t.darts := by
  have hr : 0 < regularVertices t := ht.trans_le (regularVertices_ge_darts t)
  calc
    _ ≤ ExpanderFamily.growth * regularVertices t :=
      (PreprocessingLevels.paddedSize_bounds hr).2
    _ ≤ ExpanderFamily.growth * (ExpanderFamily.growth * t.darts) :=
      Nat.mul_le_mul_left _ (regularVertices_le t)
    _ = _ := by ring

end UniqueGames.Foundations.PCP.PreprocessingTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringTables
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Table.build_darts _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Table.build_vertices _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Table.rows_at
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.PoweringTables

open PoweringWalks PoweringLabels PoweringAddresses PoweringEnumeration

def mathematicalGraph {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) :
    ConstraintGraph (Fin vertices) (PoweringTest.Dart (Fin vertices) (Fin d) n)
      (PaddedLabel (Fin d) (n + 1) (Fin 64)) :=
  PoweringTest.poweredGraph (PortTables.portGraph input) (PortTables.accepts input) n
    (finitePortSelector (PortTables.portGraph input) (n + 1))

def table {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) :
    GenericGraphTables.Table (labelCount d n) :=
  GenericGraphTables.ofEnumeratedGraph (mathematicalGraph input n) (Equiv.refl _)
    (dartEquiv vertices d n) (paddedLabelEquiv d (n + 1) 64)

@[simp] theorem table_vertices {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) : (table input n).vertices = vertices := rfl

@[simp] theorem table_darts {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) : (table input n).darts = dartCount vertices d n := rfl

theorem semantics_table {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) :
    GenericGraphTables.semantics (table input n) =
      GenericGraphTables.enumeratedGraph (mathematicalGraph input n) (Equiv.refl _)
        (dartEquiv vertices d n) (paddedLabelEquiv d (n + 1) 64) :=
  GenericGraphTables.semantics_ofGraph _

end UniqueGames.Foundations.PCP.PoweringTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringTableSemantics
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                               

namespace UniqueGames.Foundations.PCP.PoweringTableSemantics

open PoweringWalks PoweringLabels PoweringAddresses PoweringEnumeration PoweringTables

abbrev RawLabeling (vertices d n : Nat) :=
  Fin vertices → PaddedLabel (Fin d) (n + 1) (Fin 64)

abbrev EncodedLabeling (vertices d n : Nat) :=
  Fin vertices → Fin (labelCount d n)

def encodeLabeling {vertices : Nat} (d n : Nat) (labels : RawLabeling vertices d n) :
    EncodedLabeling vertices d n :=
  fun v => encodeLabel d (n + 1) 64 (labels v)

def decodeLabeling {vertices : Nat} (d n : Nat) (labels : EncodedLabeling vertices d n) :
    RawLabeling vertices d n :=
  fun v => decodeLabel d (n + 1) 64 (labels v)

@[simp] theorem decodeLabeling_encodeLabeling {vertices : Nat} (d n : Nat)
    (labels : RawLabeling vertices d n) :
    decodeLabeling d n (encodeLabeling d n labels) = labels := by
  funext v
  exact decodeLabel_encodeLabel d (n + 1) 64 (labels v)

@[simp] theorem encodeLabeling_decodeLabeling {vertices : Nat} (d n : Nat)
    (labels : EncodedLabeling vertices d n) :
    encodeLabeling d n (decodeLabeling d n labels) = labels := by
  funext v
  exact encodeLabel_decodeLabel d (n + 1) 64 (labels v)

theorem edgeSatisfied_encoded {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (labels : RawLabeling vertices d n)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) :
    (GenericGraphTables.semantics (table input n)).edgeSatisfied
      (encodeLabeling d n labels) (encodeDart vertices d n e) =
        (mathematicalGraph input n).edgeSatisfied labels e := by
  rw [semantics_table]
  unfold encodeLabeling encodeLabel encodeDart
  exact
    GenericGraphTables.enumeratedGraph_edgeSatisfied (mathematicalGraph input n)
      (Equiv.refl _) (dartEquiv vertices d n) (paddedLabelEquiv d (n + 1) 64) labels e

theorem edgeSatisfied_decoded {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (labels : EncodedLabeling vertices d n) (i : Fin (dartCount vertices d n)) :
    (GenericGraphTables.semantics (table input n)).edgeSatisfied labels i =
      (mathematicalGraph input n).edgeSatisfied (decodeLabeling d n labels)
        (decodeDart vertices d n i) := by
  have h := edgeSatisfied_encoded input n (decodeLabeling d n labels) (decodeDart vertices d n i)
  let G : ConstraintGraph (Fin vertices) (Fin (dartCount vertices d n))
      (Fin (labelCount d n)) := GenericGraphTables.semantics (table input n)
  change G.edgeSatisfied (encodeLabeling d n (decodeLabeling d n labels))
    (encodeDart vertices d n (decodeDart vertices d n i)) = _ at h
  rw [encodeLabeling_decodeLabeling] at h
  exact (congrArg (G.edgeSatisfied labels)
    (encodeDart_decodeDart vertices d n i)).symm.trans h

theorem rejectionCount_encoded {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (labels : RawLabeling vertices d n) :
    (GenericGraphTables.semantics (table input n)).rejectionCount
      (encodeLabeling d n labels) = (mathematicalGraph input n).rejectionCount labels := by
  rw [semantics_table]
  unfold encodeLabeling encodeLabel
  exact
    GenericGraphTables.enumeratedGraph_rejectionCount (mathematicalGraph input n)
      (Equiv.refl _) (dartEquiv vertices d n) (paddedLabelEquiv d (n + 1) 64) labels

theorem rejectionCount_decoded {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (labels : EncodedLabeling vertices d n) :
    (GenericGraphTables.semantics (table input n)).rejectionCount labels =
      (mathematicalGraph input n).rejectionCount (decodeLabeling d n labels) := by
  have h := rejectionCount_encoded input n (decodeLabeling d n labels)
  let G : ConstraintGraph (Fin vertices) (Fin (dartCount vertices d n))
      (Fin (labelCount d n)) := GenericGraphTables.semantics (table input n)
  change G.rejectionCount (encodeLabeling d n (decodeLabeling d n labels)) = _ at h
  rw [encodeLabeling_decodeLabeling] at h
  exact h

theorem card_darts_eq_table {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) = (table input n).darts := by
  change Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) =
    2 * vertices * d ^ (n + 1)
  simpa only [Fintype.card_fin] using Fintype.card_congr (dartEquiv vertices d n)

theorem satisfiable_iff {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) :
    (GenericGraphTables.semantics (table input n)).Satisfiable ↔
      (mathematicalGraph input n).Satisfiable := by
  constructor
  · rintro ⟨labels, satisfies⟩
    refine ⟨decodeLabeling d n labels, ?_⟩
    intro e
    have h := edgeSatisfied_decoded input n labels (encodeDart vertices d n e)
    rw [decodeDart_encodeDart] at h
    exact h.symm.trans (satisfies (encodeDart vertices d n e))
  · rintro ⟨labels, satisfies⟩
    refine ⟨encodeLabeling d n labels, ?_⟩
    intro i
    have h := edgeSatisfied_encoded input n labels (decodeDart vertices d n i)
    rw [encodeDart_decodeDart vertices d n i] at h
    exact h.trans (satisfies (decodeDart vertices d n i))

theorem preserves_satisfiability {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (h : (PortTables.baseGraph input).Satisfiable) :
    (GenericGraphTables.semantics (table input n)).Satisfiable := by
  apply (satisfiable_iff input n).mpr
  exact PoweringTest.preserves_satisfiability (PortTables.portGraph input)
    (PortTables.accepts input) (PortTables.accepts_rotation input) n
    (finitePortSelector (PortTables.portGraph input) (n + 1)) h

theorem uniform_count_gap_iff {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (epsilon : ℝ) :
    (∀ labels : EncodedLabeling vertices d n,
      epsilon * ((table input n).darts : ℝ) ≤
        ((GenericGraphTables.semantics (table input n)).rejectionCount labels : ℝ)) ↔
    (∀ labels : RawLabeling vertices d n,
      epsilon * (Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) : ℝ) ≤
        ((mathematicalGraph input n).rejectionCount labels : ℝ)) := by
  constructor
  · intro h labels
    calc
      epsilon * (Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) : ℝ) =
          epsilon * ((table input n).darts : ℝ) := by rw [card_darts_eq_table]
      _ ≤ ((GenericGraphTables.semantics (table input n)).rejectionCount
          (encodeLabeling d n labels) : ℝ) := h (encodeLabeling d n labels)
      _ = ((mathematicalGraph input n).rejectionCount labels : ℝ) :=
        congrArg (fun k : ℕ => (k : ℝ)) (rejectionCount_encoded input n labels)
  · intro h labels
    rw [rejectionCount_decoded input n labels]
    have hlabels := h (decodeLabeling d n labels)
    rw [card_darts_eq_table input n] at hlabels
    exact hlabels

theorem uniform_count_gap {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (epsilon : ℝ)
    (hgap : ∀ labels : RawLabeling vertices d n,
      epsilon * (Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) : ℝ) ≤
        ((mathematicalGraph input n).rejectionCount labels : ℝ)) :
    ∀ labels : EncodedLabeling vertices d n,
      epsilon * ((table input n).darts : ℝ) ≤
        ((GenericGraphTables.semantics (table input n)).rejectionCount labels : ℝ) :=
  (uniform_count_gap_iff input n epsilon).mpr hgap

end UniqueGames.Foundations.PCP.PoweringTableSemantics

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PreprocessingTableSpectral
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.PoweringLabels.finiteBall _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                                   

namespace UniqueGames.Foundations.PCP.PreprocessingTableSpectral

open PoweringWalks SpectralReturn

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

end UniqueGames.Foundations.PCP.PreprocessingTableSpectral

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PoweringPortReindex
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.dartNonempty _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                            

noncomputable section
namespace UniqueGames.Foundations.PCP.PoweringPortReindex
open PoweringWalks PoweringLabels PoweringReach PoweringTest
open SpectralReturn PoweringSoundness

variable {V D E A : Type*}

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
  left_inv _u := rfl
  right_inv _u := rfl

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

def pullAccepts : Edge V D → A → A → Bool :=
  fun e => accepts (e.1, ports e.2)

theorem pathAccepts_map (n : Nat) (selectors : ∀v, AddressSelector H (n+1) v)
    (w : Walk V D (n+1)) (a b : PaddedLabel E (n+1) A) :
    pathAccepts G (pullAccepts ports accepts) n
      (fun v => pullSelector G H ports rotation (selectors v)) w
      (labelEquiv ports (n+1) a) (labelEquiv ports (n+1) b) =
    pathAccepts H accepts n selectors (walkEquiv ports (n+1) w) a b := by
  classical
  unfold pathAccepts
  congr 1
  apply propext
  apply forall_congr'
  intro k
  have ht := decode_transport G H ports rotation selectors a rfl
    (tailFromStart G n w k) (tailFromStart H n (walkEquiv ports (n+1) w) k)
    (congrArg Prod.fst (edgeAt_map G H ports rotation n w k)).symm
  have hh := decode_transport G H ports rotation selectors b
    (endpoint_map G H ports rotation (n+1) w).symm
    (headFromEnd G n w k) (headFromEnd H n (walkEquiv ports (n+1) w) k)
    (by
      change (G.rot (edgeAt G n w k)).1 =
        (H.rot (edgeAt H n (walkEquiv ports (n+1) w) k)).1
      rw [edgeAt_map G H ports rotation, rotation])
  rw [ht, hh]
  simp only [pullAccepts, edgeAt_map G H ports rotation]
  rfl

def dartEquiv (n : Nat) : Dart V D n ≃ Dart V E n :=
  Equiv.prodCongr (Equiv.refl Bool) (walkEquiv ports (n+1))

theorem edgeSatisfied_map (n : Nat) (selectors : ∀v, AddressSelector H (n+1) v)
    (labels : V → PaddedLabel E (n+1) A) (e : Dart V D n) :
    (poweredGraph G (pullAccepts ports accepts) n
      (fun v => pullSelector G H ports rotation (selectors v))).edgeSatisfied
        (fun v => labelEquiv ports (n+1) (labels v)) e =
    (poweredGraph H accepts n selectors).edgeSatisfied labels (dartEquiv ports n e) := by
  rcases e with ⟨direction,w⟩
  rw [poweredGraph_edgeSatisfied]
  change _ = (poweredGraph H accepts n selectors).edgeSatisfied labels
    (direction, walkEquiv ports (n+1) w)
  rw [poweredGraph_edgeSatisfied, endpoint_map G H ports rotation]
  exact pathAccepts_map G H ports rotation accepts n selectors w _ _

theorem rejectionCount_map [Fintype V] [Fintype D] [Fintype E]
    (n : Nat) (selectors : ∀v, AddressSelector H (n+1) v)
    (labels : V → PaddedLabel E (n+1) A) :
    (poweredGraph G (pullAccepts ports accepts) n
      (fun v => pullSelector G H ports rotation (selectors v))).rejectionCount
        (fun v => labelEquiv ports (n+1) (labels v)) =
    (poweredGraph H accepts n selectors).rejectionCount labels := by
  classical
  unfold ConstraintGraph.rejectionCount
  apply Finset.card_bij (fun e _ => dartEquiv ports n e)
  · intro e he
    rw [ConstraintGraph.mem_rejectedDarts, ← edgeSatisfied_map G H ports rotation]
    exact (ConstraintGraph.mem_rejectedDarts _ _ _).mp he
  · intro e _ f _ h
    exact (dartEquiv ports n).injective h
  · intro e he
    refine ⟨(dartEquiv ports n).symm e, ?_, (dartEquiv ports n).apply_symm_apply e⟩
    rw [ConstraintGraph.mem_rejectedDarts, edgeSatisfied_map G H ports rotation,
      Equiv.apply_symm_apply]
    exact (ConstraintGraph.mem_rejectedDarts _ _ _).mp he

theorem pullReverse
    (reverse_accepts : ∀ e a b, accepts (H.rot e) b a = accepts e a b)
    (e : Edge V D) (a b : A) :
    pullAccepts ports accepts (G.rot e) b a = pullAccepts ports accepts e a b := by
  simpa only [pullAccepts, rotation] using reverse_accepts (e.1,ports e.2) a b

theorem base_edgeSatisfied_map
    (reverse_accepts : ∀ e a b, accepts (H.rot e) b a = accepts e a b)
    (assignment : V → A) (e : Edge V D) :
    (baseGraph G (pullAccepts ports accepts)
      (pullReverse G H ports rotation accepts reverse_accepts)).edgeSatisfied assignment e =
    (baseGraph H accepts reverse_accepts).edgeSatisfied assignment (e.1,ports e.2) := by
  change accepts (e.1,ports e.2) (assignment e.1) (assignment (G.rot e).1) =
    accepts (e.1,ports e.2) (assignment e.1) (assignment (H.rot (e.1,ports e.2)).1)
  rw [rotation]

theorem base_rejectionCount_map [Fintype V] [Fintype D] [Fintype E]
    (reverse_accepts : ∀ e a b, accepts (H.rot e) b a = accepts e a b)
    (assignment : V → A) :
    (baseGraph G (pullAccepts ports accepts)
      (pullReverse G H ports rotation accepts reverse_accepts)).rejectionCount assignment =
    (baseGraph H accepts reverse_accepts).rejectionCount assignment := by
  classical
  let e : Edge V D ≃ Edge V E := Equiv.prodCongr (Equiv.refl V) ports
  have edgeEq (x : Edge V D) :=
    base_edgeSatisfied_map G H ports rotation accepts reverse_accepts assignment x
  unfold ConstraintGraph.rejectionCount
  apply Finset.card_bij (fun x _ => e x)
  · intro x hx
    rw [ConstraintGraph.mem_rejectedDarts]
    change (baseGraph H accepts reverse_accepts).edgeSatisfied assignment (x.1,ports x.2) = false
    rw [← edgeEq]
    exact (ConstraintGraph.mem_rejectedDarts _ _ _).mp hx
  · intro x _ y _ h
    exact e.injective h
  · intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [ConstraintGraph.mem_rejectedDarts, edgeEq]
    change (baseGraph H accepts reverse_accepts).edgeSatisfied assignment (e (e.symm y)) = false
    rw [e.apply_symm_apply]
    exact (ConstraintGraph.mem_rejectedDarts _ _ _).mp hy

omit rotation in

theorem uniform_count_gap
    [Fintype V] [Fintype D] [Fintype E] [Nonempty V] [Nonempty D]
    [Fintype A] [Nonempty A]
    (G : PortGraph V D) (H : PortGraph V E) (ports : (Bool × D) ≃ E)
    (rotation : ∀ v d, H.rot (v, ports d) =
      (((lazyGraph G).rot (v,d)).1, ports ((lazyGraph G).rot (v,d)).2))
    (lambda : ℝ) (certificate : SpectralCertificate (lazyGraph G) lambda)
    (accepts : Edge V E → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (H.rot e) b a = accepts e a b)
    (M : Nat) (hM : 1 ≤ M)
    (selectors : ∀v, AddressSelector H (2*center (Fintype.card A) M+1) v)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hgap : ∀ assignment : V → A,
      epsilon * (Fintype.card (Edge V E) : ℝ) ≤
        ((baseGraph H accepts reverse_accepts).rejectionCount assignment : ℝ))
    (labels : V → PaddedLabel E (2*center (Fintype.card A) M+1) A) :
    (gain (Fintype.card A) M lambda *
      min epsilon (1 / ((2*center (Fintype.card A) M+1 : Nat) : ℝ))) *
        (Fintype.card (Dart V E (2*center (Fintype.card A) M)) : ℝ) ≤
      ((poweredGraph H accepts (2*center (Fintype.card A) M) selectors).rejectionCount labels : ℝ) := by
  have hbase : ∀ assignment : V → A,
      epsilon * (Fintype.card (Edge V (Bool × D)) : ℝ) ≤
      ((baseGraph (lazyGraph G) (pullAccepts ports accepts)
        (pullReverse (lazyGraph G) H ports rotation accepts reverse_accepts)).rejectionCount assignment : ℝ) := by
    intro assignment
    rw [base_rejectionCount_map (lazyGraph G) H ports rotation,
      Fintype.card_congr (Equiv.prodCongr (Equiv.refl V) ports)]
    exact hgap assignment
  have bound := PoweringGap.uniform_count_gap G lambda certificate
    (pullAccepts ports accepts)
    (pullReverse (lazyGraph G) H ports rotation accepts reverse_accepts) M hM
    (fun v => pullSelector (lazyGraph G) H ports rotation (selectors v))
    epsilon hepsilon hbase (fun v => labelEquiv ports _ (labels v))
  rw [rejectionCount_map (lazyGraph G) H ports rotation,
    Fintype.card_congr (dartEquiv (V := V) ports (2*center (Fintype.card A) M))] at bound
  exact bound

omit rotation in

theorem lazy_table_uniform_count_gap {vertices d : Nat}
    (input : PortTables.Table vertices d) (hv : 0 < vertices) (hd : 0 < d)
    (lambda : ℝ)
    (certificate : SpectralCertificate (lazyGraph (PortTables.portGraph input)) lambda)
    (M : Nat) (hM : 1 ≤ M) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hgap : ∀ assignment : Fin vertices → Fin 64,
      epsilon * (Fintype.card (Fin vertices × Fin (2*d)) : ℝ) ≤
        ((PortTables.baseGraph (PreprocessingOverlayTables.lazy input)).rejectionCount assignment : ℝ)) :
    ∀ labels : PoweringTableSemantics.EncodedLabeling vertices (2*d) (2*center 64 M),
    (gain 64 M lambda * min epsilon (1 / ((2*center 64 M+1 : Nat) : ℝ))) *
      ((PoweringTables.table (PreprocessingOverlayTables.lazy input) (2*center 64 M)).darts : ℝ) ≤
      ((GenericGraphTables.semantics
        (PoweringTables.table (PreprocessingOverlayTables.lazy input) (2*center 64 M))).rejectionCount labels : ℝ) := by
  let : Nonempty (Fin vertices) := ⟨⟨0,hv⟩⟩
  let : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  apply PoweringTableSemantics.uniform_count_gap
  intro labels
  have hrot : ∀ v p,
      (PortTables.portGraph (PreprocessingOverlayTables.lazy input)).rot
          (v, PreprocessingOverlayTables.lazyPorts d p) =
        (((lazyGraph (PortTables.portGraph input)).rot (v,p)).1,
          PreprocessingOverlayTables.lazyPorts d
            ((lazyGraph (PortTables.portGraph input)).rot (v,p)).2) := by
    intro v p
    rw [PreprocessingTableSpectral.lazy_portGraph]
    exact GraphTransport.reindex_rot _ (Equiv.refl _) _ v p
  have bound := uniform_count_gap (PortTables.portGraph input)
      (PortTables.portGraph (PreprocessingOverlayTables.lazy input))
      (PreprocessingOverlayTables.lazyPorts d) hrot lambda certificate
      (PortTables.accepts (PreprocessingOverlayTables.lazy input))
      (PortTables.accepts_rotation (PreprocessingOverlayTables.lazy input)) M hM
      (PoweringAddresses.finitePortSelector
        (PortTables.portGraph (PreprocessingOverlayTables.lazy input)) _) epsilon hepsilon
      hgap
  simp only [PortTables.Label, GraphTables.Label, Fintype.card_fin] at bound
  exact bound labels

omit rotation in

theorem lazy_table_uniform_count_gap_at {vertices d : Nat}
    (input : PortTables.Table vertices d) (hv : 0 < vertices) (hd : 0 < d)
    (lambda : ℝ)
    (certificate : SpectralCertificate (lazyGraph (PortTables.portGraph input)) lambda)
    (M : Nat) (hM : 1 ≤ M) (n : Nat) (hn : n = 2*center 64 M)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hgap : ∀ assignment : Fin vertices → Fin 64,
      epsilon * (Fintype.card (Fin vertices × Fin (2*d)) : ℝ) ≤
        ((PortTables.baseGraph (PreprocessingOverlayTables.lazy input)).rejectionCount
          assignment : ℝ)) :
    ∀ labels : PoweringTableSemantics.EncodedLabeling vertices (2*d) n,
    (gain 64 M lambda * min epsilon (1 / ((n+1 : Nat) : ℝ))) *
      ((PoweringTables.table (PreprocessingOverlayTables.lazy input) n).darts : ℝ) ≤
      ((GenericGraphTables.semantics
        (PoweringTables.table (PreprocessingOverlayTables.lazy input) n)).rejectionCount
          labels : ℝ) := by
  subst n
  exact lazy_table_uniform_count_gap input hv hd lambda certificate M hM
    epsilon hepsilon hgap

end UniqueGames.Foundations.PCP.PoweringPortReindex

end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PreprocessingRegularSoundness
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.dartNonempty _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGames.Foundations.PCP.PoweringLabels.finiteBall _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                                      

namespace UniqueGames.Foundations.PCP.PreprocessingRegularSoundness

open PoweringWalks DegreeReplacement SpectralReturn PreprocessingRegularTables

theorem internalDegree_ge_eight : 8 ≤ internalDegree := by
  simpa only [ExpanderFamily.card_port, internalDegree, pow_two] using
    ExpanderFamily.port_degree_ge_eight

theorem baseDegree_ne_zero : Expanders.baseDegree ≠ 0 := by
  intro h
  have hdegree := internalDegree_ge_eight
  simp only [internalDegree, h, Nat.zero_mul] at hdegree
  omega

theorem familyCloudTable_certificate_of_pos (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (v : Fin t.vertices)
    (hk : 0 < PreprocessingCloudIndex.cloudSize t v) :
    SpectralCertificate (ExpanderTables.graph (familyCloudTable H t v)) (1 / 2 : ℝ) := by
  let : NeZero Expanders.baseDegree := ⟨baseDegree_ne_zero⟩
  unfold familyCloudTable
  rw [dite_eq_right (Nat.ne_of_gt hk)]
  apply resizeTable_certificate
  exact ExpanderTables.family_certificate H certificate _

theorem cloudGraphs_certificate_of_pos (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (v : Fin t.vertices)
    (hk : 0 < PreprocessingCloudIndex.cloudSize t v) :
    SpectralCertificate (cloudGraphs t (padding t) (familyCloudTable H t) v)
      (1 / 2 : ℝ) := by
  exact GraphTransport.reindex_spectralCertificate _ _ _ _
    (familyCloudTable_certificate_of_pos H certificate t v hk)

theorem cloud_expansion (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (v : Fin t.vertices)
    (S : Finset (PreprocessingCloudIndex.PaddedCloud t (padding t) v))
    (hsmall : S.card ≤
      Fintype.card (PreprocessingCloudIndex.PaddedCloud t (padding t) v) / 2) :
    2 * S.card ≤ (CloudRounding.directedCut
      (fun ed => ((cloudGraphs t (padding t) (familyCloudTable H t) v).rot ed).1) S).card := by
  by_cases hk : PreprocessingCloudIndex.cloudSize t v = 0
  · have hzero : Fintype.card (PreprocessingCloudIndex.PaddedCloud t (padding t) v) = 0 := by
      rw [PreprocessingCloudIndex.card_paddedCloud, cloudSize_add_padding, hk]
      rfl
    have hs : S.card = 0 := by omega
    simp only [hs, mul_zero, Nat.zero_le]
  · exact SpectralCut.cut_card_ge_twice
      (cloudGraphs t (padding t) (familyCloudTable H t) v)
      (cloudGraphs_certificate_of_pos H certificate t v (Nat.pos_of_ne_zero hk))
      (by simpa only [Fintype.card_fin] using internalDegree_ge_eight) S (by
        change 2 * S.card ≤
          Fintype.card (PreprocessingCloudIndex.PaddedCloud t (padding t) v)
        omega)

noncomputable def roundLabels (t : GraphTables.Table)
    (labels : Fin (vertexCount t (padding t)) → GraphTables.Label) :
    Fin t.vertices → GraphTables.Label :=
  CloudRounding.roundLabels
    (paddedGraph (GraphTables.semantics t) (fun v => Fin (padding t v)))
    (fun z => labels (vertexOrder t (padding t) z))

theorem soundness (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table)
    (labels : Fin (vertexCount t (padding t)) → GraphTables.Label) :
    (GraphTables.semantics t).rejectionCount (roundLabels t labels) ≤
      (PortTables.baseGraph (regularize H t)).rejectionCount labels := by
  rw [regularize, rejectionCount_ofCloudTables]
  exact CloudRounding.padded_replacement_soundness (GraphTables.semantics t)
    (fun v => Fin (padding t v)) (cloudGraphs t (padding t) (familyCloudTable H t))
    (cloud_expansion H certificate t) (fun z => labels (vertexOrder t (padding t) z))

theorem completeness (H : BaseTable) (t : GraphTables.Table)
    (h : (GraphTables.semantics t).Satisfiable) :
    (PortTables.baseGraph (regularize H t)).Satisfiable := by
  obtain ⟨labels, hlabels⟩ := h
  refine ⟨liftedLabel t (padding t) labels, ?_⟩
  intro e
  obtain ⟨z, rfl⟩ :=
    (Equiv.prodCongr (vertexOrder t (padding t)) (portOrder internalDegree)).surjective e
  rcases z with ⟨v, p⟩
  change (PortTables.baseGraph (regularize H t)).edgeSatisfied
    (liftedLabel t (padding t) labels)
    (vertexOrder t (padding t) v, portOrder internalDegree p) = true
  rw [regularize, edgeSatisfied_ofCloudTables]
  simp only [liftedLabel, Equiv.symm_apply_apply]
  have hcomplete := replacement_complete
    (paddedGraph (GraphTables.semantics t) (fun v => Fin (padding t v)))
    (cloudGraphs t (padding t) (familyCloudTable H t)) labels
    (padded_complete (GraphTables.semantics t) (fun v => Fin (padding t v)) labels hlabels)
    (v, p)
  convert hcomplete using 1
  all_goals try with_reducible_and_instances rfl
  rfl

end UniqueGames.Foundations.PCP.PreprocessingRegularSoundness

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_PreprocessingGuarantees
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.PCP.AlphabetRetraction.rejectionCount_pullback _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Relations.oldPredicate_relationAt _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Table.build_darts _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Table.build_vertices _root_.OAI.UniqueGames.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGames.Foundations.PCP.FiniteGraph.Bundle.ofGraph_rejectionCount _root_.OAI.UniqueGames.Foundations.PCP.GenericGraphTables.semantics_ofGraph_rejectionCount _root_.OAI.VertexCover.Machine.TableMachine.lookup_valid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                                

noncomputable section

namespace UniqueGames.Foundations.PCP.PreprocessingGuarantees

open PoweringWalks SpectralReturn PreprocessingTables
open PreprocessingRegularTables (internalDegree regularize)

variable {n d e : Nat}

theorem overlay_rejectionCount (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (labels : Fin n → GraphTables.Label) :
    (PortTables.baseGraph (PreprocessingOverlayTables.overlay G H)).rejectionCount labels =
      (PortTables.baseGraph G).rejectionCount labels := by
  rw [PreprocessingOverlayTables.overlay_semantics]
  calc
    _ = (Overlay.constraintGraph (PortTables.baseGraph G) (ExpanderTables.graph H)).rejectionCount labels := by
      convert ConstraintGraph.reindex_rejectionCount
        (Overlay.constraintGraph (PortTables.baseGraph G) (ExpanderTables.graph H))
        (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _)
          (PreprocessingOverlayTables.overlayPorts d e)) (Equiv.refl _) labels using 1 ; rfl
    _ = _ := Overlay.rejectionCount_eq _ _ rfl labels

theorem lazy_rejectionCount (G : PortTables.Table n d)
    (labels : Fin n → GraphTables.Label) :
    (PortTables.baseGraph (PreprocessingOverlayTables.lazy G)).rejectionCount labels =
      (PortTables.baseGraph G).rejectionCount labels := by
  rw [PreprocessingOverlayTables.lazy_semantics]
  calc
    _ = (LazyConstraint.constraintGraph (PortTables.baseGraph G)).rejectionCount labels := by
      convert ConstraintGraph.reindex_rejectionCount
        (LazyConstraint.constraintGraph (PortTables.baseGraph G))
        (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _)
          (PreprocessingOverlayTables.lazyPorts d)) (Equiv.refl _) labels using 1 ; rfl
    _ = _ := LazyConstraint.rejectionCount_eq _ rfl labels

theorem overlayFamily_certificate (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) :
    SpectralCertificate (ExpanderTables.graph (overlayFamily H t)) (1 / 2 : ℝ) := by
  let : NeZero Expanders.baseDegree := ⟨PreprocessingRegularSoundness.baseDegree_ne_zero⟩
  apply PreprocessingRegularSoundness.resizeTable_certificate
  exact ExpanderTables.family_certificate H certificate _

theorem overlay_certificate (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) :
    SpectralCertificate (PortTables.portGraph
      (PreprocessingOverlayTables.overlay (padded H t) (overlayFamily H t))) (7 / 8 : ℝ) :=
  PreprocessingTableSpectral.overlay_certificate_seven_eighths _ _
    (vertices_positive t) rfl PreprocessingRegularSoundness.internalDegree_ge_eight
    (overlayFamily_certificate H certificate t)

theorem rejectionCount_eq_regularized (H : BaseTable) (t : GraphTables.Table)
    (labels : Fin (vertices t) → GraphTables.Label) :
    (PortTables.baseGraph (preprocess H t)).rejectionCount labels =
      (PortTables.baseGraph (regularize H t)).rejectionCount (restrictedLabel t labels) := by
  unfold preprocess PreprocessingTables.degree
  rw [lazy_rejectionCount, overlay_rejectionCount]
  exact PreprocessingPaddingTables.pad_rejectionCount _ _ labels

def roundLabels (t : GraphTables.Table)
    (labels : Fin (vertices t) → GraphTables.Label) : Fin t.vertices → GraphTables.Label :=
  PreprocessingRegularSoundness.roundLabels t (restrictedLabel t labels)

theorem soundness (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (labels : Fin (vertices t) → GraphTables.Label) :
    (GraphTables.semantics t).rejectionCount (roundLabels t labels) ≤
      (PortTables.baseGraph (preprocess H t)).rejectionCount labels := by
  rw [rejectionCount_eq_regularized]
  exact PreprocessingRegularSoundness.soundness H certificate t (restrictedLabel t labels)

theorem completeness (H : BaseTable) (t : GraphTables.Table)
    (h : (GraphTables.semantics t).Satisfiable) :
    (PortTables.baseGraph (preprocess H t)).Satisfiable := by
  have hp : (PortTables.baseGraph (padded H t)).Satisfiable :=
    (PreprocessingPaddingTables.pad_satisfiable_iff _ _).mpr
      (PreprocessingRegularSoundness.completeness H t h)
  obtain ⟨labels, hlabels⟩ := hp
  refine ⟨labels, ?_⟩
  apply (ConstraintGraph.rejectionCount_eq_zero_iff _ labels).mp
  unfold preprocess PreprocessingTables.degree
  rw [lazy_rejectionCount, overlay_rejectionCount]
  exact (ConstraintGraph.rejectionCount_eq_zero_iff _ labels).mpr hlabels

theorem gap_transfer_real (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (ht : 0 < t.darts)
    (epsilon : ℝ) (he : 0 ≤ epsilon)
    (lower : ∀ labels : Fin t.vertices → GraphTables.Label,
      epsilon * t.darts ≤ ((GraphTables.semantics t).rejectionCount labels : ℝ))
    (labels : Fin (vertices t) → GraphTables.Label) :
    (epsilon / Preprocessing.sizeFactor) *
        Fintype.card (Fin (vertices t) × Fin PreprocessingTables.degree) ≤
      ((PortTables.baseGraph (preprocess H t)).rejectionCount labels : ℝ) := by
  have hs : (0 : ℝ) < Preprocessing.sizeFactor :=
    Nat.cast_pos.mpr Preprocessing.sizeFactor_positive
  have hcount : Fintype.card (Fin (vertices t) × Fin PreprocessingTables.degree) ≤
      Preprocessing.sizeFactor * t.darts := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    calc
      _ ≤ (ExpanderFamily.growth ^ 2 * t.darts) * PreprocessingTables.degree :=
        Nat.mul_le_mul_right _ (vertices_le_of_positive t ht)
      _ = _ := by rw [PreprocessingTables.degree_eq]; unfold Preprocessing.sizeFactor; ring
  have hcountR : (Fintype.card (Fin (vertices t) × Fin PreprocessingTables.degree) : ℝ) ≤
      (Preprocessing.sizeFactor : ℝ) * t.darts := by exact_mod_cast hcount
  calc
    _ ≤ (epsilon / Preprocessing.sizeFactor) *
        ((Preprocessing.sizeFactor : ℝ) * t.darts) :=
      mul_le_mul_of_nonneg_left hcountR (div_nonneg he hs.le)
    _ = epsilon * t.darts := by field_simp
    _ ≤ ((GraphTables.semantics t).rejectionCount (roundLabels t labels) : ℝ) := lower _
    _ ≤ _ := Nat.cast_le.mpr (soundness H certificate t labels)

end UniqueGames.Foundations.PCP.PreprocessingGuarantees
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_RawInitialTables
attribute [-instance] _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.slotFintype _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.slotInhabited _root_.OAI.UniqueGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.VertexCover.ClauseProjection.instDecidableConsistent _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.BinaryFormula.dense_clause_count _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGames.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.baseAccepts_eq_true_iff _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.card_ClauseContext _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.card_VariableContext _root_.OAI.UniqueGames.Foundations.Hastad.SourceContexts.localConsistent_eq_true_iff _root_.OAI.UniqueGames.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGames.Foundations.Hastad.SourceOccurrences.nBits_eq _root_.OAI.UniqueGames.Foundations.Hastad.SourceSoundness.leftTable_answer _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Table.build_darts _root_.OAI.UniqueGames.Foundations.PCP.AlphabetTable.Table.build_vertices _root_.OAI.UniqueGames.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudRank_cloudSelect _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudRank_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_cloudRank _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.mem_cloudDarts _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.paddedCloudRank_new _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.paddedCloudRank_new_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.paddedCloudRank_old _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingCloudIndex.paddedCloudRank_old_val _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_dummy _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_internal _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.accepts_original _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.vertexOrder_dummy _root_.OAI.UniqueGames.Foundations.PCP.PreprocessingRegularTables.vertexOrder_original _root_.OAI.VertexCover.Machine.TableMachine.lookup_valid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                         

namespace UniqueGames.Foundations.PCP.RawInitialTables

open Target GraphTables

def slotOrder : Slot ≃ Fin 3 where
  toFun
    | .first => 0
    | .second => 1
    | .third => 2
  invFun i := if i = 0 then .first else if i = 1 then .second else .third
  left_inv s := by cases s <;> rfl
  right_inv i := by fin_cases i <;> rfl

def labelOrder : AlphabetRetraction.Label64 ≃ GraphTables.Label := binaryOrder 6

def vertexOrder (F : Formula) :
    InitialGraph.Vertex F ≃ Fin (F.«variables» + F.clauses.length + 1) :=
  ((finSumFinEquiv.sumCongr unitOrder).trans finSumFinEquiv)

def eventOrder (F : Formula) : RandomEvent F ≃ Fin (F.clauses.length * 3) :=
  ((Equiv.refl (Fin F.clauses.length)).prodCongr slotOrder).trans finProdFinEquiv

def dartOrder (F : Formula) : InitialGraph.Dart F ≃ Fin (6 * F.clauses.length + 1) :=
  (((((eventOrder F).prodCongr finTwoEquiv.symm).trans finProdFinEquiv).sumCongr
    unitOrder).trans finSumFinEquiv).trans (finCongr (by omega))

def raw64 (F : Formula) : ConstraintGraph (InitialGraph.Vertex F)
    (InitialGraph.Dart F) AlphabetRetraction.Label64 :=
  AlphabetRetraction.pullback (InitialGraph.raw F) AlphabetRetraction.decode64

def table (F : Formula) : GraphTables.Table :=
  GraphTables.ofEnumeratedGraph (raw64 F) (vertexOrder F) (dartOrder F) labelOrder

@[simp] theorem table_vertices (F : Formula) :
    (table F).vertices = F.«variables» + F.clauses.length + 1 := rfl

@[simp] theorem table_darts (F : Formula) : (table F).darts = 6 * F.clauses.length + 1 := rfl

theorem table_darts_positive (F : Formula) : 0 < (table F).darts := by
  rw [table_darts]; omega

theorem raw64_satisfiable_iff (F : Formula) : (raw64 F).Satisfiable ↔ F.Satisfiable :=
  (AlphabetRetraction.satisfiable_pullback_iff (InitialGraph.raw F)
    AlphabetRetraction.decode64 AlphabetRetraction.encode64
      AlphabetRetraction.decode_encode64).trans (InitialGraph.raw_satisfiable_iff F)

theorem table_semantics (F : Formula) :
    GraphTables.semantics (table F) =
      (raw64 F).reindex (vertexOrder F) (dartOrder F) labelOrder := by
  change GraphTables.semantics (GraphTables.ofGraph
    (GraphTables.enumeratedGraph (raw64 F) (vertexOrder F) (dartOrder F) labelOrder)) = _
  rw [GraphTables.semantics_ofGraph]
  rfl

theorem table_satisfiable_iff (F : Formula) :
    (GraphTables.semantics (table F)).Satisfiable ↔ F.Satisfiable := by
  rw [table_semantics]
  exact ((raw64 F).satisfiable_reindex (vertexOrder F) (dartOrder F) labelOrder).trans
    (raw64_satisfiable_iff F)

end UniqueGames.Foundations.PCP.RawInitialTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_RoundGap
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                 

noncomputable section

namespace UniqueGames.Foundations.PCP.RoundGap

open AmplificationRound

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [Nonempty E]

def poweredLower (epsilon : ℝ) : ℝ :=
  PoweringSoundness.gain (Fintype.card Label) FinalConstants.windowHalf (31 / 32) *
    min (epsilon / (Preprocessing.sizeFactor : ℝ)) FinalConstants.cap

theorem poweredLower_nonnegative (epsilon : ℝ) (he : 0 ≤ epsilon) :
    0 ≤ poweredLower epsilon := by
  have hg := PoweringGap.gain_nonneg (Fintype.card Label)
    FinalConstants.windowHalf (31 / 32) (by norm_num)
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := by
    exact_mod_cast Preprocessing.sizeFactor_positive
  exact mul_nonneg hg (le_min (div_nonneg he hs.le) FinalConstants.cap_positive.le)

end UniqueGames.Foundations.PCP.RoundGap
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_RoundTables
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instDecidableConsistent _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                    

namespace UniqueGames.Foundations.PCP.RoundTables

opaque fixedWalkParameter : {n : Nat // n = 2 * FinalConstants.endpointLength} :=
  ⟨2 * FinalConstants.endpointLength, rfl⟩

def walkParameter : Nat := fixedWalkParameter.val

theorem walkParameter_eq : walkParameter = 2 * FinalConstants.endpointLength :=
  fixedWalkParameter.property

def alphabet : Nat := PoweringTables.labelCount PreprocessingTables.degree walkParameter

theorem alphabet_positive : 0 < alphabet := by
  unfold alphabet PoweringTables.labelCount
  exact Nat.pow_pos (by decide)

def powered (H : BaseTable) (table : GraphTables.Table) : GenericGraphTables.Table alphabet :=
  PoweringTables.table (PreprocessingTables.preprocess H table) walkParameter

def build (H : BaseTable) (table : GraphTables.Table) : GraphTables.Table :=
  AlphabetTable.Table.build (powered H table)

def sizeFactor : Nat := AlphabetGraphBounds.sizeFactor alphabet *
  (ExpanderFamily.growth ^ 2 * (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1)))

theorem sizeFactor_positive : 0 < sizeFactor := by
  unfold sizeFactor
  apply Nat.mul_pos (AlphabetGraphBounds.sizeFactor_positive alphabet)
  apply Nat.mul_pos
  · exact Nat.pow_pos (Nat.zero_lt_one.trans ExpanderFamily.growth_gt_one)
  · omega

theorem powered_vertices (H : BaseTable) (table : GraphTables.Table) :
    (powered H table).vertices = PreprocessingTables.vertices table := rfl

theorem powered_darts (H : BaseTable) (table : GraphTables.Table) :
    (powered H table).darts = 2 * PreprocessingTables.vertices table *
      PreprocessingTables.degree ^ (walkParameter + 1) := rfl

theorem build_darts_positive (H : BaseTable) (table : GraphTables.Table) :
    0 < (build H table).darts := by
  change 0 < (AlphabetTable.Table.build (powered H table)).darts
  rw [AlphabetTableBounds.build_darts, powered_darts]
  exact Nat.mul_pos (Nat.mul_pos
    (Nat.mul_pos (by decide) (PreprocessingTables.vertices_positive table))
    (Nat.pow_pos degree_positive)) (dartFactor_positive alphabet)

theorem build_size_le (H : BaseTable) (table : GraphTables.Table)
    (ht : 0 < table.darts) :
    (build H table).vertices + (build H table).darts ≤
      sizeFactor * (table.vertices + table.darts) := by
  have hv := PreprocessingTables.vertices_le_of_positive table ht
  have he : (powered H table).vertices + (powered H table).darts =
      PreprocessingTables.vertices table *
        (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1)) := by
    rw [powered_vertices, powered_darts]
    ring
  have hp := Nat.mul_le_mul_right
    (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1)) hv
  calc
    _ ≤ AlphabetGraphBounds.sizeFactor alphabet *
        ((powered H table).vertices + (powered H table).darts) :=
      AlphabetTableBounds.build_total_le (powered H table)
    _ = AlphabetGraphBounds.sizeFactor alphabet *
        (PreprocessingTables.vertices table *
          (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1))) := by rw [he]
    _ ≤ AlphabetGraphBounds.sizeFactor alphabet *
        ((ExpanderFamily.growth ^ 2 * table.darts) *
          (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1))) :=
      Nat.mul_le_mul_left _ hp
    _ = sizeFactor * table.darts := by unfold sizeFactor; ring
    _ ≤ sizeFactor * (table.vertices + table.darts) :=
      Nat.mul_le_mul_left _ (Nat.le_add_left _ _)

theorem build_completeness (H : BaseTable) (table : GraphTables.Table)
    (sat : (GraphTables.semantics table).Satisfiable) :
    (GraphTables.semantics (build H table)).Satisfiable := by
  let : Nonempty (Fin alphabet) := ⟨⟨0, alphabet_positive⟩⟩
  exact AlphabetTable.Table.perfect_completeness (powered H table)
    (PoweringTableSemantics.preserves_satisfiability
      (PreprocessingTables.preprocess H table) walkParameter
      (PreprocessingGuarantees.completeness H table sat))

abbrev Input := {table : GraphTables.Table // 0 < table.darts}

instance instNonemptyFinDartsValTableLtNatOfNat (input : Input) : Nonempty (Fin input.val.darts) := ⟨⟨0, input.property⟩⟩

def step (H : BaseTable) (input : Input) : Input :=
  ⟨build H input.val, build_darts_positive H input.val⟩

def initial (F : Target.Formula) : Input :=
  ⟨RawInitialTables.table F, RawInitialTables.table_darts_positive F⟩

def size (input : Input) : Nat := input.val.vertices + input.val.darts

def Satisfiable (input : Input) : Prop := (GraphTables.semantics input.val).Satisfiable

noncomputable def gap (input : Input) : ℝ := (GraphTables.semantics input.val).gap

theorem size_positive (input : Input) : 0 < size input :=
  input.property.trans_le (Nat.le_add_left _ _)

theorem gap_nonnegative (input : Input) : 0 ≤ gap input :=
  (GraphTables.semantics input.val).gap_nonnegative

theorem one_le_size_mul_gap (input : Input) (unsat : ¬ Satisfiable input) :
    1 ≤ (size input : ℝ) * gap input := by
  have h := (GraphTables.semantics input.val).inverse_card_le_gap_of_unsatisfiable unsat
  have hp : (0 : ℝ) < input.val.darts := Nat.cast_pos.mpr input.property
  simp only [Fintype.card_fin] at h
  have hd := (div_le_iff₀ hp).mp h
  have hsize : (input.val.darts : ℝ) ≤ (size input : ℝ) := by
    exact_mod_cast (Nat.le_add_left input.val.darts input.val.vertices)
  exact (show 1 ≤ (input.val.darts : ℝ) * gap input by
    simpa only [gap, mul_comm] using hd).trans
    (mul_le_mul_of_nonneg_right hsize (gap_nonnegative input))

theorem initial_satisfiable_iff (F : Target.Formula) : Satisfiable (initial F) ↔ F.Satisfiable :=
  RawInitialTables.table_satisfiable_iff F

theorem step_completeness (H : BaseTable) (input : Input) :
    Satisfiable input → Satisfiable (step H input) := build_completeness H input.val

theorem step_size (H : BaseTable) (input : Input) :
    size (step H input) ≤ sizeFactor * size input := build_size_le H input.val input.property

end UniqueGames.Foundations.PCP.RoundTables

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_RoundTableGap
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                                                                      

namespace UniqueGames.Foundations.PCP.RoundTableGap

open RoundTables
open PoweringWalks SpectralReturn

variable (H : BaseTable)
  (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))

include certificate

theorem powered_count_gap (input : Input)
    (labeling : Fin (powered H input.val).vertices → Fin alphabet) :
    RoundGap.poweredLower (gap input) * ((powered H input.val).darts : ℝ) ≤
      ((GenericGraphTables.semantics (powered H input.val)).rejectionCount labeling : ℝ) := by
  let old := PreprocessingOverlayTables.overlay
    (PreprocessingTables.padded H input.val) (PreprocessingTables.overlayFamily H input.val)
  have hd : 0 < (PreprocessingRegularTables.internalDegree + 1) +
      PreprocessingRegularTables.internalDegree := by omega
  let : Nonempty (Fin ((PreprocessingRegularTables.internalDegree + 1) +
      PreprocessingRegularTables.internalDegree)) := ⟨⟨0, hd⟩⟩
  have spectral : SpectralCertificate (lazyGraph (PortTables.portGraph old)) (31 / 32 : ℝ) :=
    LazySpectral.lazy_certificate_31_32 (PortTables.portGraph old)
      (PreprocessingGuarantees.overlay_certificate H certificate input.val)
  have lower := PreprocessingGuarantees.gap_transfer_real H certificate input.val input.property
    (gap input) (gap_nonnegative input)
    (by simpa only [Fintype.card_fin] using
      ((GraphTables.semantics input.val).le_gap_iff (gap input)).mp le_rfl)
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := Nat.cast_pos.mpr Preprocessing.sizeFactor_positive
  have hn : walkParameter = 2 * PoweringSoundness.center 64 FinalConstants.windowHalf :=
    walkParameter_eq
  have bound := PoweringPortReindex.lazy_table_uniform_count_gap_at old
    (PreprocessingTables.vertices_positive input.val) hd (31 / 32) spectral
    FinalConstants.windowHalf FinalConstants.windowHalf_positive walkParameter hn
    (gap input / Preprocessing.sizeFactor) (div_nonneg (gap_nonnegative input) hs.le)
    lower labeling
  have hw : walkParameter + 1 = FinalConstants.walkLength := by
    rw [walkParameter_eq]
    rfl
  simp only [RoundGap.poweredLower, PoweringFinalConstants.card_alphabet,
    hw, FinalConstants.cap, powered, PreprocessingTables.preprocess, old] at bound ⊢
  exact bound

theorem build_count_gap (input : Input)
    (labeling : Fin (build H input.val).vertices → GraphTables.Label) :
    min (2 * gap input) FinalConstants.cap * ((build H input.val).darts : ℝ) ≤
      ((GraphTables.semantics (build H input.val)).rejectionCount labeling : ℝ) := by
  have h := AlphabetTableBounds.gap_transfer_real alphabet_positive (powered H input.val)
    (RoundGap.poweredLower (gap input))
    (RoundGap.poweredLower_nonnegative (gap input) (gap_nonnegative input))
    (powered_count_gap H certificate input) labeling
  have scalar : min (2 * gap input) FinalConstants.cap ≤
      RoundGap.poweredLower (gap input) / 12288 := by
    simpa only [RoundGap.poweredLower, FinalConstants.cap, FinalConstants.walkLength,
      PoweringFinalConstants.center_eq] using
      PoweringFinalConstants.composed_scaled_gap (gap input) (gap_nonnegative input)
  exact (mul_le_mul_of_nonneg_right scalar (Nat.cast_nonneg _)).trans h

theorem step_gap (input : Input) :
    min (2 * gap input) FinalConstants.cap ≤ gap (step H input) := by
  apply ((GraphTables.semantics (step H input).val).le_gap_iff _).mpr
  intro labeling
  rw [Fintype.card_fin]
  exact build_count_gap H certificate input labeling

end UniqueGames.Foundations.PCP.RoundTableGap

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_Reveal
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.dartNonempty _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                      
section

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def revealLaw (μ : FiniteDistribution (X × Y)) :
    FiniteDistribution ((X × Y) × (X ⊕ Y)) :=
  (μ.product (FiniteDistribution.uniform Bool)).pushforward
    (fun z => (z.1, revealEndpoint z.1 z.2))

theorem revealLaw_weight (μ : FiniteDistribution (X × Y)) (q : X × Y) (r : X ⊕ Y) :
    (revealLaw μ).weight (q,r) =
      (if r = Sum.inl q.1 then μ.weight q / 2 else 0) +
      (if r = Sum.inr q.2 then μ.weight q / 2 else 0) := by
  classical
  rcases q with ⟨x,y⟩
  simp only [revealLaw, FiniteDistribution.pushforward, FiniteDistribution.product,
    Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
  simp [revealEndpoint, FiniteDistribution.uniform, div_eq_mul_inv, add_comm, eq_comm]

def revealFirstLaw (μ : FiniteDistribution (X × Y)) :
    FiniteDistribution ((X ⊕ Y) × (X × Y)) :=
  (revealLaw μ).transport (Equiv.prodComm _ _)

omit [DecidableEq X] [DecidableEq Y] in
@[simp] theorem revealFirstLaw_weight (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (q : X × Y) :
    (revealFirstLaw μ).weight (r,q) = (revealLaw μ).weight (q,r) := rfl

def revealFallback (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) :
    FiniteDistribution (X × Y) :=
  match r with
  | Sum.inl x => μ.pushforward (fun q => (x,q.2))
  | Sum.inr y => μ.pushforward (fun q => (q.1,y))

def revealProfile (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) :
    FiniteDistribution (X × Y) :=
  gameConditionalKernel (revealFirstLaw μ) (revealFallback μ r) r

theorem revealProfile_inl_support (μ : FiniteDistribution (X × Y))
    (x : X) (q : X × Y) (h : q.1 ≠ x) :
    (revealProfile μ (Sum.inl x)).weight q = 0 := by
  classical
  rcases q with ⟨x',y⟩
  dsimp at h
  simp only [revealProfile, gameConditionalKernel, toGameLaw, conditionalKernel]
  split
  · simp [revealFallback, FiniteDistribution.pushforward, Fintype.sum_prod_type,
      Prod.mk.injEq, Ne.symm h]
  · simp [revealLaw_weight, Ne.symm h]

theorem revealProfile_inr_support (μ : FiniteDistribution (X × Y))
    (y : Y) (q : X × Y) (h : q.2 ≠ y) :
    (revealProfile μ (Sum.inr y)).weight q = 0 := by
  classical
  rcases q with ⟨x,y'⟩
  dsimp at h
  simp only [revealProfile, gameConditionalKernel, toGameLaw, conditionalKernel]
  split
  · simp [revealFallback, FiniteDistribution.pushforward, Fintype.sum_prod_type,
      Prod.mk.injEq, Ne.symm h]
  · simp [revealLaw_weight, Ne.symm h]

def revealInputLaw (μ : FiniteDistribution (X × Y)) : FiniteDistribution (X ⊕ Y) :=
  (revealLaw μ).pushforward Prod.snd

theorem revealInputLaw_weight (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) :
    (revealInputLaw μ).weight r = firstMarginal (revealFirstLaw μ).weight r := by
  classical
  cases r <;>
    simp [revealInputLaw, FiniteDistribution.pushforward, firstMarginal, Fintype.sum_prod_type]

theorem reveal_profile_recombination (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (q : X × Y) :
    (revealInputLaw μ).weight r * (revealProfile μ r).weight q =
      (revealLaw μ).weight (q,r) := by
  rw [revealInputLaw_weight]
  exact gameConditionalKernel_recombine (revealFirstLaw μ) (revealFallback μ r) r q

theorem revealInputLaw_inl (μ : FiniteDistribution (X × Y)) (x : X) :
    (revealInputLaw μ).weight (Sum.inl x) = (∑ y, μ.weight (x,y)) / 2 := by
  classical
  rw [revealInputLaw_weight]
  simp [firstMarginal, Fintype.sum_prod_type, revealLaw_weight, div_eq_mul_inv]
  rw [Finset.sum_comm]
  simp [← Finset.sum_mul]

theorem revealProfile_inl_diagonal (μ : FiniteDistribution (X × Y)) (x : X) (y : Y) :
    (revealProfile μ (Sum.inl x)).weight (x,y) =
      conditionalKernel μ.weight (μ.pushforward Prod.snd).weight x y := by
  classical
  have hm : firstMarginal (revealFirstLaw μ).weight (Sum.inl x) =
      firstMarginal μ.weight x / 2 := by
    rw [← revealInputLaw_weight, revealInputLaw_inl]
    rfl
  have hf : (revealFallback μ (Sum.inl x)).weight (x,y) =
      (μ.pushforward Prod.snd).weight y := by
    simp [revealFallback, FiniteDistribution.pushforward, Prod.mk.injEq]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : q.2 = y <;> simp [hq]
  simp only [revealProfile, gameConditionalKernel, toGameLaw, conditionalKernel, hm]
  by_cases h : firstMarginal μ.weight x = 0
  · simpa [h] using hf
  · have hh : firstMarginal μ.weight x / 2 ≠ 0 := div_ne_zero h (by norm_num)
    simp only [ite_eq_right h, ite_eq_right hh, revealFirstLaw_weight, revealLaw_weight,
      ite_true, Sum.inl_ne_inr, ite_false, add_zero]
    field_simp

theorem revealLaw_sum_left (μ : FiniteDistribution (X × Y)) (q : X × Y) :
    (∑ x, (revealLaw μ).weight (q, Sum.inl x)) = μ.weight q / 2 := by
  classical
  simp [revealLaw_weight]

theorem revealLaw_sum_right (μ : FiniteDistribution (X × Y)) (q : X × Y) :
    (∑ y, (revealLaw μ).weight (q, Sum.inr y)) = μ.weight q / 2 := by
  classical
  simp [revealLaw_weight]

theorem reveal_product_factorization {ι : Type*} [Fintype ι]
    (μ : FiniteDistribution (X × Y)) (r : ι → X ⊕ Y) (q : ι → X × Y) :
    (∏ i, (revealInputLaw μ).weight (r i)) *
      (∏ i, (revealProfile μ (r i)).weight (q i)) =
        ∏ i, (revealLaw μ).weight (q i,r i) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact reveal_profile_recombination μ (r i) (q i)

theorem reveal_product_forget {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : FiniteDistribution (X × Y)) (q : ι → X × Y) :
    (∑ r : ι → X ⊕ Y,
      (∏ i, (revealInputLaw μ).weight (r i)) *
        (∏ i, (revealProfile μ (r i)).weight (q i))) =
      ∏ i, μ.weight (q i) := by
  classical
  simp_rw [reveal_product_factorization]
  calc
    _ = ∏ i, ∑ r : X ⊕ Y, (revealLaw μ).weight (q i,r) :=
      (Fintype.prod_sum (fun (i : ι) (r : X ⊕ Y) => (revealLaw μ).weight (q i,r))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Fintype.sum_sum_type, revealLaw_sum_left, revealLaw_sum_right]
      ring

theorem reveal_product_expectation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : FiniteDistribution (X × Y)) (f : (ι → X × Y) → ℝ) :
    (∑ r : ι → X ⊕ Y,
      (∏ i, (revealInputLaw μ).weight (r i)) *
        ∑ q : ι → X × Y, (∏ i, (revealProfile μ (r i)).weight (q i)) * f q) =
      ∑ q : ι → X × Y, (∏ i, μ.weight (q i)) * f q := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  rw [reveal_product_forget]

end
end UniqueGames.Foundations.Repetition

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_MaskedVariation
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                               
section

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]

def maskedModel (μ : Games.FiniteDistribution (X × Y)) (p : S × (X × Y) → ℝ) :
    (S × (X ⊕ Y)) × (X × Y) → ℝ := fun z =>
  Information.firstMarginal (maskedJoint p) z.1 * (revealProfile μ z.1.2).weight z.2

def leftRevealModel (μ : Games.FiniteDistribution (X × Y)) (p : S × (X × Y) → ℝ) :
    S × (X × Y) → ℝ := fun z =>
  (∑ y, p (z.1, (z.2.1, y))) * (revealProfile μ (Sum.inl z.2.1)).weight z.2

def rightRevealModel (μ : Games.FiniteDistribution (X × Y)) (p : S × (X × Y) → ℝ) :
    S × (X × Y) → ℝ := fun z =>
  (∑ x, p (z.1, (x, z.2.2))) * (revealProfile μ (Sum.inr z.2.2)).weight z.2

omit [Fintype S] in
theorem abs_masked_inl (μ : Games.FiniteDistribution (X × Y))
    (p : S × (X × Y) → ℝ) (s : S) (u x : X) (y : Y) :
    |maskedJoint p ((s, Sum.inl u), (x, y)) - maskedModel μ p ((s, Sum.inl u), (x, y))| =
      if x = u then |p (s, (x, y)) - leftRevealModel μ p (s, (x, y))| / 2 else 0 := by
  by_cases hx : x = u
  · subst x
    simp only [maskedModel, maskedJoint_firstMarginal_inl]
    simpa [maskedJoint, leftRevealModel] using
      abs_half_sub_half_mul (p (s, (u, y))) (∑ v, p (s, (u, v)))
        ((revealProfile μ (Sum.inl u)).weight (u, y))
  · have hs := revealProfile_inl_support μ u (x, y) hx
    simp [maskedJoint, maskedModel, hs, hx, Ne.symm hx]

omit [Fintype S] in
theorem abs_masked_inr (μ : Games.FiniteDistribution (X × Y))
    (p : S × (X × Y) → ℝ) (s : S) (v : Y) (x : X) (y : Y) :
    |maskedJoint p ((s, Sum.inr v), (x, y)) - maskedModel μ p ((s, Sum.inr v), (x, y))| =
      if y = v then |p (s, (x, y)) - rightRevealModel μ p (s, (x, y))| / 2 else 0 := by
  by_cases hy : y = v
  · subst y
    simp only [maskedModel, maskedJoint_firstMarginal_inr]
    simpa [maskedJoint, rightRevealModel] using
      abs_half_sub_half_mul (p (s, (x, v))) (∑ u, p (s, (u, v)))
        ((revealProfile μ (Sum.inr v)).weight (x, v))
  · have hs := revealProfile_inr_support μ v (x, y) hy
    simp [maskedJoint, maskedModel, hs, hy, Ne.symm hy]

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_PartialReveal
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                             
section

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
noncomputable section
variable {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def partialRevealWeight (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (u : I → X × Y) : ℝ :=
  μ.weight (u j) * ∏ i : {i : I // i ≠ j}, (revealLaw μ).weight (u i.1,rest i)

theorem product_reveal_at (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (r : X ⊕ Y) (rest : {i : I // i ≠ j} → X ⊕ Y) (u : I → X × Y) :
    (∏ i, (revealLaw μ).weight (u i,mergeAt j r rest i)) =
      (if r = Sum.inl (u j).1 then partialRevealWeight μ j rest u / 2 else 0) +
      (if r = Sum.inr (u j).2 then partialRevealWeight μ j rest u / 2 else 0) := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ j]
  simp only [mergeAt_self, mergeAt_other, revealLaw_weight]
  by_cases hl : r = Sum.inl (u j).1 <;> by_cases hr : r = Sum.inr (u j).2 <;>
    simp [hl, hr, partialRevealWeight, revealLaw_weight] <;> ring

def partialRevealMarginal (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    (T × ({i : I // i ≠ j} → X ⊕ Y)) × (X × Y) → ℝ := by
  classical
  exact fun z => ∑ u, if u j = z.2 then
    partialRevealWeight μ j z.1.2 u * likelihood z.1.1 u else 0

def fullRevealMarginal (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    (T × (I → X ⊕ Y)) × (X × Y) → ℝ := by
  classical
  exact fun z => ∑ u, if u j = z.2 then
    (∏ i, (revealLaw μ).weight (u i,z.1.2 i)) * likelihood z.1.1 u else 0

omit [Fintype T] in

theorem fullRevealMarginal_merge (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) (t : T)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (r : X ⊕ Y) (q : X × Y) :
    fullRevealMarginal μ j likelihood ((t,mergeAt j r rest),q) =
      maskedJoint (partialRevealMarginal μ j likelihood) (((t,rest),r),q) := by
  classical
  unfold fullRevealMarginal
  simp_rw [product_reveal_at]
  have hpoint (u : I → X × Y) :
      (if u j = q then
        ((if r = Sum.inl (u j).1 then partialRevealWeight μ j rest u / 2 else 0) +
         (if r = Sum.inr (u j).2 then partialRevealWeight μ j rest u / 2 else 0)) *
          likelihood t u else 0) =
      (if r = Sum.inl q.1 then
        (if u j = q then partialRevealWeight μ j rest u * likelihood t u else 0) / 2 else 0) +
      (if r = Sum.inr q.2 then
        (if u j = q then partialRevealWeight μ j rest u * likelihood t u else 0) / 2 else 0) := by
    by_cases hu : u j = q
    · rw [hu]
      by_cases hl : r = Sum.inl q.1 <;> by_cases hr : r = Sum.inr q.2 <;>
        simp [hl, hr] <;> ring
    · simp [hu]
  simp_rw [hpoint]
  simp [maskedJoint, partialRevealMarginal, Finset.sum_add_distrib,
    Finset.sum_ite_irrel, div_eq_mul_inv, Finset.sum_mul]

def fullRevealModel (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    (T × (I → X ⊕ Y)) × (X × Y) → ℝ := fun z =>
  Information.firstMarginal (fullRevealMarginal μ j likelihood) z.1 *
    (revealProfile μ (z.1.2 j)).weight z.2

omit [Fintype T] in
theorem fullRevealModel_merge (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) (t : T)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (r : X ⊕ Y) (q : X × Y) :
    fullRevealModel μ j likelihood ((t,mergeAt j r rest),q) =
      maskedModel μ (partialRevealMarginal μ j likelihood) (((t,rest),r),q) := by
  simp only [fullRevealModel, Information.firstMarginal, fullRevealMarginal_merge,
    mergeAt_self, maskedModel]

theorem fullReveal_totalVariation (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    Information.totalVariation (fullRevealMarginal μ j likelihood) (fullRevealModel μ j likelihood) =
      Information.totalVariation (maskedJoint (partialRevealMarginal μ j likelihood))
        (maskedModel μ (partialRevealMarginal μ j likelihood)) := by
  calc
    _ = Information.totalVariation
        (fun z => fullRevealMarginal μ j likelihood ((revealSplitEquiv (T := T) j).symm z))
        (fun z => fullRevealModel μ j likelihood ((revealSplitEquiv (T := T) j).symm z)) :=
      (totalVariation_comp_equiv (revealSplitEquiv (T := T) j).symm _ _).symm
    _ = _ := by
      congr 1 <;> funext z
      · exact fullRevealMarginal_merge μ j likelihood z.1.1.1 z.1.1.2 z.1.2 z.2
      · exact fullRevealModel_merge μ j likelihood z.1.1.1 z.1.1.2 z.1.2 z.2

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_SelectedInformation
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Hastad.SourceGame.baseGame_accepts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                   
section

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

theorem iid_coordinate_split {Ω : Type*} [Fintype Ω] {n : Nat}
    (μ : FiniteDistribution Ω) (selected : Finset (Fin n)) :
    (μ.iid n).transport (coordinateSplitEquiv selected) =
      (FiniteDistribution.table (fun _ : selected => μ)).product
        (FiniteDistribution.table (fun _ : {i : Fin n // i ∉ selected} => μ)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change (∏ i, μ.weight (mergeCoordinates selected x.1 x.2 i)) =
    (∏ i : selected, μ.weight (x.1 i)) *
      ∏ i : {i : Fin n // i ∉ selected}, μ.weight (x.2 i)
  have h := Fintype.prod_subtype_mul_prod_subtype (fun i : Fin n => i ∈ selected)
    (fun i => μ.weight (mergeCoordinates selected x.1 x.2 i))
  have hi : Subtype.fintype (fun i : Fin n => i ∈ selected) =
      Finset.Subtype.fintype selected := Subsingleton.elim _ _
  rw [hi] at h
  calc
    _ = (∏ i : {i : Fin n // i ∈ selected},
        μ.weight (mergeCoordinates selected x.1 x.2 i.1)) *
        ∏ i : {i : Fin n // i ∉ selected},
          μ.weight (mergeCoordinates selected x.1 x.2 i.1) := h.symm
    _ = _ := by
      congr 1 <;> apply Finset.prod_congr rfl <;> intro i _ <;>
        simp [mergeCoordinates, i.property]

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]
  {n : Nat}

def selectedAnswerLabel
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (questions : (Fin n → Q₁) × (Fin n → Q₂)) :
    SelectedLabels (A₁ := A₁) (A₂ := A₂) selected :=
  (fun i => strategy.1 questions.1 i.1, fun i => strategy.2 questions.2 i.1)

def selectedLikelihood (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (fixed : selected → Q₁ × Q₂)
    (label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) : ℝ := by
  classical
  let questions := selectedQuestionTuple selected fixed remaining
  exact if selectedAnswerLabel strategy selected questions = label then
    (if G.selectedWins strategy selected questions then 1 else 0) else 0

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedLikelihood_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (fixed : selected → Q₁ × Q₂)
    (label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    0 ≤ selectedLikelihood G strategy selected fixed label remaining := by
  classical
  dsimp only [selectedLikelihood]
  split_ifs <;> norm_num

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedLikelihood_sum (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (fixed : selected → Q₁ × Q₂)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    (∑ label, selectedLikelihood G strategy selected fixed label remaining) =
      if G.selectedWins strategy selected (selectedQuestionTuple selected fixed remaining)
      then 1 else 0 := by
  classical
  simp [selectedLikelihood]

def selectedSplitLaw (G : Game Q₁ Q₂ A₁ A₂) (selected : Finset (Fin n)) :
    FiniteDistribution ((selected → Q₁ × Q₂) ×
      ({i : Fin n // i ∉ selected} → Q₁ × Q₂)) :=
  (FiniteDistribution.table (fun _ : selected => G.questions)).product
    (FiniteDistribution.table (fun _ : {i : Fin n // i ∉ selected} => G.questions))

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedSplit_probability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) :
    (selectedSplitLaw G selected).probability
      (fun q => G.selectedWins strategy selected (selectedQuestionTuple selected q.1 q.2)) =
        G.selectedSuccess strategy selected := by
  rw [selectedSplitLaw, ← iid_coordinate_split, FiniteDistribution.probability_transport]
  change (G.questions.iid n).probability _ =
    ((G.questions.iid n).transport (Game.tupleQuestionEquiv n)).probability _
  rw [FiniteDistribution.probability_transport]
  apply congrArg (G.questions.iid n).probability
  funext q
  congr 1
  apply Prod.ext <;> funext i <;>
    simp [selectedQuestionTuple, coordinateSplitEquiv, mergeCoordinates, Game.tupleQuestionEquiv]

def selectedInputLaw (G : Game Q₁ Q₂ A₁ A₂) (selected : Finset (Fin n)) :
    FiniteDistribution (SelectedInput Q₁ Q₂ selected) :=
  (FiniteDistribution.table (fun _ : selected => G.questions)).product
    (FiniteDistribution.table (fun _ : {i : Fin n // i ∉ selected} => revealInputLaw G.questions))

def selectedInputProfile (G : Game Q₁ Q₂ A₁ A₂) (selected : Finset (Fin n))
    (t : SelectedInput Q₁ Q₂ selected) (i : {i : Fin n // i ∉ selected}) :
    FiniteDistribution (Q₁ × Q₂) := revealProfile G.questions (t.2 i)

def selectedSideMass (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (tv : SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ :=
  ∑ u, independentProduct (fun i => (selectedInputProfile G selected tv.1 i).weight) u *
    selectedLikelihood G strategy selected tv.1.1 tv.2 u

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedSideMass_sum (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (t : SelectedInput Q₁ Q₂ selected) :
    (∑ v, selectedSideMass G strategy selected (t,v)) =
      ∑ u, independentProduct (fun i => (selectedInputProfile G selected t i).weight) u *
        (if G.selectedWins strategy selected (selectedQuestionTuple selected t.1 u)
        then 1 else 0) := by
  classical
  simp only [selectedSideMass]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, selectedLikelihood_sum]

theorem selectedSideMass_total (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) :
    (∑ tv, (selectedInputLaw G selected).weight tv.1 *
      selectedSideMass G strategy selected tv) = G.selectedSuccess strategy selected := by
  classical
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, selectedSideMass_sum]
  rw [Fintype.sum_prod_type]
  simp only [selectedInputLaw, FiniteDistribution.product, FiniteDistribution.table,
    selectedInputProfile, independentProduct]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  have hforget (fixed : selected → Q₁ × Q₂) :=
    reveal_product_expectation G.questions
      (fun u : {i : Fin n // i ∉ selected} → Q₁ × Q₂ =>
        if G.selectedWins strategy selected (selectedQuestionTuple selected fixed u)
        then (1 : ℝ) else 0)
  simp_rw [hforget]
  have h := selectedSplit_probability G strategy selected
  simpa [selectedSplitLaw, FiniteDistribution.probability, FiniteDistribution.product,
    FiniteDistribution.table, Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_assoc] using h

def selectedSideWeight (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (tv : SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ :=
  (selectedInputLaw G selected).weight tv.1 * selectedSideMass G strategy selected tv /
    G.selectedSuccess strategy selected

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_SelectedJoint
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                             
section

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedJointWeight (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (z : (SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
      ({i : Fin n // i ∉ selected} → Q₁ × Q₂)) : ℝ :=
  (selectedInputLaw G selected).weight z.1.1 *
    independentProduct (fun i => (selectedInputProfile G selected z.1.1 i).weight) z.2 *
      selectedLikelihood G strategy selected z.1.1.1 z.1.2 z.2 /
        G.selectedSuccess strategy selected

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedJointWeight_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (z) : 0 ≤ selectedJointWeight G strategy selected z := by
  apply div_nonneg
  · exact mul_nonneg
      (mul_nonneg ((selectedInputLaw G selected).nonnegative _)
        ((independentProduct_isProbability _
          (fun i => gameLaw_isProbability (selectedInputProfile G selected z.1.1 i))).1 z.2))
      (selectedLikelihood_nonnegative G strategy selected z.1.1.1 z.1.2 z.2)
  · exact G.selectedSuccess_nonnegative strategy selected

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedJointWeight_firstMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (tv) :
    firstMarginal (selectedJointWeight G strategy selected) tv =
      selectedSideWeight G strategy selected tv := by
  simp only [firstMarginal, selectedJointWeight, selectedSideWeight, selectedSideMass,
    div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem selectedJointWeight_isProbability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    IsProbability (selectedJointWeight G strategy selected) := by
  constructor
  · exact selectedJointWeight_nonnegative G strategy selected
  · rw [Fintype.sum_prod_type]
    change (∑ tv, firstMarginal (selectedJointWeight G strategy selected) tv) = 1
    simp_rw [selectedJointWeight_firstMarginal, selectedSideWeight, div_eq_mul_inv]
    rw [← Finset.sum_mul, selectedSideMass_total, mul_inv_cancel₀ positive.ne']

def selectedJointLaw (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :=
  toGameLaw (selectedJointWeight G strategy selected)
    (selectedJointWeight_isProbability G strategy selected positive)

theorem selectedJointWeight_factorization (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (tv) (u) :
    selectedJointWeight G strategy selected (tv,u) =
      (∏ i : selected, G.questions.weight (tv.1.1 i)) *
        (∏ i : {i : Fin n // i ∉ selected}, (revealLaw G.questions).weight (u i,tv.1.2 i)) *
          selectedLikelihood G strategy selected tv.1.1 tv.2 u /
            G.selectedSuccess strategy selected := by
  unfold selectedJointWeight
  simp only [selectedInputLaw, FiniteDistribution.product, FiniteDistribution.table,
    independentProduct, selectedInputProfile]
  rw [mul_assoc (∏ i : selected, G.questions.weight (tv.1.1 i)), reveal_product_factorization]

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_SelectedMarginal
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Hastad.SourceGame.baseGame_accepts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                
section

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedRawMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) :
    (SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
      (Q₁ × Q₂) → ℝ := by
  classical
  exact fun z => ∑ u, if u j = z.2 then selectedJointWeight G strategy selected (z.1,u) else 0

theorem selectedRawMarginal_firstMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) (tv) :
    firstMarginal (selectedRawMarginal G strategy selected j) tv =
      selectedSideWeight G strategy selected tv := by
  classical
  simp only [firstMarginal, selectedRawMarginal]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact selectedJointWeight_firstMarginal G strategy selected tv

theorem selectedRawMarginal_isProbability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    IsProbability (selectedRawMarginal G strategy selected j) := by
  classical
  constructor
  · intro z
    apply Finset.sum_nonneg
    intro u _
    split
    · exact selectedJointWeight_nonnegative G strategy selected (z.1,u)
    · exact le_rfl
  · rw [Fintype.sum_prod_type]
    change (∑ tv, firstMarginal (selectedRawMarginal G strategy selected j) tv) = 1
    simp_rw [selectedRawMarginal_firstMarginal, selectedSideWeight, div_eq_mul_inv]
    rw [← Finset.sum_mul, selectedSideMass_total, mul_inv_cancel₀ positive.ne']

def selectedOutsideLikelihood (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (t : (selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)
    (u : {i : Fin n // i ∉ selected} → Q₁ × Q₂) : ℝ :=
  (∏ i : selected, G.questions.weight (t.1 i)) *
    selectedLikelihood G strategy selected t.1 t.2 u / G.selectedSuccess strategy selected

theorem selectedRawMarginal_fullReveal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) (z) :
    selectedRawMarginal G strategy selected j
        ((selectedObservationEquiv (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected).symm z) =
      fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected) z := by
  classical
  change selectedRawMarginal G strategy selected j
    (((z.1.1.1,z.1.2),z.1.1.2),z.2) = _
  simp only [selectedRawMarginal, fullRevealMarginal]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : u j = z.2
  · simp only [ite_eq_left hu, selectedJointWeight_factorization, selectedOutsideLikelihood]
    ring
  · simp [hu]

def selectedInformationRadius (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) : ℝ :=
  Real.sqrt ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
    (Real.log (Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ) +
      Real.log (1 / G.selectedSuccess strategy selected)))

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_AlphabetBudget
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Hastad.SourceGame.baseGame_accepts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                              
section

namespace UniqueGames.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : ℕ}

omit [DecidableEq Q₁] [DecidableEq Q₂] in

theorem selectedInformationRadius_le [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (ell : ℝ)
    (hell : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    selectedInformationRadius G strategy selected ≤
      Real.sqrt (((n : ℝ) - selected.card) *
        ((selected.card : ℝ) * ell + logTwo (1 / G.selectedSuccess strategy selected))) := by
  have hprob : 1 ≤ 1 / G.selectedSuccess strategy selected := by
    apply (le_div_iff₀ positive).2
    simpa using G.selectedSuccess_le_one strategy selected
  have hbudget := add_le_add (selectedLabels_log_le (A₁ := A₁) (A₂ := A₂) selected ell hell)
    (log_le_logTwo hprob)
  unfold selectedInformationRadius
  rw [← unusedCoordinates_card_real selected]
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg _)

omit [DecidableEq Q₁] [DecidableEq Q₂] in

theorem exists_coordinate_le_information_budget [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (ell : ℝ)
    (hell : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell)
    (hselected : selected.card < n)
    (error : {i : Fin n // i ∉ selected} → ℝ)
    (hsum : (∑ j, error j) ≤ 15 * selectedInformationRadius G strategy selected) :
    ∃ j : {i : Fin n // i ∉ selected}, error j ≤ 15 * Real.sqrt
      (((selected.card : ℝ) * ell + logTwo (1 / G.selectedSuccess strategy selected)) /
        ((n : ℝ) - selected.card)) := by
  classical
  have hcard : 0 < Fintype.card {i : Fin n // i ∉ selected} := by
    rw [unusedCoordinates_card]
    exact Nat.sub_pos_of_lt hselected
  let : Nonempty {i : Fin n // i ∉ selected} := Fintype.card_pos_iff.mp hcard
  have hden : 0 < (n : ℝ) - selected.card := by
    rw [← unusedCoordinates_card_real selected]
    exact_mod_cast hcard
  have htotal := hsum.trans (mul_le_mul_of_nonneg_left
    (selectedInformationRadius_le G strategy selected positive ell hell) (by norm_num : (0 : ℝ) ≤ 15))
  rw [sqrt_budget_factor _ _ hden] at htotal
  have havg : (∑ j, error j) ≤ ∑ _j : {i : Fin n // i ∉ selected},
      15 * Real.sqrt
        (((selected.card : ℝ) * ell + logTwo (1 / G.selectedSuccess strategy selected)) /
          ((n : ℝ) - selected.card)) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      unusedCoordinates_card_real, mul_assoc, mul_left_comm] using htotal
  obtain ⟨j, _, hj⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty havg
  exact ⟨j, hj⟩

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_SharedSampling
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                              
section

namespace UniqueGames.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

universe u

def traceSeedLaw {σ : Type*} [Fintype σ] (μ : FiniteDistribution σ) :
    (n : Nat) → FiniteDistribution (TraceSeed σ n)
  | 0 => { weight := fun _ => 1, nonnegative := by intro; norm_num,
           normalized := by simp }
  | n + 1 => μ.product (traceSeedLaw μ n)

theorem traceSeedLaw_expectation {σ : Type*} [Fintype σ]
    (μ : FiniteDistribution σ) (n : Nat) (f : List σ → ℝ) :
    (traceSeedLaw μ n).expectation (fun seed => f (traceList n seed)) =
      CorrelatedSampling.traceAverage μ.weight n f := by
  induction n generalizing f with
  | zero => simp [traceSeedLaw, traceList, FiniteDistribution.expectation,
      CorrelatedSampling.traceAverage]
  | succ n ih =>
      change (μ.product (traceSeedLaw μ n)).expectation
        (fun seed => f (seed.1 :: traceList n seed.2)) = _
      rw [FiniteDistribution.expectation_product]
      simp only [CorrelatedSampling.traceAverage, FiniteDistribution.expectation]
      apply Finset.sum_congr rfl
      intro s _
      congr 1
      exact ih (fun xs => f (s :: xs))

def sharedOutputLaw {X Y S Seed : Type*}
    [Fintype X] [Fintype Y] [Fintype S] [Fintype Seed] [DecidableEq S]
    (μ : FiniteDistribution (X × Y)) (seedLaw : FiniteDistribution Seed)
    (left : Seed → X → S) (right : Seed → Y → S) :
    FiniteDistribution ((X × Y) × S × S) :=
  (μ.product seedLaw).pushforward
    (fun z => (z.1, left z.2 z.1.1, right z.2 z.1.2))

theorem sharedOutputLaw_weight {X Y S Seed : Type*}
    [Fintype X] [Fintype Y] [Fintype S] [Fintype Seed] [DecidableEq S]
    (μ : FiniteDistribution (X × Y)) (seedLaw : FiniteDistribution Seed)
    (left : Seed → X → S) (right : Seed → Y → S) (x : X) (y : Y) (a b : S) :
    (sharedOutputLaw μ seedLaw left right).weight ((x,y),a,b) =
      μ.weight (x,y) * seedLaw.expectation
        (fun seed => if left seed x = a ∧ right seed y = b then 1 else 0) := by
  classical
  simp only [sharedOutputLaw, FiniteDistribution.pushforward,
    FiniteDistribution.product, Fintype.sum_prod_type, Prod.mk.injEq]
  simp only [and_assoc, ite_and]
  simp [FiniteDistribution.expectation, Finset.mul_sum, mul_ite]

section Rectangle

open CorrelatedSampling

variable {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S]
  [Nonempty S] [DecidableEq S]

def samplerLocal (thresholds : List ℝ) (profile : X → FiniteDistribution S)
    (fallback : S) (n : Nat) (seed : TraceSeed (RectangleSeed thresholds S) n)
    (x : X) : S :=
  localSample (rectangleAccept thresholds (profile x).weight) Prod.fst fallback
    (traceList n seed)

def samplerOutputLaw (thresholds : List ℝ) (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (n : Nat) : FiniteDistribution ((X × Y) × S × S) :=
  sharedOutputLaw μ (traceSeedLaw (rectangleDistribution thresholds) n)
    (samplerLocal thresholds L fallback n) (samplerLocal thresholds R fallback n)

omit [Nonempty S] [DecidableEq S] in
theorem probability_weight_le_one (μ : FiniteDistribution S) (s : S) : μ.weight s ≤ 1 := by
  calc
    μ.weight s ≤ ∑ t, μ.weight t :=
      Finset.single_le_sum (fun t _ => μ.nonnegative t) (Finset.mem_univ s)
    _ = 1 := μ.normalized

theorem samplerOutputLaw_diagonal (thresholds : List ℝ)
    (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (hL : ∀ x s, (L x).weight s ∈ thresholds)
    (hR : ∀ y s, (R y).weight s ∈ thresholds)
    (fallback : S) (n : Nat) (x : X) (y : Y) (a : S) :
    μ.weight (x,y) * min ((L x).weight a) ((R y).weight a) /
        (1 + Information.totalVariation (L x).weight (R y).weight) *
        (1 - eventMass (rectangleWeight thresholds)
          (fun s => !(rectangleAccept thresholds (L x).weight s ||
            rectangleAccept thresholds (R y).weight s)) ^ n) ≤
      (samplerOutputLaw thresholds μ L R fallback n).weight ((x,y),a,a) := by
  have h := rectangle_label_diagonal_bound thresholds (L x).weight (R y).weight
    fallback a (hL x) (hR y) (L x).nonnegative (R y).nonnegative
    (probability_weight_le_one (L x)) (probability_weight_le_one (R y))
    (L x).normalized (R y).normalized n
  rw [samplerOutputLaw, sharedOutputLaw_weight]
  have he : (traceSeedLaw (rectangleDistribution (α := S) thresholds) n).expectation
      (fun seed => if samplerLocal thresholds L fallback n seed x = a ∧
        samplerLocal thresholds R fallback n seed y = a then 1 else 0) =
      traceAverage (rectangleWeight thresholds) n
        (localDiagonal (rectangleAccept thresholds (L x).weight)
          (rectangleAccept thresholds (R y).weight) Prod.fst fallback a) := by
    exact traceSeedLaw_expectation (rectangleDistribution (α := S) thresholds) n
      (localDiagonal (rectangleAccept thresholds (L x).weight)
        (rectangleAccept thresholds (R y).weight) Prod.fst fallback a)
  rw [he]
  simp only [Information.totalVariation, CorrelatedSampling.totalVariation] at h ⊢
  simpa only [mul_div_assoc, mul_assoc] using
    mul_le_mul_of_nonneg_left h (μ.nonnegative (x,y))

theorem samplerOutputLaw_uniform_diagonal
    (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (n : Nat) (x : X) (y : Y) (a : S) :
    μ.weight (x,y) * min ((L x).weight a) ((R y).weight a) /
        (1 + Information.totalVariation (L x).weight (R y).weight) *
        (1 - uniformRejectionRate S ^ n) ≤
      (samplerOutputLaw (sharedProfileThresholds L R) μ L R fallback n).weight ((x,y),a,a) := by
  have hp := pow_le_pow_left₀ (sharedProfileReject_nonnegative L R x y)
    (sharedProfile_reject_le_rate L R x y) n
  have hco : 0 ≤ μ.weight (x,y) * min ((L x).weight a) ((R y).weight a) /
      (1 + Information.totalVariation (L x).weight (R y).weight) :=
    div_nonneg (mul_nonneg (μ.nonnegative (x,y))
      (le_min ((L x).nonnegative a) ((R y).nonnegative a)))
      (by linarith [Information.totalVariation_nonneg (L x).weight (R y).weight])
  have h := samplerOutputLaw_diagonal (sharedProfileThresholds L R) μ L R
    (left_mem_sharedProfileThresholds L R) (right_mem_sharedProfileThresholds L R)
    fallback n x y a
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left hp 1) hco).trans h

theorem samplerOutputLaw_totalVariation
    (p : FiniteDistribution ((X × Y) × S)) (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (n : Nat) :
    Information.totalVariation
      (samplerOutputLaw (sharedProfileThresholds L R) μ L R fallback n).weight
      (diagonalWeights p.weight) ≤
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (L z.1.1).weight z.2) +
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (R z.1.2).weight z.2) +
      uniformRejectionRate S ^ n := by
  apply diagonal_sampler_totalVariation_le p.weight μ.weight
    (fun xy => (L xy.1).weight) (fun xy => (R xy.2).weight) _
    (Information.gameLaw_isProbability p) (Information.gameLaw_isProbability μ)
    (fun xy => Information.gameLaw_isProbability (L xy.1))
    (fun xy => Information.gameLaw_isProbability (R xy.2))
    (Information.gameLaw_isProbability _)
    (pow_nonneg (uniformRejectionRate_nonnegative S) n)
  · exact pow_le_one₀ (uniformRejectionRate_nonnegative S)
      (uniformRejectionRate_lt_one S).le
  · intro xy a
    exact samplerOutputLaw_uniform_diagonal μ L R fallback n xy.1 xy.2 a

theorem samplerOutputLaw_arbitrarily_close
    (p : FiniteDistribution ((X × Y) × S)) (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (η : ℝ) (hη : 0 < η) : ∃ n : Nat,
    Information.totalVariation
      (samplerOutputLaw (sharedProfileThresholds L R) μ L R fallback n).weight
      (diagonalWeights p.weight) ≤
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (L z.1.1).weight z.2) +
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (R z.1.2).weight z.2) + η := by
  obtain ⟨n,hn⟩ := exists_uniformRejectionRate_pow_lt S η hη
  exact ⟨n, (samplerOutputLaw_totalVariation p μ L R fallback n).trans
    (by linarith)⟩

end Rectangle

end
end UniqueGames.Foundations.Repetition

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_CompletedSampling
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                 
section

namespace UniqueGames.Foundations.Repetition.CompletedSampling

open scoped BigOperators
open Games

noncomputable section

section DistributionIdentities

variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

theorem mixture_pushforward_base (μ : FiniteDistribution A) (f : A → B)
    (K : B → FiniteDistribution C) :
    (μ.pushforward f).mixture K = μ.mixture (fun a => K (f a)) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro «c»
  exact FiniteDistribution.expectation_pushforward μ f (fun b => (K b).weight «c»)

theorem product_pushforward_eq_mixture_right (μ : FiniteDistribution A)
    (ν : FiniteDistribution B) (f : A × B → C) :
    (μ.product ν).pushforward f =
      ν.mixture (fun b => μ.pushforward (fun a => f (a, b))) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro «c»
  simp only [FiniteDistribution.pushforward, FiniteDistribution.product,
    FiniteDistribution.mixture, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : f (a, b) = «c» <;> simp [h, mul_comm]

theorem product_product_pushforward_eq_mixture (μ : FiniteDistribution A)
    (ν : FiniteDistribution B) (κ : FiniteDistribution C) (f : A → B → C → D) :
    (μ.product (ν.product κ)).pushforward (fun z => f z.1 z.2.1 z.2.2) =
      (μ.product ν).mixture
        (fun z => κ.pushforward (fun «c» => f z.1 z.2 «c»)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro d
  simp only [FiniteDistribution.pushforward, FiniteDistribution.product,
    FiniteDistribution.mixture, Fintype.sum_prod_type]
  simp only [Finset.mul_sum, mul_ite, mul_zero, mul_assoc]

theorem mixture_totalVariation_le (μ ν : FiniteDistribution A)
    (K : A → FiniteDistribution B) :
    (μ.mixture K).totalVariation (ν.mixture K) ≤ μ.totalVariation ν := by
  simpa only [FiniteDistribution.totalVariation, FiniteDistribution.mixture,
    Information.totalVariation, kernelPushforward] using
      totalVariation_kernelPushforward_le μ.weight ν.weight
        (fun a => (K a).weight) (fun a => Information.gameLaw_isProbability (K a))

end DistributionIdentities

section Diagonal

variable {Z S : Type*} [Fintype Z] [Fintype S]

def diagonalLaw (σ : FiniteDistribution (Z × S)) : FiniteDistribution (Z × S × S) :=
  Information.toGameLaw (diagonalWeights σ.weight)
    (diagonalWeights_isProbability _ (Information.gameLaw_isProbability σ))

theorem diagonalLaw_eq_pushforward (σ : FiniteDistribution (Z × S)) :
    diagonalLaw σ = σ.pushforward (fun z => (z.1, z.2, z.2)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  rintro ⟨z, a, b⟩
  change diagonalWeights σ.weight (z, a, b) =
    (σ.pushforward (fun t => (t.1, t.2, t.2))).weight (z, a, b)
  simp only [diagonalWeights, FiniteDistribution.pushforward,
    Fintype.sum_prod_type, Prod.mk.injEq]
  by_cases hab : a = b
  · subst b
    simp [ite_and]
  · simp [hab, ite_and]

theorem diagonalLaw_mixture {T : Type*} [Fintype T]
    (σ : FiniteDistribution (Z × S)) (K : Z × S × S → FiniteDistribution T) :
    (diagonalLaw σ).mixture K = σ.mixture (fun z => K (z.1, z.2, z.2)) := by
  rw [diagonalLaw_eq_pushforward, mixture_pushforward_base]

end Diagonal

section Completion

variable {X Y S Γ U V : Type*}
  [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ] [Fintype U] [Fintype V]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S]

def seedLaw (γ : FiniteDistribution Γ)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    FiniteDistribution (Seed Γ X Y S U V) :=
  γ.product (KernelSampling.seedLaw L R)

def completionKernel (L : X × S → FiniteDistribution U)
    (R : Y × S → FiniteDistribution V) (z : (X × Y) × S × S) :
    FiniteDistribution (U × V) :=
  (L (z.1.1, z.2.1)).product (R (z.1.2, z.2.2))

def outputLaw (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    FiniteDistribution (U × V) :=
  (seedLaw γ L R).mixture (fun seed =>
    μ.pushforward (fun q => (left sL seed q.1, right sR seed q.2)))

theorem outputLaw_eq_product_pushforward
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    outputLaw μ γ sL sR L R =
      (μ.product (seedLaw γ L R)).pushforward
        (fun z => (left sL z.2 z.1.1, right sR z.2 z.1.2)) := by
  exact (product_pushforward_eq_mixture_right μ (seedLaw γ L R)
    (fun z : (X × Y) × Seed Γ X Y S U V =>
      (left sL z.2 z.1.1, right sR z.2 z.1.2))).symm

theorem outputLaw_eq_mixture
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    outputLaw μ γ sL sR L R =
      (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
  calc
    outputLaw μ γ sL sR L R =
        (μ.product γ).mixture (fun z =>
          (KernelSampling.seedLaw L R).pushforward (fun table =>
            (KernelSampling.readLeft table (z.1.1, sL z.2 z.1.1),
             KernelSampling.readRight table (z.1.2, sR z.2 z.1.2)))) := by
      rw [outputLaw_eq_product_pushforward]
      exact product_product_pushforward_eq_mixture μ γ (KernelSampling.seedLaw L R)
        (fun q seed table =>
          (KernelSampling.readLeft table (q.1, sL seed q.1),
           KernelSampling.readRight table (q.2, sR seed q.2)))
    _ = (μ.product γ).mixture (fun z =>
        completionKernel L R (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) := by
      apply congrArg ((μ.product γ).mixture)
      funext z
      exact KernelSampling.read_joint_pushforward L R
        (z.1.1, sL z.2 z.1.1) (z.1.2, sR z.2 z.1.2)
    _ = (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
      exact (mixture_pushforward_base (μ.product γ)
        (fun z => (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) (completionKernel L R)).symm

omit [DecidableEq X] [DecidableEq Y] [DecidableEq S] in
                                                                                 
theorem diagonalLaw_completion_mixture
    (σ : FiniteDistribution ((X × Y) × S))
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    (diagonalLaw σ).mixture (completionKernel L R) =
      σ.mixture (fun z => (L (z.1.1, z.2)).product (R (z.1.2, z.2))) := by
  exact diagonalLaw_mixture σ (completionKernel L R)

theorem outputLaw_totalVariation_le
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V)
    (σ : FiniteDistribution ((X × Y) × S)) :
    (outputLaw μ γ sL sR L R).totalVariation
        (σ.mixture (fun z => (L (z.1.1, z.2)).product (R (z.1.2, z.2)))) ≤
      (sharedOutputLaw μ γ sL sR).totalVariation (diagonalLaw σ) := by
  rw [outputLaw_eq_mixture, ← diagonalLaw_completion_mixture σ L R]
  exact mixture_totalVariation_le _ _ (completionKernel L R)

end Completion

section CoordinateCompletion

variable {I X Y S Γ : Type*}
  [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y] [DecidableEq S]

def coordinateOutputLaw (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y)) :
    FiniteDistribution ((I → X) × (I → Y)) :=
  (seedLaw γ L R).mixture (fun seed => μ.pushforward
    (fun q => (coordinateLeft j sL seed q.1, coordinateRight j sR seed q.2)))

theorem coordinateOutputLaw_eq_mixture
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y))
    (hL : ∀ q xs, (L q).weight xs ≠ 0 → xs j = q.1)
    (hR : ∀ q ys, (R q).weight ys ≠ 0 → ys j = q.1) :
    coordinateOutputLaw μ γ j sL sR L R =
      (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
  calc
    coordinateOutputLaw μ γ j sL sR L R =
        (μ.product (seedLaw γ L R)).pushforward
          (fun z => (coordinateLeft j sL z.2 z.1.1,
            coordinateRight j sR z.2 z.1.2)) := by
      exact (product_pushforward_eq_mixture_right μ (seedLaw γ L R)
        (fun z : (X × Y) × Seed Γ X Y S (I → X) (I → Y) =>
          (coordinateLeft j sL z.2 z.1.1, coordinateRight j sR z.2 z.1.2))).symm
    _ = (μ.product γ).mixture (fun z =>
        (KernelSampling.seedLaw L R).pushforward (fun table =>
          (KernelSampling.completedLeft j table (z.1.1, sL z.2 z.1.1),
           KernelSampling.completedRight j table (z.1.2, sR z.2 z.1.2)))) := by
      exact product_product_pushforward_eq_mixture μ γ (KernelSampling.seedLaw L R)
        (fun q seed table =>
          (KernelSampling.completedLeft j table (q.1, sL seed q.1),
           KernelSampling.completedRight j table (q.2, sR seed q.2)))
    _ = (μ.product γ).mixture (fun z =>
        completionKernel L R (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) := by
      apply congrArg ((μ.product γ).mixture)
      funext z
      exact KernelSampling.completed_joint_pushforward L R j hL hR
        (z.1.1, sL z.2 z.1.1) (z.1.2, sR z.2 z.1.2)
    _ = (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
      exact (mixture_pushforward_base (μ.product γ)
        (fun z => (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) (completionKernel L R)).symm

theorem coordinateOutputLaw_eq_outputLaw
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y))
    (hL : ∀ q xs, (L q).weight xs ≠ 0 → xs j = q.1)
    (hR : ∀ q ys, (R q).weight ys ≠ 0 → ys j = q.1) :
    coordinateOutputLaw μ γ j sL sR L R = outputLaw μ γ sL sR L R := by
  rw [coordinateOutputLaw_eq_mixture μ γ j sL sR L R hL hR, outputLaw_eq_mixture]

theorem coordinateOutputLaw_totalVariation_le
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y))
    (hL : ∀ q xs, (L q).weight xs ≠ 0 → xs j = q.1)
    (hR : ∀ q ys, (R q).weight ys ≠ 0 → ys j = q.1)
    (σ : FiniteDistribution ((X × Y) × S)) :
    (coordinateOutputLaw μ γ j sL sR L R).totalVariation
        (σ.mixture (fun z => (L (z.1.1, z.2)).product (R (z.1.2, z.2)))) ≤
      (sharedOutputLaw μ γ sL sR).totalVariation (diagonalLaw σ) := by
  rw [coordinateOutputLaw_eq_outputLaw μ γ j sL sR L R hL hR]
  exact outputLaw_totalVariation_le μ γ sL sR L R σ

end CoordinateCompletion

end

end UniqueGames.Foundations.Repetition.CompletedSampling

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_LocalSimulation
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGames.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                               
section

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games CorrelatedSampling
noncomputable section
variable {Q₁ Q₂ A₁ A₂ S : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype S]
  [Nonempty A₁] [Nonempty A₂] [Nonempty S]
  [DecidableEq Q₁] [DecidableEq Q₂] [DecidableEq S] {n : Nat}

theorem coordinate_probability_le_value_of_local_completion
    (G : Game Q₁ Q₂ A₁ A₂) (j : Fin n)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (σ : FiniteDistribution ((Q₁ × Q₂) × S))
    (profileL : Q₁ → FiniteDistribution S) (profileR : Q₂ → FiniteDistribution S)
    (completionL : Q₁ × S → FiniteDistribution (Fin n → Q₁))
    (completionR : Q₂ × S → FiniteDistribution (Fin n → Q₂))
    (supportL : ∀ q xs, (completionL q).weight xs ≠ 0 → xs j = q.1)
    (supportR : ∀ q ys, (completionR q).weight ys ≠ 0 → ys j = q.1)
    (fallback : S) :
    (σ.mixture (fun z => (completionL (z.1.1,z.2)).product
      (completionR (z.1.2,z.2)))).probability (G.coordinateWin strategy j) ≤
      G.value +
        (2 * Information.totalVariation σ.weight
          (fun z => G.questions.weight z.1 * (profileL z.1.1).weight z.2) +
         2 * Information.totalVariation σ.weight
          (fun z => G.questions.weight z.1 * (profileR z.1.2).weight z.2)) := by
  let targetLaw := σ.mixture (fun z => (completionL (z.1.1,z.2)).product (completionR (z.1.2,z.2)))
  let δ := 2 * Information.totalVariation σ.weight
      (fun z => G.questions.weight z.1 * (profileL z.1.1).weight z.2) +
    2 * Information.totalVariation σ.weight
      (fun z => G.questions.weight z.1 * (profileR z.1.2).weight z.2)
  change targetLaw.probability (G.coordinateWin strategy j) ≤ G.value + δ
  by_contra h
  have gap : 0 < targetLaw.probability (G.coordinateWin strategy j) - (G.value + δ) :=
    sub_pos.mpr (lt_of_not_ge h)
  let η := (targetLaw.probability (G.coordinateWin strategy j) - (G.value + δ)) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨N,hN⟩ := samplerOutputLaw_arbitrarily_close σ G.questions profileL profileR fallback η hη
  let thresholds := sharedProfileThresholds profileL profileR
  let γ := traceSeedLaw (rectangleDistribution (α := S) thresholds) N
  let sL := samplerLocal thresholds profileL fallback N
  let sR := samplerLocal thresholds profileR fallback N
  have hvariation := CompletedSampling.coordinateOutputLaw_totalVariation_le
    G.questions γ j sL sR completionL completionR supportL supportR σ
  have hclose : (CompletedSampling.coordinateOutputLaw G.questions γ j sL sR completionL completionR).totalVariation targetLaw ≤ δ + η :=
    hvariation.trans hN
  have hsuccess := G.coordinate_probability_le_value_add_embedding_distance j targetLaw
    (CompletedSampling.seedLaw γ completionL completionR)
    (CompletedSampling.coordinateLeft j sL) (CompletedSampling.coordinateRight j sR)
    (CompletedSampling.coordinateLeft_preserves j sL)
    (CompletedSampling.coordinateRight_preserves j sR) strategy
  have hsym : targetLaw.totalVariation
      (G.localEmbeddingLaw (CompletedSampling.seedLaw γ completionL completionR)
        (CompletedSampling.coordinateLeft j sL) (CompletedSampling.coordinateRight j sR)) =
      (CompletedSampling.coordinateOutputLaw G.questions γ j sL sR completionL completionR).totalVariation targetLaw := by
    unfold FiniteDistribution.totalVariation
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    exact abs_sub_comm _ _
  rw [hsym] at hsuccess
  dsimp [η] at hclose
  linarith

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_Completion
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                          
section

namespace UniqueGames.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem factorized_completion_row
    (left : X → ℝ) (right : Y → ℝ)
    (hl : ∀ x, 0 ≤ left x) (hr : ∀ y, 0 ≤ right y)
    (defaultLeft : FiniteDistribution X) (defaultRight : FiniteDistribution Y)
    («c» : ℝ) (xy : X × Y) :
    (∑ z : X × Y, «c» * left z.1 * right z.2) *
      ((normalizeOr left hl defaultLeft).product
        (normalizeOr right hr defaultRight)).weight xy = «c» * left xy.1 * right xy.2 := by
  have hm : (∑ z : X × Y, «c» * left z.1 * right z.2) =
      «c» * (∑ z, left z) * (∑ z, right z) := by
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [productWeight_mass]
  rw [hm]
  exact local_completion_recombination left right hl hr defaultLeft defaultRight «c» xy.1 xy.2

end
end UniqueGames.Foundations.Repetition

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_SelectedCommon
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                              
section

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

theorem partialRevealMarginal_isProbability
    {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (μ : FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ)
    (hp : IsProbability (fullRevealMarginal μ j likelihood)) :
    IsProbability (partialRevealMarginal μ j likelihood) := by
  apply (maskedJoint_isProbability_iff _).mp
  have h := isProbability_comp_equiv (revealSplitEquiv (T := T) j).symm _ hp
  have he : (fun z => fullRevealMarginal μ j likelihood
      ((revealSplitEquiv (T := T) j).symm z)) =
      maskedJoint (partialRevealMarginal μ j likelihood) := by
    funext z
    exact fullRevealMarginal_merge μ j likelihood z.1.1.1 z.1.1.2 z.1.2 z.2
  rw [he] at h
  exact h

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selected_fullReveal_isProbability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    IsProbability (fullRevealMarginal G.questions j
      (selectedOutsideLikelihood G strategy selected)) := by
  have h := isProbability_comp_equiv
    (selectedObservationEquiv (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected).symm
    _ (selectedRawMarginal_isProbability G strategy selected positive j)
  have he : (fun z => selectedRawMarginal G strategy selected j
      ((selectedObservationEquiv (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected).symm z)) =
      fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected) := by
    funext z
    exact selectedRawMarginal_fullReveal G strategy selected j z
  rw [he] at h
  exact h

def selectedCommonLaw (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j × (Q₁ × Q₂)) :=
  toGameLaw (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
    (partialRevealMarginal_isProbability G.questions j _
      (selected_fullReveal_isProbability G strategy selected positive j))

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_SelectedJointGame
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Hastad.SourceGame.baseGame_accepts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                 
section

namespace UniqueGames.Foundations.Repetition

open scoped BigOperators
open Games Information
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedSplit_question_probability (G : Game Q₁ Q₂ A₁ A₂)
    (selected : Finset (Fin n))
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (selectedSplitLaw G selected).probability
      (fun q => event (selectedQuestionTuple selected q.1 q.2)) =
        (G.repetition n).questions.probability event := by
  rw [selectedSplitLaw, ← iid_coordinate_split, FiniteDistribution.probability_transport]
  change (G.questions.iid n).probability _ =
    ((G.questions.iid n).transport (Game.tupleQuestionEquiv n)).probability event
  rw [FiniteDistribution.probability_transport]
  apply congrArg (G.questions.iid n).probability
  funext q
  congr 1
  apply Prod.ext <;> funext i <;>
    simp [selectedQuestionTuple, coordinateSplitEquiv, mergeCoordinates, Game.tupleQuestionEquiv]

theorem selectedJoint_eventMass (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (∑ tv : SelectedInput Q₁ Q₂ selected ×
        SelectedLabels (A₁ := A₁) (A₂ := A₂) selected,
      (selectedInputLaw G selected).weight tv.1 *
        ∑ u, independentProduct
          (fun i => (selectedInputProfile G selected tv.1 i).weight) u *
            selectedLikelihood G strategy selected tv.1.1 tv.2 u *
              (if event (selectedQuestionTuple selected tv.1.1 u) then 1 else 0)) =
      (G.repetition n).questions.probability
        (fun q => G.selectedWins strategy selected q && event q) := by
  classical
  have hlabel (t : SelectedInput Q₁ Q₂ selected) :
      (∑ v, ∑ u, independentProduct
        (fun i => (selectedInputProfile G selected t i).weight) u *
          selectedLikelihood G strategy selected t.1 v u *
            (if event (selectedQuestionTuple selected t.1 u) then 1 else 0)) =
      ∑ u, independentProduct
        (fun i => (selectedInputProfile G selected t i).weight) u *
          (if G.selectedWins strategy selected (selectedQuestionTuple selected t.1 u) &&
            event (selectedQuestionTuple selected t.1 u) then 1 else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    rw [← Finset.sum_mul, ← Finset.mul_sum, selectedLikelihood_sum]
    cases hw : G.selectedWins strategy selected (selectedQuestionTuple selected t.1 u) <;>
      cases he : event (selectedQuestionTuple selected t.1 u) <;> simp []
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, hlabel]
  rw [Fintype.sum_prod_type]
  simp only [selectedInputLaw, FiniteDistribution.product, FiniteDistribution.table,
    selectedInputProfile, independentProduct]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  have hforget (fixed : selected → Q₁ × Q₂) :=
    reveal_product_expectation G.questions
      (fun u : {i : Fin n // i ∉ selected} → Q₁ × Q₂ =>
        if G.selectedWins strategy selected (selectedQuestionTuple selected fixed u) &&
          event (selectedQuestionTuple selected fixed u) then (1 : ℝ) else 0)
  simp_rw [hforget]
  have h := selectedSplit_question_probability G selected
    (fun q => G.selectedWins strategy selected q && event q)
  simpa [selectedSplitLaw, FiniteDistribution.probability, FiniteDistribution.product,
    FiniteDistribution.table, Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_assoc] using h

theorem selectedJointLaw_question_probability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (selectedJointLaw G strategy selected positive).probability
      (fun z => event (selectedQuestionTuple selected z.1.1.1 z.2)) =
        ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).probability
          event := by
  classical
  erw [FiniteDistribution.probability_condition]
  change
    (∑ z : (SelectedInput Q₁ Q₂ selected ×
        SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
          ({i : Fin n // i ∉ selected} → Q₁ × Q₂),
      if event (selectedQuestionTuple selected z.1.1.1 z.2)
      then selectedJointWeight G strategy selected z else 0) =
        (G.repetition n).questions.probability
          (fun q => G.selectedWins strategy selected q && event q) /
            G.selectedSuccess strategy selected
  calc
    _ = (∑ tv : SelectedInput Q₁ Q₂ selected ×
          SelectedLabels (A₁ := A₁) (A₂ := A₂) selected,
        (selectedInputLaw G selected).weight tv.1 *
          ∑ u, independentProduct
            (fun i => (selectedInputProfile G selected tv.1 i).weight) u *
              selectedLikelihood G strategy selected tv.1.1 tv.2 u *
                (if event (selectedQuestionTuple selected tv.1.1 u) then 1 else 0)) /
        G.selectedSuccess strategy selected := by
      conv_lhs => rw [Fintype.sum_prod_type]
      simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro tv _
      apply Finset.sum_congr rfl
      intro u _
      cases he : event (selectedQuestionTuple selected tv.1.1 u) <;>
        simp [selectedJointWeight, div_eq_mul_inv, mul_assoc]
    _ = _ := by rw [selectedJoint_eventMass]

end
end UniqueGames.Foundations.Repetition

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_QuestionMarginal
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGames.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                
section

namespace UniqueGames.Foundations.Repetition

open scoped BigOperators
open Games Information

noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]
  {n : Nat}

def selectedTupleLikelihood (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (questions : Fin n → Q₁ × Q₂) : ℝ :=
  if G.selectedWins strategy selected (Game.tupleQuestionEquiv n questions) then 1 else 0

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedTupleLikelihood_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (questions : Fin n → Q₁ × Q₂) :
    0 ≤ selectedTupleLikelihood G strategy selected questions := by
  unfold selectedTupleLikelihood
  split <;> norm_num

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedTupleLikelihood_le_one (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (questions : Fin n → Q₁ × Q₂) :
    selectedTupleLikelihood G strategy selected questions ≤ 1 := by
  unfold selectedTupleLikelihood
  split <;> norm_num

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedTupleLikelihood_mass (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) :
    (∑ questions, independentProduct (fun _ : Fin n => G.questions.weight) questions *
      selectedTupleLikelihood G strategy selected questions) =
        G.selectedSuccess strategy selected := by
  classical
  change _ = ((G.questions.iid n).transport (Game.tupleQuestionEquiv n)).probability
    (G.selectedWins strategy selected)
  rw [FiniteDistribution.probability_transport]
  simp only [FiniteDistribution.probability, FiniteDistribution.iid, independentProduct,
    selectedTupleLikelihood, mul_ite, mul_one, mul_zero]

def selectedQuestionMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (i : Fin n) : FiniteDistribution (Q₁ × Q₂) :=
  ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).pushforward
    (fun questions => (questions.1 i, questions.2 i))

theorem selectedQuestionMarginal_weight (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (i : Fin n) :
    (selectedQuestionMarginal G strategy selected positive i).weight =
      coordinateMarginal
        (posterior (independentProduct (fun _ : Fin n => G.questions.weight))
          (selectedTupleLikelihood G strategy selected) (G.selectedSuccess strategy selected)) i := by
  classical
  funext a
  simp only [selectedQuestionMarginal, FiniteDistribution.pushforward,
    FiniteDistribution.condition, coordinateMarginal]
  refine Fintype.sum_equiv (Game.tupleQuestionEquiv (Q₁ := Q₁) (Q₂ := Q₂) n).symm _ _ ?_
  intro questions
  cases he : G.selectedWins strategy selected questions <;>
    simp [Game.repetition_question_weight, Game.tupleQuestionEquiv,
      posterior, independentProduct, selectedTupleLikelihood, Game.selectedSuccess, he]

theorem selectedQuestionMarginal_totalVariation_sq_sum_le_log
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ i : Fin n,
      (selectedQuestionMarginal G strategy selected positive i).totalVariation G.questions ^ 2) ≤
        Real.log (1 / G.selectedSuccess strategy selected) := by
  classical
  change (∑ i : Fin n, Information.totalVariation
    (selectedQuestionMarginal G strategy selected positive i).weight G.questions.weight ^ 2) ≤ _
  simp_rw [selectedQuestionMarginal_weight]
  exact posterior_coordinate_totalVariation_sq_sum_le_log
    (fun _ : Fin n => G.questions.weight) (fun _ => gameLaw_isProbability G.questions)
    (selectedTupleLikelihood G strategy selected)
    (selectedTupleLikelihood_nonnegative G strategy selected)
    (selectedTupleLikelihood_le_one G strategy selected)
    positive (selectedTupleLikelihood_mass G strategy selected)

theorem unselectedQuestionMarginal_totalVariation_sq_sum_le_log
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ i : {i : Fin n // i ∉ selected},
      (selectedQuestionMarginal G strategy selected positive i.1).totalVariation G.questions ^ 2) ≤
        Real.log (1 / G.selectedSuccess strategy selected) := by
  classical
  let d : Fin n → ℝ := fun i =>
    (selectedQuestionMarginal G strategy selected positive i).totalVariation G.questions
  have hfull := selectedQuestionMarginal_totalVariation_sq_sum_le_log G strategy selected positive
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun i : Fin n => i ∈ selected)
    (fun i => d i ^ 2)
  have hinst : Subtype.fintype (fun i : Fin n => i ∈ selected) =
      Finset.Subtype.fintype selected := Subsingleton.elim _ _
  rw [hinst] at hsplit
  have hselected : 0 ≤ ∑ i : {i : Fin n // i ∈ selected}, d i.1 ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  change (∑ i : {i : Fin n // i ∉ selected}, d i.1 ^ 2) ≤ _
  change (∑ i : Fin n, d i ^ 2) ≤ _ at hfull
  linarith

theorem unselectedQuestionMarginal_totalVariation_sum_le_sqrt
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ i : {i : Fin n // i ∉ selected},
      (selectedQuestionMarginal G strategy selected positive i.1).totalVariation G.questions) ≤
        Real.sqrt ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
          Real.log (1 / G.selectedSuccess strategy selected)) := by
  classical
  let d : {i : Fin n // i ∉ selected} → ℝ := fun i =>
    (selectedQuestionMarginal G strategy selected positive i.1).totalVariation G.questions
  have hsq := unselectedQuestionMarginal_totalVariation_sq_sum_le_log G strategy selected positive
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset {i : Fin n // i ∉ selected}) d (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hcs
  have hln : 0 ≤ Real.log (1 / G.selectedSuccess strategy selected) :=
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)).trans hsq
  have hcard : 0 ≤ (Fintype.card {i : Fin n // i ∉ selected} : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hsq hcard
  have hsqrt := Real.sq_sqrt (mul_nonneg hcard hln)
  have hsqrtpos := Real.sqrt_nonneg
    ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
      Real.log (1 / G.selectedSuccess strategy selected))
  change (∑ i, d i) ≤ _
  change (∑ i, d i ^ 2) ≤ _ at hsq
  change (Fintype.card {i : Fin n // i ∉ selected} : ℝ) * (∑ i, d i ^ 2) ≤ _ at hmul
  nlinarith

end

end UniqueGames.Foundations.Repetition

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_SelectedCommonMarginal
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGames.Foundations.Hastad.SourceGame.baseGame_accepts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                      
section

namespace UniqueGames.Foundations.Repetition

open scoped BigOperators
open Games Information
noncomputable section

variable {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem partialRevealMarginal_secondMarginal
    (μ : FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    secondMarginal (partialRevealMarginal μ j likelihood) =
      secondMarginal (fullRevealMarginal μ j likelihood) := by
  classical
  funext q
  calc
    _ = ∑ z : (T × ({i : I // i ≠ j} → X ⊕ Y)) × (X ⊕ Y),
        maskedJoint (partialRevealMarginal μ j likelihood) (z,q) := by
      simp [secondMarginal, Fintype.sum_prod_type, maskedJoint]
    _ = _ := by
      apply Fintype.sum_equiv (revealDataSplitEquiv (T := T) j).symm
      intro z
      exact (fullRevealMarginal_merge μ j likelihood z.1.1 z.1.2 z.2 q).symm

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selectedFullReveal_secondMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) :
    secondMarginal (fullRevealMarginal G.questions j
      (selectedOutsideLikelihood G strategy selected)) =
        secondMarginal (selectedRawMarginal G strategy selected j) := by
  classical
  funext q
  apply Fintype.sum_equiv
    (selectedObservationDataEquiv (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected).symm
  intro z
  exact (selectedRawMarginal_fullReveal G strategy selected j (z,q)).symm

theorem selectedRawMarginal_secondMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    secondMarginal (selectedRawMarginal G strategy selected j) =
      (selectedQuestionMarginal G strategy selected positive j.1).weight := by
  classical
  funext q
  calc
    _ = (selectedJointLaw G strategy selected positive).probability
        (fun z => decide (z.2 j = q)) := by
      simp only [secondMarginal, selectedRawMarginal, FiniteDistribution.probability,
        selectedJointLaw, toGameLaw, Fintype.sum_prod_type, decide_eq_true_eq]
    _ = ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).probability
        (fun questions => decide ((questions.1 j.1,questions.2 j.1) = q)) := by
      have h := selectedJointLaw_question_probability G strategy selected positive
        (fun questions => decide ((questions.1 j.1,questions.2 j.1) = q))
      simpa [selectedQuestionTuple, mergeCoordinates, j.property] using h
    _ = _ := by
      rw [FiniteDistribution.weight_eq_probability_singleton, selectedQuestionMarginal,
        FiniteDistribution.probability_pushforward]

theorem selectedCommonLaw_secondMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    secondMarginal (selectedCommonLaw G strategy selected positive j).weight =
      (selectedQuestionMarginal G strategy selected positive j.1).weight := by
  change secondMarginal (partialRevealMarginal G.questions j
    (selectedOutsideLikelihood G strategy selected)) = _
  rw [partialRevealMarginal_secondMarginal, selectedFullReveal_secondMarginal]
  exact selectedRawMarginal_secondMarginal G strategy selected positive j

end
end UniqueGames.Foundations.Repetition

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_ProfileCorrection
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                 
section

namespace UniqueGames.Foundations.Repetition.ProfileCorrection
open scoped BigOperators
open UniqueGames.Foundations.Information
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

theorem left_profile_correction
    (p : X × (S × Y) → ℝ) (μ : X × Y → ℝ)
    (fallbackS : S → ℝ) (fallbackY : Y → ℝ)
    (hp : IsProbability p) (hμ : IsProbability μ)
    (hS : IsProbability fallbackS) (hY : IsProbability fallbackY) :
    totalVariation p (fun z => μ (z.1, z.2.2) *
      conditionalKernel (seedQuestionMarginal p) fallbackS z.1 z.2.1) ≤
    totalVariation p (fun z => seedQuestionMarginal p (z.1, z.2.1) *
      conditionalKernel μ fallbackY z.1 z.2.2) +
    totalVariation (firstMarginal p) (firstMarginal μ) := by
  let σ := seedQuestionMarginal p
  let L := conditionalKernel σ fallbackS
  let M := conditionalKernel μ fallbackY
  let k : X → S × Y → ℝ := fun x sy => L x sy.1 * M x sy.2
  let «c» : X × (S × Y) → ℝ := fun z => σ (z.1,z.2.1) * M z.1 z.2.2
  let d : X × (S × Y) → ℝ := fun z => μ (z.1,z.2.2) * L z.1 z.2.1
  have hσ : IsProbability σ := seedQuestionMarginal_isProbability p hp
  have hk : ∀ x, IsProbability (k x) := by
    intro x
    exact kernelProduct_isProbability (L x) (fun _ : S => M x)
      (conditionalKernel_isProbability σ fallbackS hσ hS x)
      (fun _ => conditionalKernel_isProbability μ fallbackY hμ hY x)
  have hc : «c» = fun z => firstMarginal σ z.1 * k z.1 z.2 := by
    funext z
    change σ (z.1,z.2.1) * M z.1 z.2.2 =
      firstMarginal σ z.1 * (L z.1 z.2.1 * M z.1 z.2.2)
    rw [← mul_assoc, marginal_mul_conditionalKernel σ fallbackS hσ]
  have hd : d = fun z => firstMarginal μ z.1 * k z.1 z.2 := by
    funext z
    change μ (z.1,z.2.2) * L z.1 z.2.1 =
      firstMarginal μ z.1 * (L z.1 z.2.1 * M z.1 z.2.2)
    calc
      _ = (firstMarginal μ z.1 * M z.1 z.2.2) * L z.1 z.2.1 := by
        rw [marginal_mul_conditionalKernel μ fallbackY hμ]
      _ = _ := by ring
  have hmiddle : totalVariation «c» d =
      totalVariation (firstMarginal σ) (firstMarginal μ) := by
    rw [hc, hd]
    exact totalVariation_joint_common_kernel _ _ k hk
  have result := totalVariation_triangle p «c» d
  rw [hmiddle] at result
  have hmarg : firstMarginal σ = firstMarginal p := seedQuestionMarginal_first p
  rw [hmarg] at result
  exact result
end
end UniqueGames.Foundations.Repetition.ProfileCorrection
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_ProfileBounds
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                             
section

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

theorem leftCommonProfile_isProbability (p : S × (X × Y) → ℝ) (fallback : S → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) (x : X) :
    IsProbability (leftCommonProfile p fallback x) :=
  conditionalKernel_isProbability _ _ (leftCommonMarginal_isProbability p hp) hf x

theorem leftCommonProfile_error [DecidableEq X] [DecidableEq Y]
    (p : S × (X × Y) → ℝ) (μ : FiniteDistribution (X × Y)) (fallback : S → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) :
    totalVariation p (fun z => μ.weight z.2 * leftCommonProfile p fallback z.2.1 z.1) ≤
      totalVariation p (leftRevealModel μ p) + totalVariation (secondMarginal p) μ.weight := by
  let e := swapSeedLeft (S := S) (X := X) (Y := Y)
  let p' : X × (S × Y) → ℝ := fun z => p (e z)
  have h := ProfileCorrection.left_profile_correction p' μ.weight fallback
    (μ.pushforward Prod.snd).weight
    (isProbability_comp_equiv e p hp) (gameLaw_isProbability μ) hf
    (gameLaw_isProbability (μ.pushforward Prod.snd))
  have hs : ProfileCorrection.seedQuestionMarginal p' = leftCommonMarginal p := rfl
  have hc : (fun z : X × (S × Y) => ProfileCorrection.seedQuestionMarginal p' (z.1,z.2.1) *
      conditionalKernel μ.weight (μ.pushforward Prod.snd).weight z.1 z.2.2) =
      fun z => leftRevealModel μ p (e z) := by
    funext z
    change (∑ y, p (z.2.1,(z.1,y))) *
      conditionalKernel μ.weight (μ.pushforward Prod.snd).weight z.1 z.2.2 =
      (∑ y, p (z.2.1,(z.1,y))) *
        (revealProfile μ (Sum.inl z.1)).weight (z.1,z.2.2)
    rw [revealProfile_inl_diagonal]
  have hd : (fun z : X × (S × Y) => μ.weight (z.1,z.2.2) *
      conditionalKernel (ProfileCorrection.seedQuestionMarginal p') fallback z.1 z.2.1) =
      fun z => μ.weight (e z).2 * leftCommonProfile p fallback (e z).2.1 (e z).1 := rfl
  rw [hc, hd] at h
  change totalVariation (fun z => p (e z)) _ ≤
    totalVariation (fun z => p (e z)) _ + _ at h
  rw [totalVariation_comp_equiv e p (leftRevealModel μ p)] at h
  rw [totalVariation_comp_equiv e p
    (fun z => μ.weight z.2 * leftCommonProfile p fallback z.2.1 z.1)] at h
  have hm : firstMarginal p' = firstMarginal (secondMarginal p) := by
    funext x
    simp only [firstMarginal, secondMarginal, Fintype.sum_prod_type, p', e, swapSeedLeft]
    exact Finset.sum_comm
  rw [hm] at h
  exact h.trans (add_le_add le_rfl (firstMarginal_totalVariation_le (secondMarginal p) μ.weight))

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_RightProfileBounds
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                  
section

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

theorem rightCommonProfile_isProbability (p : S × (X × Y) → ℝ) (fallback : S → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) (y : Y) :
    IsProbability (rightCommonProfile p fallback y) :=
  leftCommonProfile_isProbability (fun z => p (swapQuestionEndpoints z)) fallback
    (isProbability_comp_equiv swapQuestionEndpoints p hp) hf y

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_SelectedProfiles
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
attribute [-simp] _root_.OAI.UniqueGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                
section

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

theorem finiteDistribution_nonempty {A : Type*} [Fintype A] (μ : FiniteDistribution A) :
    Nonempty A := by
  have hsum : (∑ a, μ.weight a) ≠ 0 := by rw [μ.normalized]; norm_num
  obtain ⟨a, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact ⟨a⟩

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedProfileFallback (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  (selectedCommonLaw G strategy selected positive j).pushforward Prod.fst

def selectedLeftProfile (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) (x : Q₁) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  toGameLaw
    (leftCommonProfile (selectedCommonLaw G strategy selected positive j).weight
      (selectedProfileFallback G strategy selected positive j).weight x)
    (leftCommonProfile_isProbability _ _
      (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
      (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j)) x)

def selectedRightProfile (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) (y : Q₂) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  toGameLaw
    (rightCommonProfile (selectedCommonLaw G strategy selected positive j).weight
      (selectedProfileFallback G strategy selected positive j).weight y)
    (rightCommonProfile_isProbability _ _
      (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
      (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j)) y)

def selectedLeftProfileError (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) : ℝ :=
  totalVariation (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedLeftProfile G strategy selected positive j z.2.1).weight z.1)

def selectedRightProfileError (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) : ℝ :=
  totalVariation (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedRightProfile G strategy selected positive j z.2.2).weight z.1)

theorem selectedLeftProfileError_le (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    selectedLeftProfileError G strategy selected positive j ≤
      totalVariation (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (leftRevealModel G.questions
          (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))) +
      totalVariation (secondMarginal (selectedCommonLaw G strategy selected positive j).weight)
        G.questions.weight :=
  leftCommonProfile_error _ G.questions _
    (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
    (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j))

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_SelectedProfileBudget
attribute [-instance] _root_.OAI.UniqueGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.dartNonempty _root_.OAI.UniqueGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                     
section

namespace UniqueGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedQuestionRadius_le_informationRadius [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) :
    Real.sqrt ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
      Real.log (1 / G.selectedSuccess strategy selected)) ≤
      selectedInformationRadius G strategy selected := by
  have hcard : (1 : ℝ) ≤ Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) := by
    exact_mod_cast (Nat.succ_le_of_lt
      (Fintype.card_pos : 0 < Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)))
  have hlog := Real.log_nonneg hcard
  have hnonneg : 0 ≤ (Fintype.card {i : Fin n // i ∉ selected} : ℝ) := Nat.cast_nonneg _
  unfold selectedInformationRadius
  apply Real.sqrt_le_sqrt
  nlinarith

def selectedEmbeddingError (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) : ℝ :=
  2 * selectedLeftProfileError G strategy selected positive j +
    2 * selectedRightProfileError G strategy selected positive j

end
end UniqueGames.Foundations.Repetition
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Repetition_SelectionSequence
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                 
section

namespace UniqueGames.Foundations.Repetition.SelectionSequence

open UniqueGames.Foundations.Games

section ActualGame

variable {Q₁ Q₂ A₁ A₂ : Type*}
variable [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
variable [Nonempty A₁] [Nonempty A₂]

def ConditionalCoordinateBound (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (ell : ℝ) : Prop :=
  ∀ (S : Finset (Fin n)) (_hcard : S.card < n)
    (hp : 0 < G.selectedSuccess strategy S),
    ∃ j, j ∉ S ∧
      (((G.repetition n).questions.condition (G.selectedWins strategy S) hp).probability
        (G.coordinateWin strategy j)) ≤
        G.value + 15 * Real.sqrt
          (((S.card : ℝ) * ell + logTwo (1 / G.selectedSuccess strategy S)) /
            ((n : ℝ) - S.card))

theorem repetition_success_le_of_conditionalCoordinateBound
    (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    {v ell : ℝ} (hvalue : G.value ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell)
    (hcoordinate : ConditionalCoordinateBound G n strategy ell) :
    (G.repetition n).success strategy ≤
      (1 - (1 - v)^3 / 6000)^((n : ℝ) / ell) := by
  have hpositive : ∀ S : Finset (Fin n), S.card < n →
      0 < G.selectedSuccess strategy S →
      ∃ j, j ∉ S ∧ SetStep (G.selectedSuccess strategy) v ell S j := by
    intro S hcard hp
    obtain ⟨j, hj, hbound⟩ := hcoordinate S hcard hp
    refine ⟨j, hj, ?_⟩
    change G.selectedSuccess strategy (insert j S) ≤ _
    rw [G.selectedSuccess_insert strategy S j hp]
    exact mul_le_mul_of_nonneg_left
      (hbound.trans (add_le_add hvalue (le_refl _))) (le_of_lt hp)
  obtain ⟨p, hp0, hpnonneg, hpmono, hrec, hpn⟩ :=
    exists_scalar_sequence (G.selectedSuccess strategy) v ell
      (G.selectedSuccess_empty strategy) (G.selectedSuccess_nonnegative strategy)
      (G.selectedSuccess_antitone strategy) hpositive
  have hbound := scalar_bound_6000 p n
    (G.value_nonnegative.trans hvalue) hv1 hell hp0 hpnonneg hpmono hrec
  rw [hpn, G.selectedSuccess_univ strategy] at hbound
  exact hbound

end ActualGame

end UniqueGames.Foundations.Repetition.SelectionSequence

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_TableIteration
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instDecidableConsistent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                       
section

namespace UniqueGames.Foundations.PCP.TableIteration

open RoundTables
open Target Complexity

def run (H : BaseTable) : Nat → Input → Input := AmplificationIteration.run (step H)

def runTables (H : BaseTable) : Nat → GraphTables.Table → GraphTables.Table :=
  AmplificationIteration.run (build H)

theorem run_val (H : BaseTable) (n : Nat) (input : Input) :
    (run H n input).val = runTables H n input.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change build H (run H n input).val = build H (runTables H n input.val)
      rw [ih]

def iterationCount (F : Formula) : Nat := AmplificationIteration.rounds (size (initial F))

def output (H : BaseTable) (F : Formula) : Input := run H (iterationCount F) (initial F)

def outputTable (H : BaseTable) (F : Formula) : GraphTables.Table :=
  runTables H (iterationCount F) (RawInitialTables.table F)

theorem output_val (H : BaseTable) (F : Formula) : (output H F).val = outputTable H F :=
  run_val H (iterationCount F) (initial F)

def gapMap (H : BaseTable) (F : Formula) : Formula := FinalTableFormula.output (outputTable H F)

opaque degreeData : {n : Nat // sizeFactor ≤ 2 ^ n} :=
  ⟨AmplificationIteration.rounds sizeFactor, (AmplificationIteration.rounds_large sizeFactor).le⟩

def polynomialDegree : Nat := degreeData.val

theorem sizeFactor_le_power : sizeFactor ≤ 2 ^ polynomialDegree :=
  degreeData.property

theorem run_completeness (H : BaseTable) (n : Nat) (input : Input)
    (sat : Satisfiable input) : Satisfiable (run H n input) :=
  AmplificationIteration.run_preserves (step H) Satisfiable (step_completeness H) n input sat

theorem output_completeness (H : BaseTable) (F : Formula) (sat : F.Satisfiable) :
    Satisfiable (output H F) :=
  run_completeness H _ _ ((initial_satisfiable_iff F).mpr sat)

theorem gapMap_completeness (H : BaseTable) (F : Formula) (sat : F.Satisfiable) :
    (gapMap H F).Satisfiable := by
  apply (FinalTableFormula.satisfiable_iff (outputTable H F)).mpr
  rw [← output_val]
  exact output_completeness H F sat

theorem output_darts_positive (H : BaseTable) (F : Formula) : 0 < (outputTable H F).darts := by
  rw [← output_val]
  exact (output H F).property

theorem gapMap_nonempty (H : BaseTable) (F : Formula) : (gapMap H F).clauses ≠ [] :=
  FinalTableFormula.nonempty (outputTable H F) (output_darts_positive H F)

theorem run_size (H : BaseTable) (n : Nat) (input : Input) :
    size (run H n input) ≤ sizeFactor ^ n * size input :=
  AmplificationIteration.run_size (step H) size sizeFactor (step_size H) n input

end UniqueGames.Foundations.PCP.TableIteration

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_PCP_TableGapReduction
attribute [-instance] _root_.OAI.VertexCover.ClauseProjection.instDecidableConsistent _root_.OAI.VertexCover.ClauseProjection.instFintypePattern _root_.OAI.VertexCover.Machine.BoundedMemory.instFintypeMemory _root_.OAI.VertexCover.Machine.Compose.instFintypeState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                          
section

namespace UniqueGames.Foundations.PCP.TableGapReduction

open RoundTables TableIteration SpectralReturn Target

variable (H : BaseTable)
  (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))

include certificate

theorem output_gap (F : Formula) (unsat : ¬ F.Satisfiable) :
    FinalConstants.cap ≤ gap (TableIteration.output H F) := by
  have hu : ¬ Satisfiable (initial F) := fun sat => unsat ((initial_satisfiable_iff F).mp sat)
  exact AmplificationIteration.run_reaches_cap (step H) gap FinalConstants.cap
    FinalConstants.cap_positive.le FinalConstants.cap_le_one (RoundTableGap.step_gap H certificate)
    (size (initial F)) (initial F) (gap_nonnegative (initial F))
    (one_le_size_mul_gap (initial F) hu)

theorem output_count_gap (F : Formula) (unsat : ¬ F.Satisfiable)
    (labeling : Fin (outputTable H F).vertices → GraphTables.Label) :
    (outputTable H F).darts ≤ FinalConstants.walkLength *
      (GraphTables.semantics (outputTable H F)).rejectionCount labeling := by
  have hp := output_darts_positive H F
  let : Nonempty (Fin (outputTable H F).darts) := ⟨⟨0, hp⟩⟩
  have bound := output_gap H certificate F unsat
  change FinalConstants.cap ≤ (GraphTables.semantics (TableIteration.output H F).val).gap at bound
  rw [output_val] at bound
  have count := ((GraphTables.semantics (outputTable H F)).le_gap_iff FinalConstants.cap).mp bound labeling
  simp only [Fintype.card_fin] at count
  have ht : (0 : ℝ) < FinalConstants.walkLength := Nat.cast_pos.mpr FinalConstants.walkLength_positive
  have divided : ((outputTable H F).darts : ℝ) / FinalConstants.walkLength ≤
      ((GraphTables.semantics (outputTable H F)).rejectionCount labeling : ℝ) := by
    simpa only [FinalConstants.cap, one_div_mul_eq_div] using count
  have multiplied := (div_le_iff₀ ht).mp divided
  exact_mod_cast (show ((outputTable H F).darts : ℝ) ≤ (FinalConstants.walkLength : ℝ) *
      ((GraphTables.semantics (outputTable H F)).rejectionCount labeling : ℝ) by
    simpa only [mul_comm] using multiplied)

theorem gapMap_clauseGap (F : Formula) (unsat : ¬ F.Satisfiable) :
    Hastad.SourceGap.ClauseGap (gapMap H F) PCPIteration.finalClauseGap :=
  FinalTableFormula.clauseGap (outputTable H F) (output_darts_positive H F)
    (output_count_gap H certificate F unsat)

omit certificate in
theorem finalClauseGap_le_one : PCPIteration.finalClauseGap ≤ 1 := by
  have hw : (1 : ℚ) ≤ (FinalConstants.walkLength : ℚ) := by
    exact_mod_cast FinalConstants.walkLength_positive
  have hd : (0 : ℚ) < 40960 * (FinalConstants.walkLength : ℚ) := by positivity
  rw [PCPIteration.finalClauseGap, div_le_one hd]
  linarith

end UniqueGames.Foundations.PCP.TableGapReduction

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end


