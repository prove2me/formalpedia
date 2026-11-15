-- Prove2me | Definitions.Def_InfoLossLAR_NativeBundle_07_Part_2_Subpart_2
-- name    : InfoLossLAR_NativeBundle_07_Part_2_Subpart_2
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T15:30:52.656084+00:00
-- url     : https://prove2.me/theorems/be462da0-38b7-40bf-8bf7-61fe98c0fb4a
-- title:
--   Paired-root and background polynomial evaluation data
-- statement:
--   This package defines selected and paired-root coefficient interfaces, coordinate projections, body and diffuse paired evaluations, leg and background polynomial evaluation, endpoint and independent-background data, and root-reference expectations.
--
--   These finite data interfaces describe the full closed-cycle and shared-background experiments used in the affine response construction. They retain the distinction between joint laws and individual marginals. Supporting constructor identities are preserved from the original source; subsequent analytic bounds and sampler guarantees remain separate theorems.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0. Complete original data source units Definitions.Def_InfoLossLAR_Native_CurrentAFT_UniformCycleSelection, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CycleRootExpansion, Definitions.Def_InfoLossLAR_Native_CurrentAFT_SelectedRootComponent, Definitions.Def_InfoLossLAR_Native_CurrentAFT_PairedRootInput, Definitions.Def_InfoLossLAR_Native_CurrentAFT_PairedRootCentering, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RootCoordinateProjection, Definitions.Def_InfoLossLAR_Native_CurrentAFT_PairedRootProjection, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BodyChannelEvaluation, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BackgroundAtomEvaluation, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BodyPairEvaluation, Definitions.Def_InfoLossLAR_Native_CurrentAFT_DiffusePairEvaluation, Definitions.Def_InfoLossLAR_Native_CurrentAFT_MixedPairEvaluation, Definitions.Def_InfoLossLAR_Native_CurrentAFT_PairQuadraticEvaluation, Definitions.Def_InfoLossLAR_Native_CurrentAFT_LegPolynomialEvaluation, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BackgroundPolynomialEvaluation, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BackgroundEndpointLaw, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RootBackgroundPolynomial, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RootIndependentBackground, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RootReferenceExpectation. Scope wrappers and source-body hashes are recorded in compact_part2_split/manifest.json. SHA256 c7358709dadd7053b8186d15c6326796765af17fd2f294a53ed2a694e47cdfce.

import Definitions.Def_InfoLossLAR_NativeBundle_07_Part_2_Subpart_1

section







/-! # Exact uniform permutation restriction to distinct labeled sites -/

namespace CurrentAFT.CycleSelections

open AFT
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {Selected Pool : Type*} [Fintype Selected] [Fintype Pool] [DecidableEq Pool]

local instance _root_.CurrentAFT.CycleSelections.instDecidableEqEmbedding_currentAFT : DecidableEq (Selected ↪ Pool) := Classical.decEq _

/-- Postcomposition is a genuine permutation of the complete embedding type. -/
def embeddingAction (permutation : Equiv.Perm Pool) : (Selected ↪ Pool) ≃ (Selected ↪ Pool) where
  toFun sites := sites.trans permutation.toEmbedding
  invFun sites := sites.trans permutation.symm.toEmbedding
  left_inv sites := by ext slot; exact permutation.symm_apply_apply _
  right_inv sites := by ext slot; exact permutation.apply_symm_apply _

/-- Every pair of ordered distinct selections is related by a whole-pool
permutation. The complement is completed by an actual finite equivalence. -/
def selectionPermutation (first second : Selected ↪ Pool) : Equiv.Perm Pool :=
  (first.toEquivRange.symm.trans second.toEquivRange).extendSubtype

theorem selectionPermutation_apply (first second : Selected ↪ Pool) (slot : Selected) :
    selectionPermutation first second (first slot) = second slot := by
  rw [selectionPermutation, Equiv.extendSubtype_apply_of_mem _ _ ⟨slot, rfl⟩]
  change second (first.toEquivRange.symm ⟨first slot, ⟨slot, rfl⟩⟩) = second slot
  congr 1
  exact first.toEquivRange.symm_apply_apply slot

/-- A whole-pool uniform permutation sends every fixed distinct selection
to the literal uniform law on ordered embeddings. -/
theorem uniform_permutation_selection (labels : Selected ↪ Pool) :
    (FiniteDist.uniform (Equiv.Perm Pool)).map
      (fun permutation => labels.trans permutation.toEmbedding) =
        @FiniteDist.uniform (Selected ↪ Pool) _ ⟨labels⟩ := by
  letI : Nonempty (Selected ↪ Pool) := ⟨labels⟩
  let law := (FiniteDist.uniform (Equiv.Perm Pool)).map
    (fun permutation => labels.trans permutation.toEmbedding)
  have hconstant (first second : Selected ↪ Pool) : law.weight first = law.weight second := by
    let swap := selectionPermutation first second
    have hfirst : first.trans swap.toEmbedding = second := by
      ext slot
      exact selectionPermutation_apply first second slot
    have h := Equiv.sum_comp (Equiv.mulLeft swap)
      (fun permutation : Equiv.Perm Pool =>
        if labels.trans permutation.toEmbedding = second then
          (FiniteDist.uniform (Equiv.Perm Pool)).weight permutation else 0)
    dsimp only [law]
    simp only [FiniteDist.map_weight]
    apply Eq.trans _ h
    apply Finset.sum_congr rfl
    intro permutation _
    have hequal : labels.trans (swap * permutation).toEmbedding = second ↔
        labels.trans permutation.toEmbedding = first := by
      constructor
      · intro he
        apply (embeddingAction swap).injective
        change (labels.trans permutation.toEmbedding).trans swap.toEmbedding = first.trans swap.toEmbedding
        rw [hfirst]
        exact he
      · intro he
        change (labels.trans permutation.toEmbedding).trans swap.toEmbedding = second
        rw [he, hfirst]
    simp only [Equiv.coe_mulLeft, hequal, FiniteDist.uniform_weight]
  ext output
  change law.weight output = _
  have hsum : (Fintype.card (Selected ↪ Pool) : ℝ) * law.weight output = 1 := by
    have h := law.sum_one
    have hfixed : ∀ sites, law.weight sites = law.weight output := fun sites => hconstant sites output
    simpa only [hfixed, Finset.sum_const, nsmul_eq_mul, Finset.card_univ] using h
  have hcard : (0 : ℝ) < Fintype.card (Selected ↪ Pool) := by exact_mod_cast Fintype.card_pos
  rw [FiniteDist.uniform_weight]
  apply (mul_left_cancel₀ hcard.ne')
  rw [hsum]
  field_simp

/-- Inverse permutations have the same uniform restriction law, matching
the manuscript's endpoint relabeling convention. -/
theorem uniform_inverse_permutation_selection (labels : Selected ↪ Pool) :
    (FiniteDist.uniform (Equiv.Perm Pool)).map
      (fun permutation => labels.trans permutation.symm.toEmbedding) =
        @FiniteDist.uniform (Selected ↪ Pool) _ ⟨labels⟩ := by
  have huniform := FiniteDist.uniform_map_equiv (Equiv.inv (Equiv.Perm Pool))
  rw [← huniform, FiniteDist.map_map]
  exact uniform_permutation_selection labels

/-- Specialization to the actual finite-body selection law. -/
theorem body_permutation_selection (body order : ℕ) (horder : order ≤ body)
    (labels : Selection body order) :
    (FiniteDist.uniform (Equiv.Perm (Fin body))).map
      (fun permutation => labels.trans permutation.symm.toEmbedding) =
        selectionLaw body order horder := by
  unfold selectionLaw
  exact uniform_inverse_permutation_selection labels

/-- The literal uniform whole-body permutation experiment, restricted to
fixed labeled output positions, is the actual selected-root mixture. -/
theorem uniform_permuted_selectedLaw {Scalar : Type*} [Fintype Scalar]
    (body order modulus : ℕ) [NeZero modulus] (horder : order ≤ body)
    (source : FiniteDist Scalar) (value : Scalar → ZMod modulus) (labels : Selection body order) :
    (FiniteDist.uniform (Equiv.Perm (Fin body))).mix
      (fun permutation => (ProtectedCycle.relabeledCycleLaw body modulus source value permutation).map
        (fun root slot => root (labels slot))) =
      averagedSelectedLaw body order modulus horder source value := by
  have hchannel (permutation : Equiv.Perm (Fin body)) :
      (ProtectedCycle.relabeledCycleLaw body modulus source value permutation).map
        (fun root slot => root (labels slot)) =
          selectedLaw body order modulus source value (labels.trans permutation.symm.toEmbedding) := by
    unfold ProtectedCycle.relabeledCycleLaw selectedLaw
    rw [FiniteDist.map_map]
    rfl
  simp_rw [hchannel]
  unfold averagedSelectedLaw
  rw [← body_permutation_selection body order horder labels, FiniteDist.mix_map]

end

end CurrentAFT.CycleSelections

end

section









/-!
# Exact finite response expansion for the actual permuted closed cycle

The response acts on arbitrary joint, vector-valued tests. Its source law
is the literal uniform body permutation of the complete protected cycle.
The independent term and all singleton cancellations are proved under
support-only positivity, so no inverse of a zero root atom is used.
-/

namespace CurrentAFT.CycleRootExpansion

open AFT CycleSelections
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {Index Color Value : Type*} [Fintype Index] [DecidableEq Index] [Fintype Color]
  [AddCommGroup Value] [Module ℝ Value]

def expectationLinear (law : FiniteDist Color) : (Color → Value) →ₗ[ℝ] Value where
  toFun test := ∑ color, law.weight color • test color
  map_add' first second := by simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' scalar test := by
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro color _
    rw [mul_comm]

def componentResponse (joint : FiniteDist (Index → Color))
    (reference : Index → FiniteDist Color) (selected : Finset Index) :
    ((Index → Color) → Value) →ₗ[ℝ] Value where
  toFun test := ∑ word, ((FiniteDist.independent reference).weight word *
    Hoeffding.densityComponent reference joint.weight selected word) • test word
  map_add' first second := by simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' scalar test := by
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro word _
    rw [mul_comm]















section Actual

local instance currentModulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

abbrev Root (security : ℕ) := ZMod (Parameters.modulus security)
abbrev Vertex (security : ℕ) := Fin (Parameters.bodySize security)

def rootReference (security : ℕ) : FiniteDist (Root security) :=
  ProtectedCycle.differenceLaw (DiffuseProfiles.edgeLaw security)
    (fun scalar => ((scalar : ℤ) : Root security))

/-- The body permutation is genuinely averaged independently of the latent
edges; the complete closing edge is part of every conditional law. -/
def rootLaw (security : ℕ) : FiniteDist (Vertex security → Root security) :=
  (FiniteDist.uniform (Equiv.Perm (Vertex security))).mix
    (ProtectedCycle.relabeledCycleLaw (Parameters.bodySize security) (Parameters.modulus security)
      (DiffuseProfiles.edgeLaw security) (fun scalar => ((scalar : ℤ) : Root security)))

theorem rootLaw_selected (security order : ℕ) (horder : order ≤ Parameters.bodySize security)
    (labels : Selection (Parameters.bodySize security) order) :
    (rootLaw security).map (fun roots slot => roots (labels slot)) =
      averagedSelectedLaw (Parameters.bodySize security) order (Parameters.modulus security) horder
        (DiffuseProfiles.edgeLaw security) (fun scalar => ((scalar : ℤ) : Root security)) := by
  rw [rootLaw, FiniteDist.map_mix]
  exact uniform_permuted_selectedLaw _ _ _ horder _ _ labels





def actualComponent (security : ℕ) (selected : Finset (Vertex security)) :
    ((Vertex security → Root security) → Value) →ₗ[ℝ] Value :=
  componentResponse (rootLaw security) (fun _ => rootReference security) selected







def selectedCoefficient (security order : ℕ)
    (labels : Selection (Parameters.bodySize security) order) : (Fin order → Root security) → ℝ :=
  centeredRootDensity ((rootLaw security).map (fun roots slot => roots (labels slot)))
    (fun _ => rootReference security)

/-- The full permutation experiment is exactly the selected-root law used
in the quantitative cycle estimate. The complete coefficient norm is
controlled, uniformly over all fixed distinct output labels. -/
theorem selectedCoefficient_norm (security order : ℕ) (hpositive : 1 ≤ order)
    (hbody : 2 * order ≤ Parameters.bodySize security)
    (labels : Selection (Parameters.bodySize security) order) :
    Real.sqrt ((FiniteDist.independent (fun _ : Fin order => rootReference security)).l2Sq
      (selectedCoefficient security order labels)) ≤
      (((2 * (order + 1) : ℕ) : ℝ) ^ order) * currentRootTag security ^ order := by
  unfold selectedCoefficient
  rw [rootLaw_selected security order (by omega) labels]
  exact current_averaged_centered_norm_le security order hpositive hbody



variable {Control : Type*} [Fintype Control]



end Actual

end

end CurrentAFT.CycleRootExpansion

end

section





/-! # The actual Hoeffding component is the quantitative selected-root coefficient -/
namespace CurrentAFT.SelectedRootComponent
open AFT CycleSelections CycleRootExpansion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize
local instance currentModulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩







end
end CurrentAFT.SelectedRootComponent

end

section



















/-! # The actual joint root coefficient and the one original control kernel

All roots of a selected primary group remain together with its single
control input. Untagged roots and dummy controls integrate out isometrically.
-/
namespace CurrentAFT.PairedRootInput
open AFT ActualBlockFock TaggedSelection PairedRootPlacement RaisingPatternBudget
  GradedControlAlgebra ControlNorm ControlCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

abbrev ControlInput {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : ActiveGroup selection tagged → Type :=
  Sum.elim (RoleInput security r s) (fun _ => Unit)

instance controlInputFintype {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : ActiveGroup selection tagged) :
    Fintype (ControlInput selection tagged index) := by
  cases index with
  | inl index => exact roleInputFintype security r s index
  | inr _ => exact inferInstanceAs (Fintype Unit)

def controlReference {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    (index : ActiveGroup selection tagged) → FiniteDist (ControlInput selection tagged index)
  | .inl index => roleReference security r s index
  | .inr _ => FiniteDist.uniform Unit

def controlKernel {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security))
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (word : (index : ActiveGroup selection tagged) → ControlInput selection tagged index) : ℝ :=
  RaisingPatternKernel.inputJoint security kernel (fun index => word (.inl index))

theorem controlKernel_energy {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security))
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    (FiniteDist.dependentIndependent (controlReference selection tagged)).l2Sq
      (controlKernel selection tagged kernel) =
      blockEnergy (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) kernel.val := by
  rw [← RaisingPatternKernel.inputJoint_energy security kernel]
  unfold FiniteDist.l2Sq FiniteDist.expectation
  rw [← (Equiv.prodPiEquivSumPi (RoleInput security r s)
    (fun _ : HitKept selection tagged => Unit)).sum_comp]
  simp only [Fintype.sum_prod_type, FiniteDist.dependentIndependent_weight,
    Fintype.prod_sum_type, controlReference, controlKernel, ControlInput,
    Equiv.prodPiEquivSumPi, Equiv.sumPiEquivProdPi, Equiv.coe_fn_symm_mk,
    Sum.elim_inl, Sum.elim_inr]
  simp [FiniteDist.uniform]

def labels {security : ℕ}
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    CycleSelections.Selection (Parameters.bodySize security) tagged.card :=
  (tagged.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype _)).trans layout.toEmbedding

def sourceEmbedding {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : Fin tagged.card ↪ Sigma (groupRootSlots selection tagged) :=
  tagged.equivFin.symm.toEmbedding.trans (tagEmbedding selection tagged)







abbrev GroupInput {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :=
  GroupedSourceNorm.GroupWord (Root := CycleRootExpansion.Root security)
    (groupRootSlots selection tagged) (ControlInput selection tagged)

def reference {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :=
  FiniteDist.dependentIndependent
    (GroupedSourceNorm.groupReference (groupRootSlots selection tagged) (ControlInput selection tagged)
      (CycleRootExpansion.rootReference security) (controlReference selection tagged))

def jointInput {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (word : GroupInput selection tagged) : ℝ :=
  CycleRootExpansion.selectedCoefficient security tagged.card (labels tagged layout)
    (fun index => (word (sourceEmbedding selection tagged index).fst).1
      (sourceEmbedding selection tagged index).snd) *
    controlKernel selection tagged kernel (fun index => (word index).2)

def jointInputLinear {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s →ₗ[ℝ]
      (GroupInput selection tagged → ℝ) where
  toFun := jointInput selection tagged layout
  map_add' first second := by
    funext word
    simp only [jointInput, controlKernel, RaisingPatternKernel.inputJoint,
      Submodule.coe_add, Pi.add_apply, mul_add]
  map_smul' scalar kernel := by
    funext word
    simp only [jointInput, controlKernel, RaisingPatternKernel.inputJoint,
      Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- This is the full joint input energy, with exactly one copy of the
original canonical control energy even if a group contains two tags. -/
theorem jointInput_energy {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    (reference selection tagged).l2Sq (jointInput selection tagged layout kernel) =
      (FiniteDist.independent (fun _ : Fin tagged.card => CycleRootExpansion.rootReference security)).l2Sq
        (CycleRootExpansion.selectedCoefficient security tagged.card (labels tagged layout)) *
      blockEnergy (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) kernel.val := by
  unfold reference jointInput
  rw [GroupedSourceNorm.embedded_product_input_energy, controlKernel_energy]

theorem jointInput_norm {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (hpositive : 1 ≤ tagged.card) (hbody : 2 * tagged.card ≤ Parameters.bodySize security) :
    Real.sqrt ((reference selection tagged).l2Sq (jointInput selection tagged layout kernel)) ≤
      (((2 * (tagged.card + 1) : ℕ) : ℝ) ^ tagged.card) *
        CycleSelections.currentRootTag security ^ tagged.card *
        blockL2 (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) kernel.val := by
  rw [jointInput_energy, Real.sqrt_mul (FiniteDist.l2Sq_nonneg _ _)]
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hroot := CycleRootExpansion.selectedCoefficient_norm security tagged.card hpositive hbody
    (labels tagged layout)
  let rootNorm (dec : DecidableEq (Fin tagged.card)) : ℝ :=
    Real.sqrt ((@FiniteDist.independent _ _ _ _ dec
      (fun _ : Fin tagged.card => CycleRootExpansion.rootReference security)).l2Sq
      (CycleRootExpansion.selectedCoefficient security tagged.card (labels tagged layout)))
  have hnorm : rootNorm (classicalFinDecidableEq tagged.card) = rootNorm (instDecidableEqFin tagged.card) :=
    congrArg rootNorm (Subsingleton.elim _ _)
  change rootNorm (classicalFinDecidableEq tagged.card) ≤ _
  rw [hnorm]
  exact hroot

end
end CurrentAFT.PairedRootInput

end

section













/-! # Coordinate centering of the true joint root and control source -/
namespace CurrentAFT.PairedRootCentering
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  ControlCoordinates RaisingPatternBudget
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

def rootDensity {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (roots : Sigma (groupRootSlots selection tagged) → CycleRootExpansion.Root security) : ℝ :=
  CycleRootExpansion.selectedCoefficient security tagged.card (labels tagged layout)
    (roots ∘ sourceEmbedding selection tagged)















end
end CurrentAFT.PairedRootCentering

end

section










/-! # Exact root-coordinate averaging and centering on joint control inputs -/
namespace CurrentAFT.RootCoordinateProjection
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

variable {Index Root Control : Type*} [Fintype Index] [DecidableEq Index]
  [Fintype Root] [Fintype Control]

abbrev Input := (Index → Root) × Control

def reference (root : FiniteDist Root) (control : FiniteDist Control) :
    FiniteDist (Input (Index := Index) (Root := Root) (Control := Control)) :=
  (FiniteDist.independent (fun _ : Index => root)).prod control

def average (root : FiniteDist Root) (index : Index) :
    (Input (Index := Index) (Root := Root) (Control := Control) → ℝ) →ₗ[ℝ]
      (Input (Index := Index) (Root := Root) (Control := Control) → ℝ) where
  toFun score sample := root.expectation (fun value => score (Function.update sample.1 index value, sample.2))
  map_add' first second := by funext sample; exact FiniteDist.expectation_add root _ _
  map_smul' scalar score := by funext sample; exact FiniteDist.expectation_const_mul root scalar _

def center (root : FiniteDist Root) (index : Index) :
    (Input (Index := Index) (Root := Root) (Control := Control) → ℝ) →ₗ[ℝ]
      (Input (Index := Index) (Root := Root) (Control := Control) → ℝ) :=
  LinearMap.id - average root index

omit [Fintype Index] [Fintype Control] in
theorem average_apply (root : FiniteDist Root) (index : Index)
    (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ) (sample : Input) :
    average root index score sample = root.expectation (fun value =>
      score (Function.update sample.1 index value, sample.2)) := rfl

omit [Fintype Index] [Fintype Control] in
theorem center_apply (root : FiniteDist Root) (index : Index)
    (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ) (sample : Input) :
    center root index score sample = score sample - average root index score sample := rfl

def insert (index : Index) (value : Root) (rest : {other : Index // other ≠ index} → Root) : Index → Root :=
  (Equiv.funSplitAt index Root).symm (value, rest)

omit [Fintype Index] [Fintype Root] in
theorem update_insert (index : Index) (first second : Root)
    (rest : {other : Index // other ≠ index} → Root) :
    Function.update (insert index first rest) index second = insert index second rest := by
  funext other
  by_cases hequal : other = index
  · subst other
    simp [insert, Equiv.funSplitAt, Equiv.piSplitAt]
  · simp [insert, Equiv.funSplitAt, Equiv.piSplitAt, hequal]

theorem energy_split (root : FiniteDist Root) (control : FiniteDist Control) (index : Index)
    (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ) :
    (reference (Index := Index) root control).l2Sq score =
      ∑ ctrl, control.weight ctrl * ∑ rest : {other : Index // other ≠ index} → Root,
        (∏ other : {other : Index // other ≠ index}, root.weight (rest other)) *
          root.l2Sq (fun value => score (insert index value rest, ctrl)) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Index) (Classical.decEq Index)
  unfold reference FiniteDist.l2Sq
  rw [FiniteDist.expectation_prod, FiniteDist.expectation_comm]
  change (∑ ctrl, control.weight ctrl * (FiniteDist.independent (fun _ : Index => root)).expectation
    (fun roots => score (roots, ctrl) ^ 2)) = _
  apply Finset.sum_congr rfl
  intro ctrl _
  apply congrArg (fun value => control.weight ctrl * value)
  have h := FiniteDist.expectation_independent_split (fun _ : Index => root) index
    (fun roots => score (roots, ctrl) ^ 2)
  exact h

theorem average_energy_le (root : FiniteDist Root) (control : FiniteDist Control) (index : Index)
    (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ) :
    (reference (Index := Index) root control).l2Sq (average root index score) ≤
      (reference (Index := Index) root control).l2Sq score := by
  rw [energy_split root control index, energy_split root control index]
  apply Finset.sum_le_sum
  intro ctrl _
  apply mul_le_mul_of_nonneg_left _ (control.nonneg ctrl)
  apply Finset.sum_le_sum
  intro rest _
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun other _ => root.nonneg (rest other))
  simp only [average_apply, update_insert, FiniteDist.l2Sq, FiniteDist.expectation_const]
  exact BlockFock.mean_square_le root _

theorem center_energy_le (root : FiniteDist Root) (control : FiniteDist Control) (index : Index)
    (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ) :
    (reference (Index := Index) root control).l2Sq (center root index score) ≤
      (reference (Index := Index) root control).l2Sq score := by
  rw [energy_split root control index, energy_split root control index]
  apply Finset.sum_le_sum
  intro ctrl _
  apply mul_le_mul_of_nonneg_left _ (control.nonneg ctrl)
  apply Finset.sum_le_sum
  intro rest _
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun other _ => root.nonneg (rest other))
  simp only [center_apply, average_apply, update_insert]
  exact TensorChannel.center_energy_le root (fun value => score (insert index value rest, ctrl))





omit [Fintype Index] [Fintype Control] in
theorem average_idempotent (root : FiniteDist Root) (index : Index)
    (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ) :
    average root index (average root index score) = average root index score := by
  funext sample
  simp only [average_apply, Function.update_idem, FiniteDist.expectation_const]

omit [Fintype Index] [Fintype Control] in
theorem center_mean_zero (root : FiniteDist Root) (index : Index)
    (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ) :
    average root index (center root index score) = 0 := by
  change average root index (score - average root index score) = 0
  rw [map_sub, average_idempotent, sub_self]

omit [Fintype Index] [Fintype Control] in
theorem average_commute (root : FiniteDist Root) (first second : Index) (hne : first ≠ second)
    (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ) :
    average root first (average root second score) = average root second (average root first score) := by
  funext sample
  simp only [average_apply]
  rw [FiniteDist.expectation_comm]
  apply congrArg root.expectation
  funext secondValue
  apply congrArg root.expectation
  funext firstValue
  rw [Function.update_comm hne]

omit [Fintype Index] [Fintype Control] in
theorem average_center_commute (root : FiniteDist Root) (first second : Index) (hne : first ≠ second)
    (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ) :
    average root first (center root second score) = center root second (average root first score) := by
  change average root first (score - average root second score) =
    average root first score - average root second (average root first score)
  rw [map_sub, average_commute root first second hne]

omit [Fintype Index] [Fintype Control] in
theorem center_commute (root : FiniteDist Root) (first second : Index) (hne : first ≠ second)
    (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ) :
    center root first (center root second score) = center root second (center root first score) := by
  change center root second score - average root first (center root second score) =
    center root second (score - average root first score)
  rw [map_sub, average_center_commute root first second hne]

def coordinate (root : FiniteDist Root) (index : Index) (tagged : Bool) :
    (Input (Index := Index) (Root := Root) (Control := Control) → ℝ) →ₗ[ℝ]
      (Input (Index := Index) (Root := Root) (Control := Control) → ℝ) :=
  if tagged then center root index else average root index

theorem coordinate_energy_le (root : FiniteDist Root) (control : FiniteDist Control) (index : Index)
    (tagged : Bool) (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ) :
    (reference (Index := Index) root control).l2Sq (coordinate root index tagged score) ≤
      (reference (Index := Index) root control).l2Sq score := by
  cases tagged
  · exact average_energy_le root control index score
  · exact center_energy_le root control index score

omit [Fintype Index] [Fintype Control] in
theorem coordinate_commute (root : FiniteDist Root) (first second : Index) (hne : first ≠ second)
    (firstTag secondTag : Bool) (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ) :
    coordinate root first firstTag (coordinate root second secondTag score) =
      coordinate root second secondTag (coordinate root first firstTag score) := by
  cases firstTag <;> cases secondTag
  · exact average_commute root first second hne score
  · exact average_center_commute root first second hne score
  · exact (average_center_commute root second first hne.symm score).symm
  · exact center_commute root first second hne score

def sequence (root : FiniteDist Root) : List (Index × Bool) →
    ((Input (Index := Index) (Root := Root) (Control := Control) → ℝ) →ₗ[ℝ]
      (Input (Index := Index) (Root := Root) (Control := Control) → ℝ))
  | [] => LinearMap.id
  | (index, tagged) :: rest => (coordinate root index tagged).comp (sequence root rest)

theorem sequence_energy_le (root : FiniteDist Root) (control : FiniteDist Control)
    (coordinates : List (Index × Bool)) (score : Input (Index := Index) (Root := Root) (Control := Control) → ℝ) :
    (reference (Index := Index) root control).l2Sq (sequence root coordinates score) ≤
      (reference (Index := Index) root control).l2Sq score := by
  induction coordinates with
  | nil => exact le_rfl
  | cons item rest ih =>
    exact (coordinate_energy_le root control item.1 item.2 (sequence root rest score)).trans ih



end
end CurrentAFT.RootCoordinateProjection

end

section















namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.DependentTensorComposition
end CurrentAFT.DependentTensorComposition
namespace CurrentAFT.DependentTensorFixedInput
end CurrentAFT.DependentTensorFixedInput





/-! # The root mask preserves the actual joint selected coefficient

Tagged coordinates are centered and unused root coordinates are averaged.
The full joint density is unchanged under every resulting local projection.
-/
namespace CurrentAFT.PairedRootProjection
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  PairedRootCentering ControlCoordinates GroupedRootUpdates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
local instance slotDecidableEq {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged) :
    DecidableEq (groupRootSlots selection tagged group) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount









def mask {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged) :
    List (groupRootSlots selection tagged group × Bool) :=
  (Finset.univ : Finset (groupRootSlots selection tagged group)).toList.map
    (fun slot => (slot, decide (rootEmbedding selection tagged ⟨group, slot⟩ ∈ tagged)))

def projector {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged) :
    (((groupRootSlots selection tagged group → CycleRootExpansion.Root security) ×
      ControlInput selection tagged group) → ℝ) →ₗ[ℝ]
    (((groupRootSlots selection tagged group → CycleRootExpansion.Root security) ×
      ControlInput selection tagged group) → ℝ) :=
  RootCoordinateProjection.sequence (CycleRootExpansion.rootReference security) (mask selection tagged group)









end
end CurrentAFT.PairedRootProjection

end

section












/-! Exact rectangular weighted tensor adjunction for actual safe-body channels. -/

namespace CurrentAFT.BodyChannelEvaluation

open AFT ControlCoordinates LeadingEvaluation DiffuseProfiles ProposalPrimary ActualControls
  PrimaryTensorInverse PrimaryMassFamilies BackgroundFamilies BackgroundEvaluation BackgroundFirstEvaluation
  MarkedPairLeading LocalCoefficientFamily LocalCoefficientEvaluation
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference MarkedPairLeading.bodyConvolution

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def rectangularForm {Input Output : Type*} [Fintype Output]
    (input : Input → ℝ) (output : Output → ℝ)
    (channel : (Input → ℝ) →ₗ[ℝ] (Output → ℝ)) (point : Input) : MvPolynomial Output ℝ :=
  ∑ value, MvPolynomial.C (output value * channel (Pi.single point 1) value / input point) * MvPolynomial.X value



def weightedEmbedding {Input Output : Type*} [Fintype Input] (input : FiniteDist Input) (embedding : Input → Output) :
    (Input → ℝ) →ₗ[ℝ] (Output → ℝ) where
  toFun density := fun output => ∑ point, input.weight point * density point * (Pi.single (embedding point) (1 : ℝ) : Output → ℝ) output
  map_add' first second := by
    funext output
    simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' scalar density := by
    funext output
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro point _
    ring



def safeMass (security : ℕ) : (SafePalette security → ℝ) →ₗ[ℝ] (ActualControls.Palette security → ℝ) :=
  weightedEmbedding (bodyReference security) Subtype.val

def bodyDensityChannel (security : ℕ) :
    (SafePalette security → ℝ) →ₗ[ℝ] (ActualControls.Palette security → ℝ) :=
  (diagonal (fun output => ((primaryLaw security).weight output)⁻¹)).comp
    ((bodyConvolution security).comp (safeMass security))





def bodyTensorMass (security degree : ℕ) (density : (Fin degree → SafePalette security) → ℝ) :
    (Fin degree → ActualControls.Palette security) → ℝ :=
  fun output => referenceWeight security degree output * TensorChannel.apply degree (fun _ => bodyDensityChannel security) density output

















end

end CurrentAFT.BodyChannelEvaluation

end

section












/-! Exact evaluation of the actual free and translated background atoms. -/

namespace CurrentAFT.BackgroundAtomEvaluation

open AFT ControlCoordinates DiffuseProfiles ProposalPrimary ActualControls
  BackgroundFamilies BackgroundEvaluation BackgroundFirstEvaluation BodyChannelEvaluation
  BackgroundCertificates BackgroundTranslations FringeCertificate
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _





end

end CurrentAFT.BackgroundAtomEvaluation

end

section












/-! Literal degree-two evaluation through the actual safe body channel. -/

namespace CurrentAFT.BodyPairEvaluation

open AFT ControlCoordinates ControlProduct LeadingEvaluation DiffuseProfiles ProposalPrimary ActualControls
  PrimaryTensorInverse PrimaryMassFamilies BackgroundFamilies BackgroundEvaluation BodyChannelEvaluation
  PairCertificateFamilies DiffusePair DiffusePairBounds LocalCoefficientFamily LocalCoefficientEvaluation
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
  MarkedPairLeading.bodyConvolution DiffusePair.safePairProfile

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _



















end

end CurrentAFT.BodyPairEvaluation

end

section












/-! The actual protected diffuse pair has exactly its constructed certificate. -/

namespace CurrentAFT.DiffusePairEvaluation

open AFT AFT.SafeConvolution AFT.SafePair ControlCoordinates LeadingEvaluation
  DiffuseProfiles ProposalPrimary ActualControls PrimaryMassFamilies PairReindex PairSmoothing
  BackgroundEvaluation BodyChannelEvaluation BodyPairEvaluation DiffusePair DiffusePairBounds FringeCertificate
  DiffusePairResidual DiffusePairResidualRates DiffusePairCertificates LocalCoefficientFamily
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
  MarkedPairLeading.bodyConvolution DiffusePair.safePairProfile DiffusePairResidual.seedProfile
  DiffusePairResidual.rootResiduePairLaw BodyChannelEvaluation.bodyTensorMass DiffusePairBounds.bodyPairDensity

noncomputable def cyclicEquiv (modulus : ℕ) [NeZero modulus] (shift : ZMod modulus) : Fin modulus ≃ Fin modulus :=
  (ZMod.finEquiv modulus).toEquiv.trans ((Equiv.addRight shift).trans (ZMod.finEquiv modulus).toEquiv.symm)

















end

end CurrentAFT.DiffusePairEvaluation

end

section












/-! Exact evaluation of the marked mixed primary/body certificate. -/

namespace CurrentAFT.MixedPairEvaluation

open AFT ControlCoordinates LeadingEvaluation DiffuseProfiles ProposalPrimary ActualControls
  PrimaryTensorInverse PrimaryMassFamilies BackgroundEvaluation BodyChannelEvaluation BodyPairEvaluation
  MarkedPairCertificates MarkedPairLeading MarkedPairSeed LocalCoefficientFamily LocalCoefficientEvaluation
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
  MarkedPairLeading.bodyConvolution MarkedPairSeed.seedDensity

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _





def mixedPolynomial {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForms : Primary → MvPolynomial Variable ℝ) (bodyForms : Body → MvPolynomial Variable ℝ)
    (density : Primary → Body → ℝ) : MvPolynomial Variable ℝ :=
  ∑ color, ∑ center, MvPolynomial.C (primary.weight color * body.weight center * density color center) *
    primaryForms color * bodyForms center



















end

end CurrentAFT.MixedPairEvaluation

end

section













namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.ActualPairBridge
end CurrentAFT.ActualPairBridge
namespace CurrentAFT.DiffusePair
end CurrentAFT.DiffusePair
namespace CurrentAFT.DiffusePair.pairBlur
end CurrentAFT.DiffusePair.pairBlur
namespace CurrentAFT.DiffusePair.pairSeedLaw
end CurrentAFT.DiffusePair.pairSeedLaw
namespace CurrentAFT.DiffusePair.pairStart
end CurrentAFT.DiffusePair.pairStart
namespace CurrentAFT.LocalReferenceEnergy
end CurrentAFT.LocalReferenceEnergy
namespace CurrentAFT.LocalReferenceEnergy.diffusePairAt
end CurrentAFT.LocalReferenceEnergy.diffusePairAt
namespace CurrentAFT.LocalReferenceEnergy.publicBlurLaw
end CurrentAFT.LocalReferenceEnergy.publicBlurLaw
namespace CurrentAFT.LocalReferenceEnergy.signedDiffusePair
end CurrentAFT.LocalReferenceEnergy.signedDiffusePair
namespace CurrentAFT.LocalReferenceEnergy.signedMarkedPair
end CurrentAFT.LocalReferenceEnergy.signedMarkedPair
namespace CurrentAFT.ProposalSymmetry
end CurrentAFT.ProposalSymmetry
namespace CurrentAFT.ProposalSymmetry.directionLaw
end CurrentAFT.ProposalSymmetry.directionLaw




/-! Exact physical evaluation of both actual branches of the conditional pair. -/

namespace CurrentAFT.PairQuadraticEvaluation

open AFT AFT.SafePair AFT.RepresentedPolynomial ControlCoordinates LeadingEvaluation
  DiffuseProfiles ProposalPrimary ActualControls PrimaryMassFamilies BackgroundFamilies
  BackgroundEvaluation BackgroundFirstEvaluation BackgroundAtomEvaluation MixedPairEvaluation
  DiffusePairEvaluation PairQuadraticFamilies LocalCoefficientFamily MarkedPairLeading
  LocalReferenceEnergy ActualPairBridge FringeCertificate
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
  MarkedPairLeading.bodyConvolution

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _







def conditionalPairLaw (security : ℕ) (scalar : Scalar security) : FiniteDist (Pair security) :=
  (primaryLaw security).mix (fun primary => pairAt security primary scalar)





end

end CurrentAFT.PairQuadraticEvaluation

end

section














/-! Literal independent-root, same-scalar leg background generating polynomial. -/

namespace CurrentAFT.LegPolynomialEvaluation

open AFT AFT.RepresentedPolynomial ControlCoordinates GradedControlAlgebra LeadingEvaluation
  DiffuseProfiles ProposalPrimary ActualControls PrimaryMassFamilies BackgroundFamilies
  BackgroundEvaluation BackgroundFirstEvaluation BackgroundAtomEvaluation PairQuadraticEvaluation
  BackgroundCertificates BackgroundTranslations BackgroundLinear LocalCoefficientFamily
  LocalReferenceEnergy FirstHistogram FringeCertificate BodyRootAverages
  ConditionalPairMean LegBackgroundFamilies HistogramMean
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount ProposalPrimary.primaryLaw ActualControls.bodyReference

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

abbrev Scalar (security : ℕ) := LocalReferenceEnergy.Scalar security

def profileEvaluation (security order : ℕ) :=
  (TruncatedOutput.quotientMap (Variable := ActualControls.Palette security) order).toLinearMap.comp
    (profileForm (Color := ActualControls.Palette security))

def attachmentLaw (security : ℕ) (scalar : Scalar security) : FiniteDist (ActualControls.Palette security) :=
  rootAverage security (shiftedSafeLaw security scalar.val)





def attachmentDeviation (security : ℕ) (scalar : Scalar security) : ActualControls.Palette security → ℝ :=
  (attachmentLaw security scalar).weight - uniformProfile security















def conditionalLegGenerating (security : ℕ) (scalar : Scalar security) : MvPolynomial (ActualControls.Palette security) ℝ :=
  tripleGenerating (uniformProfile security) (fun first second attached =>
    (conditionalPairLaw security scalar).weight (first, second) * (attachmentLaw security scalar).weight attached)

def legGenerating (security : ℕ) : MvPolynomial (ActualControls.Palette security) ℝ :=
  ∑ scalar, (scalarLaw security).weight scalar • conditionalLegGenerating security scalar













end

end CurrentAFT.LegPolynomialEvaluation

end

section












/-!
# The complete actual independent-root background law and its physical image

The common queue is averaged after the complete product is formed. Each leg
uses its own actual scalar, shared between that leg's pair and attachment.
All generating factors are centered at the actual uniform palette law.
-/

namespace CurrentAFT.BackgroundPolynomialEvaluation

open AFT AFT.RepresentedPolynomial ControlCoordinates GradedControlAlgebra LeadingEvaluation
  DiffuseProfiles ProposalPrimary ActualControls BackgroundFamilies BackgroundEvaluation
  BackgroundAtomEvaluation BackgroundCertificates BackgroundTranslations BackgroundPopulationBounds
  LocalReferenceEnergy PairQuadraticEvaluation LegPolynomialEvaluation BodyRootAverages
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount ProposalPrimary.primaryLaw ActualControls.bodyReference

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def finiteGenerating {State Variable : Type*} [Fintype State]
    (law : FiniteDist State) (factor : State → MvPolynomial Variable ℝ) : MvPolynomial Variable ℝ :=
  ∑ state, MvPolynomial.C (law.weight state) * factor state







def queueLaw (security : ℕ) (shift : ℤ) : FiniteDist (ActualControls.Palette security) :=
  rootAverage security (shiftedSafeLaw security shift)









def fixedQueueGenerating (security : ℕ) (queue : ℤ) : MvPolynomial (ActualControls.Palette security) ℝ :=
  singleGenerating (FringeCertificate.uniformProfile security) (convolvedCenterLaw security).weight ^ freeCount security *
    singleGenerating (FringeCertificate.uniformProfile security) (queueLaw security queue).weight ^ Parameters.modulus security *
    legGenerating security ^ Parameters.legCount security


























end

end CurrentAFT.BackgroundPolynomialEvaluation

end

section












/-! Fixed endpoint numbering for the actual complete background experiment.
This numbering is a deterministic equivalence, not the final random endpoint
permutation used by the transport construction. -/

namespace CurrentAFT.BackgroundEndpointLaw

open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls
  BackgroundPopulationBounds BackgroundPolynomialEvaluation BackgroundEvaluation
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize

















local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _







end

end CurrentAFT.BackgroundEndpointLaw

end

section




























































namespace AFT
end AFT
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.BlockProducts
end AFT.BlockProducts
namespace AFT.BlockProducts.taggedBlockMass
end AFT.BlockProducts.taggedBlockMass
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPairResidualInput
end AFT.GaussianSource.actualPairResidualInput
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.actualRootLaw
end AFT.GaussianSource.actualRootLaw
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.extraSample
end AFT.GaussianSource.extraSample
namespace AFT.GaussianSource.optionalShift
end AFT.GaussianSource.optionalShift
namespace AFT.GaussianSource.optionalShift.match_1
end AFT.GaussianSource.optionalShift.match_1
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.GaussianSource.pairNeumannConstant
end AFT.GaussianSource.pairNeumannConstant
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.GaussianSource.rootMarginal
end AFT.GaussianSource.rootMarginal
namespace AFT.HistogramNormalization
end AFT.HistogramNormalization
namespace AFT.HistogramNormalization.mixtureMass
end AFT.HistogramNormalization.mixtureMass
namespace AFT.JointPhysicalChannel
end AFT.JointPhysicalChannel
namespace AFT.JointPhysicalChannel.mass
end AFT.JointPhysicalChannel.mass
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.HasOrder
end AFT.RepresentedPolynomial.HasOrder
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.backgroundLogarithm
end AFT.RepresentedPolynomial.backgroundLogarithm
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.inversePrimarySeed
end AFT.RepresentedPolynomial.inversePrimarySeed
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.profileForm
end AFT.RepresentedPolynomial.profileForm
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.reference
end AFT.RootSlice.reference
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.RowBound
end AFT.SafeConvolution.RowBound
namespace AFT.SafeConvolution.SupBound
end AFT.SafeConvolution.SupBound
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
namespace AFT.SafeConvolution.uniformCanonical
end AFT.SafeConvolution.uniformCanonical
namespace AFT.SafePair
end AFT.SafePair
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointDifference
end AFT.V7Calibration.activeEndpointDifference
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualCanonicalPairResidualInput
end AFT.V7Calibration.actualCanonicalPairResidualInput
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualConditionalForwardPolynomial
end AFT.V7Calibration.actualConditionalForwardPolynomial
namespace AFT.V7Calibration.actualControlResponseLinear
end AFT.V7Calibration.actualControlResponseLinear
namespace AFT.V7Calibration.actualControlRootDefectLinear
end AFT.V7Calibration.actualControlRootDefectLinear
namespace AFT.V7Calibration.actualControlRootSetResponseLinear
end AFT.V7Calibration.actualControlRootSetResponseLinear
namespace AFT.V7Calibration.actualCorrelatedForwardPolynomial
end AFT.V7Calibration.actualCorrelatedForwardPolynomial
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualCovarianceTable
end AFT.V7Calibration.actualCovarianceTable
namespace AFT.V7Calibration.actualEndpointHigherTable
end AFT.V7Calibration.actualEndpointHigherTable
namespace AFT.V7Calibration.actualEndpointSeed
end AFT.V7Calibration.actualEndpointSeed
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualForwardRootDefectPolynomial
end AFT.V7Calibration.actualForwardRootDefectPolynomial
namespace AFT.V7Calibration.actualInactiveBodyPairDensity
end AFT.V7Calibration.actualInactiveBodyPairDensity
namespace AFT.V7Calibration.actualInactiveBodyPairInput
end AFT.V7Calibration.actualInactiveBodyPairInput
namespace AFT.V7Calibration.actualInactiveBodyPairMass
end AFT.V7Calibration.actualInactiveBodyPairMass
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualIndependentControlResponseLinear
end AFT.V7Calibration.actualIndependentControlResponseLinear
namespace AFT.V7Calibration.actualIndependentForwardPolynomial
end AFT.V7Calibration.actualIndependentForwardPolynomial
namespace AFT.V7Calibration.actualInitialBackgroundCorrection
end AFT.V7Calibration.actualInitialBackgroundCorrection
namespace AFT.V7Calibration.actualJointTaggedOutput
end AFT.V7Calibration.actualJointTaggedOutput
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedFringeInput
end AFT.V7Calibration.actualMarkedFringeInput
namespace AFT.V7Calibration.actualMarkedInput
end AFT.V7Calibration.actualMarkedInput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualMarkedSafeDensity
end AFT.V7Calibration.actualMarkedSafeDensity
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualPairCompletionInput
end AFT.V7Calibration.actualPairCompletionInput
namespace AFT.V7Calibration.actualPairReferenceInput
end AFT.V7Calibration.actualPairReferenceInput
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualRootResponseLinear
end AFT.V7Calibration.actualRootResponseLinear
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.actual_body_population_expectation
end AFT.V7Calibration.actual_body_population_expectation
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.attachedBodyAtSource
end AFT.V7Calibration.attachedBodyAtSource
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.blockBackgroundError
end AFT.V7Calibration.blockBackgroundError
namespace AFT.V7Calibration.blockBackgroundLinear
end AFT.V7Calibration.blockBackgroundLinear
namespace AFT.V7Calibration.blockBackgroundLinear.match_1
end AFT.V7Calibration.blockBackgroundLinear.match_1
namespace AFT.V7Calibration.blockBodyMeanProfile
end AFT.V7Calibration.blockBodyMeanProfile
namespace AFT.V7Calibration.blockBodyMeanProfile.match_1
end AFT.V7Calibration.blockBodyMeanProfile.match_1
namespace AFT.V7Calibration.blockBodyMeanTable
end AFT.V7Calibration.blockBodyMeanTable
namespace AFT.V7Calibration.blockBodyMeanTable.match_1
end AFT.V7Calibration.blockBodyMeanTable.match_1
namespace AFT.V7Calibration.blockPhysicalPolynomial
end AFT.V7Calibration.blockPhysicalPolynomial
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.endpointCoefficient
end AFT.V7Calibration.endpointCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.V7Calibration.globalLinearProfile
end AFT.V7Calibration.globalLinearProfile
namespace AFT.V7Calibration.globalLinearTable
end AFT.V7Calibration.globalLinearTable
namespace AFT.V7Calibration.globalMeanChangeTable
end AFT.V7Calibration.globalMeanChangeTable
namespace AFT.V7Calibration.globalMeanTable
end AFT.V7Calibration.globalMeanTable
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairDensity
end AFT.V7Calibration.inactiveCanonicalPairDensity
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactiveEndpointMarginalDensity
end AFT.V7Calibration.inactiveEndpointMarginalDensity
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactivePairShift
end AFT.V7Calibration.inactivePairShift
namespace AFT.V7Calibration.inactivePairSources
end AFT.V7Calibration.inactivePairSources
namespace AFT.V7Calibration.inactivePairStarts
end AFT.V7Calibration.inactivePairStarts
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.independentRootResponseLinear
end AFT.V7Calibration.independentRootResponseLinear
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localAttachedMeanInputTable
end AFT.V7Calibration.localAttachedMeanInputTable
namespace AFT.V7Calibration.localBackgroundLinear
end AFT.V7Calibration.localBackgroundLinear
namespace AFT.V7Calibration.localBodyMixture
end AFT.V7Calibration.localBodyMixture
namespace AFT.V7Calibration.localCovarianceInputTable
end AFT.V7Calibration.localCovarianceInputTable
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.localPrimaryMeanInputTable
end AFT.V7Calibration.localPrimaryMeanInputTable
namespace AFT.V7Calibration.primaryPairSeed
end AFT.V7Calibration.primaryPairSeed
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap
namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.CycleRootPolynomial
end CurrentAFT.CycleRootPolynomial
namespace CurrentAFT.CycleRootPolynomial.polynomialComponent
end CurrentAFT.CycleRootPolynomial.polynomialComponent
namespace CurrentAFT.CycleRootPolynomial.polynomialDefect
end CurrentAFT.CycleRootPolynomial.polynomialDefect




/-! Actual root-dependent background block polynomials and their exact constant coordinates. -/

namespace CurrentAFT.RootBackgroundPolynomial

open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls
  LocalReferenceEnergy ActualBlockFock ActualBlockMean BackgroundPolynomialEvaluation
  CycleRootExpansion CycleRootPolynomial ConditionalHistogramMean ActualCycleMeanMGF
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
  CycleRootExpansion.rootLaw CycleRootExpansion.rootReference

local instance blockIndexDecidableEq (security : ℕ) : DecidableEq (BlockIndex security) := Classical.decEq _





def blockGenerating {Slot : Type*} [Fintype Slot] (security : ℕ)
    (law : FiniteDist (Slot → ActualControls.Palette security)) : MvPolynomial (ActualControls.Palette security) ℝ :=
  finiteGenerating law (fun output => ∏ slot, centeredFactor (FringeCertificate.uniformProfile security) (output slot))











theorem shiftEquiv_eq_of_cast (security : ℕ) (first second : ℤ)
    (hequal : (first : Root security) = (second : Root security)) :
    shiftEquiv security first = shiftEquiv security second := by
  unfold shiftEquiv
  rw [hequal]













def rootedResidues (security : ℕ) (permutation : Equiv.Perm (BodyIndex security))
    (latent : BodyIndex security → Edge security) : Vertex security → Root security :=
  fun vertex => (rootAt security permutation latent vertex : Root security)











end

end CurrentAFT.RootBackgroundPolynomial

end

section













/-! Independent actual root marginals reproduce the constructed background factors. -/

namespace CurrentAFT.RootIndependentBackground

open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls
  LocalReferenceEnergy ActualBlockFock ActualBlockMean ActualCycleMeanMGF
  BackgroundPolynomialEvaluation BackgroundEndpointLaw RootBackgroundPolynomial
  CycleRootExpansion CycleRootPolynomial BodyRootAverages PairQuadraticEvaluation
  PositiveFirstCoefficient LegPolynomialEvaluation BackgroundTranslations
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
  CycleRootExpansion.rootLaw CycleRootExpansion.rootReference

def tripleEquiv {Color : Type*} : (Fin 3 → Color) ≃ ((Color × Color) × Color) where
  toFun word := ((word 0, word 1), word 2)
  invFun word := ![word.1.1, word.1.2, word.2]
  left_inv word := by funext index; fin_cases index <;> rfl
  right_inv word := rfl

local instance finOneDecidableEq : DecidableEq (Fin 1) := Classical.decEq _
local instance finThreeDecidableEq : DecidableEq (Fin 3) := Classical.decEq _
local instance blockIndexDecidableEq (security : ℕ) : DecidableEq (BlockIndex security) := Classical.decEq _









































end

end CurrentAFT.RootIndependentBackground

end

section













/-! # Exact conversion between modular roots and the original integer blur -/
namespace CurrentAFT.RootReferenceExpectation
open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy FirstHistogram CycleRootExpansion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize

theorem rootReference_periodic_expectation (security : ℕ) (value : ℤ → ℝ)
    (hperiodic : ∀ first second : ℤ, (first : Root security) = (second : Root security) →
      value first = value second) :
    (rootReference security).expectation (fun root => value (root.val : ℤ)) =
      (publicBlurLaw security).expectation (fun pair => value (pair.2.val - pair.1.val)) := by
  unfold rootReference ProtectedCycle.differenceLaw
  rw [FiniteDist.expectation_map]
  have hvalue (pair : BlurSeed security) :
      value (((((pair.1 : ℤ) : Root security) - ((pair.2 : ℤ) : Root security)).val : ℕ) : ℤ) =
        value (pair.1.val - pair.2.val) := by
    apply hperiodic
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_sub]
  simp only [FiniteDist.expectation, Function.comp_apply, hvalue, publicBlurLaw,
    Fintype.sum_prod_type, FiniteDist.prod_weight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring

theorem publicBlur_seed_expectation (security : ℕ) (value : ℤ → ℝ) :
    (publicBlurLaw security).expectation (fun pair => value (pair.2.val - pair.1.val)) =
      (actualSeedLaw security).expectation (fun seed => value (actualBlur security seed)) := by
  simp only [FiniteDist.expectation, publicBlurLaw, actualSeedLaw, actualBlur,
    Fintype.sum_prod_type, FiniteDist.prod_weight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, FiniteDist.sum_one, one_mul]
  ring

theorem rootReference_seed_expectation (security : ℕ) (value : ℤ → ℝ)
    (hperiodic : ∀ first second : ℤ, (first : Root security) = (second : Root security) →
      value first = value second) :
    (rootReference security).expectation (fun root => value (root.val : ℤ)) =
      (actualSeedLaw security).expectation (fun seed => value (actualBlur security seed)) :=
  (rootReference_periodic_expectation security value hperiodic).trans (publicBlur_seed_expectation security value)

end
end CurrentAFT.RootReferenceExpectation

end


