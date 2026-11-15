-- Prove2me | Definitions.Def_InfoLossLAR_NativeBundle_07_Part_1
-- name    : InfoLossLAR_NativeBundle_07_Part_1
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T14:03:21.968987+00:00
-- url     : https://prove2.me/theorems/a2ef5715-829a-449e-9136-1828b3507612
-- title:
--   Grouped root kernels and coefficient-raising data
-- statement:
--   This package defines the grouped root updates and kernel products, local coefficient families and norms, and the finite coefficient-raising maps used by the current response construction. The primary and body source coordinates remain explicit in these finite families.
--
--   At fixed truncation order $R$, the families retain precisely the admissible arities
--   $$\mathcal A_R=\{(r,s)\in\mathbb N^2:r+s\le R\}.$$
--   The grouped operators act on the corresponding canonical coefficient fibers. This supplies the data interfaces for the subsequent raising and complete-response estimates; it does not assume the resulting error bounds.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0; native source modules lean/CurrentAFT/ActualBackgroundInverse.lean, lean/CurrentAFT/PairedRootPlacement.lean, lean/CurrentAFT/PairedRootDegrees.lean, lean/CurrentAFT/GroupedSourceNorm.lean, lean/CurrentAFT/GroupedRootUpdates.lean, lean/CurrentAFT/GroupedKernelNorm.lean, lean/CurrentAFT/GroupedKernelCanonical.lean, lean/CurrentAFT/GroupedKernelProduct.lean, lean/CurrentAFT/GroupedKernelProductImage.lean, lean/CurrentAFT/GroupedKernelProductFinite.lean, lean/CurrentAFT/IndependentPairedReference.lean, lean/CurrentAFT/LocalCoefficientFamily.lean, lean/CurrentAFT/LocalCoefficientEvaluation.lean, lean/CurrentAFT/NormalizedLocalPolynomial.lean, lean/CurrentAFT/IndependentReferenceEnergy.lean, lean/CurrentAFT/LocalCoefficientNorm.lean, lean/CurrentAFT/LocalRaisingFirst.lean, lean/CurrentAFT/LocalRaisingLinear.lean, lean/CurrentAFT/LocalRaisingNorm.lean, lean/CurrentAFT/LocalRaisingBounds.lean, lean/CurrentAFT/CoefficientHilbert.lean, lean/CurrentAFT/BackgroundEvaluation.lean, lean/CurrentAFT/BackgroundFirstEvaluation.lean, lean/CurrentAFT/CanonicalReconstruction.lean, lean/CurrentAFT/GlobalRaising.lean, lean/CurrentAFT/OrdinaryRaising.lean, lean/CurrentAFT/CompleteRaising.lean, lean/CurrentAFT/RaisingChannels.lean, lean/CurrentAFT/RaisingPatternBudget.lean, lean/CurrentAFT/RaisingPatternKernel.lean. Exact oracle-selected Definition bodies; split from the unaccepted NativeBundle_07 after its recorded server timeout. Source SHA256 49345d99ce11f428a2595033b3ecb2aa25cbefc57e416bb9a239d4a7e3bb00fe. Header-only transitive import reduction verified by Lean module-data and parser oracles; imported module closure and all non-import source bytes are unchanged. Alternate sparse native dependencies preserve the original non-import body bytes and all public types; this header-only packaging is recorded in sparse_live/manifest.json. Current source SHA256 b9d7b0d2615e402db3ffff53ffc386abc8f513dcafa5bc3ec7ff8d6e4a09e580.

import Definitions.Def_InfoLossLAR_NativeCompactPrefix_04











section














/-! Exact unit constant and a stable finite inverse for the actual averaged background. -/

namespace CurrentAFT.ActualBackgroundInverse

open AFT GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverse GradedInverseNorm
  Augmentation RoleProduct DiffuseProfiles ProposalPrimary ActualControls BackgroundRates BackgroundFamilies
  BackgroundLinear LegBackgroundFamilies BackgroundScalarZero BackgroundPopulationBounds ActualBackground
open Filter
open scoped BigOperators Classical Topology

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
  ActualBackground.background ActualBackground.fixedQueueBackground

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _













def inverseThreshold (order : ℕ) : ℕ :=
  max (max order numericalThreshold) (2 * order * (order + 1) ^ order * numericalThreshold)

theorem theta_le_half (security order : ℕ) (hsecurity : inverseThreshold order ≤ security) :
    stabilityConstant order / (Parameters.base security : ℝ) ^ 6 ≤ 1 / 2 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hbaseNat : 2 * order * (order + 1) ^ order * numericalThreshold ≤ Parameters.base security := by
    have h := (le_max_right (max order numericalThreshold) (2 * order * (order + 1) ^ order * numericalThreshold)).trans hsecurity
    unfold Parameters.base
    omega
  have hbase : 2 * stabilityConstant order ≤ (Parameters.base security : ℝ) := by
    simpa only [stabilityConstant, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using
      Nat.cast_le (α := ℝ).mpr hbaseNat
  have hpower : (Parameters.base security : ℝ) ≤ (Parameters.base security : ℝ) ^ 6 :=
    by simpa only [pow_one] using pow_le_pow_right₀ hb1 (show 1 ≤ 6 by omega)
  apply (div_le_iff₀ (pow_pos hb _)).mpr
  linarith





end

end CurrentAFT.ActualBackgroundInverse

end

section











/-! # The actual two root slots of each selected primary control -/
namespace CurrentAFT.PairedRootPlacement
open AFT ActualBlockFock TaggedSelection PairedOutputPlacement
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def selectedRootSlots (r s : ℕ) : Fin r ⊕ Fin s → Type
  | .inl _ => Fin 2
  | .inr _ => Fin 1

instance selectedRootSlotsFintype (r s : ℕ) (index : Fin r ⊕ Fin s) :
    Fintype (selectedRootSlots r s index) := by
  cases index with
  | inl _ => exact inferInstanceAs (Fintype (Fin 2))
  | inr _ => exact inferInstanceAs (Fintype (Fin 1))

/-- Primary root zero belongs to its compensator, and root one belongs
to its own leg attachment. The paired control is kept as one group. -/
def selectedRootEquiv (r s : ℕ) : Sigma (selectedRootSlots r s) ≃ RemovedLabel r s where
  toFun
    | ⟨.inl index, slot⟩ => Fin.cases (.inr (.inl index)) (fun _ => .inl index) slot
    | ⟨.inr index, _⟩ => .inr (.inr index)
  invFun
    | .inl index => ⟨.inl index, (1 : Fin 2)⟩
    | .inr (.inl index) => ⟨.inl index, (0 : Fin 2)⟩
    | .inr (.inr index) => ⟨.inr index, (0 : Fin 1)⟩
  left_inv := by
    rintro ⟨index | index, slot⟩
    · change Fin 2 at slot
      fin_cases slot <;> rfl
    · have hequal : slot = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst slot
      rfl
  right_inv := by rintro (index | (index | index)) <;> rfl

def allRootEquiv {security r s : ℕ} (selection : Selection security r s) :
    (Sigma (selectedRootSlots r s) ⊕ selection.kept) ≃ BlockIndex security :=
  (Equiv.sumCongr (selectedRootEquiv r s) (Equiv.refl _)).trans (blockEquiv selection)

@[simp] theorem allRoot_compensator {security r s : ℕ} (selection : Selection security r s) (index : Fin r) :
    allRootEquiv selection (.inl ⟨.inl index, (0 : Fin 2)⟩) = .inr (.inl (selection.compensator index)) := rfl

@[simp] theorem allRoot_attachment {security r s : ℕ} (selection : Selection security r s) (index : Fin r) :
    allRootEquiv selection (.inl ⟨.inl index, (1 : Fin 2)⟩) = .inl (selection.primary index) := rfl

@[simp] theorem allRoot_body {security r s : ℕ} (selection : Selection security r s) (index : Fin s) :
    allRootEquiv selection (.inl ⟨.inr index, (0 : Fin 1)⟩) = .inr (.inl (selection.body index)) := rfl

@[simp] theorem allRoot_kept {security r s : ℕ} (selection : Selection security r s) (index : selection.kept) :
    allRootEquiv selection (.inr index) = index.val := rfl

abbrev HitKept {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :=
  {index : selection.kept // index.val ∈ tagged}

def activeRootEmbedding {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    (Sigma (selectedRootSlots r s) ⊕ HitKept selection tagged) ↪ BlockIndex security :=
  (Function.Embedding.sumMap (Function.Embedding.refl _) (Function.Embedding.subtype _)).trans
    (allRootEquiv selection).toEmbedding

theorem tagged_in_active_range {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : BlockIndex security) (hindex : index ∈ tagged) :
    index ∈ Set.range (activeRootEmbedding selection tagged) := by
  obtain ⟨source, hsource⟩ := (allRootEquiv selection).surjective index
  cases source with
  | inl source => exact ⟨.inl source, hsource⟩
  | inr source =>
    have hsourceval : source.val = index := hsource
    exact ⟨.inr ⟨source, by rw [hsourceval]; exact hindex⟩, hsource⟩

def activeTagEmbedding {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    tagged ↪ (Sigma (selectedRootSlots r s) ⊕ HitKept selection tagged) where
  toFun index := Classical.choose (tagged_in_active_range selection tagged index.val index.property)
  inj' := by
    intro first second hequal
    have hfirst := Classical.choose_spec (tagged_in_active_range selection tagged first.val first.property)
    have hsecond := Classical.choose_spec (tagged_in_active_range selection tagged second.val second.property)
    apply Subtype.ext
    dsimp only at hequal
    rw [← hfirst, ← hsecond, hequal]

@[simp] theorem activeTag_image {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : tagged) :
    activeRootEmbedding selection tagged (activeTagEmbedding selection tagged index) = index.val :=
  Classical.choose_spec (tagged_in_active_range selection tagged index.val index.property)

abbrev ActiveGroup {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) := (Fin r ⊕ Fin s) ⊕ HitKept selection tagged

def groupRootSlots {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : ActiveGroup selection tagged → Type
  | .inl index => selectedRootSlots r s index
  | .inr _ => Fin 1

instance groupRootSlotsFintype {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : ActiveGroup selection tagged) :
    Fintype (groupRootSlots selection tagged index) := by
  cases index with
  | inl index => exact selectedRootSlotsFintype r s index
  | inr _ => exact inferInstanceAs (Fintype (Fin 1))

def singletonSlotsEquiv (Index : Type*) : Sigma (fun _ : Index => Fin 1) ≃ Index where
  toFun := Sigma.fst
  invFun index := ⟨index, 0⟩
  left_inv := by
    rintro ⟨index, slot⟩
    have hequal : slot = 0 := Subsingleton.elim _ _
    subst slot
    rfl
  right_inv _ := rfl

def activeSlotsEquiv {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    Sigma (groupRootSlots selection tagged) ≃
      (Sigma (selectedRootSlots r s) ⊕ HitKept selection tagged) :=
  (Equiv.sumSigmaDistrib (groupRootSlots selection tagged)).trans
    (Equiv.sumCongr (Equiv.refl _) (singletonSlotsEquiv (HitKept selection tagged)))

def rootEmbedding {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : Sigma (groupRootSlots selection tagged) ↪ BlockIndex security :=
  (activeSlotsEquiv selection tagged).toEmbedding.trans (activeRootEmbedding selection tagged)

def tagEmbedding {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : tagged ↪ Sigma (groupRootSlots selection tagged) :=
  (activeTagEmbedding selection tagged).trans (activeSlotsEquiv selection tagged).symm.toEmbedding

@[simp] theorem tag_image {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : tagged) :
    rootEmbedding selection tagged (tagEmbedding selection tagged index) = index.val := by
  change activeRootEmbedding selection tagged
    ((activeSlotsEquiv selection tagged) ((activeSlotsEquiv selection tagged).symm _)) = _
  rw [Equiv.apply_symm_apply, activeTag_image]

theorem hitKept_card_le {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : Fintype.card (HitKept selection tagged) ≤ tagged.card := by
  have h := Fintype.card_le_of_injective
    (fun index : HitKept selection tagged => (⟨index.val.val, index.property⟩ : tagged)) (by
      intro first second hequal
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun index : tagged => index.val) hequal)
  simpa only [Fintype.card_coe] using h

theorem activeGroup_card_le {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    Fintype.card (ActiveGroup selection tagged) ≤ r + s + tagged.card := by
  simp only [ActiveGroup, Fintype.card_sum, Fintype.card_fin]
  exact Nat.add_le_add_left (hitKept_card_le selection tagged) _

end
end CurrentAFT.PairedRootPlacement

end

section











/-! # Exact tag counts in the actual paired groups

A paired group with two tagged roots consumes two output degrees. All
other active groups consume at least one. These finite counts permit a
degree cutoff without summing all root subsets in a norm bound.
-/
namespace CurrentAFT.PairedRootDegrees
open AFT ActualBlockFock TaggedSelection PairedRootPlacement
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _

abbrev TaggedSlot {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged) :=
  {slot : groupRootSlots selection tagged group // rootEmbedding selection tagged ⟨group, slot⟩ ∈ tagged}

def physicalTagsEquiv {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    tagged ≃ {slot : Sigma (groupRootSlots selection tagged) // rootEmbedding selection tagged slot ∈ tagged} where
  toFun index := ⟨tagEmbedding selection tagged index, by rw [tag_image]; exact index.property⟩
  invFun slot := ⟨rootEmbedding selection tagged slot.val, slot.property⟩
  left_inv index := by apply Subtype.ext; exact tag_image selection tagged index
  right_inv slot := by
    apply Subtype.ext
    apply (rootEmbedding selection tagged).injective
    exact tag_image selection tagged ⟨rootEmbedding selection tagged slot.val, slot.property⟩

def groupedTagsEquiv {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    {slot : Sigma (groupRootSlots selection tagged) // rootEmbedding selection tagged slot ∈ tagged} ≃
      Sigma (TaggedSlot selection tagged) where
  toFun slot := ⟨slot.val.fst, ⟨slot.val.snd, slot.property⟩⟩
  invFun slot := ⟨⟨slot.fst, slot.snd.val⟩, slot.snd.property⟩
  left_inv := by rintro ⟨⟨group, slot⟩, hslot⟩; rfl
  right_inv := by rintro ⟨group, ⟨slot, hslot⟩⟩; rfl

def tagCount {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged) : ℕ :=
  Fintype.card (TaggedSlot selection tagged group)

theorem sum_tagCount {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    ∑ group, tagCount selection tagged group = tagged.card := by
  have h := Fintype.card_congr ((physicalTagsEquiv selection tagged).trans (groupedTagsEquiv selection tagged))
  simpa only [Fintype.card_coe, Fintype.card_sigma, tagCount] using h.symm

def minimumDegree {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged) : ℕ :=
  max 1 (tagCount selection tagged group)

theorem tags_le_degree {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    tagged.card ≤ ∑ group, minimumDegree selection tagged group := by
  rw [← sum_tagCount selection tagged]
  exact Finset.sum_le_sum (fun group _ => le_max_right 1 (tagCount selection tagged group))

theorem tagCount_le_slots {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged) :
    tagCount selection tagged group ≤ Fintype.card (groupRootSlots selection tagged group) :=
  Fintype.card_subtype_le _

theorem ordinary_minimumDegree {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin s) :
    minimumDegree selection tagged (.inl (.inr index)) = 1 := by
  have h := tagCount_le_slots selection tagged (.inl (.inr index))
  change tagCount selection tagged (.inl (.inr index)) ≤ Fintype.card (Fin 1) at h
  norm_num only [Fintype.card_fin] at h
  exact max_eq_left h

theorem kept_minimumDegree {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : HitKept selection tagged) :
    minimumDegree selection tagged (.inr index) = 1 := by
  have h := tagCount_le_slots selection tagged (.inr index)
  change tagCount selection tagged (.inr index) ≤ Fintype.card (Fin 1) at h
  norm_num only [Fintype.card_fin] at h
  exact max_eq_left h

theorem primary_minimumDegree_le_two {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin r) :
    minimumDegree selection tagged (.inl (.inl index)) ≤ 2 := by
  have h := tagCount_le_slots selection tagged (.inl (.inl index))
  change tagCount selection tagged (.inl (.inl index)) ≤ Fintype.card (Fin 2) at h
  norm_num only [Fintype.card_fin] at h
  exact max_le (by omega) h

theorem primary_tagCount {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin r) :
    tagCount selection tagged (.inl (.inl index)) =
      (if Sum.inr (Sum.inl (selection.compensator index)) ∈ tagged then 1 else 0) +
      (if Sum.inl (selection.primary index) ∈ tagged then 1 else 0) := by
  unfold tagCount TaggedSlot
  rw [Fintype.card_subtype]
  change (Finset.univ.filter (fun slot : Fin 2 =>
    rootEmbedding selection tagged ⟨.inl (.inl index), slot⟩ ∈ tagged)).card = _
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_two]
  rfl

theorem primary_minimumDegree_two_requires_attachment {security r s : ℕ}
    (selection : Selection security r s) (tagged : Finset (BlockIndex security)) (index : Fin r)
    (hdegree : minimumDegree selection tagged (.inl (.inl index)) = 2) :
    Sum.inl (selection.primary index) ∈ tagged := by
  have hcount := primary_tagCount selection tagged index
  unfold minimumDegree at hdegree
  by_contra hnot
  rw [if_neg hnot] at hcount
  split_ifs at hcount <;> omega

end
end CurrentAFT.PairedRootDegrees

end

section










/-!
# Exact regrouping of joint root and control inputs

The root density and the public control kernel remain joint functions.
Grouping each physical channel's roots with its one control is an exact
Hilbert isometry, including channels with two roots or no control.
-/
namespace CurrentAFT.GroupedSourceNorm
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _

variable {Group Root : Type*} [Fintype Group] [Fintype Root]
  (RootSlots ControlInput : Group → Type*)
  [∀ group, Fintype (RootSlots group)] [∀ group, Fintype (ControlInput group)]

abbrev GroupWord := (group : Group) → ((RootSlots group → Root) × ControlInput group)
abbrev GlobalWord := (Sigma RootSlots → Root) × ((group : Group) → ControlInput group)

def wordEquiv : GlobalWord (Root := Root) RootSlots ControlInput ≃
    GroupWord (Root := Root) RootSlots ControlInput where
  toFun word group := (fun slot => word.1 ⟨group, slot⟩, word.2 group)
  invFun word := (fun slot => (word slot.fst).1 slot.snd, fun group => (word group).2)
  left_inv word := by cases word; rfl
  right_inv _ := rfl

def groupReference (root : FiniteDist Root) (control : (group : Group) → FiniteDist (ControlInput group))
    (group : Group) : FiniteDist ((RootSlots group → Root) × ControlInput group) :=
  (FiniteDist.independent (fun _ : RootSlots group => root)).prod (control group)

def globalReference (root : FiniteDist Root) (control : (group : Group) → FiniteDist (ControlInput group)) :
    FiniteDist (GlobalWord (Root := Root) RootSlots ControlInput) :=
  (FiniteDist.independent (fun _ : Sigma RootSlots => root)).prod (FiniteDist.dependentIndependent control)

/-- Fubini and coordinate regrouping preserve the entire squared norm. -/
theorem group_energy (root : FiniteDist Root) (control : (group : Group) → FiniteDist (ControlInput group))
    (input : GlobalWord (Root := Root) RootSlots ControlInput → ℝ) :
    (FiniteDist.dependentIndependent (groupReference RootSlots ControlInput root control)).l2Sq
      (input ∘ (wordEquiv RootSlots ControlInput).symm) =
        (globalReference RootSlots ControlInput root control).l2Sq input := by
  unfold FiniteDist.l2Sq FiniteDist.expectation
  rw [← (wordEquiv RootSlots ControlInput).sum_comp]
  apply Finset.sum_congr rfl
  intro word _
  simp only [Function.comp_apply, FiniteDist.dependentIndependent_weight,
    groupReference, globalReference, FiniteDist.prod_weight, FiniteDist.independent,
    wordEquiv, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Fintype.prod_sigma, Finset.prod_mul_distrib]

/-- Independence is used only between the whole root word and the whole
control word. Neither of their densities is required to factor. -/
theorem product_input_energy (root : FiniteDist Root)
    (control : (group : Group) → FiniteDist (ControlInput group))
    (rootDensity : (Sigma RootSlots → Root) → ℝ)
    (controlKernel : ((group : Group) → ControlInput group) → ℝ) :
    (FiniteDist.dependentIndependent (groupReference RootSlots ControlInput root control)).l2Sq
      (fun word => rootDensity (fun slot => (word slot.fst).1 slot.snd) * controlKernel (fun group => (word group).2)) =
      (FiniteDist.independent (fun _ : Sigma RootSlots => root)).l2Sq rootDensity *
        (FiniteDist.dependentIndependent control).l2Sq controlKernel := by
  change (FiniteDist.dependentIndependent (groupReference RootSlots ControlInput root control)).l2Sq
    ((fun word : GlobalWord (Root := Root) RootSlots ControlInput => rootDensity word.1 * controlKernel word.2) ∘
      (wordEquiv RootSlots ControlInput).symm) = _
  rw [group_energy]
  simp only [globalReference, FiniteDist.l2Sq, FiniteDist.expectation, FiniteDist.prod_weight,
    Fintype.sum_prod_type, mul_pow]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro roots _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro controls _
  ring

/-- Unused independent root coordinates are integrated exactly. This
allows a selected group to retain both root slots even when just one is
tagged, with the original joint selected-root norm unchanged. -/
theorem embedded_product_input_energy {RootLabel : Type*} [Fintype RootLabel]
    (root : FiniteDist Root) (control : (group : Group) → FiniteDist (ControlInput group))
    (labels : RootLabel ↪ Sigma RootSlots) (rootDensity : (RootLabel → Root) → ℝ)
    (controlKernel : ((group : Group) → ControlInput group) → ℝ) :
    (FiniteDist.dependentIndependent (groupReference RootSlots ControlInput root control)).l2Sq
      (fun word => rootDensity (fun label => (word (labels label).fst).1 (labels label).snd) *
        controlKernel (fun group => (word group).2)) =
      (FiniteDist.independent (fun _ : RootLabel => root)).l2Sq rootDensity *
        (FiniteDist.dependentIndependent control).l2Sq controlKernel := by
  have h := product_input_energy RootSlots ControlInput root control
    (fun roots => rootDensity (roots ∘ labels)) controlKernel
  dsimp only [Function.comp_def] at h
  rw [h]
  apply congrArg (fun value => value * (FiniteDist.dependentIndependent control).l2Sq controlKernel)
  exact CanonicalMoments.independent_embedding_expectation root labels (fun roots => rootDensity roots ^ 2)

end
end CurrentAFT.GroupedSourceNorm

end

section








/-! # Exact coordinate updates before and after root/control grouping -/
namespace CurrentAFT.GroupedRootUpdates
open AFT GroupedSourceNorm
open scoped Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
local instance classicalSigmaDecidableEq {Index : Type*} {Fiber : Index → Type*} :
    DecidableEq (Sigma Fiber) := Classical.decEq _

variable {Group Root : Type*} [DecidableEq Group] (Slots Control : Group → Type*)
  [∀ group, DecidableEq (Slots group)]

def roots (word : (group : Group) → (Slots group → Root) × Control group) : Sigma Slots → Root :=
  fun slot => (word slot.fst).1 slot.snd

def controls (word : (group : Group) → (Slots group → Root) × Control group) : (group : Group) → Control group :=
  fun group => (word group).2

def updateRoot (word : (group : Group) → (Slots group → Root) × Control group)
    (group : Group) (slot : Slots group) (value : Root) :=
  Function.update word group (Function.update (word group).1 slot value, (word group).2)







end
end CurrentAFT.GroupedRootUpdates

end

section










/-!
# Mixed-alphabet grouped joint kernels and exact flattening

The entire joint function is retained through the coordinate equivalence.
Reindexing is isometric and the genuine separate symmetrization contracts;
neither operation introduces a color-alphabet or tensor-rank factor.
-/

namespace CurrentAFT.GroupedKernelNorm

open AFT ControlCoordinates ControlProduct ControlNorm
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _

variable {Group Primary Body : Type*} [Fintype Group] [Fintype Primary] [Fintype Body]
  (PrimarySlots BodySlots : Group → Type*)
  [∀ group, Fintype (PrimarySlots group)] [∀ group, Fintype (BodySlots group)]

abbrev GroupWord := (group : Group) →
  ((PrimarySlots group → Primary) × (BodySlots group → Body))

def wordEquiv :
    ((Sigma PrimarySlots → Primary) × (Sigma BodySlots → Body)) ≃
      GroupWord (Primary := Primary) (Body := Body) PrimarySlots BodySlots where
  toFun word group := (fun slot => word.1 ⟨group, slot⟩, fun slot => word.2 ⟨group, slot⟩)
  invFun word := (fun slot => (word slot.1).1 slot.2, fun slot => (word slot.1).2 slot.2)
  left_inv word := by cases word; rfl
  right_inv word := by rfl

def localReference (primary : FiniteDist Primary) (body : FiniteDist Body) (group : Group) :
    FiniteDist ((PrimarySlots group → Primary) × (BodySlots group → Body)) :=
  (FiniteDist.independent (fun _ : PrimarySlots group => primary)).prod
    (FiniteDist.independent (fun _ : BodySlots group => body))

def flatten (kernel : GroupWord (Primary := Primary) (Body := Body) PrimarySlots BodySlots → ℝ) :
    Kernel (Primary := Primary) (Body := Body) (Sigma PrimarySlots) (Sigma BodySlots) :=
  fun colors centers => kernel (wordEquiv PrimarySlots BodySlots (colors, centers))

/-- Genuine finite Fubini for both output alphabets at once, on an
arbitrary joint function of all grouped outputs. -/
theorem flatten_energy (primary : FiniteDist Primary) (body : FiniteDist Body)
    (kernel : GroupWord (Primary := Primary) (Body := Body) PrimarySlots BodySlots → ℝ) :
    blockEnergy primary body (flatten PrimarySlots BodySlots kernel) =
      (FiniteDist.dependentIndependent (localReference PrimarySlots BodySlots primary body)).l2Sq kernel := by
  unfold blockEnergy FiniteDist.l2Sq FiniteDist.expectation
  rw [← (wordEquiv (Primary := Primary) (Body := Body) PrimarySlots BodySlots).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro word _
  simp only [FiniteDist.prod_weight, FiniteDist.independent, wordEquiv, Equiv.coe_fn_symm_mk,
    flatten, Equiv.coe_fn_mk, FiniteDist.dependentIndependent_weight,
    localReference, Fintype.prod_sigma]
  rw [Finset.prod_mul_distrib]



variable {PrimaryTarget BodyTarget : Type*} [Fintype PrimaryTarget] [Fintype BodyTarget]

def canonicalize (primaryEquiv : Sigma PrimarySlots ≃ PrimaryTarget)
    (bodyEquiv : Sigma BodySlots ≃ BodyTarget)
    (kernel : GroupWord (Primary := Primary) (Body := Body) PrimarySlots BodySlots → ℝ) :
    Kernel (Primary := Primary) (Body := Body) PrimaryTarget BodyTarget :=
  symmetrize (reindexKernel primaryEquiv bodyEquiv (flatten PrimarySlots BodySlots kernel))

/-- The complete joint output can be numbered and symmetrized with
operator norm one, independently of both alphabet sizes and all ranks. -/
theorem canonicalize_energy_le (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryEquiv : Sigma PrimarySlots ≃ PrimaryTarget) (bodyEquiv : Sigma BodySlots ≃ BodyTarget)
    (kernel : GroupWord (Primary := Primary) (Body := Body) PrimarySlots BodySlots → ℝ) :
    blockEnergy primary body (canonicalize PrimarySlots BodySlots primaryEquiv bodyEquiv kernel) ≤
      (FiniteDist.dependentIndependent (localReference PrimarySlots BodySlots primary body)).l2Sq kernel := by
  apply (blockEnergy_symmetrize_le primary body _).trans_eq
  rw [blockEnergy_reindex, flatten_energy]



variable {Input : Group → Type*} [∀ group, Fintype (Input group)]

/-- Tensorization followed by actual mixed flattening and symmetrization,
for arbitrary joint input kernels and different local input alphabets. -/
theorem canonicalize_tensor_energy_le (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryEquiv : Sigma PrimarySlots ≃ PrimaryTarget) (bodyEquiv : Sigma BodySlots ≃ BodyTarget)
    (input : ∀ group, FiniteDist (Input group))
    (channel : ∀ group, (Input group → ℝ) →ₗ[ℝ]
      (((PrimarySlots group → Primary) × (BodySlots group → Body)) → ℝ))
    (bound : Group → ℝ)
    (hchannel : ∀ group score,
      (localReference PrimarySlots BodySlots primary body group).l2Sq (channel group score) ≤
        bound group ^ 2 * (input group).l2Sq score)
    (kernel : ((group : Group) → Input group) → ℝ) :
    blockEnergy primary body (canonicalize PrimarySlots BodySlots primaryEquiv bodyEquiv
      (DependentTensorChannel.apply channel kernel)) ≤
      (∏ group, bound group ^ 2) * (FiniteDist.dependentIndependent input).l2Sq kernel :=
  (canonicalize_energy_le PrimarySlots BodySlots primary body primaryEquiv bodyEquiv _).trans
    (DependentTensorChannel.energy_le input _ channel bound hchannel kernel)

end
end CurrentAFT.GroupedKernelNorm

end

section








/-! # Canonical mixed fibers of arbitrary joint grouped tensor channels -/

namespace CurrentAFT.GroupedKernelNorm
open AFT ControlCoordinates ControlProduct ControlNorm
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
local instance canonicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Group Primary Body : Type*} [Fintype Group] [Fintype Primary] [Fintype Body]
  (PrimarySlots BodySlots : Group → Type*)
  [∀ group, Fintype (PrimarySlots group)] [∀ group, Fintype (BodySlots group)]
  {Input : Group → Type*} [∀ group, Fintype (Input group)]

 theorem sigma_update_same {Index Color : Type*} {Slots : Index → Type*}
    (word : Sigma Slots → Color) (group : Index) (slot : Slots group) (color : Color) :
    (fun part : Slots group => Function.update word ⟨group, slot⟩ color ⟨group, part⟩) =
      Function.update (fun part : Slots group => word ⟨group, part⟩) slot color := by
  funext part
  by_cases hequal : part = slot
  · subst part; simp
  · simp only [Function.update_of_ne hequal, Function.update_of_ne (show
      (⟨group, part⟩ : Sigma Slots) ≠ ⟨group, slot⟩ from fun h =>
        hequal (eq_of_heq (Sigma.mk.inj_iff.mp h).2))]

 theorem sigma_update_other {Index Color : Type*} {Slots : Index → Type*}
    (word : Sigma Slots → Color) (group other : Index) (hne : other ≠ group)
    (slot : Slots group) (color : Color) :
    (fun part : Slots other => Function.update word ⟨group, slot⟩ color ⟨other, part⟩) =
      (fun part : Slots other => word ⟨other, part⟩) := by
  funext part
  apply Function.update_of_ne
  intro hequal
  exact hne (congrArg Sigma.fst hequal)

omit [Fintype Body] [∀ group, Fintype (PrimarySlots group)]
  [∀ group, Fintype (BodySlots group)] in
theorem flatten_tensor_primaryCentered (primary : FiniteDist Primary)
    (channel : ∀ group, (Input group → ℝ) →ₗ[ℝ]
      (((PrimarySlots group → Primary) × (BodySlots group → Body)) → ℝ))
    (hcentered : ∀ group score, PrimaryCentered primary
      (fun colors centers => channel group score (colors, centers)))
    (kernel : ((group : Group) → Input group) → ℝ) :
    PrimaryCentered primary
      (flatten PrimarySlots BodySlots (DependentTensorChannel.apply channel kernel)) := by
  intro selected colors centers
  rcases selected with ⟨group, slot⟩
  simp only [flatten, wordEquiv, Equiv.coe_fn_mk, DependentTensorChannel.apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro inputs _
  have hprod (color : Primary) :
      (∏ other, channel other (Pi.single (inputs other) 1)
        ((fun part => Function.update colors ⟨group, slot⟩ color ⟨other, part⟩),
          (fun part => centers ⟨other, part⟩))) =
      channel group (Pi.single (inputs group) 1)
        (Function.update (fun part => colors ⟨group, part⟩) slot color,
          fun part => centers ⟨group, part⟩) *
      ∏ other ∈ (Finset.univ : Finset Group).erase group,
        channel other (Pi.single (inputs other) 1)
          ((fun part => colors ⟨other, part⟩), (fun part => centers ⟨other, part⟩)) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ group), sigma_update_same]
    congr 1
    apply Finset.prod_congr rfl
    intro other hother
    rw [sigma_update_other colors group other (Finset.mem_erase.mp hother).1 slot color]
  simp only [hprod]
  calc
    _ = (kernel inputs * ∏ other ∈ (Finset.univ : Finset Group).erase group,
        channel other (Pi.single (inputs other) 1)
          ((fun part => colors ⟨other, part⟩), (fun part => centers ⟨other, part⟩))) *
        ∑ color, primary.weight color * channel group (Pi.single (inputs group) 1)
          (Function.update (fun part => colors ⟨group, part⟩) slot color,
            fun part => centers ⟨group, part⟩) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro color _
      ring
    _ = 0 := by rw [hcentered group (Pi.single (inputs group) 1) slot, mul_zero]

omit [Fintype Primary] [∀ group, Fintype (PrimarySlots group)]
  [∀ group, Fintype (BodySlots group)] in
theorem flatten_tensor_bodyCentered (body : FiniteDist Body)
    (channel : ∀ group, (Input group → ℝ) →ₗ[ℝ]
      (((PrimarySlots group → Primary) × (BodySlots group → Body)) → ℝ))
    (hcentered : ∀ group score, BodyCentered body
      (fun colors centers => channel group score (colors, centers)))
    (kernel : ((group : Group) → Input group) → ℝ) :
    BodyCentered body
      (flatten PrimarySlots BodySlots (DependentTensorChannel.apply channel kernel)) := by
  intro selected colors centers
  rcases selected with ⟨group, slot⟩
  simp only [flatten, wordEquiv, Equiv.coe_fn_mk, DependentTensorChannel.apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro inputs _
  have hprod (center : Body) :
      (∏ other, channel other (Pi.single (inputs other) 1)
        ((fun part => colors ⟨other, part⟩),
          fun part => Function.update centers ⟨group, slot⟩ center ⟨other, part⟩)) =
      channel group (Pi.single (inputs group) 1)
        ((fun part => colors ⟨group, part⟩),
          Function.update (fun part => centers ⟨group, part⟩) slot center) *
      ∏ other ∈ (Finset.univ : Finset Group).erase group,
        channel other (Pi.single (inputs other) 1)
          ((fun part => colors ⟨other, part⟩), (fun part => centers ⟨other, part⟩)) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ group), sigma_update_same]
    congr 1
    apply Finset.prod_congr rfl
    intro other hother
    rw [sigma_update_other centers group other (Finset.mem_erase.mp hother).1 slot center]
  simp only [hprod]
  calc
    _ = (kernel inputs * ∏ other ∈ (Finset.univ : Finset Group).erase group,
        channel other (Pi.single (inputs other) 1)
          ((fun part => colors ⟨other, part⟩), (fun part => centers ⟨other, part⟩))) *
        ∑ center, body.weight center * channel group (Pi.single (inputs group) 1)
          ((fun part => colors ⟨group, part⟩),
            Function.update (fun part => centers ⟨group, part⟩) slot center) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro center _
      ring
    _ = 0 := by rw [hcentered group (Pi.single (inputs group) 1) slot, mul_zero]

def canonicalTensor (primary : FiniteDist Primary) (body : FiniteDist Body) {r s : ℕ}
    (primaryEquiv : Sigma PrimarySlots ≃ Fin r) (bodyEquiv : Sigma BodySlots ≃ Fin s)
    (channel : ∀ group, (Input group → ℝ) →ₗ[ℝ]
      (((PrimarySlots group → Primary) × (BodySlots group → Body)) → ℝ))
    (hprimary : ∀ group score, PrimaryCentered primary
      (fun colors centers => channel group score (colors, centers)))
    (hbody : ∀ group score, BodyCentered body
      (fun colors centers => channel group score (colors, centers)))
    (kernel : ((group : Group) → Input group) → ℝ) : canonicalKernels primary body r s := by
  have hflat : flatten PrimarySlots BodySlots (DependentTensorChannel.apply channel kernel) ∈
      centeredKernelSpace primary body :=
    ⟨flatten_tensor_primaryCentered PrimarySlots BodySlots primary channel hprimary kernel,
      flatten_tensor_bodyCentered PrimarySlots BodySlots body channel hbody kernel⟩
  have hcanonical := symmetrize_centered primary body _
    (reindexKernel_centered primary body primaryEquiv bodyEquiv _ hflat)
  refine ⟨canonicalize PrimarySlots BodySlots primaryEquiv bodyEquiv
    (DependentTensorChannel.apply channel kernel), hcanonical.1, hcanonical.2, ?_⟩
  intro primaryOrder bodyOrder colors centers
  change symmetrize _ (colors ∘ primaryOrder) (centers ∘ bodyOrder) =
    symmetrize _ colors centers
  rw [symmetrize_primary_permutation, symmetrize_body_permutation]

end
end CurrentAFT.GroupedKernelNorm

end

section










/-! # Finite arity patterns of the genuine canonical coefficient product -/

namespace CurrentAFT.GroupedKernelProduct
open AFT ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

def sigmaHeadEquiv {count : ℕ} (Slots : Fin (count + 1) → Type*) :
    Sigma Slots ≃ (Slots 0 ⊕ Sigma (fun index : Fin count => Slots index.succ)) where
  toFun word := Fin.cases (fun value => Sum.inl value)
    (fun index value => Sum.inr ⟨index, value⟩) word.1 word.2
  invFun word := Sum.elim (fun value => ⟨0, value⟩)
    (fun tail => ⟨tail.1.succ, tail.2⟩) word
  left_inv word := by
    rcases word with ⟨index, value⟩
    cases index using Fin.cases <;> rfl
  right_inv word := by cases word <;> rfl

def slotsEquiv : (count : ℕ) → (sizes : Fin count → ℕ) →
    (Sigma (fun index => Fin (sizes index))) ≃ Fin (∑ index, sizes index)
  | 0, sizes => (Equiv.equivOfIsEmpty _ (Fin 0)).trans (finCongr (by simp))
  | count + 1, sizes =>
      (sigmaHeadEquiv (fun index => Fin (sizes index))).trans
        ((Equiv.sumCongr (Equiv.refl (Fin (sizes 0)))
          (slotsEquiv count (fun index => sizes index.succ))).trans
            (finSumFinEquiv.trans (finCongr (Fin.sum_univ_succ sizes).symm)))

/-- Only the finite arity choices are expanded. Colors remain arguments
of one joint kernel throughout the later Hilbert contraction. -/
theorem product_family_arity_expansion {Group : Type*} [Fintype Group]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (families : Group → KernelFamily primary body order) :
    (∏ group, families group) =
      ∑ pattern : Group → TruncatedArity order,
        ∏ group, Pi.single (pattern group) (families group (pattern group)) := by
  conv_lhs => arg 2; ext group; rw [← Finset.univ_sum_single (families group)]
  exact Fintype.prod_sum _

def embedArity (order r s : ℕ) (hdegree : r + s ≤ order) : TruncatedArity order :=
  ⟨(⟨r, by omega⟩, ⟨s, by omega⟩), hdegree⟩

def embed (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    {r s : ℕ} (hdegree : r + s ≤ order) (kernel : canonicalKernels primary body r s) :
    KernelFamily primary body order := Pi.single (embedArity order r s hdegree) kernel

theorem embed_transport (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    {r s r' s' : ℕ} (hr : r = r') (hs : s = s')
    (hdegree : r + s ≤ order) (hdegree' : r' + s' ≤ order)
    (kernel : canonicalKernels primary body r s) :
    embed primary body order hdegree' (transportKernel primary body hr hs kernel) =
      embed primary body order hdegree kernel := by
  subst r'; subst s'; rfl

theorem embed_mul (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    {r s r' s' : ℕ} (hfirst : r + s ≤ order) (hsecond : r' + s' ≤ order)
    (hdegree : (r + r') + (s + s') ≤ order)
    (first : canonicalKernels primary body r s) (second : canonicalKernels primary body r' s') :
    embed primary body order hfirst first * embed primary body order hsecond second =
      embed primary body order hdegree (homogeneousProduct primary body first second) := by
  change familyProduct primary body order
    (Pi.single (embedArity order r s hfirst) first)
    (Pi.single (embedArity order r' s' hsecond) second) = _
  exact familyProduct_single_retained primary body order
    (embedArity order r s hfirst) (embedArity order r' s' hsecond) first second hdegree

/-- Ordered iterated homogeneous products, with only the true slot-count
equalities transported between successive finite fibers. -/
def iteratedProduct (primary : FiniteDist Primary) (body : FiniteDist Body) :
    (count : ℕ) → (r s : Fin count → ℕ) →
    ((index : Fin count) → canonicalKernels primary body (r index) (s index)) →
      canonicalKernels primary body (∑ index, r index) (∑ index, s index)
  | 0, _, _, _ => scalarUnit primary body
  | count + 1, r, s, kernels =>
      transportKernel primary body (Fin.sum_univ_succ r).symm (Fin.sum_univ_succ s).symm
        (homogeneousProduct primary body (kernels 0)
          (iteratedProduct primary body count (fun index => r index.succ)
            (fun index => s index.succ) (fun index => kernels index.succ)))

theorem product_embed (primary : FiniteDist Primary) (body : FiniteDist Body) (order count : ℕ)
    (r s : Fin count → ℕ)
    (kernels : (index : Fin count) → canonicalKernels primary body (r index) (s index))
    (hdegree : (∑ index, r index) + (∑ index, s index) ≤ order)
    (hlocal : ∀ index, r index + s index ≤ order) :
    (∏ index, embed primary body order (hlocal index) (kernels index)) =
      embed primary body order hdegree (iteratedProduct primary body count r s kernels) := by
  induction count with
  | zero =>
    simp only [Fin.prod_univ_zero]
    rfl
  | succ count ih =>
    have htail : (∑ index : Fin count, r index.succ) + (∑ index : Fin count, s index.succ) ≤ order := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hdegree
      omega
    rw [Fin.prod_univ_succ, ih (fun index => r index.succ) (fun index => s index.succ)
      (fun index => kernels index.succ) htail (fun index => hlocal index.succ)]
    conv_rhs => rw [iteratedProduct]
    rw [embed_transport primary body order _ _
      (show (r 0 + ∑ index : Fin count, r index.succ) + (s 0 + ∑ index : Fin count, s index.succ) ≤ order by
        simpa only [Fin.sum_univ_succ] using hdegree) hdegree]
    exact embed_mul primary body order _ _ _ _ _

end
end CurrentAFT.GroupedKernelProduct

end

section








/-! # Exact grouped-kernel identity of iterated homogeneous products -/
namespace CurrentAFT.GroupedKernelProduct
open AFT ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GroupedKernelNorm
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
local instance productImageFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance productImageSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

def rawProduct (count : ℕ) (r s : Fin count → ℕ)
    (kernels : (index : Fin count) → DensityKernel (Primary := Primary) (Body := Body) (r index) (s index)) :
    DensityKernel (Primary := Primary) (Body := Body) (∑ index, r index) (∑ index, s index) :=
  reindexKernel (slotsEquiv count r) (slotsEquiv count s)
    (flatten (fun index => Fin (r index)) (fun index => Fin (s index))
      (fun word => ∏ index, kernels index (word index).1 (word index).2))

omit [Fintype Primary] [Fintype Body] in
theorem rawProduct_succ (count : ℕ) (r s : Fin (count + 1) → ℕ)
    (kernels : (index : Fin (count + 1)) → DensityKernel (Primary := Primary) (Body := Body) (r index) (s index)) :
    rawProduct (count + 1) r s kernels =
      reindexKernel (finCongr (Fin.sum_univ_succ r).symm) (finCongr (Fin.sum_univ_succ s).symm)
        (finDisjointTensor (kernels 0)
          (rawProduct count (fun index => r index.succ) (fun index => s index.succ)
            (fun index => kernels index.succ))) := by
  funext colors centers
  simp only [rawProduct, reindexKernel, flatten, wordEquiv, Equiv.coe_fn_mk,
    Fin.prod_univ_succ, slotsEquiv, sigmaHeadEquiv, Equiv.trans_apply,
    Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.refl_apply, Fin.cases_zero, Fin.cases_succ,
    finDisjointTensor, disjointTensor, Function.comp_def]

/-- The iterated star product equals one symmetrization of the whole
disjoint product, with every input and output coordinate retained. -/
theorem iteratedProduct_val (primary : FiniteDist Primary) (body : FiniteDist Body)
    (count : ℕ) (r s : Fin count → ℕ)
    (kernels : (index : Fin count) → canonicalKernels primary body (r index) (s index)) :
    (iteratedProduct primary body count r s kernels).val =
      symmetrize (rawProduct count r s (fun index => (kernels index).val)) := by
  induction count with
  | zero =>
    have hraw : rawProduct 0 r s (fun index => (kernels index).val) = fun _ _ => 1 := by
      funext colors centers
      simp only [rawProduct, reindexKernel, flatten, wordEquiv, Equiv.coe_fn_mk, Fin.prod_univ_zero]
    rw [hraw, symmetrize_of_symmetric _ (by intros; rfl)]
    rfl
  | succ count ih =>
    rw [iteratedProduct, transportKernel_val]
    change reindexKernel _ _ (symmetrize (finDisjointTensor (kernels 0).val
      (iteratedProduct primary body count (fun index => r index.succ)
        (fun index => s index.succ) (fun index => kernels index.succ)).val)) = _
    rw [ih, ControlCoherence.symmetrized_fin_tensor_second, reindexKernel_symmetrize, rawProduct_succ]

end
end CurrentAFT.GroupedKernelProduct

end

section








/-! # Arbitrary finite group labels for the actual iterated star product -/
namespace CurrentAFT.GroupedKernelProduct
open AFT ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GroupedKernelNorm
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
local instance productFiniteFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance productFiniteSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _

variable {Primary Body Group : Type*} [Fintype Primary] [Fintype Body] [Fintype Group]

def finiteProduct (primary : FiniteDist Primary) (body : FiniteDist Body)
    (r s : Group → ℕ) (kernels : (group : Group) → canonicalKernels primary body (r group) (s group)) :
    canonicalKernels primary body (∑ group, r group) (∑ group, s group) :=
  transportKernel primary body ((Fintype.equivFin Group).symm.sum_comp r)
    ((Fintype.equivFin Group).symm.sum_comp s)
    (iteratedProduct primary body (Fintype.card Group)
      (fun index => r ((Fintype.equivFin Group).symm index))
      (fun index => s ((Fintype.equivFin Group).symm index))
      (fun index => kernels ((Fintype.equivFin Group).symm index)))

def finiteSlotsEquiv (sizes : Group → ℕ) :
    Sigma (fun group => Fin (sizes group)) ≃ Fin (∑ group, sizes group) :=
  (Equiv.sigmaCongrLeft (β := fun group => Fin (sizes group)) (Fintype.equivFin Group).symm).symm.trans
    ((slotsEquiv (Fintype.card Group) (fun index => sizes ((Fintype.equivFin Group).symm index))).trans
      (finCongr ((Fintype.equivFin Group).symm.sum_comp sizes)))

theorem finite_product_embed (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (r s : Group → ℕ) (kernels : (group : Group) → canonicalKernels primary body (r group) (s group))
    (hdegree : (∑ group, r group) + (∑ group, s group) ≤ order)
    (hlocal : ∀ group, r group + s group ≤ order) :
    (∏ group, embed primary body order (hlocal group) (kernels group)) =
      embed primary body order hdegree (finiteProduct primary body r s kernels) := by
  unfold finiteProduct
  rw [embed_transport primary body order _ _
    (show (∑ index, r ((Fintype.equivFin Group).symm index)) +
        (∑ index, s ((Fintype.equivFin Group).symm index)) ≤ order by
      simpa only [Equiv.sum_comp] using hdegree) hdegree]
  rw [← product_embed primary body order (Fintype.card Group) _ _ _ _
    (fun index => hlocal ((Fintype.equivFin Group).symm index))]
  exact ((Fintype.equivFin Group).symm.prod_comp
    (fun group => embed primary body order (hlocal group) (kernels group))).symm

theorem finiteProduct_val (primary : FiniteDist Primary) (body : FiniteDist Body)
    (r s : Group → ℕ) (kernels : (group : Group) → canonicalKernels primary body (r group) (s group)) :
    (finiteProduct primary body r s kernels).val =
      canonicalize (fun group => Fin (r group)) (fun group => Fin (s group))
        (finiteSlotsEquiv r) (finiteSlotsEquiv s)
        (fun word => ∏ group, (kernels group).val (word group).1 (word group).2) := by
  let e := (Fintype.equivFin Group).symm
  let ep := Equiv.sigmaCongrLeft (β := fun group => Fin (r group)) e
  let eb := Equiv.sigmaCongrLeft (β := fun group => Fin (s group)) e
  have hflatten :
      flatten (fun index => Fin (r (e index))) (fun index => Fin (s (e index)))
        (fun word => ∏ index, (kernels (e index)).val (word index).1 (word index).2) =
      reindexKernel ep.symm eb.symm
        (flatten (fun group => Fin (r group)) (fun group => Fin (s group))
          (fun word => ∏ group, (kernels group).val (word group).1 (word group).2)) := by
    funext colors centers
    have h := e.prod_comp (fun group => (kernels group).val
      (fun slot => colors (ep.symm ⟨group, slot⟩)) (fun slot => centers (eb.symm ⟨group, slot⟩)))
    change (∏ index, (kernels (e index)).val (fun slot => colors ⟨index, slot⟩)
      (fun slot => centers ⟨index, slot⟩)) = _
    apply Eq.trans ?_ h
    apply Finset.prod_congr rfl
    intro index _
    apply congrArg₂ (kernels (e index)).val
    · funext slot
      exact congrArg colors (ep.symm_apply_apply ⟨index, slot⟩).symm
    · funext slot
      exact congrArg centers (eb.symm_apply_apply ⟨index, slot⟩).symm
  unfold finiteProduct
  rw [transportKernel_val, iteratedProduct_val, reindexKernel_symmetrize]
  apply congrArg ControlProduct.symmetrize
  change reindexKernel _ _ (reindexKernel _ _
    (flatten (fun index => Fin (r (e index))) (fun index => Fin (s (e index))) _)) = _
  rw [hflatten, ControlCoherence.reindexKernel_comp, ControlCoherence.reindexKernel_comp]
  rfl

end
end CurrentAFT.GroupedKernelProduct

end

section












/-!
# The complete independent-root paired reference and its exact first coefficient

The second scalar is sampled once by the genuine joint reference. Its
value enters the attachment channel after the off-body pair has been
drawn. The distinct compensator uses its own independent comparison root.
The signed mass is the literal expectation of the public paired score.
-/

namespace CurrentAFT.IndependentPairedReference

open AFT DiffuseProfiles ProposalPrimary FirstHistogram PairedResponse PhysicalSynthesis
open LocalReferenceEnergy PairedReferenceEnergy
open scoped BigOperators Classical

noncomputable section

local instance classicalFourDecidableEq : DecidableEq (Fin 4) := Classical.decEq _
local instance classicalOneDecidableEq : DecidableEq (Fin 1) := Classical.decEq _

abbrev Palette (security : ℕ) := FirstHistogram.Palette security
abbrev Scalar (security : ℕ) := FirstHistogram.Scalar security

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw actualSeedLaw

 theorem expectation_mix {Input Output : Type*} [Fintype Input] [Fintype Output]
    (law : FiniteDist Input) (kernel : Input → FiniteDist Output) (value : Output → ℝ) :
    (law.mix kernel).expectation value = law.expectation (fun input => (kernel input).expectation value) := by
  simp only [FiniteDist.expectation, FiniteDist.mix_weight, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_assoc]

 theorem expectation_atom {Color : Type*} [Fintype Color] [DecidableEq Color]
    (law : FiniteDist Color) (color : Color) : law.expectation (fun input => atom input color) = law.weight color := by
  classical
  simp [FiniteDist.expectation, atom, mul_ite]

 theorem indicator_eq_atom {Color : Type*} [DecidableEq Color]
    (first second : Color) (decision : Decidable (first = second)) :
    @ite ℝ (first = second) decision 1 0 = atom first second := by
  by_cases hequal : first = second <;> simp only [atom, hequal, if_true, if_false]

def attachmentBlurAt (security : ℕ) (scalar : Scalar security) : FiniteDist (Palette security) :=
  (actualSeedLaw security).mix (fun seed => (safeLaw security).map
    (shiftEquiv security (actualBlur security seed + scalar.val)))

theorem attachmentBlurAt_mean (security : ℕ) (output : Palette security) :
    (scalarLaw security).expectation (fun scalar => (attachmentBlurAt security scalar).weight output) =
      (bodyLaw security true).weight output := by
  unfold attachmentBlurAt bodyLaw
  simp only [FiniteDist.mix_weight, FiniteDist.map_equiv_weight, if_true]
  change (scalarLaw security).expectation (fun scalar => (actualSeedLaw security).expectation (fun seed =>
      (safeLaw security).weight ((shiftEquiv security (actualBlur security seed + scalar.val)).symm output))) =
    (actualSeedLaw security).expectation (fun seed => (safeLaw security).weight
      ((shiftEquiv security (actualBlur security seed + actualSecond security seed)).symm output))
  rw [FiniteDist.expectation_comm]
  rw [actualSeedLaw, FiniteDist.expectation_prod]
  conv_rhs => rw [FiniteDist.expectation_prod]
  simp only [actualBlur, actualSecond, FiniteDist.expectation_const]

def independentControlLaw (security : ℕ) (group : Group security) : FiniteDist (Fin 4 → Palette security) :=
  (referenceLaw security group.1).mix (fun sample =>
    ((compensatorBodyLaw security group.2).prod (attachmentBlurAt security sample.1)).map
      (fun outputs => PhysicalBlockTensors.quadrupleEquiv.symm (outputs.1, (sample.2, outputs.2))))

/-- The attachment marginal is the actual smoothed safe body law. It
does not depend on either selected public control. -/
theorem independentControlLaw_histogram (security : ℕ) (group : Group security) (output : Palette security) :
    (independentControlLaw security group).expectation (fun word => ∑ index, atom (word index) output) =
      endpointHistogram security (referenceLaw security group.1) output +
        (compensatorBodyLaw security group.2).weight output + (bodyLaw security true).weight output := by
  unfold independentControlLaw
  rw [expectation_mix]
  simp_rw [FiniteDist.expectation_map, Function.comp_def]
  have hcount (sample : JointOutput security) (outputs : Palette security × Palette security) :
      (∑ index : Fin 4, atom ((PhysicalBlockTensors.quadrupleEquiv.symm (outputs.1, (sample.2, outputs.2))) index) output) =
        atom outputs.1 output + (atom sample.2.1 output + atom sample.2.2 output) + atom outputs.2 output := by
    rw [Fin.sum_univ_four]
    simp only [PhysicalBlockTensors.quadrupleEquiv, Equiv.coe_fn_symm_mk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    ring
  simp_rw [hcount, FiniteDist.expectation_prod, FiniteDist.expectation_add, FiniteDist.expectation_const,
    expectation_atom]
  rw [reference_attachment_expectation security group.1
    (fun scalar => (attachmentBlurAt security scalar).weight output), attachmentBlurAt_mean]
  unfold endpointHistogram
  rw [FiniteDist.expectation_add]
  ring

def independentSignedMass (security : ℕ) (score : Palette security → ℝ)
    (word : Fin 4 → Palette security) : ℝ :=
  ∑ group, (groupLaw security).weight group * pairedChannel security score group *
    (independentControlLaw security group).weight word

theorem independentSigned_expectation (security : ℕ) (score : Palette security → ℝ)
    (value : (Fin 4 → Palette security) → ℝ) :
    (∑ word, independentSignedMass security score word * value word) =
      (groupLaw security).expectation (fun group => pairedChannel security score group *
        (independentControlLaw security group).expectation value) := by
  simp only [independentSignedMass, FiniteDist.expectation, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro group _
  apply Finset.sum_congr rfl
  intro word _
  ring

theorem independentSigned_mass (security : ℕ) (score : Palette security → ℝ) :
    (∑ word, independentSignedMass security score word) =
      (1 - activation security) * (primaryLaw security).expectation score := by
  have h := independentSigned_expectation security score (fun _ => 1)
  simp only [mul_one, FiniteDist.expectation_const] at h
  rw [h, pairedChannel_mean]

theorem independentSigned_mass_zero (security : ℕ) (score : Palette security → ℝ)
    (hcentered : (primaryLaw security).expectation score = 0) :
    (∑ word, independentSignedMass security score word) = 0 := by
  rw [independentSigned_mass, hcentered, mul_zero]

theorem independentSigned_first_profile (security : ℕ) (score : Palette security → ℝ)
    (hcentered : (primaryLaw security).expectation score = 0) (output : Palette security) :
    LocalTensors.signedColorCount (independentSignedMass security score) output =
      activation security * FirstResponse.response security (scoreProfile security score) output := by
  unfold LocalTensors.signedColorCount
  simp_rw [indicator_eq_atom]
  change (∑ word, independentSignedMass security score word * ∑ index, atom (word index) output) = _
  rw [independentSigned_expectation]
  simp_rw [independentControlLaw_histogram]
  have hcomplete : (groupLaw security).expectation (fun group => pairedChannel security score group *
      (endpointHistogram security (referenceLaw security group.1) output +
        (compensatorBodyLaw security group.2).weight output + (bodyLaw security true).weight output)) =
      completeHistogramResponse security score (bodyLaw security true).weight output := by
    simp only [groupLaw, FiniteDist.expectation, FiniteDist.prod_weight, Fintype.sum_prod_type,
      pairedChannel, completeHistogramResponse]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, mul_assoc]
  rw [hcomplete]
  exact completeHistogramResponse_eq_activation_response security score hcentered _ output











end

end CurrentAFT.IndependentPairedReference

end

section



















/-!
# Actual local coefficients in the current canonical graded algebra

Each selected coefficient is extracted from the physical signed mass by
the atoms `(delta - uniform) / primary`. It is transported to ordered Fin
slots, acted on by the constructed primary tensor inverse, and genuinely
symmetrized. The higher family below retains precisely the subsets with
at least two outputs. No higher response or raising operator is a premise.
-/

namespace CurrentAFT.LocalCoefficientFamily

open AFT DiffuseProfiles ProposalPrimary ActualControls
open ControlCoordinates ControlProduct GradedControlAlgebra GradedInverse
open scoped BigOperators Classical

noncomputable section

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected :=
  Classical.decEq _

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

abbrev Palette (security : ℕ) := ActualControls.Palette security
abbrev Family (security order : ℕ) := KernelFamily (primaryLaw security) (bodyReference security) order

def selectedDensity (security degree : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = degree)
    (word : Fin degree → Palette security) : ℝ :=
  LocalTensors.referenceRestrictedComponent (fun _ : Fin 4 => primaryLaw security)
    (fun _ : Fin 4 => LocalReferenceEnergy.uniformReference security) mass selected
      (word ∘ Fintype.equivFinOfCardEq hdegree)

 theorem selectedDensity_generic_canonical {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]
    (primary reference : FiniteDist Color) (hpositive : ∀ color, 0 < primary.weight color)
    (degree : ℕ) (mass : (Slot → Color) → ℝ) (selected : Finset Slot)
    (hdegree : Fintype.card selected = degree) :
    Hoeffding.Canonical (fun _ : Fin degree => primary) Finset.univ
      (fun word => LocalTensors.referenceRestrictedComponent (fun _ : Slot => primary)
        (fun _ : Slot => reference) mass selected (word ∘ Fintype.equivFinOfCardEq hdegree)) := by
  have hraw := LocalTensors.referenceRestrictedComponent_canonical
    (fun _ : Slot => primary) (fun _ : Slot => reference) (fun _ => hpositive) mass selected
  let raw : Kernel (Primary := Color) (Body := Unit) selected (Fin 0) :=
    fun colors _ => LocalTensors.referenceRestrictedComponent (fun _ : Slot => primary)
      (fun _ : Slot => reference) mass selected colors
  have hcentered : raw ∈ centeredKernelSpace primary (FiniteDist.uniform Unit) := by
    constructor
    · intro index colors _
      exact hraw.2 index (Finset.mem_univ index) colors
    · intro index
      exact Fin.elim0 index
  have htransport := reindexKernel_centered primary (FiniteDist.uniform Unit)
    (Fintype.equivFinOfCardEq hdegree) (Equiv.refl (Fin 0)) raw hcentered
  constructor
  · intro first second hequal
    have heq : first = second := funext (fun index => hequal index (Finset.mem_univ index))
    rw [heq]
  · intro index _ word
    exact htransport.1 index word Fin.elim0

theorem selectedDensity_canonical (security degree : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = degree) :
    Hoeffding.Canonical (fun _ : Fin degree => primaryLaw security) Finset.univ
      (selectedDensity security degree mass selected hdegree) :=
  selectedDensity_generic_canonical (primaryLaw security) (LocalReferenceEnergy.uniformReference security)
    (primaryReference_positive security) degree mass selected hdegree

def normalizedSelectedDensity (security degree : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = degree) :
    (Fin degree → Palette security) → ℝ :=
  PrimaryTensorInverse.tensorInverse security degree (selectedDensity security degree mass selected hdegree)



theorem normalizedSelectedDensity_canonical (security degree : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = degree) :
    Hoeffding.Canonical (fun _ : Fin degree => primaryLaw security) Finset.univ
      (normalizedSelectedDensity security degree mass selected hdegree) :=
  PrimaryTensorInverse.tensorInverse_canonical security degree _
    (selectedDensity_canonical security degree mass selected hdegree)

def selectedKernel (security degree : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = degree) :
    canonicalKernels (primaryLaw security) (bodyReference security) degree 0 := by
  let raw : DensityKernel (Primary := Palette security) (Body := SafePalette security) degree 0 :=
    fun colors _ => normalizedSelectedDensity security degree mass selected hdegree colors
  have hcanonical := normalizedSelectedDensity_canonical security degree mass selected hdegree
  have hcentered : raw ∈ centeredKernelSpace (primaryLaw security) (bodyReference security) := by
    constructor
    · intro index colors _
      exact hcanonical.2 index (Finset.mem_univ index) colors
    · intro index
      exact Fin.elim0 index
  have hs := symmetrize_centered (primaryLaw security) (bodyReference security) raw hcentered
  refine ⟨symmetrize raw, hs.1, hs.2, ?_⟩
  intro primaryOrder bodyOrder colors centers
  rw [symmetrize_primary_permutation, symmetrize_body_permutation]

def selectedArity (order : ℕ) (selected : Finset (Fin 4)) (hdegree : selected.card ≤ order) : TruncatedArity order :=
  ⟨(⟨selected.card, by omega⟩, 0), by simpa using hdegree⟩

def selectedFamily (security order : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) : Family security order :=
  if hdegree : selected.card ≤ order then
    Pi.single (selectedArity order selected hdegree)
      (selectedKernel security selected.card mass selected (by simp))
  else 0

def higherFamily (security order : ℕ) (mass : (Fin 4 → Palette security) → ℝ) : Family security order :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).filter (fun selected => 2 ≤ selected.card),
    selectedFamily security order mass selected

theorem higherFamily_vanishesBelow (security order : ℕ) (mass : (Fin 4 → Palette security) → ℝ) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 2 (higherFamily security order mass) := by
  intro arity hsmall
  unfold higherFamily
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro selected hselected
  have hcard := (Finset.mem_filter.mp hselected).2
  unfold selectedFamily
  split_ifs with hdegree
  · rw [Pi.single_eq_of_ne]
    intro hequal
    have hsmall' := hsmall
    rw [hequal] at hsmall'
    change selected.card + 0 < 2 at hsmall'
    omega
  · rfl





def massPolynomial (security degree : ℕ) (profile : (Fin degree → Palette security) → ℝ) :
    MvPolynomial (Palette security) ℝ :=
  ∑ word, MvPolynomial.C (profile word) * ∏ index, MvPolynomial.X (word index)

def primaryLeadingPolynomial (security degree : ℕ) (density : (Fin degree → Palette security) → ℝ) :
    MvPolynomial (Palette security) ℝ :=
  massPolynomial security degree (PrimaryTensorInverse.massLeading security degree density)







end

end CurrentAFT.LocalCoefficientFamily

end

section















/-! # Exact polynomial evaluation of the current normalized local coefficients -/

namespace CurrentAFT.LocalCoefficientEvaluation

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
open LocalCoefficientFamily LeadingEvaluation
open scoped BigOperators Classical

noncomputable section

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

abbrev Palette (security : ℕ) := ActualControls.Palette security

def densityPolynomial {Color Variable : Type*} [Fintype Color] (primary : FiniteDist Color)
    (forms : Color → MvPolynomial Variable ℝ) (degree : ℕ) (density : (Fin degree → Color) → ℝ) :
    MvPolynomial Variable ℝ :=
  ∑ word, MvPolynomial.C ((∏ index, primary.weight (word index)) * density word) *
    ∏ index, forms (word index)

def channelForm {Color : Type*} [Fintype Color] (primary : FiniteDist Color)
    (channel : (Color → ℝ) →ₗ[ℝ] (Color → ℝ)) (input : Color) : MvPolynomial Color ℝ :=
  ∑ output, MvPolynomial.C (primary.weight output * channel (Pi.single input 1) output / primary.weight input) *
    MvPolynomial.X output



def primaryForm (security : ℕ) : Palette security → MvPolynomial (Palette security) ℝ :=
  channelForm (primaryLaw security) (PrimaryTensorInverse.densityResponse security)

theorem primaryForm_homogeneous (security : ℕ) (input : Palette security) :
    (primaryForm security input).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro output _
  exact (MvPolynomial.isHomogeneous_C _ _).mul (MvPolynomial.isHomogeneous_X ℝ output)









def evaluation (security order : ℕ)
    (bodyForms : SafePalette security → MvPolynomial (Palette security) ℝ)
    (hbody : ∀ center, (bodyForms center).IsHomogeneous 1) :=
  LeadingEvaluation.familyHom (primaryLaw security) (bodyReference security) (primaryForm security) bodyForms
    (primaryForm_homogeneous security) hbody order





end

end CurrentAFT.LocalCoefficientEvaluation

end

section













/-!
# Actual finite normalization of a complete local paired polynomial

The positive and signed coefficients are extracted from the concrete
four-output laws. Their quotient is formed inside the current truncated
canonical algebra by its proved finite background inverse. Evaluation is
the actual polynomial algebra homomorphism, so the quotient identity is
an exact physical PGF identity modulo the stated degree cutoff.
-/

namespace CurrentAFT.NormalizedLocalPolynomial

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
open GradedControlAlgebra GradedInverse LocalCoefficientFamily LocalCoefficientEvaluation
open scoped BigOperators Classical

noncomputable section

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

abbrev Palette (security : ℕ) := ActualControls.Palette security

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

def completeFamily (security order : ℕ) (mass : (Fin 4 → Palette security) → ℝ) : Family security order :=
  (∑ word, mass word) • (1 : Family security order) +
    ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
      selectedFamily security order mass selected

theorem completeFamily_zeroArity (security order : ℕ) (mass : (Fin 4 → Palette security) → ℝ) :
    completeFamily security order mass (zeroArity order) =
      (∑ word, mass word) • (1 : Family security order) (zeroArity order) := by
  have hselected (selected : Finset (Fin 4)) (hnonempty : selected ≠ ∅) :
      selectedFamily security order mass selected (zeroArity order) = 0 := by
    unfold selectedFamily
    split_ifs with hdegree
    · rw [Pi.single_eq_of_ne]
      intro hequal
      have hcard := congrArg (fun arity : TruncatedArity order => arity.val.1.val) hequal
      change 0 = selected.card at hcard
      exact hnonempty (Finset.card_eq_zero.mp hcard.symm)
    · rfl
  unfold completeFamily
  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply]
  have hzero : (∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
      selectedFamily security order mass selected (zeroArity order)) = 0 := by
    apply Finset.sum_eq_zero
    intro selected hselectedmem
    exact hselected selected (Finset.mem_erase.mp hselectedmem).1
  rw [hzero, add_zero]



def positiveFamily (security order : ℕ) (law : FiniteDist (Fin 4 → Palette security)) : Family security order :=
  completeFamily security order law.weight



def normalizedFamily (security order : ℕ) (positive : FiniteDist (Fin 4 → Palette security))
    (signed : (Fin 4 → Palette security) → ℝ) : Family security order :=
  completeFamily security order signed *
    backgroundInverse (primaryLaw security) (bodyReference security) order (positiveFamily security order positive)





def independentPositiveLaw (security : ℕ) : FiniteDist (Fin 4 → Palette security) :=
  (PhysicalSynthesis.groupLaw security).mix (IndependentPairedReference.independentControlLaw security)

/-- The actual independent-root local normalized response. Both its
positive denominator and signed numerator come from the same complete
four-coordinate reference experiment. -/
def independentNormalized (security order : ℕ) (score : Palette security → ℝ) : Family security order :=
  normalizedFamily security order (independentPositiveLaw security)
    (IndependentPairedReference.independentSignedMass security score)



end

end CurrentAFT.NormalizedLocalPolynomial

end

section



















/-! # The independent-root local law is the genuine mixture of fixed-root laws -/
namespace CurrentAFT.IndependentReferenceEnergy

open AFT DiffuseProfiles ProposalPrimary ActualControls FirstHistogram LocalReferenceEnergy
  PairedReferenceEnergy FixedPairedFirst IndependentPairedReference PhysicalSynthesis
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

abbrev Palette (security : ℕ) := ActualControls.Palette security
abbrev Roots (security : ℕ) := FirstHistogram.Scalar security × (ActualSeed security × ActualSeed security)

def rootLaw (security : ℕ) : FiniteDist (Roots security) :=
  (scalarLaw security).prod ((actualSeedLaw security).prod (actualSeedLaw security))

theorem independentControlLaw_mixture (security : ℕ) (group : Group security)
    (value : (Fin 4 → Palette security) → ℝ) :
    (independentControlLaw security group).expectation value =
      (rootLaw security).expectation (fun roots =>
        (fixedControlLaw security (actualBlur security roots.2.1)
          (actualBlur security roots.2.2) roots.1 group).expectation value) := by
  unfold independentControlLaw
  rw [FiniteDist.expectation_mix]
  simp only [FiniteDist.expectation_map, Function.comp_apply, FiniteDist.expectation_prod]
  rw [reference_scalar_disintegration]
  simp only [compensatorBodyLaw, attachmentBlurAt, FiniteDist.expectation_map,
    FiniteDist.expectation_mix, Function.comp_def]
  unfold rootLaw
  rw [FiniteDist.expectation_prod]
  apply congrArg (scalarLaw security).expectation
  funext scalar
  rw [FiniteDist.expectation_prod]
  have hfirst := FiniteDist.expectation_comm (pairAt security group.1 scalar) (actualSeedLaw security)
    (fun pair compSeed => (actualSeedLaw security).expectation (fun attachSeed =>
      (safeLaw security).expectation (fun center =>
        value (PhysicalBlockTensors.quadrupleEquiv.symm
          (shiftEquiv security (actualBlur security compSeed) group.2,
            (pair, shiftEquiv security (actualBlur security attachSeed + scalar.val) center))))))
  rw [hfirst]
  apply congrArg (actualSeedLaw security).expectation
  funext compSeed
  rw [FiniteDist.expectation_comm (pairAt security group.1 scalar) (actualSeedLaw security)]
  apply congrArg (actualSeedLaw security).expectation
  funext attachSeed
  simp only [fixedControlLaw, FiniteDist.expectation_map, Function.comp_def,
    FiniteDist.expectation_prod, pointLaw, FiniteDist.expectation_const, attachmentAt]

theorem independentSigned_mixture_expectation (security : ℕ) (score : Palette security → ℝ)
    (value : (Fin 4 → Palette security) → ℝ) :
    (∑ word, independentSignedMass security score word * value word) =
      (rootLaw security).expectation (fun roots =>
        ∑ word, pairedMassAt security (actualBlur security roots.2.1)
          (actualBlur security roots.2.2) roots.1 score word * value word) := by
  rw [independentSigned_expectation]
  simp_rw [independentControlLaw_mixture]
  simp only [← FiniteDist.expectation_const_mul]
  rw [FiniteDist.expectation_comm]
  apply congrArg (rootLaw security).expectation
  funext roots
  simp only [FiniteDist.expectation_const_mul]
  exact (fixedMass_expectation security _ _ roots.1 score value).symm

theorem independentSigned_mixture (security : ℕ) (score : Palette security → ℝ)
    (word : Fin 4 → Palette security) :
    independentSignedMass security score word = (rootLaw security).expectation (fun roots =>
      pairedMassAt security (actualBlur security roots.2.1) (actualBlur security roots.2.2) roots.1 score word) := by
  have h := independentSigned_mixture_expectation security score (fun sample => if sample = word then 1 else 0)
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

/-- Convex averaging preserves the full joint four-coordinate energy,
including every cancellation in the score and every retained root. -/
theorem independentSigned_energy (security : ℕ) (score : Palette security → ℝ) :
    profileSquareNorm (FiniteDist.independent (fun _ : Fin 4 => uniformReference security)).weight
      (independentSignedMass security score) ≤
        (4128 * pairBudget security) * (primaryLaw security).expectation (fun color => score color ^ 2) := by
  let reference := FiniteDist.independent (fun _ : Fin 4 => uniformReference security)
  have hequal : independentSignedMass security score = fun word =>
      ∑ roots, (rootLaw security).weight roots *
        pairedMassAt security (actualBlur security roots.2.1) (actualBlur security roots.2.2) roots.1 score word := by
    funext word
    exact independentSigned_mixture security score word
  rw [hequal]
  have havg := profileSquareNorm_average_le (rootLaw security) reference.weight reference.nonneg
    (fun roots => pairedMassAt security (actualBlur security roots.2.1) (actualBlur security roots.2.2) roots.1 score)
  apply havg.trans
  calc
    _ ≤ ∑ roots, (rootLaw security).weight roots * ((4128 * pairBudget security) *
        (primaryLaw security).expectation (fun color => score color ^ 2)) := by
      apply Finset.sum_le_sum
      intro roots _
      exact mul_le_mul_of_nonneg_left (pairedMassAt_energy security _ _ roots.1 score) ((rootLaw security).nonneg roots)
    _ = _ := by rw [← Finset.sum_mul, (rootLaw security).sum_one, one_mul]

theorem fixedPositive_control (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (word : Fin 4 → Palette security) :
    (PositiveFirstCoefficient.positiveFourLaw security compensatorRoot attachmentRoot scalar).weight word =
      ∑ group, (groupLaw security).weight group *
        (fixedControlLaw security compensatorRoot attachmentRoot scalar group).weight word := by
  rw [PositiveFirstCoefficient.positiveFour_weight]
  unfold PhysicalBlockTensors.compensatedTripleMass tripleMassAt signedPairAt
  rw [compensatorAt_channel]
  simp only [groupLaw, FiniteDist.prod_weight, Fintype.sum_prod_type,
    fixedControlLaw_weight, controlMass, mul_one, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro primary _
  apply Finset.sum_congr rfl
  intro center _
  ring

theorem independentPositive_mixture_expectation (security : ℕ)
    (value : (Fin 4 → Palette security) → ℝ) :
    (NormalizedLocalPolynomial.independentPositiveLaw security).expectation value =
      (rootLaw security).expectation (fun roots =>
        (PositiveFirstCoefficient.positiveFourLaw security (actualBlur security roots.2.1)
          (actualBlur security roots.2.2) roots.1).expectation value) := by
  rw [NormalizedLocalPolynomial.independentPositiveLaw, FiniteDist.expectation_mix]
  simp_rw [independentControlLaw_mixture]
  rw [FiniteDist.expectation_comm]
  apply congrArg (rootLaw security).expectation
  funext roots
  simp only [FiniteDist.expectation, fixedPositive_control, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

theorem independentPositive_mixture (security : ℕ) (word : Fin 4 → Palette security) :
    (NormalizedLocalPolynomial.independentPositiveLaw security).weight word =
      (rootLaw security).expectation (fun roots =>
        (PositiveFirstCoefficient.positiveFourLaw security (actualBlur security roots.2.1)
          (actualBlur security roots.2.2) roots.1).weight word) := by
  have h := independentPositive_mixture_expectation security (fun sample => if sample = word then 1 else 0)
  simpa only [FiniteDist.expectation, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] using h

theorem fixedPositive_energy (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) :
    profileSquareNorm (FiniteDist.independent (fun _ : Fin 4 => uniformReference security)).weight
      (PositiveFirstCoefficient.positiveFourLaw security compensatorRoot attachmentRoot scalar).weight ≤
        16 * pairBudget security := by
  let reference := FiniteDist.independent (fun _ : Fin 4 => uniformReference security)
  have hmass : (PositiveFirstCoefficient.positiveFourLaw security compensatorRoot attachmentRoot scalar).weight =
      PhysicalBlockTensors.compensatedTripleMass (compensatorAt security compensatorRoot).weight
        (tripleMassAt security attachmentRoot scalar (fun _ => 1)) :=
    funext (PositiveFirstCoefficient.positiveFour_weight security compensatorRoot attachmentRoot scalar)
  have hfactor := PhysicalBlockTensors.compensated_triple_density_energy (uniformReference security)
    (compensatorAt security compensatorRoot).weight (tripleMassAt security attachmentRoot scalar (fun _ => 1))
  change densitySquareNorm reference.weight (fun word => PhysicalBlockTensors.compensatedTripleMass
    (compensatorAt security compensatorRoot).weight (tripleMassAt security attachmentRoot scalar (fun _ => 1)) word /
      reference.weight word) = _ at hfactor
  rw [densityScore_square] at hfactor
  rw [hmass, hfactor]
  have hcomp := compensatorAt_energy security compensatorRoot
  have htriple := tripleMassAt_energy security attachmentRoot scalar (fun _ => 1)
  simp only [one_pow, FiniteDist.expectation_const, mul_one] at htriple
  have hnonneg := profileSquareNorm_nonneg (uniformReference security).weight
    (compensatorAt security compensatorRoot).weight (uniformReference security).nonneg
  calc
    _ ≤ profileSquareNorm (uniformReference security).weight (compensatorAt security compensatorRoot).weight *
        (4 * pairBudget security) := mul_le_mul_of_nonneg_left htriple hnonneg
    _ ≤ 4 * (4 * pairBudget security) := mul_le_mul_of_nonneg_right hcomp
      (mul_nonneg (by norm_num) (pairBudget_nonneg security))
    _ = _ := by ring

theorem independentPositive_energy (security : ℕ) :
    profileSquareNorm (FiniteDist.independent (fun _ : Fin 4 => uniformReference security)).weight
      (NormalizedLocalPolynomial.independentPositiveLaw security).weight ≤ 16 * pairBudget security := by
  let reference := FiniteDist.independent (fun _ : Fin 4 => uniformReference security)
  have hequal : (NormalizedLocalPolynomial.independentPositiveLaw security).weight = fun word =>
      ∑ roots, (rootLaw security).weight roots *
        (PositiveFirstCoefficient.positiveFourLaw security (actualBlur security roots.2.1)
          (actualBlur security roots.2.2) roots.1).weight word := by
    funext word
    exact independentPositive_mixture security word
  rw [hequal]
  apply (profileSquareNorm_average_le (rootLaw security) reference.weight reference.nonneg _).trans
  calc
    _ ≤ ∑ roots, (rootLaw security).weight roots * (16 * pairBudget security) := by
      apply Finset.sum_le_sum
      intro roots _
      exact mul_le_mul_of_nonneg_left (fixedPositive_energy security _ _ roots.1) ((rootLaw security).nonneg roots)
    _ = _ := by rw [← Finset.sum_mul, (rootLaw security).sum_one, one_mul]

end
end CurrentAFT.IndependentReferenceEnergy

end

section















/-! # Genuine local coefficient norm budgets after the actual primary inverse -/

namespace CurrentAFT.LocalCoefficientNorm

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct ControlNorm
open LocalCoefficientFamily LocalReferenceEnergy PairedReferenceEnergy
open scoped BigOperators Classical

noncomputable section

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _

abbrev Palette (security : ℕ) := ActualControls.Palette security

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

 theorem blockEnergy_no_body {Primary Body Index : Type*}
    [Fintype Primary] [Fintype Body] [Fintype Index]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (kernel : (Index → Primary) → ℝ) :
    blockEnergy primary body (fun colors (_ : Fin 0 → Body) => kernel colors) =
      (FiniteDist.independent (fun _ : Index => primary)).l2Sq kernel := by
  unfold blockEnergy FiniteDist.l2Sq
  rw [FiniteDist.expectation_prod]
  simp only [FiniteDist.expectation_const]

def primaryMassEnergy (security : ℕ) (mass : (Fin 4 → Palette security) → ℝ) : ℝ :=
  profileSquareNorm (FiniteDist.independent (fun _ : Fin 4 => primaryLaw security)).weight mass

theorem selectedDensity_energy (security degree : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = degree) :
    (FiniteDist.independent (fun _ : Fin degree => primaryLaw security)).l2Sq
      (selectedDensity security degree mass selected hdegree) ≤
        ((4 : ℝ) ^ selected.card) ^ 2 * primaryMassEnergy security mass := by
  let raw : Kernel (Primary := Palette security) (Body := Unit) selected (Fin 0) :=
    fun colors _ => LocalTensors.referenceRestrictedComponent (fun _ : Fin 4 => primaryLaw security)
      (fun _ : Fin 4 => uniformReference security) mass selected colors
  rw [← blockEnergy_no_body (primaryLaw security) (FiniteDist.uniform Unit)]
  change blockEnergy (primaryLaw security) (FiniteDist.uniform Unit)
    (reindexKernel (Fintype.equivFinOfCardEq hdegree) (Equiv.refl (Fin 0)) raw) ≤ _
  rw [blockEnergy_reindex, blockEnergy_no_body]
  have h := LocalTensors.referenceRestrictedComponent_l2Sq_le (fun _ : Fin 4 => primaryLaw security)
    (fun _ : Fin 4 => uniformReference security) (fun _ => primaryReference_positive security) mass selected 2 (by norm_num)
    (fun _ color => by
      rw [uniformReference_weight]
      have hlower : 1 / (2 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight color := by
        simpa only [primaryLaw] using primaryProfile_atom_lower security color
      have hq := FirstResponse.modulus_pos security
      have hidentity : (1 / (Parameters.modulus security : ℝ)) = 2 * (1 / (2 * (Parameters.modulus security : ℝ))) := by ring
      rw [hidentity]
      exact mul_le_mul_of_nonneg_left hlower (by norm_num))
  change _ ≤ ((2 * (2 : ℝ)) ^ selected.card) ^ 2 * densitySquareNorm
    (FiniteDist.independent (fun _ : Fin 4 => primaryLaw security)).weight
    (fun word => mass word / (FiniteDist.independent (fun _ : Fin 4 => primaryLaw security)).weight word) at h
  rw [densityScore_square] at h
  simpa only [show (2 : ℝ) * 2 = 4 by norm_num, primaryMassEnergy] using h

theorem normalizedSelectedDensity_energy (security degree : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = degree) :
    (FiniteDist.independent (fun _ : Fin degree => primaryLaw security)).l2Sq
      (normalizedSelectedDensity security degree mass selected hdegree) ≤
        ((2 / activation security) ^ degree) ^ 2 * ((4 : ℝ) ^ selected.card) ^ 2 * primaryMassEnergy security mass := by
  have h := PrimaryTensorInverse.tensorInverse_energy security degree (selectedDensity security degree mass selected hdegree)
  exact h.trans ((mul_le_mul_of_nonneg_left (selectedDensity_energy security degree mass selected hdegree)
    (sq_nonneg _)).trans_eq (by ring))

theorem selectedKernel_energy (security degree : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = degree) :
    blockEnergy (primaryLaw security) (bodyReference security) (selectedKernel security degree mass selected hdegree).val ≤
      ((2 / activation security) ^ degree) ^ 2 * ((4 : ℝ) ^ selected.card) ^ 2 * primaryMassEnergy security mass := by
  change blockEnergy (primaryLaw security) (bodyReference security)
    (symmetrize (fun colors (_ : Fin 0 → SafePalette security) =>
      normalizedSelectedDensity security degree mass selected hdegree colors)) ≤ _
  apply (blockEnergy_symmetrize_le _ _ _).trans
  rw [blockEnergy_no_body]
  exact normalizedSelectedDensity_energy security degree mass selected hdegree

theorem primaryMassEnergy_uniform_le (security : ℕ) (mass : (Fin 4 → Palette security) → ℝ) :
    primaryMassEnergy security mass ≤
      16 * profileSquareNorm (FiniteDist.independent (fun _ : Fin 4 => uniformReference security)).weight mass := by
  let primary := FiniteDist.independent (fun _ : Fin 4 => primaryLaw security)
  let uniform := FiniteDist.independent (fun _ : Fin 4 => uniformReference security)
  have hu (word : Fin 4 → Palette security) : 0 < uniform.weight word := by
    change 0 < ∏ index : Fin 4, (uniformReference security).weight (word index)
    exact Finset.prod_pos (fun _ _ => by rw [uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security))
  have hcompare (word : Fin 4 → Palette security) : uniform.weight word ≤ 16 * primary.weight word := by
    have h := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin 4)))
      (fun index _ => (uniformReference security).nonneg (word index))
      (fun index _ => show (uniformReference security).weight (word index) ≤ 2 * (primaryLaw security).weight (word index) by
        rw [uniformReference_weight]
        have hlower : 1 / (2 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight (word index) := by
          simpa only [primaryLaw] using primaryProfile_atom_lower security (word index)
        have hidentity : 1 / (Parameters.modulus security : ℝ) = 2 * (1 / (2 * (Parameters.modulus security : ℝ))) := by ring
        rw [hidentity]
        exact mul_le_mul_of_nonneg_left hlower (by norm_num))
    change (∏ index : Fin 4, (uniformReference security).weight (word index)) ≤
      16 * ∏ index : Fin 4, (primaryLaw security).weight (word index)
    simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      show (2 : ℝ) ^ 4 = 16 by norm_num] using h
  unfold primaryMassEnergy profileSquareNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro word _
  have hlower : uniform.weight word / 16 ≤ primary.weight word := (div_le_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr (by
    simpa only [mul_comm] using hcompare word)
  exact (div_le_div_of_nonneg_left (sq_nonneg (mass word)) (div_pos (hu word) (by norm_num)) hlower).trans_eq (by ring)



theorem selectedKernel_norm (security degree : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = degree) :
    blockL2 (primaryLaw security) (bodyReference security) (selectedKernel security degree mass selected hdegree).val ≤
      (2 / activation security) ^ degree * (4 : ℝ) ^ selected.card * Real.sqrt (primaryMassEnergy security mass) := by
  let coefficient := (2 / activation security) ^ degree * (4 : ℝ) ^ selected.card
  have hcoefficient : 0 ≤ coefficient := by
    dsimp only [coefficient]
    exact mul_nonneg (pow_nonneg (div_nonneg (by norm_num) (activation_pos security).le) _) (by positivity)
  have h := Real.sqrt_le_sqrt (selectedKernel_energy security degree mass selected hdegree)
  change blockL2 (primaryLaw security) (bodyReference security) (selectedKernel security degree mass selected hdegree).val ≤ _ at h
  have hrewrite : ((2 / activation security) ^ degree) ^ 2 * ((4 : ℝ) ^ selected.card) ^ 2 * primaryMassEnergy security mass =
      coefficient ^ 2 * primaryMassEnergy security mass := by dsimp only [coefficient]; ring
  rw [hrewrite, Real.sqrt_mul (sq_nonneg coefficient), Real.sqrt_sq_eq_abs, abs_of_nonneg hcoefficient] at h
  exact h

theorem selectedFamily_norm (security order : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (primaryFactor bodyFactor : ℝ) (hprimaryFactor : 0 ≤ primaryFactor) :
    GradedControlNorm.familyNorm (primaryLaw security) (bodyReference security) order primaryFactor bodyFactor
      (selectedFamily security order mass selected) ≤
        primaryFactor ^ selected.card * ((2 / activation security) ^ selected.card * (4 : ℝ) ^ selected.card *
          Real.sqrt (primaryMassEnergy security mass)) := by
  unfold selectedFamily
  split_ifs with hdegree
  · rw [BackgroundFamilies.familyNorm_single]
    change gradeWeight primaryFactor bodyFactor selected.card 0 *
      blockL2 (primaryLaw security) (bodyReference security)
        (selectedKernel security selected.card mass selected (by simp)).val ≤ _
    simp only [gradeWeight, pow_zero, mul_one]
    exact mul_le_mul_of_nonneg_left (selectedKernel_norm security selected.card mass selected (by simp))
      (pow_nonneg hprimaryFactor _)
  · rw [GradedControlStability.familyNorm_zero]
    apply mul_nonneg (pow_nonneg hprimaryFactor _)
    apply mul_nonneg
    · apply mul_nonneg
      · exact pow_nonneg (div_nonneg (by norm_num) (activation_pos security).le) _
      · positivity
    · exact Real.sqrt_nonneg _

end

end CurrentAFT.LocalCoefficientNorm

end

section















/-! # The genuine first coefficient and degree raising of the actual local response -/

namespace CurrentAFT.LocalRaisingFirst

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
open GradedControlAlgebra GradedInverse LocalCoefficientFamily NormalizedLocalPolynomial BackgroundFamilies
open scoped BigOperators Classical

noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected :=
  Classical.decEq _

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

abbrev Palette (security : ℕ) := ActualControls.Palette security

theorem selectedDensity_singleton (security : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (slot : Fin 4) (hdegree : Fintype.card ({slot} : Finset (Fin 4)) = 1) (color : Palette security) :
    selectedDensity security 1 mass {slot} hdegree (fun _ => color) =
      ((∑ word, if word slot = color then mass word else 0) -
        (LocalReferenceEnergy.uniformReference security).weight color * ∑ word, mass word) /
          (primaryLaw security).weight color := by
  unfold selectedDensity
  rw [LocalTensors.referenceRestrictedComponent_singleton]
  rfl



theorem selectedKernel_one (security : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = 1)
    (colors : Fin 1 → Palette security) (centers : Fin 0 → SafePalette security) :
    (selectedKernel security 1 mass selected hdegree).val colors centers =
      normalizedSelectedDensity security 1 mass selected hdegree colors := by
  change symmetrize (fun colors (_ : Fin 0 → SafePalette security) =>
    normalizedSelectedDensity security 1 mass selected hdegree colors) colors centers = _
  rw [symmetrize_of_symmetric]
  intro primaryOrder bodyOrder input _
  congr 1
  funext index
  have hi : primaryOrder index = index := Subsingleton.elim _ _
  simp only [Function.comp_apply, hi]

theorem selectedFamily_singleton_primary (security order : ℕ) (horder : 1 ≤ order)
    (mass : (Fin 4 → Palette security) → ℝ) (slot : Fin 4) (color : Palette security) :
    primaryCoefficient (primaryLaw security) (bodyReference security) order horder
      (selectedFamily security order mass {slot}) color =
      PrimaryTensorInverse.densityInverse security (fun input =>
        ((∑ word, if word slot = input then mass word else 0) -
          (LocalReferenceEnergy.uniformReference security).weight input * ∑ word, mass word) /
            (primaryLaw security).weight input) color := by
  have hsingle : selectedFamily security order mass {slot} =
      Pi.single (primaryArity order horder) (selectedKernel security 1 mass {slot} (by simp)) := by
    unfold selectedFamily
    rw [dif_pos (by simpa using horder)]
    unfold selectedArity primaryArity
    rfl
  rw [hsingle]
  unfold primaryCoefficient
  rw [Pi.single_eq_same]
  rw [selectedKernel_one]
  unfold normalizedSelectedDensity
  change PrimaryTensorInverse.densityInverse security
    (fun input => selectedDensity security 1 mass {slot} _ (Fin.cons input Fin.elim0)) color = _
  apply congrArg (fun f => PrimaryTensorInverse.densityInverse security f color)
  funext input
  have hword : Fin.cons input Fin.elim0 = (fun _ : Fin 1 => input) := by
    funext index
    have hi := Fin.eq_zero index
    subst index
    rfl
  rw [hword]
  exact selectedDensity_singleton security mass slot _ input

def primaryProjection {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) (horder : 1 ≤ order) :
    KernelFamily primary body order →ₗ[ℝ] (Primary → ℝ) where
  toFun := primaryCoefficient primary body order horder
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem primaryProjection_one {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) (horder : 1 ≤ order) :
    primaryProjection primary body order horder 1 = 0 := by
  funext color
  change ((familyUnit primary body order) (primaryArity order horder)).val (fun _ => color) Fin.elim0 = 0
  unfold familyUnit
  rw [Pi.single_eq_of_ne]
  · rfl
  · intro hequal
    have h := congrArg (fun arity : TruncatedArity order => arity.val.1.val) hequal
    change 1 = 0 at h
    omega

theorem selectedFamily_primary_nonone (security order : ℕ) (horder : 1 ≤ order)
    (mass : (Fin 4 → Palette security) → ℝ) (selected : Finset (Fin 4)) (hcard : selected.card ≠ 1) :
    primaryProjection (primaryLaw security) (bodyReference security) order horder
      (selectedFamily security order mass selected) = 0 := by
  funext color
  unfold primaryProjection primaryCoefficient selectedFamily
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs with hdegree
  · rw [Pi.single_eq_of_ne]
    · rfl
    · intro hequal
      have h := congrArg (fun arity : TruncatedArity order => arity.val.1.val) hequal
      exact hcard h.symm
  · rfl

 theorem sum_nonempty_singletons {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (term : Finset Slot → ℝ) (hzero : ∀ selected, selected.card ≠ 1 → term selected = 0) :
    (∑ selected ∈ (Finset.univ : Finset (Finset Slot)).erase ∅, term selected) =
      ∑ slot, term {slot} := by
  let singles := (Finset.univ : Finset (Finset Slot)).filter (fun selected => selected.card = 1)
  have hsubset : singles ⊆ (Finset.univ : Finset (Finset Slot)).erase ∅ := by
    intro selected hselected
    apply Finset.mem_erase.mpr
    constructor
    · intro hequal
      have hcard := (Finset.mem_filter.mp hselected).2
      rw [hequal, Finset.card_empty] at hcard
      omega
    · exact Finset.mem_univ _
  have hreduce : (∑ selected ∈ singles, term selected) =
      ∑ selected ∈ (Finset.univ : Finset (Finset Slot)).erase ∅, term selected := by
    apply Finset.sum_subset hsubset
    intro selected _ hnot
    apply hzero
    intro hcard
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard⟩)
  rw [← hreduce]
  symm
  apply Finset.sum_bij (fun slot _ => ({slot} : Finset Slot))
  · intro slot _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.card_singleton _⟩
  · intro first _ second _ hequal
    exact Finset.singleton_injective hequal
  · intro selected hselected
    obtain ⟨slot, hequal⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hselected).2
    exact ⟨slot, Finset.mem_univ _, hequal.symm⟩
  · intro slot _
    rfl

theorem completeFamily_primary_centered (security order : ℕ) (horder : 1 ≤ order)
    (mass : (Fin 4 → Palette security) → ℝ) (hmass : ∑ word, mass word = 0) :
    primaryCoefficient (primaryLaw security) (bodyReference security) order horder
      (completeFamily security order mass) =
        PrimaryTensorInverse.densityInverse security
          (fun color => LocalTensors.signedColorCount mass color / (primaryLaw security).weight color) := by
  change primaryProjection (primaryLaw security) (bodyReference security) order horder
    (completeFamily security order mass) = _
  unfold completeFamily
  rw [map_add, map_smul, primaryProjection_one, smul_zero, zero_add, map_sum]
  funext color
  simp only [Finset.sum_apply]
  rw [sum_nonempty_singletons _ (fun selected hcard =>
    congrFun (selectedFamily_primary_nonone security order horder mass selected hcard) color)]
  simp only [primaryProjection, LinearMap.coe_mk, AddHom.coe_mk, selectedFamily_singleton_primary,
    hmass, mul_zero, sub_zero]
  have hsum : (∑ slot : Fin 4, PrimaryTensorInverse.densityInverse security
      (fun input => (∑ word, if word slot = input then mass word else 0) /
        (primaryLaw security).weight input) color) =
      PrimaryTensorInverse.densityInverse security
        (∑ slot : Fin 4, fun input => (∑ word, if word slot = input then mass word else 0) /
          (primaryLaw security).weight input) color := by
    rw [map_sum]
    simp only [Finset.sum_apply]
  rw [hsum]
  apply congrArg (fun f => PrimaryTensorInverse.densityInverse security f color)
  funext input
  simp only [Finset.sum_apply, ← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  unfold LocalTensors.signedColorCount
  apply Finset.sum_congr rfl
  intro word _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro slot _
  split_ifs <;> simp

theorem densityInverse_response (security : ℕ) (score : Palette security → ℝ) :
    PrimaryTensorInverse.densityInverse security (PrimaryTensorInverse.densityResponse security score) = score := by
  have hprofile : (fun color => (primaryLaw security).weight color *
      PrimaryTensorInverse.densityResponse security score color) =
      activation security • FirstResponse.response security (fun color => (primaryLaw security).weight color * score color) := by
    funext color
    rw [PrimaryTensorInverse.densityResponse_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [(primaryReference_positive security color).ne']
  funext color
  rw [PrimaryTensorInverse.densityInverse_apply, hprofile, map_smul]
  have hinverse : (FirstResponse.responseEquiv security).symm
      (FirstResponse.response security (fun input => (primaryLaw security).weight input * score input)) =
        fun input => (primaryLaw security).weight input * score input := by
    rw [← FirstResponse.responseEquiv_forward]
    exact (FirstResponse.responseEquiv security).symm_apply_apply _
  rw [hinverse]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [(primaryReference_positive security color).ne', (activation_pos security).ne']

theorem independentComplete_primary (security order : ℕ) (horder : 1 ≤ order)
    (score : Palette security → ℝ) (hcentered : (primaryLaw security).expectation score = 0) :
    primaryCoefficient (primaryLaw security) (bodyReference security) order horder
      (completeFamily security order (IndependentPairedReference.independentSignedMass security score)) = score := by
  rw [completeFamily_primary_centered security order horder _
    (IndependentPairedReference.independentSigned_mass_zero security score hcentered)]
  have hprofile : (fun color => LocalTensors.signedColorCount
      (IndependentPairedReference.independentSignedMass security score) color / (primaryLaw security).weight color) =
      PrimaryTensorInverse.densityResponse security score := by
    funext color
    rw [IndependentPairedReference.independentSigned_first_profile security score hcentered,
      PrimaryTensorInverse.densityResponse_apply]
    rfl
  rw [hprofile, densityInverse_response]

section Filtration

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

theorem vanishesBelow_add (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order degree : ℕ) (first second : KernelFamily primary body order)
    (hfirst : VanishesBelow primary body order degree first)
    (hsecond : VanishesBelow primary body order degree second) :
    VanishesBelow primary body order degree (first + second) := by
  intro arity hdegree
  change first arity + second arity = 0
  rw [hfirst arity hdegree, hsecond arity hdegree, add_zero]

theorem vanishesBelow_sum {Index : Type*} (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order degree : ℕ) (selected : Finset Index) (family : Index → KernelFamily primary body order)
    (hfamily : ∀ index ∈ selected, VanishesBelow primary body order degree (family index)) :
    VanishesBelow primary body order degree (∑ index ∈ selected, family index) := by
  intro arity hdegree
  simp only [Finset.sum_apply]
  exact Finset.sum_eq_zero (fun index hindex => hfamily index hindex arity hdegree)



end Filtration

theorem completeFamily_vanishes_one (security order : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (hmass : ∑ word, mass word = 0) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 1
      (completeFamily security order mass) := by
  apply vanishesBelow_one_of_zero
  rw [completeFamily_zeroArity, hmass, zero_smul]





theorem completeFamily_no_body (security order : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (arity : TruncatedArity order) (hbody : 0 < arity.val.2.val) :
    completeFamily security order mass arity = 0 := by
  have hunit : (1 : Family security order) arity = 0 := by
    change familyUnit (primaryLaw security) (bodyReference security) order arity = 0
    unfold familyUnit
    rw [Pi.single_eq_of_ne]
    intro hequal
    have h := congrArg (fun item : TruncatedArity order => item.val.2.val) hequal
    change arity.val.2.val = 0 at h
    omega
  have hselected (selected : Finset (Fin 4)) : selectedFamily security order mass selected arity = 0 := by
    unfold selectedFamily
    split_ifs with hdegree
    · rw [Pi.single_eq_of_ne]
      intro hequal
      have h := congrArg (fun item : TruncatedArity order => item.val.2.val) hequal
      change arity.val.2.val = 0 at h
      omega
    · rfl
  unfold completeFamily
  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, hunit, smul_zero, hselected,
    Finset.sum_const_zero, add_zero]



theorem independentComplete_sub_primary_raises (security order : ℕ) (horder : 1 ≤ order)
    (score : Palette security → ℝ) (hcentered : (primaryLaw security).expectation score = 0) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 2
      (completeFamily security order (IndependentPairedReference.independentSignedMass security score) -
        primaryFamily (primaryLaw security) (bodyReference security) order horder score hcentered) := by
  intro arity hsmall
  change completeFamily security order (IndependentPairedReference.independentSignedMass security score) arity -
    primaryFamily (primaryLaw security) (bodyReference security) order horder score hcentered arity = 0
  by_cases hb : 0 < arity.val.2.val
  · rw [completeFamily_no_body security order _ arity hb]
    unfold primaryFamily
    rw [Pi.single_eq_of_ne, sub_zero]
    intro hequal
    have h := congrArg (fun item : TruncatedArity order => item.val.2.val) hequal
    change arity.val.2.val = 0 at h
    omega
  · have hs : arity.val.2.val = 0 := by omega
    by_cases hr : arity.val.1.val = 0
    · have harity : arity = zeroArity order := by
        apply Subtype.ext
        exact Prod.ext (Fin.ext hr) (Fin.ext hs)
      subst arity
      rw [completeFamily_zeroArity, IndependentPairedReference.independentSigned_mass_zero security score hcentered,
        zero_smul]
      unfold primaryFamily
      rw [Pi.single_eq_of_ne, sub_zero]
      intro hequal
      have h := congrArg (fun item : TruncatedArity order => item.val.1.val) hequal
      change 0 = 1 at h
      omega
    · have hrone : arity.val.1.val = 1 := by omega
      have harity : arity = primaryArity order horder := by
        apply Subtype.ext
        exact Prod.ext (Fin.ext hrone) (Fin.ext hs)
      subst arity
      apply sub_eq_zero.mpr
      unfold primaryFamily
      rw [Pi.single_eq_same]
      apply Subtype.ext
      funext (colors : Fin 1 → Palette security) (centers : Fin 0 → SafePalette security)
      have hcolors : colors = (fun _ => colors 0) := by
        funext index
        have hi := Fin.eq_zero index
        subst index
        rfl
      have hcenters : centers = Fin.elim0 := Subsingleton.elim _ _
      rw [hcolors, hcenters]
      exact congrFun (independentComplete_primary security order horder score hcentered) (colors 0)

/-- The actual degree-raising local response, built from the physical
four-coordinate laws and the proved finite inverse of their positive
reference polynomial. -/
def localRaising (security order : ℕ) (horder : 1 ≤ order)
    (score : Palette security → ℝ) (hcentered : (primaryLaw security).expectation score = 0) : Family security order :=
  independentNormalized security order score -
    primaryFamily (primaryLaw security) (bodyReference security) order horder score hcentered



end
end CurrentAFT.LocalRaisingFirst

end

section











/-! # Actual local responses are linear in the common public score -/
namespace CurrentAFT.LocalRaisingLinear

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
open GradedControlAlgebra GradedInverse LocalCoefficientFamily NormalizedLocalPolynomial LocalRaisingFirst
open scoped BigOperators Classical

noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

abbrev Palette (security : ℕ) := ActualControls.Palette security

def selectedDensityLinear (security degree : ℕ) (selected : Finset (Fin 4))
    (hdegree : Fintype.card selected = degree) :
    ((Fin 4 → Palette security) → ℝ) →ₗ[ℝ] ((Fin degree → Palette security) → ℝ) where
  toFun := fun mass => selectedDensity security degree mass selected hdegree
  map_add' first second := by
    funext word
    simp only [selectedDensity, LocalTensors.referenceRestrictedComponent, Pi.add_apply,
      add_mul, Finset.sum_add_distrib]
  map_smul' scalar mass := by
    funext word
    simp only [selectedDensity, LocalTensors.referenceRestrictedComponent, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum]

def normalizedSelectedLinear (security degree : ℕ) (selected : Finset (Fin 4))
    (hdegree : Fintype.card selected = degree) :=
  (PrimaryTensorInverse.tensorInverse security degree).comp (selectedDensityLinear security degree selected hdegree)

def selectedKernelLinear (security degree : ℕ) (selected : Finset (Fin 4))
    (hdegree : Fintype.card selected = degree) :
    ((Fin 4 → Palette security) → ℝ) →ₗ[ℝ]
      canonicalKernels (primaryLaw security) (bodyReference security) degree 0 where
  toFun := fun mass => selectedKernel security degree mass selected hdegree
  map_add' first second := by
    apply Subtype.ext
    have hraw : (fun colors (_ : Fin 0 → SafePalette security) =>
        normalizedSelectedDensity security degree (first + second) selected hdegree colors) =
        (fun colors (_ : Fin 0 → SafePalette security) => normalizedSelectedDensity security degree first selected hdegree colors) +
        (fun colors (_ : Fin 0 → SafePalette security) => normalizedSelectedDensity security degree second selected hdegree colors) := by
      funext colors _
      exact congrFun ((normalizedSelectedLinear security degree selected hdegree).map_add first second) colors
    change ControlProduct.symmetrize _ = ControlProduct.symmetrize _ + ControlProduct.symmetrize _
    rw [hraw]
    exact (symmetrizeLinear (PS := Fin degree) (BS := Fin 0)).map_add _ _
  map_smul' scalar mass := by
    apply Subtype.ext
    have hraw : (fun colors (_ : Fin 0 → SafePalette security) =>
        normalizedSelectedDensity security degree (scalar • mass) selected hdegree colors) =
        scalar • (fun colors (_ : Fin 0 → SafePalette security) =>
          normalizedSelectedDensity security degree mass selected hdegree colors) := by
      funext colors _
      exact congrFun ((normalizedSelectedLinear security degree selected hdegree).map_smul scalar mass) colors
    change ControlProduct.symmetrize _ = scalar • ControlProduct.symmetrize _
    rw [hraw]
    exact (symmetrizeLinear (PS := Fin degree) (BS := Fin 0)).map_smul scalar _

def selectedFamilyLinear (security order : ℕ) (selected : Finset (Fin 4)) :
    ((Fin 4 → Palette security) → ℝ) →ₗ[ℝ] Family security order where
  toFun := fun mass => selectedFamily security order mass selected
  map_add' first second := by
    unfold selectedFamily
    split_ifs with hdegree
    · have hkernel := (selectedKernelLinear security selected.card selected (by simp)).map_add first second
      funext arity
      by_cases hequal : arity = selectedArity order selected hdegree
      · subst arity
        simp only [Pi.add_apply, Pi.single_eq_same]
        exact hkernel
      · simp only [Pi.add_apply, Pi.single_eq_of_ne hequal, add_zero]
    · exact (add_zero _).symm
  map_smul' scalar mass := by
    unfold selectedFamily
    split_ifs with hdegree
    · have hkernel := (selectedKernelLinear security selected.card selected (by simp)).map_smul scalar mass
      funext arity
      by_cases hequal : arity = selectedArity order selected hdegree
      · subst arity
        simp only [Pi.smul_apply, Pi.single_eq_same]
        exact hkernel
      · simp only [Pi.smul_apply, Pi.single_eq_of_ne hequal, smul_zero]
    · exact (smul_zero _).symm

def completeFamilyLinear (security order : ℕ) :
    ((Fin 4 → Palette security) → ℝ) →ₗ[ℝ] Family security order where
  toFun := completeFamily security order
  map_add' first second := by
    unfold completeFamily
    simp only [Pi.add_apply, Finset.sum_add_distrib, add_smul]
    simp only [show ∀ selected, selectedFamily security order (first + second) selected =
      selectedFamily security order first selected + selectedFamily security order second selected from
        fun selected => (selectedFamilyLinear security order selected).map_add first second,
      Finset.sum_add_distrib]
    abel
  map_smul' scalar mass := by
    unfold completeFamily
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_smul]
    simp only [show ∀ selected, selectedFamily security order (scalar • mass) selected =
      scalar • selectedFamily security order mass selected from
        fun selected => (selectedFamilyLinear security order selected).map_smul scalar mass,
      ← Finset.smul_sum, smul_add, RingHom.id_apply]

def independentSignedLinear (security : ℕ) :
    (Palette security → ℝ) →ₗ[ℝ] ((Fin 4 → Palette security) → ℝ) where
  toFun := IndependentPairedReference.independentSignedMass security
  map_add' first second := by
    funext word
    simp only [IndependentPairedReference.independentSignedMass, map_add, Pi.add_apply,
      mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' scalar score := by
    funext word
    simp only [IndependentPairedReference.independentSignedMass, map_smul, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro group _
    ring

def independentNormalizedLinear (security order : ℕ) :
    (Palette security → ℝ) →ₗ[ℝ] Family security order where
  toFun := independentNormalized security order
  map_add' first second := by
    unfold independentNormalized normalizedFamily
    rw [show IndependentPairedReference.independentSignedMass security (first + second) =
      IndependentPairedReference.independentSignedMass security first +
      IndependentPairedReference.independentSignedMass security second from
        (independentSignedLinear security).map_add first second]
    rw [show completeFamily security order
      (IndependentPairedReference.independentSignedMass security first +
        IndependentPairedReference.independentSignedMass security second) =
      completeFamily security order (IndependentPairedReference.independentSignedMass security first) +
      completeFamily security order (IndependentPairedReference.independentSignedMass security second) from
        (completeFamilyLinear security order).map_add _ _, add_mul]
  map_smul' scalar score := by
    unfold independentNormalized normalizedFamily
    rw [show IndependentPairedReference.independentSignedMass security (scalar • score) =
      scalar • IndependentPairedReference.independentSignedMass security score from
        (independentSignedLinear security).map_smul scalar score]
    rw [show completeFamily security order (scalar • IndependentPairedReference.independentSignedMass security score) =
      scalar • completeFamily security order (IndependentPairedReference.independentSignedMass security score) from
        (completeFamilyLinear security order).map_smul scalar _, smul_mul_assoc, RingHom.id_apply]

/-- A score is centered once relative to the common primary law, independently
of every hidden root and every choice of distinct public-control indices. -/
def centeredScores (security : ℕ) : Submodule ℝ (Palette security → ℝ) where
  carrier := {score | (primaryLaw security).expectation score = 0}
  zero_mem' := by simp [FiniteDist.expectation]
  add_mem' {first second} hfirst hsecond := by
    change (primaryLaw security).expectation first = 0 at hfirst
    change (primaryLaw security).expectation second = 0 at hsecond
    change (primaryLaw security).expectation (fun color => first color + second color) = 0
    rw [FiniteDist.expectation_add, hfirst, hsecond, add_zero]
  smul_mem' scalar score hscore := by
    change (primaryLaw security).expectation (fun color => scalar * score color) = 0
    rw [FiniteDist.expectation_const_mul, hscore, mul_zero]

def primaryEmbeddingLinear (security order : ℕ) (horder : 1 ≤ order) :
    centeredScores security →ₗ[ℝ] Family security order where
  toFun := fun score => BackgroundFamilies.primaryFamily (primaryLaw security) (bodyReference security)
    order horder score.val score.property
  map_add' first second := by
    unfold BackgroundFamilies.primaryFamily
    rw [← Pi.single_add]
    rfl
  map_smul' scalar score := by
    unfold BackgroundFamilies.primaryFamily
    rw [← Pi.single_smul]
    rfl

def localRaisingLinear (security order : ℕ) (horder : 1 ≤ order) :
    centeredScores security →ₗ[ℝ] Family security order :=
  (independentNormalizedLinear security order).comp (centeredScores security).subtype -
    primaryEmbeddingLinear security order horder





end
end CurrentAFT.LocalRaisingLinear

end

section















/-! # Actual higher local coefficients and their graded finite norm -/
namespace CurrentAFT.LocalRaisingNorm

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct ControlNorm
  GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverse GradedInverseNorm
  LocalCoefficientFamily LocalCoefficientNorm NormalizedLocalPolynomial LocalRaisingFirst BackgroundFamilies
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
abbrev Palette (security : ℕ) := ActualControls.Palette security

theorem independentComplete_eq_primary_add_higher (security order : ℕ) (horder : 1 ≤ order)
    (score : Palette security → ℝ) (hcentered : (primaryLaw security).expectation score = 0) :
    completeFamily security order (IndependentPairedReference.independentSignedMass security score) =
      primaryFamily (primaryLaw security) (bodyReference security) order horder score hcentered +
        higherFamily security order (IndependentPairedReference.independentSignedMass security score) := by
  funext arity
  change completeFamily security order (IndependentPairedReference.independentSignedMass security score) arity =
    primaryFamily (primaryLaw security) (bodyReference security) order horder score hcentered arity +
      higherFamily security order (IndependentPairedReference.independentSignedMass security score) arity
  by_cases hsmall : arity.val.1.val + arity.val.2.val < 2
  · rw [higherFamily_vanishesBelow security order _ arity hsmall, add_zero]
    exact sub_eq_zero.mp (independentComplete_sub_primary_raises security order horder score hcentered arity hsmall)
  · have hprimary : primaryFamily (primaryLaw security) (bodyReference security)
        order horder score hcentered arity = 0 := by
      unfold primaryFamily
      rw [Pi.single_eq_of_ne]
      intro hequal
      have h := congrArg (fun item : TruncatedArity order => item.val.1.val + item.val.2.val) hequal
      change arity.val.1.val + arity.val.2.val = 1 + 0 at h
      omega
    rw [hprimary, zero_add]
    unfold completeFamily higherFamily
    simp only [IndependentPairedReference.independentSigned_mass_zero security score hcentered,
      zero_smul, zero_add, Finset.sum_apply]
    symm
    apply Finset.sum_subset
    · intro selected hselected
      apply Finset.mem_erase.mpr
      constructor
      · intro hequal
        have hcard := (Finset.mem_filter.mp hselected).2
        rw [hequal, Finset.card_empty] at hcard
        omega
      · exact Finset.mem_univ _
    · intro selected _ hnot
      have hcard : selected.card < 2 := by
        by_contra! hcard
        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard⟩)
      unfold selectedFamily
      split_ifs with hdegree
      · rw [Pi.single_eq_of_ne]
        intro hequal
        have h := congrArg (fun item : TruncatedArity order => item.val.1.val + item.val.2.val) hequal
        change arity.val.1.val + arity.val.2.val = selected.card + 0 at h
        omega
      · rfl

def higherEnvelope (security : ℕ) (primaryFactor : ℝ) : ℝ :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).filter (fun selected => 2 ≤ selected.card),
    (8 * primaryFactor / activation security) ^ selected.card

theorem higherFamily_norm (security order : ℕ) (mass : (Fin 4 → Palette security) → ℝ)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor) :
    familyNorm (primaryLaw security) (bodyReference security) order primaryFactor bodyFactor
      (higherFamily security order mass) ≤
        higherEnvelope security primaryFactor * Real.sqrt (primaryMassEnergy security mass) := by
  unfold higherFamily higherEnvelope
  apply (familyNorm_sum_le _ _ order primaryFactor bodyFactor hprimary hbody _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro selected _
  apply (selectedFamily_norm security order mass selected primaryFactor bodyFactor hprimary).trans_eq
  calc
    _ = (primaryFactor * (2 / activation security) * 4) ^ selected.card *
        Real.sqrt (primaryMassEnergy security mass) := by rw [mul_pow, mul_pow]; ring
    _ = _ := by congr 1; congr 1; ring



theorem higherEnvelope_le (security : ℕ) (primaryFactor : ℝ) (hprimary : 0 ≤ primaryFactor)
    (hsmall : 8 * primaryFactor / activation security ≤ 1) :
    higherEnvelope security primaryFactor ≤ 16 * (8 * primaryFactor / activation security) ^ 2 := by
  have ht : 0 ≤ 8 * primaryFactor / activation security :=
    div_nonneg (mul_nonneg (by norm_num) hprimary) (activation_pos security).le
  unfold higherEnvelope
  calc
    _ ≤ ∑ _ ∈ (Finset.univ : Finset (Finset (Fin 4))).filter (fun selected => 2 ≤ selected.card),
        (8 * primaryFactor / activation security) ^ 2 := by
      apply Finset.sum_le_sum
      intro selected hselected
      exact pow_le_pow_of_le_one ht hsmall (Finset.mem_filter.mp hselected).2
    _ = ((Finset.univ : Finset (Finset (Fin 4))).filter (fun selected => 2 ≤ selected.card)).card *
        (8 * primaryFactor / activation security) ^ 2 := by simp
    _ ≤ 16 * (8 * primaryFactor / activation security) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact_mod_cast (show ((Finset.univ : Finset (Finset (Fin 4))).filter
        (fun selected => 2 ≤ selected.card)).card ≤ 16 by
          calc
            _ ≤ Fintype.card (Finset (Fin 4)) := Finset.card_le_univ _
            _ = 16 := by simp)

def nonemptyEnvelope (security : ℕ) (primaryFactor : ℝ) : ℝ :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
    (8 * primaryFactor / activation security) ^ selected.card

theorem positiveFamily_defect_norm (security order : ℕ) (law : FiniteDist (Fin 4 → Palette security))
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor) :
    familyNorm (primaryLaw security) (bodyReference security) order primaryFactor bodyFactor
      (positiveFamily security order law - 1) ≤
        nonemptyEnvelope security primaryFactor * Real.sqrt (primaryMassEnergy security law.weight) := by
  have hequal : positiveFamily security order law - 1 =
      ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
        selectedFamily security order law.weight selected := by
    unfold positiveFamily completeFamily
    rw [law.sum_one, one_smul]
    abel
  rw [hequal]
  apply (familyNorm_sum_le _ _ order primaryFactor bodyFactor hprimary hbody _ _).trans
  unfold nonemptyEnvelope
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro selected _
  apply (selectedFamily_norm security order law.weight selected primaryFactor bodyFactor hprimary).trans_eq
  calc
    _ = (primaryFactor * (2 / activation security) * 4) ^ selected.card *
        Real.sqrt (primaryMassEnergy security law.weight) := by rw [mul_pow, mul_pow]; ring
    _ = _ := by congr 1; congr 1; ring

theorem nonemptyEnvelope_le (security : ℕ) (primaryFactor : ℝ) (hprimary : 0 ≤ primaryFactor)
    (hsmall : 8 * primaryFactor / activation security ≤ 1) :
    nonemptyEnvelope security primaryFactor ≤ 16 * (8 * primaryFactor / activation security) := by
  have ht : 0 ≤ 8 * primaryFactor / activation security :=
    div_nonneg (mul_nonneg (by norm_num) hprimary) (activation_pos security).le
  unfold nonemptyEnvelope
  calc
    _ ≤ ∑ _ ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
        (8 * primaryFactor / activation security) := by
      apply Finset.sum_le_sum
      intro selected hselected
      have hcard : 1 ≤ selected.card := by
        have hne := (Finset.mem_erase.mp hselected).1
        have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
        omega
      simpa only [pow_one] using pow_le_pow_of_le_one ht hsmall hcard
    _ = ((Finset.univ : Finset (Finset (Fin 4))).erase ∅).card *
        (8 * primaryFactor / activation security) := by simp
    _ ≤ 16 * (8 * primaryFactor / activation security) := by
      apply mul_le_mul_of_nonneg_right _ ht
      exact_mod_cast (show ((Finset.univ : Finset (Finset (Fin 4))).erase ∅).card ≤ 16 by
        calc
          _ ≤ Fintype.card (Finset (Fin 4)) := Finset.card_le_univ _
          _ = 16 := by simp)

theorem actual_channel_factor (security : ℕ) :
    8 * BackgroundRates.primaryFactor security / activation security ≤
      32 / (Parameters.base security : ℝ) ^ 63 := by
  have hb := FirstResponse.base_pos security
  have hp : 0 ≤ BackgroundRates.primaryFactor security := by
    rw [BackgroundRates.primaryFactor_eq]
    positivity
  calc
    _ = (8 * BackgroundRates.primaryFactor security) * (1 / activation security) := by ring
    _ ≤ (8 * BackgroundRates.primaryFactor security) * (4 * (Parameters.base security : ℝ)) :=
      mul_le_mul_of_nonneg_left (FirstResponse.activation_inverse_le security) (by positivity)
    _ = _ := by
      rw [BackgroundRates.primaryFactor_eq, show 64 = 63 + 1 by omega, pow_succ]
      field_simp [hb.ne']
      ring

theorem actual_channel_factor_le_one (security : ℕ) :
    8 * BackgroundRates.primaryFactor security / activation security ≤ 1 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hb2 : (2 : ℝ) ≤ Parameters.base security := by exact_mod_cast Parameters.base_ge_two security
  have h5 : (32 : ℝ) ≤ (Parameters.base security : ℝ) ^ 5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hb2 5
    norm_num only [show (2 : ℝ) ^ 5 = 32 by norm_num] at h
    exact h
  have hpower : (Parameters.base security : ℝ) ^ 5 ≤ (Parameters.base security : ℝ) ^ 63 :=
    pow_le_pow_right₀ hb1 (by omega)
  exact (actual_channel_factor security).trans ((div_le_one (pow_pos hb _)).mpr (h5.trans hpower))

theorem actual_higherEnvelope (security : ℕ) :
    higherEnvelope security (BackgroundRates.primaryFactor security) ≤
      16384 / (Parameters.base security : ℝ) ^ 126 := by
  have hp : 0 ≤ BackgroundRates.primaryFactor security := by unfold BackgroundRates.primaryFactor; positivity
  have ht : 0 ≤ 8 * BackgroundRates.primaryFactor security / activation security :=
    div_nonneg (mul_nonneg (by norm_num) hp) (activation_pos security).le
  calc
    _ ≤ 16 * (8 * BackgroundRates.primaryFactor security / activation security) ^ 2 :=
      higherEnvelope_le security _ hp (actual_channel_factor_le_one security)
    _ ≤ 16 * (32 / (Parameters.base security : ℝ) ^ 63) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht (actual_channel_factor security) 2) (by norm_num)
    _ = _ := by rw [div_pow, ← pow_mul]; norm_num; ring

theorem actual_nonemptyEnvelope (security : ℕ) :
    nonemptyEnvelope security (BackgroundRates.primaryFactor security) ≤
      512 / (Parameters.base security : ℝ) ^ 63 := by
  have hp : 0 ≤ BackgroundRates.primaryFactor security := by unfold BackgroundRates.primaryFactor; positivity
  exact (nonemptyEnvelope_le security _ hp (actual_channel_factor_le_one security)).trans
    ((mul_le_mul_of_nonneg_left (actual_channel_factor security) (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by ring))

end
end CurrentAFT.LocalRaisingNorm

end

section













/-!
# Current parameter bounds for the constructed local raising response

All budgets below are derived from the concrete four-output reference law,
its actual primary inverse, and the current two control populations. The
finite inverse is bounded after an explicit fixed-constant threshold. No
local norm estimate, response identity, or invertibility is a premise.
-/
namespace CurrentAFT.LocalRaisingBounds

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct ControlNorm
  GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverse GradedInverseNorm
  LocalCoefficientFamily LocalCoefficientNorm NormalizedLocalPolynomial LocalRaisingFirst LocalRaisingNorm
  BackgroundFamilies LocalReferenceEnergy PairedReferenceEnergy IndependentReferenceEnergy
open Filter
open scoped BigOperators Classical Topology
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
abbrev Palette (security : ℕ) := ActualControls.Palette security

def coefficientNorm (security order : ℕ) (family : Family security order) : ℝ :=
  familyNorm (primaryLaw security) (bodyReference security) order
    (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) family

def pairConstant : ℝ := 524288 + 17180131328 * Real.exp Real.pi

def higherConstant : ℝ := 16384 * Real.sqrt 66048 * Real.sqrt pairConstant

def positiveConstant : ℝ := 8192 * Real.sqrt pairConstant

def raisingConstant : ℝ := 2 * (higherConstant + positiveConstant)

theorem pairConstant_nonneg : 0 ≤ pairConstant := by unfold pairConstant; positivity

theorem higherConstant_nonneg : 0 ≤ higherConstant := by unfold higherConstant; positivity

theorem positiveConstant_nonneg : 0 ≤ positiveConstant := by unfold positiveConstant; positivity

 theorem primaryFactor_nonneg (security : ℕ) : 0 ≤ BackgroundRates.primaryFactor security := by
  unfold BackgroundRates.primaryFactor
  positivity

 theorem bodyFactor_nonneg (security : ℕ) : 0 ≤ BackgroundRates.bodyFactor security := by
  unfold BackgroundRates.bodyFactor BackgroundRates.radius
  positivity

 theorem base_ge_one (security : ℕ) : (1 : ℝ) ≤ Parameters.base security := by
  exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)

theorem pairBudget_sqrt_polynomial (security : ℕ) :
    Real.sqrt (pairBudget security) ≤ Real.sqrt pairConstant * (Parameters.base security : ℝ) ^ 24 := by
  have hpower : (Parameters.base security : ℝ) ^ 47 ≤ (Parameters.base security : ℝ) ^ 48 :=
    pow_le_pow_right₀ (base_ge_one security) (by omega)
  have hbudget : pairBudget security ≤ pairConstant * (Parameters.base security : ℝ) ^ 48 :=
    (pairBudget_polynomial security).trans (mul_le_mul_of_nonneg_left hpower pairConstant_nonneg)
  apply (Real.sqrt_le_sqrt hbudget).trans_eq
  rw [Real.sqrt_mul pairConstant_nonneg, show (48 : ℕ) = 24 * 2 by omega, pow_mul,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (pow_nonneg (FirstResponse.base_pos security).le _)]

theorem independentSigned_primaryMass_sqrt (security : ℕ) (score : Palette security → ℝ) :
    Real.sqrt (primaryMassEnergy security (IndependentPairedReference.independentSignedMass security score)) ≤
      Real.sqrt 66048 * Real.sqrt pairConstant * (Parameters.base security : ℝ) ^ 24 *
        Real.sqrt ((primaryLaw security).expectation (fun color => score color ^ 2)) := by
  have hinput := (primaryLaw security).l2Sq_nonneg score
  have hmass : primaryMassEnergy security (IndependentPairedReference.independentSignedMass security score) ≤
      (66048 * pairBudget security) * (primaryLaw security).expectation (fun color => score color ^ 2) :=
    (primaryMassEnergy_uniform_le security _).trans ((mul_le_mul_of_nonneg_left
      (independentSigned_energy security score) (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by ring))
  calc
    _ ≤ Real.sqrt ((66048 * pairBudget security) *
        (primaryLaw security).expectation (fun color => score color ^ 2)) := Real.sqrt_le_sqrt hmass
    _ = Real.sqrt 66048 * Real.sqrt (pairBudget security) *
        Real.sqrt ((primaryLaw security).expectation (fun color => score color ^ 2)) := by
      rw [Real.sqrt_mul (mul_nonneg (by norm_num) (pairBudget_nonneg security)), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 66048)]
    _ ≤ _ := by
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pairBudget_sqrt_polynomial security)
        (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)).trans_eq (by ring)

theorem independentHigher_norm (security order : ℕ) (score : Palette security → ℝ) :
    coefficientNorm security order
      (higherFamily security order (IndependentPairedReference.independentSignedMass security score)) ≤
        (higherConstant / (Parameters.base security : ℝ) ^ 102) *
          Real.sqrt ((primaryLaw security).expectation (fun color => score color ^ 2)) := by
  have hb := FirstResponse.base_pos security
  have h := higherFamily_norm security order (IndependentPairedReference.independentSignedMass security score)
    (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
    (primaryFactor_nonneg security) (bodyFactor_nonneg security)
  apply h.trans
  apply (mul_le_mul (actual_higherEnvelope security) (independentSigned_primaryMass_sqrt security score)
    (Real.sqrt_nonneg _) (by positivity : (0 : ℝ) ≤ 16384 / (Parameters.base security : ℝ) ^ 126)).trans_eq
  unfold higherConstant
  rw [show (126 : ℕ) = 102 + 24 by omega, pow_add]
  field_simp [hb.ne']

theorem independentPositive_primaryMass_sqrt (security : ℕ) :
    Real.sqrt (primaryMassEnergy security (independentPositiveLaw security).weight) ≤
      16 * Real.sqrt pairConstant * (Parameters.base security : ℝ) ^ 24 := by
  have hmass : primaryMassEnergy security (independentPositiveLaw security).weight ≤ 256 * pairBudget security :=
    (primaryMassEnergy_uniform_le security _).trans ((mul_le_mul_of_nonneg_left
      (independentPositive_energy security) (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by ring))
  calc
    _ ≤ Real.sqrt (256 * pairBudget security) := Real.sqrt_le_sqrt hmass
    _ = 16 * Real.sqrt (pairBudget security) := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 256)]; norm_num
    _ ≤ _ := (mul_le_mul_of_nonneg_left (pairBudget_sqrt_polynomial security)
      (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by ring)

theorem independentPositive_defect (security order : ℕ) :
    coefficientNorm security order (positiveFamily security order (independentPositiveLaw security) - 1) ≤
      positiveConstant / (Parameters.base security : ℝ) ^ 39 := by
  have hb := FirstResponse.base_pos security
  have h := positiveFamily_defect_norm security order (independentPositiveLaw security)
    (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
    (primaryFactor_nonneg security) (bodyFactor_nonneg security)
  apply h.trans
  apply (mul_le_mul (actual_nonemptyEnvelope security) (independentPositive_primaryMass_sqrt security)
    (Real.sqrt_nonneg _) (by positivity : (0 : ℝ) ≤ 512 / (Parameters.base security : ℝ) ^ 63)).trans_eq
  unfold positiveConstant
  rw [show (63 : ℕ) = 39 + 24 by omega, pow_add]
  field_simp [hb.ne']
  ring

def positiveInverse (security order : ℕ) : Family security order :=
  backgroundInverse (primaryLaw security) (bodyReference security) order
    (positiveFamily security order (independentPositiveLaw security))

theorem positiveInverse_bounds (security order : ℕ)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ)) :
    coefficientNorm security order (positiveInverse security order) ≤ 2 ∧
      coefficientNorm security order (positiveInverse security order - 1) ≤
        2 * positiveConstant / (Parameters.base security : ℝ) ^ 39 := by
  let theta := positiveConstant / (Parameters.base security : ℝ) ^ 39
  have htheta : 0 ≤ theta := div_nonneg positiveConstant_nonneg (pow_nonneg (FirstResponse.base_pos security).le _)
  have hpower : (Parameters.base security : ℝ) ≤ (Parameters.base security : ℝ) ^ 39 := by
    simpa only [pow_one] using pow_le_pow_right₀ (base_ge_one security) (show 1 ≤ 39 by omega)
  have hhalf : theta ≤ 1 / 2 := by
    apply (div_le_iff₀ (pow_pos (FirstResponse.base_pos security) _)).mpr
    linarith
  have hgap : theta < 1 := by linarith
  have hdefect : coefficientNorm security order (1 - positiveFamily security order (independentPositiveLaw security)) ≤ theta := by
    have hequal : (1 - positiveFamily security order (independentPositiveLaw security) : Family security order) =
      -(positiveFamily security order (independentPositiveLaw security) - 1) := by abel
    rw [hequal, coefficientNorm, familyNorm_neg]
    exact independentPositive_defect security order
  constructor
  · apply (backgroundInverse_norm_le (primaryLaw security) (bodyReference security) order
      (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
      (primaryFactor_nonneg security) (bodyFactor_nonneg security) _ theta hgap hdefect).trans
    apply (div_le_iff₀ (sub_pos.mpr hgap)).mpr
    linarith
  · apply (backgroundInverse_correction_norm_le (primaryLaw security) (bodyReference security) order
      (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
      (primaryFactor_nonneg security) (bodyFactor_nonneg security) _ theta hgap hdefect).trans
    calc
      _ ≤ theta / (1 / 2) := div_le_div_of_nonneg_left htheta (by norm_num) (by linarith)
      _ = _ := by unfold theta; ring



theorem localRaising_bound (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ))
    (score : Palette security → ℝ) (hcentered : (primaryLaw security).expectation score = 0) :
    coefficientNorm security order (localRaising security order horder score hcentered) ≤
      (raisingConstant / (Parameters.base security : ℝ) ^ 102) *
        Real.sqrt ((primaryLaw security).expectation (fun color => score color ^ 2)) := by
  let primary := primaryFamily (primaryLaw security) (bodyReference security) order horder score hcentered
  let higher := higherFamily security order (IndependentPairedReference.independentSignedMass security score)
  have hsplit : localRaising security order horder score hcentered =
      higher * positiveInverse security order + primary * (positiveInverse security order - 1) := by
    unfold localRaising independentNormalized normalizedFamily
    rw [independentComplete_eq_primary_add_higher security order horder score hcentered]
    change (primary + higher) * positiveInverse security order - primary = _
    rw [add_mul, mul_sub, mul_one]
    abel
  have hinverse := positiveInverse_bounds security order hlarge
  have hnormPrimary : coefficientNorm security order primary =
      BackgroundRates.primaryFactor security *
        Real.sqrt ((primaryLaw security).expectation (fun color => score color ^ 2)) :=
    primaryFamily_norm _ _ order horder _ _ score hcentered
  have hinput := Real.sqrt_nonneg ((primaryLaw security).expectation (fun color => score color ^ 2))
  have hprimaryNonneg := familyNorm_nonneg (primaryLaw security) (bodyReference security) order
    (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
    (primaryFactor_nonneg security) (bodyFactor_nonneg security) primary
  have hhigh := independentHigher_norm security order score
  have hnormInverseNonneg := familyNorm_nonneg (primaryLaw security) (bodyReference security) order
    (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
    (primaryFactor_nonneg security) (bodyFactor_nonneg security) (positiveInverse security order)
  have hhighBoundNonneg : 0 ≤ (higherConstant / (Parameters.base security : ℝ) ^ 102) *
      Real.sqrt ((primaryLaw security).expectation (fun color => score color ^ 2)) :=
    mul_nonneg (div_nonneg higherConstant_nonneg (pow_nonneg (FirstResponse.base_pos security).le _)) hinput
  have hpf : BackgroundRates.primaryFactor security ≤ 1 / (Parameters.base security : ℝ) ^ 63 := by
    rw [BackgroundRates.primaryFactor_eq]
    exact one_div_le_one_div_of_le (pow_pos (FirstResponse.base_pos security) _)
      (pow_le_pow_right₀ (base_ge_one security) (show 63 ≤ 64 by omega))
  have hcoef : (BackgroundRates.primaryFactor security *
        Real.sqrt ((primaryLaw security).expectation (fun color => score color ^ 2))) *
        (2 * positiveConstant / (Parameters.base security : ℝ) ^ 39) ≤
      (2 * positiveConstant / (Parameters.base security : ℝ) ^ 102) *
        Real.sqrt ((primaryLaw security).expectation (fun color => score color ^ 2)) := by
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpf hinput)
      (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) positiveConstant_nonneg)
        (pow_nonneg (FirstResponse.base_pos security).le 39))
    apply h.trans_eq
    rw [show (102 : ℕ) = 63 + 39 by omega, pow_add]
    ring
  rw [hsplit]
  calc
    _ ≤ coefficientNorm security order (higher * positiveInverse security order) +
        coefficientNorm security order (primary * (positiveInverse security order - 1)) :=
      familyNorm_add_le _ _ order _ _ (primaryFactor_nonneg security) (bodyFactor_nonneg security) _ _
    _ ≤ coefficientNorm security order higher * coefficientNorm security order (positiveInverse security order) +
        coefficientNorm security order primary * coefficientNorm security order (positiveInverse security order - 1) :=
      add_le_add (familyNorm_product_le _ _ order _ _ (primaryFactor_nonneg security) (bodyFactor_nonneg security) _ _)
        (familyNorm_product_le _ _ order _ _ (primaryFactor_nonneg security) (bodyFactor_nonneg security) _ _)
    _ ≤ ((higherConstant / (Parameters.base security : ℝ) ^ 102) *
        Real.sqrt ((primaryLaw security).expectation (fun color => score color ^ 2))) * 2 +
        coefficientNorm security order primary * (2 * positiveConstant / (Parameters.base security : ℝ) ^ 39) := by
      exact add_le_add (mul_le_mul hhigh hinverse.1 hnormInverseNonneg hhighBoundNonneg)
        (mul_le_mul_of_nonneg_left hinverse.2 hprimaryNonneg)
    _ ≤ ((higherConstant / (Parameters.base security : ℝ) ^ 102) *
        Real.sqrt ((primaryLaw security).expectation (fun color => score color ^ 2))) * 2 +
        (2 * positiveConstant / (Parameters.base security : ℝ) ^ 102) *
          Real.sqrt ((primaryLaw security).expectation (fun color => score color ^ 2)) := by
      rw [hnormPrimary]
      exact add_le_add le_rfl hcoef
    _ = _ := by unfold raisingConstant; ring



end
end CurrentAFT.LocalRaisingBounds

end

section











/-! # Finite Hilbert coordinates of the actual graded coefficient algebra -/
namespace CurrentAFT.CoefficientHilbert

open AFT ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GradedControlNorm
  GradedControlStability LocalRaisingLinear LocalRaisingBounds
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

















def centerLinear {Color : Type*} [Fintype Color] (law : FiniteDist Color) : (Color → ℝ) →ₗ[ℝ] (Color → ℝ) where
  toFun score := fun color => score color - law.expectation score
  map_add' first second := by
    funext color
    change first color + second color - law.expectation (fun point => first point + second point) = _
    rw [FiniteDist.expectation_add]
    simp only [Pi.add_apply]
    ring
  map_smul' scalar score := by
    funext color
    change scalar * score color - law.expectation (fun point => scalar * score point) = _
    rw [FiniteDist.expectation_const_mul]
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem center_mean {Color : Type*} [Fintype Color] (law : FiniteDist Color) (score : Color → ℝ) :
    law.expectation (centerLinear law score) = 0 := by
  change law.expectation (fun color => score color - law.expectation score) = 0
  rw [FiniteDist.expectation_sub, FiniteDist.expectation_const, sub_self]

theorem center_energy {Color : Type*} [Fintype Color] (law : FiniteDist Color) (score : Color → ℝ) :
    law.l2Sq (centerLinear law score) = law.l2Sq score - (law.expectation score) ^ 2 := by
  have hexpand (color : Color) : (score color - law.expectation score) ^ 2 =
      score color ^ 2 - 2 * law.expectation score * score color + (law.expectation score) ^ 2 := by ring
  unfold FiniteDist.l2Sq
  change law.expectation (fun color => (score color - law.expectation score) ^ 2) = _
  simp_rw [hexpand]
  rw [FiniteDist.expectation_add, FiniteDist.expectation_sub, FiniteDist.expectation_const_mul,
    FiniteDist.expectation_const]
  ring

theorem center_energy_le {Color : Type*} [Fintype Color] (law : FiniteDist Color) (score : Color → ℝ) :
    law.l2Sq (centerLinear law score) ≤ law.l2Sq score := by
  rw [center_energy]
  linarith [sq_nonneg (law.expectation score)]

end
end CurrentAFT.CoefficientHilbert

end

section














/-!
# The actual primary and safe-body endpoint forms for background families

Primary forms use the genuine calibrated first response. Body forms use
the actual protected cyclic root convolution of a safe-center Dirac mass.
-/

namespace CurrentAFT.BackgroundEvaluation

open AFT ControlCoordinates LeadingEvaluation DiffuseProfiles ProposalPrimary ActualControls
  PrimaryTensorInverse PrimaryMassFamilies MarkedPairLeading LocalCoefficientFamily LocalCoefficientEvaluation
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def bodyForm (security : ℕ) (center : SafePalette security) : MvPolynomial (ActualControls.Palette security) ℝ :=
  RepresentedPolynomial.profileForm (bodyConvolution security (Pi.single center.val 1))

theorem bodyForm_homogeneous (security : ℕ) (center : SafePalette security) : (bodyForm security center).IsHomogeneous 1 := by
  rw [bodyForm, RepresentedPolynomial.profileForm_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro output _
  exact (MvPolynomial.isHomogeneous_C _ _).mul (MvPolynomial.isHomogeneous_X ℝ output)

def evaluation (security order : ℕ) :=
  LocalCoefficientEvaluation.evaluation security order (bodyForm security) (bodyForm_homogeneous security)









end

end CurrentAFT.BackgroundEvaluation

end

section












/-! Literal degree-one primary evaluation for the concrete background certificates. -/

namespace CurrentAFT.BackgroundFirstEvaluation

open AFT ControlCoordinates LeadingEvaluation DiffuseProfiles ProposalPrimary ActualControls
  PrimaryTensorInverse PrimaryMassFamilies BackgroundFamilies BackgroundEvaluation
  LocalCoefficientFamily LocalCoefficientEvaluation FringeCertificate BackgroundTranslations
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _


















end

end CurrentAFT.BackgroundFirstEvaluation

end

section














/-!
# Actual two-alphabet canonical point reconstruction

Every joint kernel is kept intact in its finite reference sum. The two
slot families use their own reference laws. No product assumption on the
input kernel is made.
-/

namespace CurrentAFT.CanonicalReconstruction

open AFT ControlCoordinates ControlProduct
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

def pointTensor {r s : ℕ} (primary : FiniteDist Primary) (body : FiniteDist Body)
    (sourcePrimary : Fin r → Primary) (sourceBody : Fin s → Body) :
    DensityKernel (Primary := Primary) (Body := Body) r s :=
  fun colors centers =>
    (∏ index, Hoeffding.centeredAtom primary (sourcePrimary index) (colors index)) *
      ∏ index, Hoeffding.centeredAtom body (sourceBody index) (centers index)









 theorem atomProduct_centered {Color Index : Type*} [Fintype Color] [Fintype Index]
    [DecidableEq Index] (law : FiniteDist Color) (hpositive : ∀ color, 0 < law.weight color)
    (source output : Index → Color) (fixed : Index) :
    (∑ color, law.weight color *
      ∏ index, Hoeffding.centeredAtom law (source index) (Function.update output fixed color index)) = 0 := by
  have hproduct (color : Color) :
      (∏ index, Hoeffding.centeredAtom law (source index) (Function.update output fixed color index)) =
        Hoeffding.centeredAtom law (source fixed) color *
          ∏ index ∈ Finset.univ.erase fixed, Hoeffding.centeredAtom law (source index) (output index) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ fixed), Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro index hindex
    rw [Function.update_of_ne (Finset.mem_erase.mp hindex).1]
  simp only [hproduct, ← mul_assoc, ← Finset.sum_mul,
    Hoeffding.centeredAtom_mean law hpositive, zero_mul]

theorem pointTensor_centered (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hprimary : ∀ color, 0 < primary.weight color) (hbody : ∀ color, 0 < body.weight color)
    {r s : ℕ} (sourcePrimary : Fin r → Primary) (sourceBody : Fin s → Body) :
    pointTensor primary body sourcePrimary sourceBody ∈ centeredKernelSpace primary body := by
  constructor
  · intro index colors centers
    simp only [pointTensor, ← mul_assoc, ← Finset.sum_mul,
      atomProduct_centered primary hprimary sourcePrimary colors index, zero_mul]
  · intro index colors centers
    simp only [pointTensor]
    calc
      _ = (∏ primaryIndex, Hoeffding.centeredAtom primary (sourcePrimary primaryIndex) (colors primaryIndex)) *
          ∑ color, body.weight color *
            ∏ bodyIndex, Hoeffding.centeredAtom body (sourceBody bodyIndex) (Function.update centers index color bodyIndex) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro color _
        ring
      _ = 0 := by rw [atomProduct_centered body hbody sourceBody centers index, mul_zero]

def pointKernel (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hprimary : ∀ color, 0 < primary.weight color) (hbody : ∀ color, 0 < body.weight color)
    {r s : ℕ} (sourcePrimary : Fin r → Primary) (sourceBody : Fin s → Body) :
    canonicalKernels primary body r s := by
  let raw := pointTensor primary body sourcePrimary sourceBody
  have hcenter := symmetrize_centered primary body raw
    (pointTensor_centered primary body hprimary hbody sourcePrimary sourceBody)
  refine ⟨symmetrize raw, hcenter.1, hcenter.2, ?_⟩
  intro primaryOrder bodyOrder colors centers
  rw [symmetrize_primary_permutation, symmetrize_body_permutation]



end

end CurrentAFT.CanonicalReconstruction

end

section














/-!
# The primary part of the actual finite-sum degree-raising response

The leading coefficient is the original canonical joint kernel. Every
nonleading pattern replaces a nonempty set of its primary slots by the
constructed local raising response. All source coordinates are summed
against the original joint kernel and the two actual product references;
no factorization of that kernel is assumed. Ordinary reciprocal corrections
are added separately in `CompleteRaising`.
-/
namespace CurrentAFT.GlobalRaising

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
  GradedControlAlgebra GradedInverse LocalCoefficientFamily LocalRaisingFirst LocalRaisingLinear
  BackgroundFamilies
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
abbrev Palette (security : ℕ) := ActualControls.Palette security

def primaryAtom (security : ℕ) (source : Palette security) : centeredScores security :=
  ⟨Hoeffding.centeredAtom (primaryLaw security) source,
    Hoeffding.centeredAtom_mean _ (primaryReference_positive security) source⟩

def primaryPoint (security order : ℕ) (horder : 1 ≤ order) (source : Palette security) : Family security order :=
  primaryEmbeddingLinear security order horder (primaryAtom security source)

def raisedPoint (security order : ℕ) (horder : 1 ≤ order) (source : Palette security) : Family security order :=
  localRaisingLinear security order horder (primaryAtom security source)

def bodyPoint (security order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) : Family security order :=
  bodyFamily (primaryLaw security) (bodyReference security) order horder
    (Hoeffding.centeredAtom (bodyReference security) source)
      (Hoeffding.centeredAtom_mean _ (bodyReference_positive security) source)







section Filtration
variable {Primary Body Index : Type*} [Fintype Primary] [Fintype Body]

theorem vanishesBelow_smul (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order degree : ℕ) (scalar : ℝ) (family : KernelFamily primary body order)
    (hfamily : VanishesBelow primary body order degree family) :
    VanishesBelow primary body order degree (scalar • family) := by
  intro arity hdegree
  change scalar • family arity = 0
  rw [hfamily arity hdegree, smul_zero]

theorem vanishesBelow_prod (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (selected : Finset Index) (degree : Index → ℕ)
    (family : Index → KernelFamily primary body order)
    (hfamily : ∀ index ∈ selected, VanishesBelow primary body order (degree index) (family index)) :
    VanishesBelow primary body order (∑ index ∈ selected, degree index) (∏ index ∈ selected, family index) := by
  induction selected using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    exact vanishesBelow_zero primary body order _
  | @insert index selected hnot ih =>
    rw [Finset.sum_insert hnot, Finset.prod_insert hnot]
    exact vanishesBelow_mul primary body order _ _ _ _
      (hfamily index (Finset.mem_insert_self _ _))
      (ih (fun other hother => hfamily other (Finset.mem_insert_of_mem hother)))

end Filtration

































end
end CurrentAFT.GlobalRaising

end

section



















/-!
# The actual ordinary group's normalized response

Its signed numerator retains the original safe body slot. The reciprocal
of its positive output polynomial is represented solely by new primary
slots, using the constructed first-primary inverse. Thus reciprocal
corrections do not create body slots.
-/
namespace CurrentAFT.OrdinaryRaising

open AFT DiffuseProfiles ProposalPrimary ActualControls FringeCertificate BackgroundCertificates
  ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GradedControlNorm GradedControlStability
  GradedInverse GradedInverseNorm LocalCoefficientFamily LocalRaisingFirst LocalRaisingBounds
  PrimaryTensorInverse PrimaryMassFamilies BackgroundFamilies LocalReferenceEnergy
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
abbrev Palette (security : ℕ) := ActualControls.Palette security

def deviation (security : ℕ) : Palette security → ℝ :=
  (convolvedCenterLaw security).weight - uniformProfile security

theorem deviation_mass (security : ℕ) : ∑ color, deviation security color = 0 := by
  have hq := (FirstResponse.modulus_pos security).ne'
  simp only [deviation, Pi.sub_apply, uniformProfile, Finset.sum_sub_distrib, FiniteDist.sum_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  norm_num

theorem convolvedCenter_height (security : ℕ) (output : Palette security) :
    (convolvedCenterLaw security).weight output ≤ 4 / (Parameters.modulus security : ℝ) := by
  rw [convolvedCenterLaw_weight]
  unfold rootConvolutionProfile
  calc
    _ ≤ ∑ seed, (actualSeedLaw security).weight seed * (4 / (Parameters.modulus security : ℝ)) := by
      apply Finset.sum_le_sum
      intro seed _
      exact mul_le_mul_of_nonneg_left (centerLaw_height security _) ((actualSeedLaw security).nonneg seed)
    _ = _ := by rw [← Finset.sum_mul, (actualSeedLaw security).sum_one, one_mul]

theorem convolvedCenter_uniform_energy (security : ℕ) :
    profileSquareNorm (uniformReference security).weight (convolvedCenterLaw security).weight ≤ 4 := by
  have h := BlockDensity.profile_energy_le_ratio (uniformReference security).weight
    (convolvedCenterLaw security).weight 4
    (fun color => by rw [uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security))
    (convolvedCenterLaw security).nonneg (fun color => by
      rw [uniformReference_weight]
      exact (convolvedCenter_height security color).trans_eq (by ring))
  simpa only [FiniteDist.sum_one, mul_one] using h

theorem profile_primary_energy_le_uniform (security : ℕ) (profile : Palette security → ℝ) :
    profileSquareNorm (primaryLaw security).weight profile ≤
      2 * profileSquareNorm (uniformReference security).weight profile := by
  unfold profileSquareNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro color _
  have hq := FirstResponse.modulus_pos security
  have hlower : 1 / (2 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight color := by
    simpa only [primaryLaw] using primaryProfile_atom_lower security color
  exact (div_le_div_of_nonneg_left (sq_nonneg (profile color)) (by positivity) hlower).trans_eq (by
    rw [uniformReference_weight]
    ring)

theorem deviation_energy (security : ℕ) : profileSquareNorm (primaryLaw security).weight (deviation security) ≤ 20 := by
  have hself := (profile_primary_energy_le_uniform security (convolvedCenterLaw security).weight).trans
    (mul_le_mul_of_nonneg_left (convolvedCenter_uniform_energy security) (by norm_num : (0 : ℝ) ≤ 2))
  have h := FringeCertificate.profileSquareNorm_sub_le_two security (convolvedCenterLaw security).weight (uniformProfile security)
  exact h.trans (by linarith [uniformProfile_square_le_two security])

def positiveAtom (security order : ℕ) (horder : 1 ≤ order) : Family security order :=
  massCertificateFamily security order 1 horder (oneWordProfile (deviation security))
    (oneWordProfile_centered _ (deviation_mass security)) (oneWordProfile_symmetric _)



theorem positiveAtom_norm (security order : ℕ) (horder : 1 ≤ order) :
    coefficientNorm security order (positiveAtom security order horder) ≤
      40 / (Parameters.base security : ℝ) ^ 63 := by
  have hb := FirstResponse.base_pos security
  have ha := activation_pos security
  have hp : 0 ≤ BackgroundRates.primaryFactor security := by unfold BackgroundRates.primaryFactor; positivity
  have hinv : 2 / activation security ≤ 8 * (Parameters.base security : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (FirstResponse.activation_inverse_le security) (show (0 : ℝ) ≤ 2 by norm_num)
    convert h using 1 <;> first | rfl | ring
  have henergyEq : massEnergy security 1 (oneWordProfile (deviation security)) =
      profileSquareNorm (primaryLaw security).weight (deviation security) :=
    oneWordProfile_energy (primaryLaw security).weight (deviation security)
  have hsqrt : Real.sqrt (massEnergy security 1 (oneWordProfile (deviation security))) ≤ 5 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, (henergyEq.le.trans (deviation_energy security)).trans (by norm_num)⟩
  have h := massCertificateFamily_norm security order 1 horder
    (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) hp
    (oneWordProfile (deviation security)) (oneWordProfile_centered _ (deviation_mass security)) (oneWordProfile_symmetric _)
  simp only [pow_one] at h
  calc
    _ ≤ BackgroundRates.primaryFactor security * (2 / activation security) *
        Real.sqrt (massEnergy security 1 (oneWordProfile (deviation security))) := h
    _ ≤ (1 / (Parameters.base security : ℝ) ^ 64) * (8 * (Parameters.base security : ℝ)) * 5 :=
      mul_le_mul (mul_le_mul (le_of_eq (BackgroundRates.primaryFactor_eq security)) hinv (by positivity) (by positivity))
        hsqrt (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by field_simp; norm_num

def positiveFamily (security order : ℕ) (horder : 1 ≤ order) : Family security order :=
  1 + positiveAtom security order horder

def positiveInverse (security order : ℕ) (horder : 1 ≤ order) : Family security order :=
  backgroundInverse (primaryLaw security) (bodyReference security) order (positiveFamily security order horder)



def normalizedFamily (security order : ℕ) (horder : 1 ≤ order)
    (score : SafePalette security → ℝ) (hcentered : (bodyReference security).expectation score = 0) : Family security order :=
  bodyFamily (primaryLaw security) (bodyReference security) order horder score hcentered * positiveInverse security order horder

def raisingFamily (security order : ℕ) (horder : 1 ≤ order)
    (score : SafePalette security → ℝ) (hcentered : (bodyReference security).expectation score = 0) : Family security order :=
  bodyFamily (primaryLaw security) (bodyReference security) order horder score hcentered * (positiveInverse security order horder - 1)









theorem positiveInverse_bounds (security order : ℕ) (horder : 1 ≤ order) :
    coefficientNorm security order (positiveInverse security order horder) ≤ 2 ∧
      coefficientNorm security order (positiveInverse security order horder - 1) ≤
        80 / (Parameters.base security : ℝ) ^ 63 := by
  have hb := FirstResponse.base_pos security
  have hp : 0 ≤ BackgroundRates.primaryFactor security := by unfold BackgroundRates.primaryFactor; positivity
  have hbody : 0 ≤ BackgroundRates.bodyFactor security := by unfold BackgroundRates.bodyFactor BackgroundRates.radius; positivity
  let theta := 40 / (Parameters.base security : ℝ) ^ 63
  have htheta : 0 ≤ theta := by dsimp only [theta]; positivity
  have htwo : (2 : ℝ) ≤ Parameters.base security := by exact_mod_cast Parameters.base_ge_two security
  have hone : (1 : ℝ) ≤ Parameters.base security := by linarith
  have h7 : (128 : ℝ) ≤ (Parameters.base security : ℝ) ^ 7 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 7
    norm_num only [show (2 : ℝ) ^ 7 = 128 by norm_num] at h
    exact h
  have hpower : (Parameters.base security : ℝ) ^ 7 ≤ (Parameters.base security : ℝ) ^ 63 :=
    pow_le_pow_right₀ hone (by omega)
  have hhalf : theta ≤ 1 / 2 := by
    apply (div_le_iff₀ (pow_pos hb _)).mpr
    linarith
  have hgap : theta < 1 := by linarith
  have hdefect : coefficientNorm security order (1 - positiveFamily security order horder) ≤ theta := by
    have hequal : (1 - positiveFamily security order horder : Family security order) = -positiveAtom security order horder := by
      unfold positiveFamily
      abel
    rw [hequal]
    unfold LocalRaisingBounds.coefficientNorm
    rw [familyNorm_neg]
    exact positiveAtom_norm security order horder
  constructor
  · apply (backgroundInverse_norm_le _ _ order _ _ hp hbody _ theta hgap hdefect).trans
    apply (div_le_iff₀ (sub_pos.mpr hgap)).mpr
    linarith
  · apply (backgroundInverse_correction_norm_le _ _ order _ _ hp hbody _ theta hgap hdefect).trans
    calc
      _ ≤ theta / (1 / 2) := div_le_div_of_nonneg_left htheta (by norm_num) (by linarith)
      _ = _ := by dsimp only [theta]; ring

theorem raisingFamily_norm (security order : ℕ) (horder : 1 ≤ order)
    (score : SafePalette security → ℝ) (hcentered : (bodyReference security).expectation score = 0) :
    coefficientNorm security order (raisingFamily security order horder score hcentered) ≤
      (80 / (Parameters.base security : ℝ) ^ 63) * BackgroundRates.bodyFactor security *
        Real.sqrt ((bodyReference security).l2Sq score) := by
  have hp : 0 ≤ BackgroundRates.primaryFactor security := by unfold BackgroundRates.primaryFactor; positivity
  have hbody : 0 ≤ BackgroundRates.bodyFactor security := by unfold BackgroundRates.bodyFactor BackgroundRates.radius; positivity
  have hnorm : coefficientNorm security order (bodyFamily (primaryLaw security) (bodyReference security)
      order horder score hcentered) = BackgroundRates.bodyFactor security * Real.sqrt ((bodyReference security).l2Sq score) :=
    bodyFamily_norm _ _ order horder _ _ score hcentered
  unfold LocalRaisingBounds.coefficientNorm at hnorm
  unfold raisingFamily
  apply (familyNorm_product_le _ _ order _ _ hp hbody _ _).trans
  rw [hnorm]
  exact (mul_le_mul_of_nonneg_left (positiveInverse_bounds security order horder).2
    (mul_nonneg hbody (Real.sqrt_nonneg _))).trans_eq (by ring)

def centeredBodyScores (security : ℕ) : Submodule ℝ (SafePalette security → ℝ) where
  carrier := {score | (bodyReference security).expectation score = 0}
  zero_mem' := by simp [FiniteDist.expectation]
  add_mem' {first second} hfirst hsecond := by
    change (bodyReference security).expectation first = 0 at hfirst
    change (bodyReference security).expectation second = 0 at hsecond
    change (bodyReference security).expectation (fun color => first color + second color) = 0
    rw [FiniteDist.expectation_add, hfirst, hsecond, add_zero]
  smul_mem' scalar score hscore := by
    change (bodyReference security).expectation (fun color => scalar * score color) = 0
    rw [FiniteDist.expectation_const_mul, hscore, mul_zero]

def bodyEmbeddingLinear (security order : ℕ) (horder : 1 ≤ order) :
    centeredBodyScores security →ₗ[ℝ] Family security order where
  toFun score := bodyFamily (primaryLaw security) (bodyReference security) order horder score.val score.property
  map_add' first second := by unfold bodyFamily; rw [← Pi.single_add]; rfl
  map_smul' scalar score := by unfold bodyFamily; rw [← Pi.single_smul]; rfl

def raisingLinear (security order : ℕ) (horder : 1 ≤ order) :
    centeredBodyScores security →ₗ[ℝ] Family security order where
  toFun score := raisingFamily security order horder score.val score.property
  map_add' first second := by
    change bodyEmbeddingLinear security order horder (first + second) * _ = _
    rw [map_add, add_mul]
    rfl
  map_smul' scalar score := by
    change bodyEmbeddingLinear security order horder (scalar • score) * _ = _
    rw [map_smul, smul_mul_assoc, RingHom.id_apply]
    rfl

end
end CurrentAFT.OrdinaryRaising


end

section













/-!
# Both-role independent-root raising operator

Each nonempty pattern may replace primary or ordinary selected controls.
Ordinary numerators retain their original safe body slot, while their
positive reciprocal emits only primary slots. Every joint input is kept
inside its actual two-reference finite sum.
-/
namespace CurrentAFT.CompleteRaising

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
  GradedControlAlgebra GradedInverse LocalCoefficientFamily LocalRaisingFirst LocalRaisingLinear
  BackgroundFamilies GlobalRaising
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
abbrev Palette (security : ℕ) := ActualControls.Palette security

def bodyAtom (security : ℕ) (source : SafePalette security) : OrdinaryRaising.centeredBodyScores security :=
  ⟨Hoeffding.centeredAtom (bodyReference security) source,
    Hoeffding.centeredAtom_mean _ (bodyReference_positive security) source⟩

def ordinaryRaisedPoint (security order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) : Family security order :=
  OrdinaryRaising.raisingLinear security order horder (bodyAtom security source)

def slotLeading (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security) :
    Fin r ⊕ Fin s → Family security order :=
  Sum.elim (fun index => primaryPoint security order horder (sourcePrimary index))
    (fun index => bodyPoint security order horder (sourceBody index))

def slotRaised (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security) :
    Fin r ⊕ Fin s → Family security order :=
  Sum.elim (fun index => raisedPoint security order horder (sourcePrimary index))
    (fun index => ordinaryRaisedPoint security order horder (sourceBody index))

def selectedPointProduct (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Fin r ⊕ Fin s)) (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security) :
    Family security order :=
  ∏ slot : Fin r ⊕ Fin s, if slot ∈ selected then slotRaised security order horder sourcePrimary sourceBody slot
    else slotLeading security order horder sourcePrimary sourceBody slot



def selectedCorrection (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Fin r ⊕ Fin s)) (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    Family security order :=
  ∑ sourcePrimary, ∑ sourceBody,
    ((∏ index, (primaryLaw security).weight (sourcePrimary index)) *
      (∏ index, (bodyReference security).weight (sourceBody index)) * kernel.val sourcePrimary sourceBody) •
        selectedPointProduct security order horder selected sourcePrimary sourceBody

def selectedCorrectionLinear (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Fin r ⊕ Fin s)) :
    canonicalKernels (primaryLaw security) (bodyReference security) r s →ₗ[ℝ] Family security order where
  toFun := selectedCorrection security order horder selected
  map_add' first second := by
    simp only [selectedCorrection, Submodule.coe_add, Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' scalar kernel := by
    simp only [selectedCorrection, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro sourcePrimary _
    apply Finset.sum_congr rfl
    intro sourceBody _
    rw [smul_smul]
    congr 1
    ring

def homogeneousCorrectionLinear (security order : ℕ) (horder : 1 ≤ order) (r s : ℕ) :
    canonicalKernels (primaryLaw security) (bodyReference security) r s →ₗ[ℝ] Family security order :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin r ⊕ Fin s))).erase ∅,
    selectedCorrectionLinear security order horder selected



def raisingLinear (security order : ℕ) (horder : 1 ≤ order) : Family security order →ₗ[ℝ] Family security order where
  toFun family := ∑ arity : TruncatedArity order,
    homogeneousCorrectionLinear security order horder arity.val.1.val arity.val.2.val (family arity)
  map_add' first second := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' scalar family := by simp only [Pi.smul_apply, map_smul, ← Finset.smul_sum, RingHom.id_apply]



end
end CurrentAFT.CompleteRaising

end

section



















/-! # Actual local Hilbert channels for both kinds of selected controls -/
namespace CurrentAFT.RaisingChannels

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct ControlNorm
  GradedControlAlgebra GradedControlNorm GradedControlStability LocalCoefficientFamily
  LocalRaisingLinear LocalRaisingFirst LocalRaisingBounds CoefficientHilbert
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance safeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
abbrev Palette (security : ℕ) := ActualControls.Palette security

def primaryProjection (security : ℕ) : (Palette security → ℝ) →ₗ[ℝ] centeredScores security :=
  (centerLinear (primaryLaw security)).codRestrict (centeredScores security) (fun score => center_mean _ score)

def bodyProjection (security : ℕ) : (SafePalette security → ℝ) →ₗ[ℝ] OrdinaryRaising.centeredBodyScores security :=
  (centerLinear (bodyReference security)).codRestrict (OrdinaryRaising.centeredBodyScores security) (fun score => center_mean _ score)

def primaryLeading (security order : ℕ) (horder : 1 ≤ order) : (Palette security → ℝ) →ₗ[ℝ] Family security order :=
  (primaryEmbeddingLinear security order horder).comp (primaryProjection security)

def primaryRaised (security order : ℕ) (horder : 1 ≤ order) : (Palette security → ℝ) →ₗ[ℝ] Family security order :=
  (localRaisingLinear security order horder).comp (primaryProjection security)

def bodyLeading (security order : ℕ) (horder : 1 ≤ order) : (SafePalette security → ℝ) →ₗ[ℝ] Family security order :=
  (OrdinaryRaising.bodyEmbeddingLinear security order horder).comp (bodyProjection security)

def bodyRaised (security order : ℕ) (horder : 1 ≤ order) : (SafePalette security → ℝ) →ₗ[ℝ] Family security order :=
  (OrdinaryRaising.raisingLinear security order horder).comp (bodyProjection security)

 theorem primaryFactor_nonneg (security : ℕ) : 0 ≤ BackgroundRates.primaryFactor security := by
  unfold BackgroundRates.primaryFactor
  positivity

 theorem bodyFactor_nonneg (security : ℕ) : 0 ≤ BackgroundRates.bodyFactor security := by
  unfold BackgroundRates.bodyFactor BackgroundRates.radius
  positivity

theorem primaryLeading_norm (security order : ℕ) (horder : 1 ≤ order) (score : Palette security → ℝ) :
    LocalRaisingBounds.coefficientNorm security order (primaryLeading security order horder score) ≤
      BackgroundRates.primaryFactor security * Real.sqrt ((primaryLaw security).l2Sq score) := by
  change LocalRaisingBounds.coefficientNorm security order
    (BackgroundFamilies.primaryFamily (primaryLaw security) (bodyReference security) order horder
      (centerLinear (primaryLaw security) score) (center_mean _ score)) ≤ _
  rw [LocalRaisingBounds.coefficientNorm, BackgroundFamilies.primaryFamily_norm]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (center_energy_le _ score)) (primaryFactor_nonneg security)

theorem primaryRaised_norm (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ)) (score : Palette security → ℝ) :
    LocalRaisingBounds.coefficientNorm security order (primaryRaised security order horder score) ≤
      (raisingConstant / (Parameters.base security : ℝ) ^ 102) * Real.sqrt ((primaryLaw security).l2Sq score) := by
  have h := localRaising_bound security order horder hlarge (centerLinear (primaryLaw security) score) (center_mean _ score)
  apply h.trans
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (center_energy_le _ score)) (by
    unfold raisingConstant
    exact div_nonneg (mul_nonneg (by norm_num) (add_nonneg higherConstant_nonneg positiveConstant_nonneg))
      (pow_nonneg (FirstResponse.base_pos security).le _))

theorem bodyLeading_norm (security order : ℕ) (horder : 1 ≤ order) (score : SafePalette security → ℝ) :
    LocalRaisingBounds.coefficientNorm security order (bodyLeading security order horder score) ≤
      BackgroundRates.bodyFactor security * Real.sqrt ((bodyReference security).l2Sq score) := by
  change LocalRaisingBounds.coefficientNorm security order
    (BackgroundFamilies.bodyFamily (primaryLaw security) (bodyReference security) order horder
      (centerLinear (bodyReference security) score) (center_mean _ score)) ≤ _
  rw [LocalRaisingBounds.coefficientNorm, BackgroundFamilies.bodyFamily_norm]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (center_energy_le _ score)) (bodyFactor_nonneg security)

theorem bodyRaised_norm (security order : ℕ) (horder : 1 ≤ order) (score : SafePalette security → ℝ) :
    LocalRaisingBounds.coefficientNorm security order (bodyRaised security order horder score) ≤
      ((80 / (Parameters.base security : ℝ) ^ 63) * BackgroundRates.bodyFactor security) *
        Real.sqrt ((bodyReference security).l2Sq score) := by
  have h := OrdinaryRaising.raisingFamily_norm security order horder (centerLinear (bodyReference security) score) (center_mean _ score)
  apply h.trans
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (center_energy_le _ score))
    (mul_nonneg (by positivity) (bodyFactor_nonneg security))

theorem centerLinear_single {Color : Type*} [Fintype Color] (law : FiniteDist Color)
    (hpositive : ∀ color, 0 < law.weight color) (source : Color) :
    centerLinear law (Pi.single source 1) = law.weight source • Hoeffding.centeredAtom law source := by
  classical
  have hmean : law.expectation (Pi.single source 1) = law.weight source := by
    simp [FiniteDist.expectation, Pi.single_apply]
  funext color
  change (Pi.single source (1 : ℝ) : Color → ℝ) color - law.expectation (Pi.single source 1) = _
  rw [hmean]
  by_cases hequal : color = source
  · subst color
    simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, Hoeffding.centeredAtom, if_true]
    field_simp [(hpositive source).ne']
  · simp only [Pi.single_eq_of_ne hequal, Pi.smul_apply, smul_eq_mul, Hoeffding.centeredAtom,
      Ne.symm hequal, if_false]
    ring

theorem primaryProjection_single (security : ℕ) (source : Palette security) :
    primaryProjection security (Pi.single source 1) =
      (primaryLaw security).weight source • GlobalRaising.primaryAtom security source := by
  apply Subtype.ext
  exact centerLinear_single _ (primaryReference_positive security) source

theorem bodyProjection_single (security : ℕ) (source : SafePalette security) :
    bodyProjection security (Pi.single source 1) =
      (bodyReference security).weight source • CompleteRaising.bodyAtom security source := by
  apply Subtype.ext
  funext color
  change centerLinear (bodyReference security) (Pi.single source 1) color =
    (bodyReference security).weight source * Hoeffding.centeredAtom (bodyReference security) source color
  exact congrFun (centerLinear_single _ (bodyReference_positive security) source) color

theorem primaryLeading_single (security order : ℕ) (horder : 1 ≤ order) (source : Palette security) :
    primaryLeading security order horder (Pi.single source 1) =
      (primaryLaw security).weight source • GlobalRaising.primaryPoint security order horder source := by
  unfold primaryLeading
  rw [LinearMap.comp_apply, primaryProjection_single, map_smul]
  rfl

theorem primaryRaised_single (security order : ℕ) (horder : 1 ≤ order) (source : Palette security) :
    primaryRaised security order horder (Pi.single source 1) =
      (primaryLaw security).weight source • GlobalRaising.raisedPoint security order horder source := by
  unfold primaryRaised
  rw [LinearMap.comp_apply, primaryProjection_single, map_smul]
  rfl

theorem bodyLeading_single (security order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) :
    bodyLeading security order horder (Pi.single source 1) =
      (bodyReference security).weight source • GlobalRaising.bodyPoint security order horder source := by
  unfold bodyLeading
  rw [LinearMap.comp_apply, bodyProjection_single, map_smul]
  rfl

theorem bodyRaised_single (security order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) :
    bodyRaised security order horder (Pi.single source 1) =
      (bodyReference security).weight source • CompleteRaising.ordinaryRaisedPoint security order horder source := by
  unfold bodyRaised
  rw [LinearMap.comp_apply, bodyProjection_single, map_smul]
  rfl

section Fibers
variable {Primary Body Input : Type*} [Fintype Primary] [Fintype Body] [Fintype Input]

def outputReference (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) (arity : TruncatedArity order) :=
  (FiniteDist.independent (fun _ : Fin arity.val.1.val => primary)).prod
    (FiniteDist.independent (fun _ : Fin arity.val.2.val => body))

def fiberLinear (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) (arity : TruncatedArity order) :
    KernelFamily primary body order →ₗ[ℝ]
      (((Fin arity.val.1.val → Primary) × (Fin arity.val.2.val → Body)) → ℝ) where
  toFun family word := (family arity).val word.1 word.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem fiber_weighted_norm_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    (arity : TruncatedArity order) (family : KernelFamily primary body order) :
    gradeWeight primaryFactor bodyFactor arity.val.1.val arity.val.2.val *
      Real.sqrt ((outputReference primary body order arity).l2Sq (fiberLinear primary body order arity family)) ≤
        familyNorm primary body order primaryFactor bodyFactor family := by
  change gradeWeight primaryFactor bodyFactor arity.val.1.val arity.val.2.val *
    blockL2 primary body (family arity).val ≤ _
  unfold familyNorm
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun other : TruncatedArity order => gradeWeight primaryFactor bodyFactor other.val.1.val other.val.2.val *
      blockL2 primary body (family other).val)
    (fun other _ => mul_nonneg (gradeWeight_nonneg _ _ hprimary hbody _ _) (blockL2_nonneg primary body _))
    (Finset.mem_univ arity)

theorem fiber_energy_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 < primaryFactor) (hbody : 0 < bodyFactor)
    (input : FiniteDist Input) (channel : (Input → ℝ) →ₗ[ℝ] KernelFamily primary body order)
    (bound : ℝ) (hchannel : ∀ score, familyNorm primary body order primaryFactor bodyFactor (channel score) ≤
      bound * Real.sqrt (input.l2Sq score)) (arity : TruncatedArity order) (score : Input → ℝ) :
    (outputReference primary body order arity).l2Sq ((fiberLinear primary body order arity).comp channel score) ≤
      (bound / gradeWeight primaryFactor bodyFactor arity.val.1.val arity.val.2.val) ^ 2 * input.l2Sq score := by
  let weight := gradeWeight primaryFactor bodyFactor arity.val.1.val arity.val.2.val
  have hw : 0 < weight := by unfold weight gradeWeight; positivity
  have h := (fiber_weighted_norm_le primary body order primaryFactor bodyFactor hprimary.le hbody.le arity (channel score)).trans (hchannel score)
  have hsqrt : Real.sqrt ((outputReference primary body order arity).l2Sq
      (fiberLinear primary body order arity (channel score))) ≤
      (bound / weight) * Real.sqrt (input.l2Sq score) := by
    rw [show (bound / weight) * Real.sqrt (input.l2Sq score) =
      (bound * Real.sqrt (input.l2Sq score)) / weight by ring]
    apply (le_div_iff₀ hw).mpr
    calc
      _ = weight * Real.sqrt ((outputReference primary body order arity).l2Sq
          (fiberLinear primary body order arity (channel score))) := by ring
      _ ≤ _ := h
  have hsquared := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2
  simpa only [Real.sq_sqrt (FiniteDist.l2Sq_nonneg _ _), mul_pow, LinearMap.comp_apply] using hsquared

end Fibers

end
end CurrentAFT.RaisingChannels

end

section















/-! # Current-parameter budgets for every mixed-role raising pattern -/
namespace CurrentAFT.RaisingPatternBudget

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct ControlNorm
  GradedControlAlgebra GradedControlNorm LocalCoefficientFamily LocalRaisingBounds RaisingChannels
open Filter
open scoped BigOperators Classical Topology
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
abbrev Palette (security : ℕ) := ActualControls.Palette security
abbrev Role (r s : ℕ) := Fin r ⊕ Fin s

abbrev RoleInput (security r s : ℕ) : Role r s → Type :=
  Sum.elim (fun _ => Palette security) (fun _ => SafePalette security)

instance roleInputFintype (security r s : ℕ) (role : Role r s) : Fintype (RoleInput security r s role) := by
  cases role <;> dsimp only [RoleInput, Sum.elim_inl, Sum.elim_inr] <;> infer_instance

def roleReference (security r s : ℕ) : (role : Role r s) → FiniteDist (RoleInput security r s role)
  | .inl _ => primaryLaw security
  | .inr _ => bodyReference security

def roleFactor (security r s : ℕ) : Role r s → ℝ :=
  Sum.elim (fun _ => BackgroundRates.primaryFactor security) (fun _ => BackgroundRates.bodyFactor security)

def roleCost (security : ℕ) {r s : ℕ} (selected : Finset (Role r s)) : Role r s → ℝ
  | .inl index => if Sum.inl index ∈ selected then raisingConstant / (Parameters.base security : ℝ) ^ 102
      else BackgroundRates.primaryFactor security
  | .inr index => if Sum.inr index ∈ selected then (80 / (Parameters.base security : ℝ) ^ 63) * BackgroundRates.bodyFactor security
      else BackgroundRates.bodyFactor security

def roleChannel (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ} (selected : Finset (Role r s)) :
    (role : Role r s) → (RoleInput security r s role → ℝ) →ₗ[ℝ] Family security order
  | .inl index => if Sum.inl index ∈ selected then primaryRaised security order horder else primaryLeading security order horder
  | .inr index => if Sum.inr index ∈ selected then bodyRaised security order horder else bodyLeading security order horder

def rolePoint (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ} (selected : Finset (Role r s)) :
    (role : Role r s) → RoleInput security r s role → Family security order
  | .inl index, source => if Sum.inl index ∈ selected then GlobalRaising.raisedPoint security order horder source
      else GlobalRaising.primaryPoint security order horder source
  | .inr index, source => if Sum.inr index ∈ selected then CompleteRaising.ordinaryRaisedPoint security order horder source
      else GlobalRaising.bodyPoint security order horder source

theorem roleChannel_single (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s)) (role : Role r s) (source : RoleInput security r s role) :
    roleChannel security order horder selected role (Pi.single source 1) =
      (roleReference security r s role).weight source • rolePoint security order horder selected role source := by
  cases role with
  | inl index =>
    dsimp only [roleChannel, roleReference, rolePoint]
    split_ifs
    · exact primaryRaised_single security order horder source
    · exact primaryLeading_single security order horder source
  | inr index =>
    dsimp only [roleChannel, roleReference, rolePoint]
    split_ifs
    · exact bodyRaised_single security order horder source
    · exact bodyLeading_single security order horder source

theorem roleChannel_norm (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ)) {r s : ℕ}
    (selected : Finset (Role r s)) (role : Role r s) (score : RoleInput security r s role → ℝ) :
    LocalRaisingBounds.coefficientNorm security order (roleChannel security order horder selected role score) ≤
      roleCost security selected role * Real.sqrt ((roleReference security r s role).l2Sq score) := by
  cases role with
  | inl index =>
    dsimp only [roleChannel, roleReference, roleCost]
    split_ifs
    · exact primaryRaised_norm security order horder hlarge score
    · exact primaryLeading_norm security order horder score
  | inr index =>
    dsimp only [roleChannel, roleReference, roleCost]
    split_ifs
    · exact bodyRaised_norm security order horder score
    · exact bodyLeading_norm security order horder score

theorem primaryFactor_pos (security : ℕ) : 0 < BackgroundRates.primaryFactor security := by
  rw [BackgroundRates.primaryFactor_eq]
  exact one_div_pos.mpr (pow_pos (FirstResponse.base_pos security) _)

theorem bodyFactor_pos (security : ℕ) : 0 < BackgroundRates.bodyFactor security := by
  have hpool : (0 : ℝ) < BackgroundRates.ordinaryPool security := by exact_mod_cast BackgroundRates.ordinaryPool_pos security
  have hradius : 0 < BackgroundRates.radius security := by
    unfold BackgroundRates.radius
    exact Real.rpow_pos_of_pos (FirstResponse.base_pos security) _
  unfold BackgroundRates.bodyFactor
  exact mul_pos hradius (inv_pos.mpr (Real.sqrt_pos.mpr hpool))

theorem raisingConstant_nonneg : 0 ≤ raisingConstant :=
  mul_nonneg (by norm_num) (add_nonneg higherConstant_nonneg positiveConstant_nonneg)

theorem roleCost_nonneg (security : ℕ) {r s : ℕ} (selected : Finset (Role r s)) (role : Role r s) :
    0 ≤ roleCost security selected role := by
  cases role <;> dsimp only [roleCost] <;> split_ifs
  · exact div_nonneg raisingConstant_nonneg (pow_nonneg (FirstResponse.base_pos security).le _)
  · exact (primaryFactor_pos security).le
  · exact mul_nonneg (by positivity) (bodyFactor_pos security).le
  · exact (bodyFactor_pos security).le

def relativeBudget (security : ℕ) : ℝ := (raisingConstant + 80) / (Parameters.base security : ℝ) ^ 38

theorem relativeBudget_nonneg (security : ℕ) : 0 ≤ relativeBudget security :=
  div_nonneg (add_nonneg raisingConstant_nonneg (by norm_num)) (pow_nonneg (FirstResponse.base_pos security).le _)

theorem roleCost_le (security : ℕ) {r s : ℕ} (selected : Finset (Role r s)) (role : Role r s) :
    roleCost security selected role ≤ roleFactor security r s role *
      (if role ∈ selected then relativeBudget security else 1) := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  cases role with
  | inl index =>
    dsimp only [roleCost, roleFactor, Sum.elim_inl]
    split_ifs
    · have hequal : raisingConstant / (Parameters.base security : ℝ) ^ 102 =
          BackgroundRates.primaryFactor security * (raisingConstant / (Parameters.base security : ℝ) ^ 38) := by
        rw [BackgroundRates.primaryFactor_eq, show (102 : ℕ) = 64 + 38 by omega, pow_add]
        ring
      rw [hequal]
      apply mul_le_mul_of_nonneg_left _ (primaryFactor_pos security).le
      apply div_le_div_of_nonneg_right _ (pow_nonneg hb.le _)
      linarith
    · rw [mul_one]
  | inr index =>
    dsimp only [roleCost, roleFactor, Sum.elim_inr]
    split_ifs
    · have hdiv : 80 / (Parameters.base security : ℝ) ^ 63 ≤ relativeBudget security := by
        calc
          _ ≤ 80 / (Parameters.base security : ℝ) ^ 38 :=
            div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _)
              (pow_le_pow_right₀ hb1 (show 38 ≤ 63 by omega))
          _ ≤ _ := div_le_div_of_nonneg_right (by linarith [raisingConstant_nonneg]) (pow_nonneg hb.le _)
      exact (mul_le_mul_of_nonneg_right hdiv (bodyFactor_pos security).le).trans_eq (mul_comm _ _)
    · rw [mul_one]

theorem roleCost_product (security : ℕ) {r s : ℕ} (selected : Finset (Role r s)) :
    (∏ role : Role r s, roleCost security selected role) ≤
      gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) r s *
        relativeBudget security ^ selected.card := by
  apply (Finset.prod_le_prod (fun role _ => roleCost_nonneg security selected role)
    (fun role _ => roleCost_le security selected role)).trans_eq
  rw [Finset.prod_mul_distrib]
  have hfactor : (∏ role : Role r s, roleFactor security r s role) =
      gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) r s := by
    simp [roleFactor, gradeWeight, Fintype.prod_sum_type]
  rw [hfactor]
  congr 1
  simp

theorem nonempty_roleCost_product (security : ℕ) {r s : ℕ} (selected : Finset (Role r s))
    (hnonempty : selected.Nonempty) (hsmall : relativeBudget security ≤ 1) :
    (∏ role : Role r s, roleCost security selected role) ≤
      gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) r s * relativeBudget security := by
  apply (roleCost_product security selected).trans
  apply mul_le_mul_of_nonneg_left _
    (gradeWeight_nonneg _ _ (primaryFactor_pos security).le (bodyFactor_pos security).le _ _)
  simpa only [pow_one] using pow_le_pow_of_le_one (relativeBudget_nonneg security) hsmall
    (Finset.card_pos.mpr hnonempty)

theorem relativeBudget_small_eventually : ∀ᶠ security : ℕ in atTop, relativeBudget security ≤ 1 := by
  obtain ⟨threshold, hthreshold⟩ := exists_nat_ge (raisingConstant + 80)
  filter_upwards [eventually_ge_atTop threshold] with security hsecurity
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hlarge : raisingConstant + 80 ≤ (Parameters.base security : ℝ) :=
    hthreshold.trans (Nat.cast_le.mpr (show threshold ≤ Parameters.base security by unfold Parameters.base; omega))
  apply (div_le_one (pow_pos hb _)).mpr
  exact hlarge.trans (by simpa only [pow_one] using pow_le_pow_right₀ hb1 (show 1 ≤ 38 by omega))

end
end CurrentAFT.RaisingPatternBudget

end

section















/-! # Genuine mixed-role joint tensors for each local arity pattern -/
namespace CurrentAFT.RaisingPatternKernel

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct ControlNorm
  GradedControlAlgebra GradedControlNorm LocalCoefficientFamily LocalRaisingBounds RaisingChannels
  RaisingPatternBudget GroupedKernelNorm
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
abbrev Palette (security : ℕ) := ActualControls.Palette security

def totalPrimary {r s order : ℕ} (pattern : Role r s → TruncatedArity order) : ℕ :=
  ∑ role, (pattern role).val.1.val

def totalBody {r s order : ℕ} (pattern : Role r s → TruncatedArity order) : ℕ :=
  ∑ role, (pattern role).val.2.val

abbrev primarySlots {r s order : ℕ} (pattern : Role r s → TruncatedArity order) (role : Role r s) :=
  Fin (pattern role).val.1.val

abbrev bodySlots {r s order : ℕ} (pattern : Role r s → TruncatedArity order) (role : Role r s) :=
  Fin (pattern role).val.2.val

def primaryEquiv {r s order : ℕ} (pattern : Role r s → TruncatedArity order) :
    Sigma (primarySlots pattern) ≃ Fin (totalPrimary pattern) :=
  GroupedKernelProduct.finiteSlotsEquiv (fun role => (pattern role).val.1.val)

def bodyEquiv {r s order : ℕ} (pattern : Role r s → TruncatedArity order) :
    Sigma (bodySlots pattern) ≃ Fin (totalBody pattern) :=
  GroupedKernelProduct.finiteSlotsEquiv (fun role => (pattern role).val.2.val)

def inputJoint (security : ℕ) {r s : ℕ}
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s)
    (word : (role : Role r s) → RoleInput security r s role) : ℝ :=
  kernel.val (fun index => word (Sum.inl index)) (fun index => word (Sum.inr index))

theorem inputJoint_energy (security : ℕ) {r s : ℕ}
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    (FiniteDist.dependentIndependent (roleReference security r s)).l2Sq (inputJoint security kernel) =
      blockEnergy (primaryLaw security) (bodyReference security) kernel.val := by
  unfold FiniteDist.l2Sq FiniteDist.expectation
  rw [← (Equiv.prodPiEquivSumPi (fun _ : Fin r => Palette security)
    (fun _ : Fin s => SafePalette security)).sum_comp]
  rw [Fintype.sum_prod_type, blockEnergy_apply]
  apply Finset.sum_congr rfl
  intro colors _
  apply Finset.sum_congr rfl
  intro centers _
  simp only [FiniteDist.dependentIndependent_weight, inputJoint, roleReference,
    Fintype.prod_sum_type, Equiv.prodPiEquivSumPi, Equiv.sumPiEquivProdPi,
    Equiv.coe_fn_symm_mk, Sum.elim_inl, Sum.elim_inr, RoleInput]

def componentChannel (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s)) (pattern : Role r s → TruncatedArity order) (role : Role r s) :
    (RoleInput security r s role → ℝ) →ₗ[ℝ]
      (((primarySlots pattern role → Palette security) × (bodySlots pattern role → SafePalette security)) → ℝ) :=
  (fiberLinear (primaryLaw security) (bodyReference security) order (pattern role)).comp
    (roleChannel security order horder selected role)

theorem component_primaryCentered (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s)) (pattern : Role r s → TruncatedArity order) (role : Role r s)
    (score : RoleInput security r s role → ℝ) :
    PrimaryCentered (primaryLaw security) (fun colors centers =>
      componentChannel security order horder selected pattern role score (colors, centers)) :=
  (roleChannel security order horder selected role score (pattern role)).property.1

theorem component_bodyCentered (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s)) (pattern : Role r s → TruncatedArity order) (role : Role r s)
    (score : RoleInput security r s role → ℝ) :
    BodyCentered (bodyReference security) (fun colors centers =>
      componentChannel security order horder selected pattern role score (colors, centers)) :=
  (roleChannel security order horder selected role score (pattern role)).property.2.1

def patternKernel (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s)) (pattern : Role r s → TruncatedArity order)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    canonicalKernels (primaryLaw security) (bodyReference security) (totalPrimary pattern) (totalBody pattern) :=
  canonicalTensor (primarySlots pattern) (bodySlots pattern) (primaryLaw security) (bodyReference security)
    (primaryEquiv pattern) (bodyEquiv pattern) (componentChannel security order horder selected pattern)
      (component_primaryCentered security order horder selected pattern)
      (component_bodyCentered security order horder selected pattern) (inputJoint security kernel)

def localWeight (security : ℕ) {r s order : ℕ} (pattern : Role r s → TruncatedArity order) (role : Role r s) : ℝ :=
  gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
    (pattern role).val.1.val (pattern role).val.2.val

theorem localWeight_pos (security : ℕ) {r s order : ℕ} (pattern : Role r s → TruncatedArity order) (role : Role r s) :
    0 < localWeight security pattern role := by
  have hp := primaryFactor_pos security
  have hb := bodyFactor_pos security
  unfold localWeight gradeWeight
  positivity

theorem weight_product (security : ℕ) {r s order : ℕ} (pattern : Role r s → TruncatedArity order) :
    gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
      (totalPrimary pattern) (totalBody pattern) = ∏ role, localWeight security pattern role := by
  simp only [localWeight, gradeWeight, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, totalPrimary, totalBody]

theorem patternKernel_weighted_norm (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ)) {r s : ℕ}
    (selected : Finset (Role r s)) (pattern : Role r s → TruncatedArity order)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
        (totalPrimary pattern) (totalBody pattern) *
      blockL2 (primaryLaw security) (bodyReference security) (patternKernel security order horder selected pattern kernel).val ≤
        (∏ role, roleCost security selected role) * blockL2 (primaryLaw security) (bodyReference security) kernel.val := by
  let bounds := fun role => roleCost security selected role / localWeight security pattern role
  have hchannel (role : Role r s) (score : RoleInput security r s role → ℝ) :
      (localReference (primarySlots pattern) (bodySlots pattern) (primaryLaw security) (bodyReference security) role).l2Sq
        (componentChannel security order horder selected pattern role score) ≤
          bounds role ^ 2 * (roleReference security r s role).l2Sq score :=
    fiber_energy_le (primaryLaw security) (bodyReference security) order _ _
      (primaryFactor_pos security) (bodyFactor_pos security) _ _ _
      (roleChannel_norm security order horder hlarge selected role) (pattern role) score
  have henergy := canonicalize_tensor_energy_le (primarySlots pattern) (bodySlots pattern)
    (primaryLaw security) (bodyReference security) (primaryEquiv pattern) (bodyEquiv pattern)
    (roleReference security r s) (componentChannel security order horder selected pattern)
    bounds hchannel (inputJoint security kernel)
  change blockEnergy (primaryLaw security) (bodyReference security)
    (patternKernel security order horder selected pattern kernel).val ≤ _ at henergy
  rw [inputJoint_energy] at henergy
  have hbounds : 0 ≤ ∏ role, bounds role :=
    Finset.prod_nonneg (fun role _ => div_nonneg (roleCost_nonneg security selected role) (localWeight_pos security pattern role).le)
  have hsqrt := Real.sqrt_le_sqrt henergy
  rw [Finset.prod_pow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hbounds] at hsqrt
  have hweight := gradeWeight_nonneg _ _ (primaryFactor_pos security).le (bodyFactor_pos security).le
    (totalPrimary pattern) (totalBody pattern)
  apply (mul_le_mul_of_nonneg_left hsqrt hweight).trans_eq
  change _ = _
  rw [weight_product]
  have hcancel : (∏ role, localWeight security pattern role) * (∏ role, bounds role) =
      ∏ role, roleCost security selected role := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro role _
    dsimp only [bounds]
    field_simp [(localWeight_pos security pattern role).ne']
  rw [← mul_assoc, hcancel]
  rfl

def patternFamily (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s)) (pattern : Role r s → TruncatedArity order)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) : Family security order :=
  if hdegree : totalPrimary pattern + totalBody pattern ≤ order then
    GroupedKernelProduct.embed (primaryLaw security) (bodyReference security) order hdegree
      (patternKernel security order horder selected pattern kernel)
  else 0

theorem patternFamily_norm (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ)) {r s : ℕ}
    (selected : Finset (Role r s)) (pattern : Role r s → TruncatedArity order)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    LocalRaisingBounds.coefficientNorm security order (patternFamily security order horder selected pattern kernel) ≤
      (∏ role, roleCost security selected role) * blockL2 (primaryLaw security) (bodyReference security) kernel.val := by
  unfold patternFamily
  split_ifs with hdegree
  · unfold GroupedKernelProduct.embed LocalRaisingBounds.coefficientNorm
    rw [BackgroundFamilies.familyNorm_single]
    exact patternKernel_weighted_norm security order horder hlarge selected pattern kernel
  · rw [LocalRaisingBounds.coefficientNorm, GradedControlStability.familyNorm_zero]
    exact mul_nonneg (Finset.prod_nonneg (fun role _ => roleCost_nonneg security selected role)) (blockL2_nonneg _ _ _)

end
end CurrentAFT.RaisingPatternKernel

end


