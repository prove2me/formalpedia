-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
-- name    : LeanPool_FormalLearningTheory_Complexity_Measurability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:34:42.135322+00:00
-- url     : https://prove2.me/theorems/0b92e3fe-3747-4b1d-835a-54aeb2a38d56
-- title:
--   Measurability
-- statement:
--   Definitions and structural lemmas for Measurability, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Measurability.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
class MeasurableConceptClass (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) : Prop where
  /-- Every concept in C is measurable -/
  mem_measurable : ∀ h ∈ C, Measurable h
  /-- All concepts X → Bool are measurable (for disagreement sets) -/
  all_measurable : ∀ c : Concept X Bool, Measurable c
  /-- Uniform convergence bad event is NullMeasurableSet -/
  wellBehaved : WellBehavedVC X C
theorem MeasurableConceptClass.hmeas_C
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool) [h : MeasurableConceptClass X C] :
    ∀ c ∈ C, Measurable c :=
  h.mem_measurable
class UniversallyMeasurableSpace (X : Type u) [MeasurableSpace X] : Prop where
  /-- All Bool-valued functions on X are measurable -/
  all_concepts_measurable : ∀ c : Concept X Bool, Measurable c
  /-- All concept classes over X have well-behaved uniform convergence events -/
  all_classes_wellBehaved : ∀ C : ConceptClass X Bool, WellBehavedVC X C
instance (priority := 50) MeasurableConceptClass.ofUniversallyMeasurable
    {X : Type u} [MeasurableSpace X] [h : UniversallyMeasurableSpace X]
    (C : ConceptClass X Bool) : MeasurableConceptClass X C where
  mem_measurable := fun c _ => h.all_concepts_measurable c
  all_measurable := h.all_concepts_measurable
  wellBehaved := h.all_classes_wellBehaved C
instance (priority := 60) MeasurableHypotheses.ofMeasurableConceptClass
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool) [MeasurableConceptClass X C] :
    MeasurableHypotheses X C where
  mem_measurable := MeasurableConceptClass.hmeas_C C
instance (priority := 50) MeasurableBoolSpace.ofUniversallyMeasurable
    {X : Type u} [MeasurableSpace X] [h : UniversallyMeasurableSpace X] :
    MeasurableBoolSpace X where
  all_bool_measurable := h.all_concepts_measurable
noncomputable def oneSidedGhostGap
    {X : Type u}
    (h : Concept X Bool) (c : Concept X Bool) (m : ℕ)
    (p : (Fin m → X) × (Fin m → X)) : ℝ :=
  EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
  EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool)
noncomputable def absGhostGap
    {X : Type u}
    (h : Concept X Bool) (c : Concept X Bool) (m : ℕ)
    (p : (Fin m → X) × (Fin m → X)) : ℝ :=
  |oneSidedGhostGap h c m p|
noncomputable def ghostGapVals
    {X : Type u}
    (C : ConceptClass X Bool) (c : Concept X Bool) (m : ℕ)
    (p : (Fin m → X) × (Fin m → X)) : Set ℝ :=
  {r | ∃ h ∈ C, r = oneSidedGhostGap h c m p}
noncomputable def absGhostGapVals
    {X : Type u}
    (C : ConceptClass X Bool) (c : Concept X Bool) (m : ℕ)
    (p : (Fin m → X) × (Fin m → X)) : Set ℝ :=
  {r | ∃ h ∈ C, r = absGhostGap h c m p}
noncomputable def ghostGapSup
    {X : Type u}
    (C : ConceptClass X Bool) (c : Concept X Bool) (m : ℕ)
    (p : (Fin m → X) × (Fin m → X)) : ℝ :=
  sSup (ghostGapVals C c m p)
noncomputable def absGhostGapSup
    {X : Type u}
    (C : ConceptClass X Bool) (c : Concept X Bool) (m : ℕ)
    (p : (Fin m → X) × (Fin m → X)) : ℝ :=
  sSup (absGhostGapVals C c m p)
def KrappWirthV (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) : Prop :=
  ∀ (c : Concept X Bool) (m : ℕ),
    Measurable (ghostGapSup C c m)
def KrappWirthVAbs (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) : Prop :=
  ∀ (c : Concept X Bool) (m : ℕ),
    Measurable (absGhostGapSup C c m)
def KrappWirthU (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) : Prop :=
  ∀ (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (m : ℕ),
    Measurable (fun xs : Fin m → X =>
      sSup {r | ∃ h ∈ C, r =
        |TrueErrorReal X h c D -
         EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool)|})
class KrappWirthWellBehaved (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) : Prop extends MeasurableHypotheses X C where
  V_measurable : KrappWirthV X C
  U_measurable : KrappWirthU X C
noncomputable def empErrGrid (m : ℕ) : Finset ℝ :=
  if m = 0 then {0}
  else (Finset.range (m + 1)).image (fun (k : ℕ) => (k : ℝ) / (m : ℝ))
noncomputable def ghostGapGrid (m : ℕ) : Finset ℝ :=
  ((empErrGrid m).product (empErrGrid m)).image (fun ab => ab.1 - ab.2)
lemma empiricalError_mem_empErrGrid
    {X : Type u}
    (h : Concept X Bool) {m : ℕ}
    (S : Fin m → X × Bool) :
    EmpiricalError X Bool h S (zeroOneLoss Bool) ∈ empErrGrid m := by
  by_cases hm : m = 0
  · simp [EmpiricalError, empErrGrid, hm]
  · simp only [EmpiricalError, hm, ↓reduceIte, empErrGrid]
    set k := (Finset.univ.filter (fun i : Fin m => h (S i).1 ≠ (S i).2)).card
    have hsum : Finset.univ.sum (fun i => zeroOneLoss Bool (h (S i).1) (S i).2) = (k : ℝ) := by
      simp only [zeroOneLoss, k]
      have : ∀ i : Fin m, (if h (S i).1 = (S i).2 then (0 : ℝ) else 1) =
          if h (S i).1 ≠ (S i).2 then 1 else 0 := by
        intro i; split_ifs <;> simp_all
      simp_rw [this, Finset.sum_boole]
    rw [hsum]
    have hk : k < m + 1 := by
      have := (Finset.card_filter_le (Finset.univ : Finset (Fin m))
        (fun i => h (S i).1 ≠ (S i).2)).trans_eq (Finset.card_fin m)
      omega
    exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
lemma oneSidedGhostGap_mem_grid
    {X : Type u}
    (h : Concept X Bool) (c : Concept X Bool) (m : ℕ)
    (p : (Fin m → X) × (Fin m → X)) :
    oneSidedGhostGap h c m p ∈ ghostGapGrid m := by
  simp only [ghostGapGrid, oneSidedGhostGap]
  exact Finset.mem_image.mpr
    ⟨(EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool),
      EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool)),
     Finset.mem_product.mpr
       ⟨empiricalError_mem_empErrGrid h (fun i => (p.2 i, c (p.2 i))),
        empiricalError_mem_empErrGrid h (fun i => (p.1 i, c (p.1 i)))⟩,
     rfl⟩
lemma ghostGapVals_finite
    {X : Type u}
    (C : ConceptClass X Bool) (c : Concept X Bool) (m : ℕ)
    (p : (Fin m → X) × (Fin m → X)) :
    (ghostGapVals C c m p).Finite :=
  (Finset.finite_toSet (ghostGapGrid m)).subset (fun _r ⟨h, _, hr⟩ =>
    hr ▸ oneSidedGhostGap_mem_grid h c m p)
lemma wellBehaved_event_eq_preimage_gapSup
    {X : Type u}
    (C : ConceptClass X Bool) (c : Concept X Bool) (m : ℕ) (ε : ℝ)
    (hC : C.Nonempty) :
    {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
      oneSidedGhostGap h c m p ≥ ε / 2}
    = ghostGapSup C c m ⁻¹' Set.Ici (ε / 2) := by
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ici, ghostGapSup]
  constructor
  · rintro ⟨h_wit, hh_wit, hge⟩
    calc ε / 2 ≤ oneSidedGhostGap h_wit c m p := hge
      _ ≤ sSup (ghostGapVals C c m p) :=
          le_csSup (ghostGapVals_finite C c m p).bddAbove
            (show oneSidedGhostGap h_wit c m p ∈ ghostGapVals C c m p from
              ⟨h_wit, hh_wit, rfl⟩)
  · intro hp
    have hne : (ghostGapVals C c m p).Nonempty := by
      obtain ⟨h0, hh0⟩ := hC
      exact ⟨oneSidedGhostGap h0 c m p, h0, hh0, rfl⟩
    have h_attained : sSup (ghostGapVals C c m p) ∈ ghostGapVals C c m p :=
      hne.csSup_mem (ghostGapVals_finite C c m p)
    obtain ⟨h_star, hh_star, h_eq⟩ := h_attained
    exact ⟨h_star, hh_star, by rw [← h_eq]; exact hp⟩
theorem KrappWirthWellBehaved.toWellBehavedVC
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool) [h : KrappWirthWellBehaved X C] :
    WellBehavedVC X C := by
  intro D _ c m ε
  by_cases hC : C.Nonempty
  · have hV := h.V_measurable c m
    have hEq : {p : (Fin m → X) × (Fin m → X) | ∃ h_1 ∈ C,
        EmpiricalError X Bool h_1 (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h_1 (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
      = ghostGapSup C c m ⁻¹' Set.Ici (ε / 2) := by
      simpa only [oneSidedGhostGap] using wellBehaved_event_eq_preimage_gapSup C c m ε hC
    rw [hEq]
    exact (hV measurableSet_Ici).nullMeasurableSet
  · -- C empty → event is empty → NullMeasurableSet
    have : {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
      EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
      EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2} = ∅ := by
      ext p; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h, hh, -⟩; exact hC ⟨h, hh⟩
    rw [this]; exact MeasureTheory.nullMeasurableSet_empty
instance (priority := 75) MeasurableConceptClass.ofKrappWirth
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool) [h : KrappWirthWellBehaved X C]
    [hbool : MeasurableBoolSpace X] : MeasurableConceptClass X C where
  mem_measurable := h.mem_measurable
  all_measurable := hbool.all_bool_measurable
  wellBehaved := KrappWirthWellBehaved.toWellBehavedVC C
def WellBehavedVCAutomatic : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (C : ConceptClass X Bool),
    MeasurableHypotheses X C → VCDim X C < ⊤ → WellBehavedVC X C
def KrappWirthSeparation : Prop :=
  ∃ (X : Type) (_ : MeasurableSpace X) (C : ConceptClass X Bool),
    MeasurableHypotheses X C ∧ WellBehavedVC X C ∧ ¬ KrappWirthWellBehaved X C
def WellBehavedVCMeasTarget
    (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) : Prop :=
  ∀ (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool), Measurable c →
    ∀ (m : ℕ) (ε : ℝ),
      MeasureTheory.NullMeasurableSet
        {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
          EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
          EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
        ((MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
         (MeasureTheory.Measure.pi (fun _ : Fin m => D)))
def KrappWirthSeparationMeasTarget : Prop :=
  ∃ (C : ConceptClass ℝ Bool),
    MeasurableHypotheses ℝ C ∧
    WellBehavedVCMeasTarget ℝ C ∧
    ¬ KrappWirthWellBehaved ℝ C


