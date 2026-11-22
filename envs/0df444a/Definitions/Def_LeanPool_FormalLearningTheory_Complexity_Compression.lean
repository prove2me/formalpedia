-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Compression
-- name    : LeanPool_FormalLearningTheory_Complexity_Compression
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:35:00.964606+00:00
-- url     : https://prove2.me/theorems/3a208045-8ae4-4c26-aee4-8e54319e7ef2
-- title:
--   Compression
-- statement:
--   Definitions and structural lemmas for Compression, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Compression.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_FiniteVCApprox
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_FiniteSupportUC
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
noncomputable section
universe u
attribute [local instance] Classical.propDecidable
def pointSupport {X : Type u} {m : ℕ} (S : Fin m → X × Bool) : Finset X :=
  Finset.univ.image (fun i => (S i).1)
def labeledSampleOfFinset {X : Type u} (c : X → Bool) (Z : Finset X) :
    Fin Z.card → X × Bool :=
  fun i => let x := (Z.equivFin.symm i : X); (x, c x)
def supportError {X : Type u} (Y : Finset X) (q : FinitePMF ↥Y)
    (h : X → Bool) (c : X → Bool) : ℝ :=
  ∑ y : ↥Y, q.prob y * (if h (y : X) = c (y : X) then (0 : ℝ) else 1)
structure ProperFiniteSupportLearner (X : Type u) (C : ConceptClass X Bool) where
  /-- Uniform upper bound on the selected support size. -/
  sampleBound : ℕ
  /-- Learner evaluated on a finite labeled sample. -/
  learn : {m : ℕ} → (Fin m → X × Bool) → (X → Bool)
  output_mem : ∀ {m : ℕ} (S : Fin m → X × Bool), learn S ∈ C
  good_on_support : ∀ (c : X → Bool) (_ : c ∈ C) (Y : Finset X)
    (q : FinitePMF ↥Y),
    ∃ Z : Finset X, Z ⊆ Y ∧ Z.card ≤ sampleBound ∧
      supportError Y q (learn (labeledSampleOfFinset c Z)) c ≤ 1 / 3
def disagreementFamily
    {X : Type u} (C : ConceptClass X Bool)
    (c : X → Bool) (Y : Finset X) : Finset (↥Y → Bool) :=
  Finset.univ.image (fun (h : ↥Y → Bool) => h) |>.filter (fun a =>
    ∃ h ∈ C, ∀ y : ↥Y, a y = decide (h (y : X) ≠ c (y : X)))
def boundedSubsamples {X : Type u} (Y : Finset X) (s : ℕ) : Finset (Finset X) :=
  Y.powerset.filter (fun Z => Z.card ≤ s)
def hypothesisEnvelope {X : Type u} {C : ConceptClass X Bool}
    (L : ProperFiniteSupportLearner X C) (c : X → Bool) (Y : Finset X) :
    Finset (X → Bool) :=
  (boundedSubsamples Y L.sampleBound).image (fun Z =>
    L.learn (labeledSampleOfFinset c Z))
def agreeTest {X : Type u} (c : X → Bool) (x : X)
    (HY : Finset (X → Bool)) : ↥HY → Bool :=
  fun h => decide (h.val x = c x)
def agreeTests {X : Type u} (c : X → Bool) (Y : Finset X)
    (HY : Finset (X → Bool)) : Finset (↥HY → Bool) :=
  Y.image (fun x => agreeTest c x HY)
def encodeWitnessInfo
    {X : Type u} [DecidableEq X]
    (kernel : Finset (X × Bool)) (c : X → Bool) (K : ℕ)
    (W : Finset X) : Finset (Fin K) :=
  W.attach.biUnion (fun x =>
    if hmk : ((x : X), c x) ∈ kernel then
      if hlt : (kernel.equivFin ⟨((x : X), c x), hmk⟩).val < K then
        {⟨(kernel.equivFin ⟨((x : X), c x), hmk⟩).val, hlt⟩}
      else ∅
    else ∅)
def decodeWitnessXCoords
    {X : Type u} (Z : Finset (X × Bool)) {K : ℕ} (idxs : Finset (Fin K)) : Finset X :=
  idxs.biUnion (fun idx =>
    if h : (idx : ℕ) < Z.card then
      {((Z.equivFin.symm ⟨(idx : ℕ), h⟩ : Z) : X × Bool).1}
    else ∅)
def decodeWitnessLabel {X : Type u} [DecidableEq X] (Z : Finset (X × Bool)) : X → Bool :=
  fun x => decide ((x, true) ∈ Z)
abbrev CompressionSchemeWithInfo0 (X : Type u) (Y : Type) (C : ConceptClass X Y) :=
  CompressionSchemeWithInfo.{u, 0, 0} X Y C
abbrev IncidenceInfo (T K : ℕ) : Type := Fin T → Finset (Fin K)
instance instFintypeIncidenceInfo (T K : ℕ) : Fintype (IncidenceInfo T K) := inferInstance
def mkIncidenceScheme
    {X : Type u} {C : ConceptClass X Bool}
    (T K : ℕ)
    (compressCore : {m : ℕ} → (Fin m → X × Bool) → Finset (X × Bool) × IncidenceInfo T K)
    (reconstructCore : Finset (X × Bool) → IncidenceInfo T K → (X → Bool))
    (hsmall : ∀ {m : ℕ} (S : Fin m → X × Bool), (compressCore S).1.card ≤ K)
    (hsub : ∀ {m : ℕ} (S : Fin m → X × Bool), ↑(compressCore S).1 ⊆ Set.range S)
    (hcorrect : ∀ {m : ℕ} (S : Fin m → X × Bool),
      (∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2) →
      ∀ i : Fin m,
        reconstructCore (compressCore S).1 (compressCore S).2 (S i).1 = (S i).2) :
    CompressionSchemeWithInfo0 X Bool C := by
  classical
  let InfoTy : Type := IncidenceInfo T K
  exact {
    Info := InfoTy
    infoFinite := inferInstance
    compress := fun {m} S => compressCore S
    reconstruct := reconstructCore
    kernelSize := K
    compress_small := hsmall
    compress_sub := hsub
    correct := hcorrect
  }
lemma sum_indicator_eq_card_filter
    {T : ℕ} (votes : Fin T → Bool) (y : Bool) :
    (∑ t : Fin T, if votes t = y then (1 : ℝ) else 0)
      = (Finset.univ.filter (fun t => votes t = y)).card := by
  simp
lemma majority_vote_eq_of_agree_gt_half
    {T : ℕ} (hT : 0 < T) (votes : Fin T → Bool) (y : Bool)
    (hmajor : ((∑ t : Fin T, if votes t = y then (1 : ℝ) else 0) / T) > (1 / 2 : ℝ)) :
    majorityVote T votes = y := by
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  by_cases hy : y
  · subst hy
    have hgt_real : (2 * (Finset.univ.filter (fun t => votes t = true)).card : ℝ) > T := by
      have hind := sum_indicator_eq_card_filter votes true
      rw [hind] at hmajor
      rw [gt_iff_lt, lt_div_iff₀ hTreal] at hmajor
      linarith
    have hgt_nat : 2 * (Finset.univ.filter (fun t => votes t = true)).card > T := by
      exact_mod_cast hgt_real
    simp [majorityVote, hgt_nat]
  · have hyf : y = false := by cases y <;> simp_all
    subst hyf
    have hgt_false_real : (2 * (Finset.univ.filter (fun t => votes t = false)).card : ℝ) > T := by
      have hind := sum_indicator_eq_card_filter votes false
      rw [hind] at hmajor
      rw [gt_iff_lt, lt_div_iff₀ hTreal] at hmajor
      linarith
    have hgt_false_nat : 2 * (Finset.univ.filter (fun t => votes t = false)).card > T := by
      exact_mod_cast hgt_false_real
    have hpartition :
        (Finset.univ.filter (fun t => votes t = true)).card +
        (Finset.univ.filter (fun t => votes t = false)).card = T := by
      simpa [Bool.eq_false_eq_not_eq_true, Finset.card_univ] using
        (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin T)))
          (p := fun t => votes t = true))
    have hnot_true_majority :
        ¬ 2 * (Finset.univ.filter (fun t => votes t = true)).card > T := by
      intro htrue; omega
    simp [majorityVote, hnot_true_majority]
def mkIncidenceSchemeOfMajority
    {X : Type u} {C : ConceptClass X Bool}
    (T K : ℕ)
    (compressCore : {m : ℕ} → (Fin m → X × Bool) → Finset (X × Bool) × IncidenceInfo T K)
    (blockHyp : Finset (X × Bool) → IncidenceInfo T K → Fin T → X → Bool)
    (rowHyp : {m : ℕ} → (S : Fin m → X × Bool) →
      (∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2) → Fin T → X → Bool)
    (hT : 0 < T)
    (hsmall : ∀ {m : ℕ} (S : Fin m → X × Bool), (compressCore S).1.card ≤ K)
    (hsub : ∀ {m : ℕ} (S : Fin m → X × Bool), ↑(compressCore S).1 ⊆ Set.range S)
    (hagree : ∀ {m : ℕ} (S : Fin m → X × Bool)
      (hreal : ∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2)
      (i : Fin m) (t : Fin T),
      blockHyp (compressCore S).1 (compressCore S).2 t (S i).1 = rowHyp S hreal t (S i).1)
    (hmajor : ∀ {m : ℕ} (S : Fin m → X × Bool)
      (hreal : ∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2)
      (i : Fin m),
      ((∑ t : Fin T,
          if rowHyp S hreal t (S i).1 = (S i).2 then (1 : ℝ) else 0) / T) > (1 / 2 : ℝ)) :
    CompressionSchemeWithInfo0 X Bool C := by
  classical
  refine mkIncidenceScheme (X := X) (C := C) T K
    compressCore
    (fun Z info x => majorityVote T (fun t => blockHyp Z info t x))
    hsmall hsub ?_
  intro m S hreal i
  have hcongr :
      majorityVote T (fun t => blockHyp (compressCore S).1 (compressCore S).2 t (S i).1)
        = majorityVote T (fun t => rowHyp S hreal t (S i).1) := by
    congr 1; funext t; exact hagree S hreal i t
  calc
    majorityVote T (fun t => blockHyp (compressCore S).1 (compressCore S).2 t (S i).1)
        = majorityVote T (fun t => rowHyp S hreal t (S i).1) := hcongr
    _ = (S i).2 :=
      majority_vote_eq_of_agree_gt_half hT
        (fun t => rowHyp S hreal t (S i).1)
        (S i).2
        (hmajor S hreal i)
def moranBlockHyp {X : Type u} {C : ConceptClass X Bool} [DecidableEq X]
    (L : ProperFiniteSupportLearner X C) {T K : ℕ}
    (Z : Finset (X × Bool)) (info : IncidenceInfo T K) (t : Fin T) (x : X) : Bool :=
  L.learn
    (labeledSampleOfFinset (decodeWitnessLabel Z) (decodeWitnessXCoords Z (info t))) x
end


