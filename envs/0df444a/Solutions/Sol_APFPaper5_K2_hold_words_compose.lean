-- Prove2me | solution 1 for APFPaper5.K2.hold_words_compose
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T20:39:58.602433+00:00
-- url     : https://prove2.me/submissions/8dd2b6b1-61c5-4105-b8d5-71f41c1a8072

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K2_hold_words
title: A word of the foundation that runs as a hold has one rearrangement, so its score is fixed by the word; the empty word scores as K1 and words one after the other compose
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
ruling: the author, 2026-11-15 11:56 HST, "C, proceed as suggested"
 (RULING_K2_score_is_K1s_score_through_the_word_2026-11-15).
source: Def_APFPaper5_K2_HoldScore (ExecutesAs, RearrangesFamily, holdScore). The builder seat's
 Def_APFPaper1_ContinuationWords (words, Executes) and Def_APFB02_EachTakesBothSides
 (EveryCombinationHeld: every combination of sides of every finite family of the distinctions is held by
 some state; the second sentence of B02 as worded in revision 2026-11-14.1 and typed in
 Def_APF_B02_DeclaredInput_r2_proposed).
consumes_inputs: B02's second sentence, in rearrangement_unique and hold_word_score_unique, as the
 hypothesis EveryCombinationHeld on the readings at the boundary. The other theorems use no declared input.
theorems:
 - (executesAs_nil, executesAs_append, executesAs_unique) the empty word runs as the identity; two words that
   run as maps, one after the other, run as the two maps composed; a word runs as at most one map.
 - (rearrangement_unique) where every combination of sides is held, and the listed distinctions are listed
   once each, a map of states rearranges them in at most one way, sides included.
 - (hold_word_score_unique) so the score through a word that runs as a hold is fixed by the word.
 - (empty_word_scores_as_K1) the empty word is a hold that rearranges nothing, and its score is K1's form.
 - (hold_words_compose) for two such words one after the other: the word runs as the composed map, the
   rearrangement is the composed one, and the score through both is the score through the second of what
   the first makes of what is held.
not claimed:
 - That any word of any world runs as a hold. That a word that runs as a map draws nothing.
 - That the readings at the boundary are the distinctions of B02's domain; they are supplied readings on the
   raw possibilities of the boundary context.
 - Anything about bills or admission of these words. Admission is the domain of the score by the ruling; it
   is not typed here.
 - No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born is
   derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K2_HoldScore
import Theorems.Thm_APFPaper5_K2_rearrangesFamily_id
import Theorems.Thm_APFPaper5_K2_rearrangesFamily_comp
import Theorems.Thm_APFPaper5_K2_nothingDrawn_of_rearranges
import Theorems.Thm_APFPaper5_K2_exists_rearranges_of_nothingDrawn
import Theorems.Thm_APFPaper5_K2_heldAfter_id
import Theorems.Thm_APFPaper5_K2_heldAfter_comp
import Theorems.Thm_APFPaper5_K2_heldAfter_add
import Theorems.Thm_APFPaper5_K2_heldAfter_smul
import Theorems.Thm_APFPaper5_K2_heldAfter_markClass
import Theorems.Thm_APFPaper5_K2_holdScore_id
import Theorems.Thm_APFPaper5_K2_holdScore_marks
import Theorems.Thm_APFPaper5_K2_holdScore_isBilinear
import Theorems.Thm_APFPaper5_K2_holdScore_eq_sum
import Theorems.Thm_APFPaper5_K2_reverse_is_inverse_of_keeps
import Theorems.Thm_APFPaper5_K2_keeps_of_reverse_is_inverse
import Theorems.Thm_APFPaper5_K2_reverse_is_inverse_iff_keeps
import Theorems.Thm_APFPaper5_K2_tableForm_heldAfter_of_keeps
import Theorems.Thm_APFPaper5_K2_ends_reversed_of_keeps
import Theorems.Thm_APFPaper5_K2_keepsTable_diag
import Theorems.Thm_APFPaper5_K2_not_keepsTable_of_diag_ne
import Theorems.Thm_APFPaper5_K2_holdScoreNull_iff_tables
import Theorems.Thm_APFPaper5_K2_source_hold_score_marks
import Theorems.Thm_APFPaper5_K2_source_hold_ends_reversed
import Mathlib.Data.Finset.Insert

set_option autoImplicit false
open APFPaper5.K1 APFPaper1.Continuation

namespace APFPaper5.K2

universe uI uX uD uC uF uW
variable {ι : Type uI}
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uW}

/-! ### Words that run as maps -/

theorem executesAs_nil_p2mProof (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop) (a : Context) :
    ExecutesAs step (Word.nil a) id :=
  fun x y => (executes_nil step a x y).trans eq_comm

theorem executesAs_append_p2mProof (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop) {a : Context}
    (W₁ W₂ : Word Frag a a) (h₁ h₂ : Raw a → Raw a)
    (e₁ : ExecutesAs step W₁ h₁) (e₂ : ExecutesAs step W₂ h₂) :
    ExecutesAs step (W₁.append W₂) (h₂ ∘ h₁) := by
  intro x z
  rw [executes_append]
  constructor
  · rintro ⟨y, hy, hz⟩
    rw [(e₁ x y).mp hy] at hz
    exact (e₂ _ z).mp hz
  · intro hz
    exact ⟨h₁ x, (e₁ x _).mpr rfl, (e₂ _ z).mpr hz⟩

theorem executesAs_unique_p2mProof (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop) {a : Context}
    (W : Word Frag a a) (h h' : Raw a → Raw a)
    (e : ExecutesAs step W h) (e' : ExecutesAs step W h') : h = h' := by
  funext x
  exact (e' x (h x)).mp ((e x (h x)).mpr rfl)

/-! ### A hold has one rearrangement -/

/-- Where every combination of sides is held and the listed distinctions are listed once each, a map of
states rearranges them in at most one way, sides included. -/
theorem rearrangement_unique_p2mProof {X : Type uX} {D : Type uD} (reads : D → X → Bool)
    (hall : APFB02.EveryCombinationHeld reads) (dist : ι → D) (hinj : Function.Injective dist)
    (h : X → X) (s s' : ι → ι) (f f' : ι → Bool)
    (r : RearrangesFamily reads dist h s f) (r' : RearrangesFamily reads dist h s' f') :
    s = s' ∧ f = f' := by
  classical
  have key : ∀ i x, xor (f i) (reads (dist (s i)) x) = xor (f' i) (reads (dist (s' i)) x) :=
    fun i x => (r i x).symm.trans (r' i x)
  have hs : ∀ i, s i = s' i := by
    intro i
    by_contra hne
    have hd : dist (s i) ≠ dist (s' i) := fun hh => hne (hinj hh)
    obtain ⟨x₁, hx₁⟩ := hall {dist (s i), dist (s' i)} (fun _ => false)
    obtain ⟨x₂, hx₂⟩ := hall {dist (s i), dist (s' i)} (fun e => decide (e = dist (s i)))
    have a1 := hx₁ (dist (s i)) (by simp)
    have b1 := hx₁ (dist (s' i)) (by simp)
    have a2 : reads (dist (s i)) x₂ = true := by
      rw [hx₂ (dist (s i)) (by simp)]
      simp
    have b2 : reads (dist (s' i)) x₂ = false := by
      rw [hx₂ (dist (s' i)) (by simp)]
      simp [hd.symm]
    have k1 := key i x₁
    have k2 := key i x₂
    rw [a1, b1] at k1
    rw [a2, b2] at k2
    generalize f i = p at k1 k2
    generalize f' i = q at k1 k2
    cases p <;> cases q <;> simp at k1 k2
  have hf : ∀ i, f i = f' i := by
    intro i
    obtain ⟨x, hx⟩ := hall {dist (s i)} (fun _ => false)
    have k := key i x
    rw [← hs i, hx (dist (s i)) (by simp)] at k
    simpa using k
  exact ⟨funext hs, funext hf⟩

/-! ### The score through a word that runs as a hold -/

/-- The score through a word that runs as a hold is fixed by the word. -/
theorem hold_word_score_unique_p2mProof [Fintype ι]
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop) {a : Context} (W : Word Frag a a)
    {D : Type uD} (reads : D → Raw a → Bool) (hall : APFB02.EveryCombinationHeld reads)
    (dist : ι → D) (hinj : Function.Injective dist) (G : ι → ι → ℝ)
    (h h' : Raw a → Raw a) (e : ExecutesAs step W h) (e' : ExecutesAs step W h')
    (s s' : ι → ι) (f f' : ι → Bool)
    (r : RearrangesFamily reads dist h s f) (r' : RearrangesFamily reads dist h' s' f') :
    holdScore G s = holdScore G s' := by
  have hh := executesAs_unique_p2mProof step W h h' e e'
  subst hh
  rw [(rearrangement_unique_p2mProof reads hall dist hinj h s s' f f' r r').1]

/-- The empty word is a hold that rearranges nothing; its score is K1's form. -/
theorem empty_word_scores_as_K1_p2mProof [Fintype ι]
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop) (a : Context)
    {D : Type uD} (reads : D → Raw a → Bool) (dist : ι → D) (G : ι → ι → ℝ) :
    ExecutesAs step (Word.nil a) id ∧ RearrangesFamily reads dist id id (fun _ => false) ∧
      ∀ x y : ι → ℝ, holdScore G id x y = tableForm G x y :=
  ⟨executesAs_nil_p2mProof step a, rearrangesFamily_id reads dist, fun _ _ => rfl⟩

/-- Two words that run as holds, one after the other. -/
theorem hold_words_compose_p2mProof [Fintype ι]
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop) {a : Context}
    (W₁ W₂ : Word Frag a a) {D : Type uD} (reads : D → Raw a → Bool) (dist : ι → D)
    (G : ι → ι → ℝ) (h₁ h₂ : Raw a → Raw a) (s₁ s₂ : ι → ι) (f₁ f₂ : ι → Bool)
    (e₁ : ExecutesAs step W₁ h₁) (e₂ : ExecutesAs step W₂ h₂)
    (r₁ : RearrangesFamily reads dist h₁ s₁ f₁) (r₂ : RearrangesFamily reads dist h₂ s₂ f₂) :
    ExecutesAs step (W₁.append W₂) (h₂ ∘ h₁) ∧
      RearrangesFamily reads dist (h₂ ∘ h₁) (s₁ ∘ s₂) (fun i => xor (f₂ i) (f₁ (s₂ i))) ∧
      ∀ x y : ι → ℝ, holdScore G (s₁ ∘ s₂) x y = holdScore G s₂ (heldAfter s₁ x) y :=
  ⟨executesAs_append_p2mProof step W₁ W₂ h₁ h₂ e₁ e₂,
    rearrangesFamily_comp reads dist h₁ h₂ s₁ s₂ f₁ f₂ r₁ r₂, fun _ _ => rfl⟩

end APFPaper5.K2


universe apfNative_uI apfNative_uD apfNative_uC apfNative_uF apfNative_uW
theorem solution :
∀ {ι : Type apfNative_uI} {Context : Type apfNative_uC} {Frag : Context → Context → Type apfNative_uF}
  {Raw : Context → Type apfNative_uW} [inst : Fintype.{apfNative_uI} ι]
  (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop) {a : Context}
  (W₁ W₂ : @APFPaper1.Continuation.Word.{apfNative_uC, apfNative_uF} Context Frag a a) {D : Type apfNative_uD}
  (reads : D → Raw a → Bool) (dist : ι → D) (G : ι → ι → Real) (h₁ h₂ : Raw a → Raw a) (s₁ s₂ : ι → ι)
  (f₁ f₂ : ι → Bool)
  (e₁ : @APFPaper5.K2.ExecutesAs.{apfNative_uC, apfNative_uF, apfNative_uW} Context Frag Raw step a W₁ h₁)
  (e₂ : @APFPaper5.K2.ExecutesAs.{apfNative_uC, apfNative_uF, apfNative_uW} Context Frag Raw step a W₂ h₂)
  (r₁ : @APFPaper5.K2.RearrangesFamily.{apfNative_uI, apfNative_uW, apfNative_uD} ι (Raw a) D reads dist h₁ s₁ f₁)
  (r₂ : @APFPaper5.K2.RearrangesFamily.{apfNative_uI, apfNative_uW, apfNative_uD} ι (Raw a) D reads dist h₂ s₂ f₂),
  And
    (@APFPaper5.K2.ExecutesAs.{apfNative_uC, apfNative_uF, apfNative_uW} Context Frag Raw step a
      (@APFPaper1.Continuation.Word.append.{apfNative_uC, apfNative_uF} Context Frag a a a W₁ W₂)
      (@Function.comp.{apfNative_uW + 1, apfNative_uW + 1, apfNative_uW + 1} (Raw a) (Raw a) (Raw a) h₂ h₁))
    (And
      (@APFPaper5.K2.RearrangesFamily.{apfNative_uI, apfNative_uW, apfNative_uD} ι (Raw a) D reads dist
        (@Function.comp.{apfNative_uW + 1, apfNative_uW + 1, apfNative_uW + 1} (Raw a) (Raw a) (Raw a) h₂ h₁)
        (@Function.comp.{apfNative_uI + 1, apfNative_uI + 1, apfNative_uI + 1} ι ι ι s₁ s₂) fun (i : ι) =>
        Bool.xor (f₂ i) (f₁ (s₂ i)))
      (∀ (x y : ι → Real),
        @Eq.{1} Real
          (@APFPaper5.K2.holdScore.{apfNative_uI} ι inst G
            (@Function.comp.{apfNative_uI + 1, apfNative_uI + 1, apfNative_uI + 1} ι ι ι s₁ s₂) x y)
          (@APFPaper5.K2.holdScore.{apfNative_uI} ι inst G s₂ (@APFPaper5.K2.heldAfter.{apfNative_uI} ι s₁ x) y))) := by
  exact @APFPaper5.K2.hold_words_compose_p2mProof
