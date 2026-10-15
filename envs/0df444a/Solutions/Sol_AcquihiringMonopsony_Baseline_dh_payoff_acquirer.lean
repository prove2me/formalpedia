-- Prove2me | solution 1 for AcquihiringMonopsony.Baseline.dh_payoff_acquirer
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-14T23:22:39.754288+00:00
-- url     : https://prove2.me/submissions/59359588-c577-4f05-a590-a848e3666e5f

import Mathlib
import Definitions.Def_AcquihiringMonopsony_Baseline_Model
set_option autoImplicit false
noncomputable section
open AcquihiringMonopsony.Baseline

private lemma dh_facts (P : Params) (hP : P.Standing) (σ : DHProfile) (hσ : IsDHEquilibrium P σ) :
    (σ.acceptA σ.wa σ.ws = true → σ.wa = P.vs + P.b) ∧
    (σ.acceptA σ.wa σ.ws = false → σ.ws = P.va - P.b) := by
  rcases hP with ⟨hb, hva, hvs⟩
  rcases hσ with ⟨⟨hwa0,hwa1⟩, ⟨hws0,hws1⟩, hyes, hno, hbestA, hbestS⟩
  have ht (x y : ℝ) (hh : y + P.b < x) : σ.acceptA x y = true := by
    cases he : σ.acceptA x y
    · have hn := hno x y he; linarith
    · rfl
  have hf (x y : ℝ) (hh : x < y + P.b) : σ.acceptA x y = false := by
    cases he : σ.acceptA x y
    · rfl
    · have hn := hyes x y he; linarith
  constructor
  · intro hy
    apply le_antisymm
    · by_contra hn
      have hlt : P.vs + P.b < σ.wa := lt_of_not_ge hn
      let x := (σ.wa + P.vs + P.b) / 2
      have hx0 : P.wl ≤ x := by dsimp [x]; linarith
      have hx : σ.ws + P.b < x := by dsimp [x]; linarith
      have ha := ht x σ.ws hx
      have hh := hbestA x hx0
      simp only [dhPayoffA, ha, hy, ite_true] at hh
      dsimp [x] at hh
      linarith
    · by_contra hn
      have hlt : σ.wa - P.b < P.vs := by linarith [lt_of_not_ge hn]
      have hmax : max P.wl (σ.wa - P.b) < P.vs := max_lt (by linarith) hlt
      obtain ⟨y, hy0, hy1⟩ := exists_between hmax
      have hyf : P.wl ≤ y := (le_max_left _ _).trans hy0.le
      have hwa : σ.wa < y + P.b := by have hh := (le_max_right _ _).trans_lt hy0; linarith
      have he := hf σ.wa y hwa
      have hh := hbestS y hyf
      simp only [dhPayoffS, he, hy, Bool.false_eq_true, ite_false, ite_true] at hh
      linarith
  · intro hn
    apply le_antisymm
    · by_contra hh
      have hlt : P.va - P.b < σ.ws := lt_of_not_ge hh
      let y := (P.va - P.b + σ.ws) / 2
      have hy0 : P.wl ≤ y := by dsimp [y]; linarith
      have hw : σ.wa < y + P.b := by dsimp [y]; linarith
      have he := hf σ.wa y hw
      have hh := hbestS y hy0
      simp only [dhPayoffS, he, hn, Bool.false_eq_true, ite_false] at hh
      dsimp [y] at hh
      linarith
    · by_contra hh
      have hlt : σ.ws + P.b < P.va := by linarith [lt_of_not_ge hh]
      have hmax : max P.wl (σ.ws + P.b) < P.va := max_lt (by linarith) hlt
      obtain ⟨x, hx0, hx1⟩ := exists_between hmax
      have hxf : P.wl ≤ x := (le_max_left _ _).trans hx0.le
      have hw : σ.ws + P.b < x := (le_max_right _ _).trans_lt hx0
      have he := ht x σ.ws hw
      have hh := hbestA x hxf
      simp only [dhPayoffA, he, hn, Bool.false_eq_true, ite_false, ite_true] at hh
      linarith

private lemma dh_classify (P : Params) (hP : P.Standing) (σ : DHProfile) (hσ : IsDHEquilibrium P σ) :
    (P.vs + P.b < P.va → σ.acceptA σ.wa σ.ws = true ∧ σ.wa = P.vs + P.b) ∧
    (P.va < P.vs + P.b → σ.acceptA σ.wa σ.ws = false ∧ σ.ws = P.va - P.b) ∧
    surplus P (σ.acceptA σ.wa σ.ws) = max P.va (P.vs + P.b) := by
  have H := dh_facts P hP σ hσ
  have hw := hσ.1.2
  have hs := hσ.2.1.2
  have ht : P.vs + P.b < P.va → σ.acceptA σ.wa σ.ws = true := by
    intro hv
    cases he : σ.acceptA σ.wa σ.ws
    · have hh := H.2 he; linarith
    · rfl
  have hf : P.va < P.vs + P.b → σ.acceptA σ.wa σ.ws = false := by
    intro hv
    cases he : σ.acceptA σ.wa σ.ws
    · rfl
    · have hh := H.1 he; linarith
  refine ⟨fun h => ⟨ht h,H.1 (ht h)⟩, fun h => ⟨hf h,H.2 (hf h)⟩, ?_⟩
  cases he : σ.acceptA σ.wa σ.ws
  · have hh := H.2 he
    simp only [surplus, he, Bool.false_eq_true, ite_false]
    rw [max_eq_right (by linarith)]
  · have hh := H.1 he
    simp only [surplus, he, ite_true]
    rw [max_eq_left (by linarith)]

private lemma ah_wages (P : Params) (σ : AHProfile) (hσ : IsAHEquilibrium P σ) :
    σ.wa = P.wl ∧ σ.ws = P.wl := by
  exact ⟨le_antisymm (hσ.1.2 P.wl le_rfl) hσ.1.1,
    le_antisymm (hσ.2.1.2 P.wl le_rfl) hσ.2.1.1⟩

private lemma ah_facts (P : Params) (σ : AHProfile) (hσ : IsAHEquilibrium P σ) :
    (P.vs < P.va → σ.p = P.vs - P.wl ∧ σ.acceptBid σ.p = true) ∧
    (P.va < P.vs → σ.acceptBid σ.p = false) := by
  have hw := ah_wages P σ hσ
  rcases hσ with ⟨hwa,hws,hyes,hno,hbid,hbest⟩
  have ht (q : ℝ) (hq : P.vs - P.wl < q) : σ.acceptBid q = true := by
    cases he : σ.acceptBid q
    · have hh := hno q he; rw [hw.2] at hh; linarith
    · rfl
  constructor
  · intro hv
    let q := (P.va + P.vs)/2-P.wl
    have hq : P.vs - P.wl < q := by dsimp [q]; linarith
    have heq := ht q hq
    have hp : σ.acceptBid σ.p = true := by
      cases he : σ.acceptBid σ.p
      · have hh := hbest q
        simp only [ahPayoffA, heq, he, Bool.false_eq_true, ite_false, ite_true, hw.1] at hh
        dsimp [q] at hh
        linarith
      · rfl
    refine ⟨le_antisymm ?_ ?_, hp⟩
    · by_contra hn
      have hh : P.vs - P.wl < σ.p := lt_of_not_ge hn
      let q' := (σ.p + P.vs - P.wl)/2
      have hq' : P.vs-P.wl < q' := by dsimp [q']; linarith
      have he' := ht q' hq'
      have hbest' := hbest q'
      simp only [ahPayoffA, he', hp, ite_true] at hbest'
      dsimp [q'] at hbest'
      linarith
    · have hh := hyes σ.p hp
      simpa [hw.2] using hh
  · intro hv
    cases he : σ.acceptBid σ.p
    · rfl
    · have hh := hyes σ.p he
      rw [hw.2] at hh
      rw [hw.1] at hbid
      linarith

private lemma ah_exists (P : Params) :
    ∃ σ : AHProfile, IsAHEquilibrium P σ ∧
      (P.vs < P.va → σ.p = P.vs-P.wl) ∧ (P.va < P.vs → σ.p = P.va-P.wl) := by
  let σ : AHProfile := ⟨min (P.vs-P.wl) (P.va-P.wl),
    fun q => decide (P.vs-P.wl ≤ q), P.wl, P.wl⟩
  refine ⟨σ, ?_, ?_, ?_⟩
  · refine ⟨⟨le_rfl,fun x hx => hx⟩, ⟨le_rfl,fun y hy => hy⟩, ?_, ?_, min_le_right _ _, ?_⟩
    · intro q hq
      simpa [σ] using hq
    · intro q hq
      have hh : ¬ (P.vs-P.wl ≤ q) := by simpa [σ] using hq
      exact (lt_of_not_ge hh).le
    · intro q
      by_cases hv : P.vs ≤ P.va
      · have hm : min (P.vs-P.wl) (P.va-P.wl) = P.vs-P.wl := min_eq_left (by linarith)
        simp only [ahPayoffA, σ, hm, decide_true, ite_true, le_refl]
        split_ifs with hq
        · have hh : P.vs-P.wl ≤ q := by simpa using hq
          linarith
        · linarith
      · have hm : min (P.vs-P.wl) (P.va-P.wl) = P.va-P.wl := min_eq_right (by linarith)
        have hn : ¬ P.vs-P.wl ≤ P.va-P.wl := by linarith
        simp only [ahPayoffA, σ, hm, hn, decide_false, Bool.false_eq_true, ite_false]
        split_ifs with hq
        · have hh : P.vs-P.wl ≤ q := by simpa using hq
          linarith
        · rfl
  · intro hv
    exact min_eq_left (by linarith)
  · intro hv
    exact min_eq_right (by linarith)

private lemma dh_exists (P : Params) (hP : P.Standing) (hne : P.va ≠ P.vs+P.b) :
    ∃ σ : DHProfile, IsDHEquilibrium P σ := by
  rcases hP with ⟨hb,hva,hvs⟩
  rcases lt_or_gt_of_ne hne with hv | hv
  · let σ : DHProfile := ⟨P.va, P.va-P.b, fun x y => decide (y+P.b < x)⟩
    refine ⟨σ, ⟨⟨?_, le_rfl⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩⟩
    · dsimp [σ]; linarith
    · dsimp [σ]; linarith
    · dsimp [σ]; linarith
    · intro x y hh
      have he : y+P.b < x := by simpa [σ] using hh
      exact he.le
    · intro x y hh
      have he : ¬ y+P.b < x := by simpa [σ] using hh
      exact le_of_not_gt he
    · intro x hx
      have hn : ¬ P.va-P.b+P.b < P.va := by linarith
      simp only [dhPayoffA, σ, hn, decide_false, Bool.false_eq_true, ite_false]
      split_ifs with he
      · have hh : P.va-P.b+P.b < x := by simpa using he
        linarith
      · rfl
    · intro y hy
      have hn : ¬ P.va-P.b+P.b < P.va := by linarith
      simp only [dhPayoffS, σ, hn, decide_false, Bool.false_eq_true, ite_false]
      split_ifs with he
      · linarith
      · have hh : ¬ y+P.b < P.va := by simpa using he
        linarith
  · let σ : DHProfile := ⟨P.vs+P.b, P.vs, fun x y => decide (y+P.b ≤ x)⟩
    refine ⟨σ, ⟨⟨?_, ?_⟩, ⟨?_, le_rfl⟩, ?_, ?_, ?_, ?_⟩⟩
    · dsimp [σ]; linarith
    · dsimp [σ]; linarith
    · dsimp [σ]; linarith
    · intro x y hh
      simpa [σ] using hh
    · intro x y hh
      have he : ¬ y+P.b ≤ x := by simpa [σ] using hh
      exact (lt_of_not_ge he).le
    · intro x hx
      simp only [dhPayoffA, σ, le_refl, decide_true, ite_true]
      split_ifs with he
      · have hh : P.vs+P.b ≤ x := by simpa using he
        linarith
      · linarith
    · intro y hy
      simp only [dhPayoffS, σ, le_refl, decide_true, ite_true]
      split_ifs with he
      · rfl
      · have hh : ¬ y+P.b ≤ P.vs+P.b := by simpa using he
        linarith

private lemma dh_pay_A (P : Params) (hP : P.Standing) (σ : DHProfile) (hσ : IsDHEquilibrium P σ) :
    dhPayoffA P σ.acceptA σ.wa σ.ws = max 0 (P.va-P.vs-P.b) := by
  have H := dh_facts P hP σ hσ
  have hw := hσ.1.2
  have hs := hσ.2.1.2
  cases he : σ.acceptA σ.wa σ.ws
  · have hh := H.2 he
    simp only [dhPayoffA, he, Bool.false_eq_true, ite_false]
    rw [max_eq_left (by linarith)]
  · have hh := H.1 he
    simp only [dhPayoffA, he, ite_true]
    rw [max_eq_right (by linarith)]
    linarith

private lemma dh_pay_E (P : Params) (hP : P.Standing) (σ : DHProfile) (hσ : IsDHEquilibrium P σ) :
    dhPayoffE P σ.acceptA σ.wa σ.ws = if P.vs+P.b ≤ P.va then P.vs+P.b else P.va := by
  have H := dh_facts P hP σ hσ
  have hw := hσ.1.2
  have hs := hσ.2.1.2
  cases he : σ.acceptA σ.wa σ.ws
  · have hh := H.2 he
    simp only [dhPayoffE, he, Bool.false_eq_true, ite_false]
    split_ifs with hv <;> linarith
  · have hh := H.1 he
    simp only [dhPayoffE, he, ite_true]
    split_ifs with hv <;> linarith
theorem solution (P : Params) (hP : P.Standing) (σ : DHProfile)
    (hσ : IsDHEquilibrium P σ) :
    dhPayoffA P σ.acceptA σ.wa σ.ws = max 0 (P.va - P.vs - P.b) := by

  exact dh_pay_A P hP σ hσ

#print axioms solution
