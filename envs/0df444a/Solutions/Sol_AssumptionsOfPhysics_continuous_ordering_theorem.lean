-- Prove2me | solution 1 for AssumptionsOfPhysics.continuous_ordering_theorem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:23:20.217419+00:00
-- url     : https://prove2.me/submissions/ac054eb9-9501-4c85-8145-675a02b3500e

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_PropertiesQuantities

open AssumptionsOfPhysics

namespace C9071Aux

lemma inner_of_infinite {Q : Type*} [LinearOrder Q] {a b : Q} (h : (Set.Icc a b).Infinite) :
    ∃ m, a < m ∧ m < b := by
  by_contra hc
  push Not at hc
  apply h
  apply (Set.toFinite ({a, b} : Set Q)).subset
  intro x hx
  rcases hx with ⟨h1, h2⟩
  rcases eq_or_lt_of_le h1 with e | l
  · simp [e]
  · have := hc x l
    have : x = b := le_antisymm h2 this
    simp [this]

lemma strict_dense {Q : Type*} [LinearOrder Q] (hD : IsDenseOrder Q) {A : Set Q}
    (hA : IsDenseSubset A) {q1 q2 : Q} (h : q1 < q2) :
    ∃ a ∈ A, ¬ IsMax a ∧ ¬ IsMin a ∧ q1 < a ∧ a < q2 := by
  obtain ⟨m1, h1, h1'⟩ := inner_of_infinite (hD q1 q2 h)
  obtain ⟨m2, h2, h2'⟩ := inner_of_infinite (hD m1 q2 h1')
  obtain ⟨a, ha, l, r⟩ := hA m1 m2 h2
  refine ⟨a, ha, ?_, ?_, lt_of_lt_of_le h1 l, lt_of_le_of_lt r h2'⟩
  · exact not_isMax_iff.2 ⟨q2, lt_of_le_of_lt r h2'⟩
  · exact not_isMin_iff.2 ⟨q1, lt_of_lt_of_le h1 l⟩

def A' {Q : Type*} [LinearOrder Q] (A : Set Q) : Set Q := {x | x ∈ A ∧ ¬ IsMax x ∧ ¬ IsMin x}

lemma strict_dense' {Q : Type*} [LinearOrder Q] (hD : IsDenseOrder Q) {A : Set Q}
    (hA : IsDenseSubset A) {q1 q2 : Q} (h : q1 < q2) :
    ∃ a : A' A, q1 < (a : Q) ∧ (a : Q) < q2 := by
  obtain ⟨a, ha, h1, h2, l, r⟩ := strict_dense hD hA h
  exact ⟨⟨a, ha, h1, h2⟩, l, r⟩

abbrev I01 : Type := Set.Ioo (0:ℚ) 1

lemma forward {Q : Type*} [LinearOrder Q] (hD : IsDenseOrder Q) (hC : IsCompleteOrder Q)
    (A : Set Q) (hAc : A.Countable) (hA : IsDenseSubset A) :
    ∃ f : Q → ℝ, StrictMono f ∧ (Set.range f).OrdConnected := by
  by_cases hne : ∃ q1 q2 : Q, q1 < q2
  swap
  · push Not at hne
    refine ⟨fun _ => 0, fun a b hab => absurd hab (not_lt.2 (hne a b)), ?_⟩
    refine ⟨?_⟩
    rintro _ ⟨q, rfl⟩ _ ⟨_, rfl⟩ z hz
    exact ⟨q, (le_antisymm hz.2 hz.1).symm⟩
  obtain ⟨q1, q2, hq⟩ := hne
  have : Countable (A' A) := (hAc.mono (fun x hx => hx.1)).to_subtype
  have : Nonempty (A' A) := by
    obtain ⟨a, -⟩ := strict_dense' hD hA hq
    exact ⟨a⟩
  have : DenselyOrdered (A' A) := ⟨fun a b hab => by
    obtain ⟨c, h1, h2⟩ := strict_dense' hD hA (show (a:Q) < b from hab)
    exact ⟨c, h1, h2⟩⟩
  have : NoMaxOrder (A' A) := ⟨fun a => by
    obtain ⟨b, hb⟩ := not_isMax_iff.1 a.2.2.1
    obtain ⟨c, h1, -⟩ := strict_dense' hD hA hb
    exact ⟨c, h1⟩⟩
  have : NoMinOrder (A' A) := ⟨fun a => by
    obtain ⟨b, hb⟩ := not_isMin_iff.1 a.2.2.2
    obtain ⟨c, -, h2⟩ := strict_dense' hD hA hb
    exact ⟨c, h2⟩⟩
  have : Nonempty I01 := ⟨⟨1/2, by norm_num, by norm_num⟩⟩
  obtain ⟨g⟩ := Order.iso_of_countable_dense (A' A) I01
  set τ : A' A → ℝ := fun a => (((g a : I01) : ℚ) : ℝ) with hτdef
  have τmono : StrictMono τ := by
    intro a b hab
    simp only [hτdef]
    exact_mod_cast (g.strictMono hab)
  have τpos : ∀ a, 0 < τ a := fun a => by
    simp only [hτdef]; exact_mod_cast (g a).2.1
  have τlt1 : ∀ a, τ a < 1 := fun a => by
    simp only [hτdef]; exact_mod_cast (g a).2.2
  -- density of τ-values
  have τdense : ∀ r y : ℝ, 0 ≤ r → r < y → y ≤ 1 → ∃ a, r < τ a ∧ τ a < y := by
    intro r y hr hry hy
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn hry
    have p0 : (0:ℚ) < p := by exact_mod_cast (lt_of_le_of_lt hr hp1)
    have p1 : p < (1:ℚ) := by exact_mod_cast (lt_of_lt_of_le hp2 hy)
    refine ⟨g.symm ⟨p, p0, p1⟩, ?_, ?_⟩ <;> simp [hτdef] <;> assumption
  let L : Q → Set ℝ := fun q => τ '' {a | (a : Q) ≤ q}
  have Lbdd : ∀ q, BddAbove (L q) := fun q => ⟨1, by
    rintro _ ⟨a, -, rfl⟩; exact (τlt1 a).le⟩
  let f : Q → ℝ := fun q => sSup (L q)
  have f0 : ∀ q, 0 ≤ f q := fun q => Real.sSup_nonneg (by
    rintro _ ⟨a, -, rfl⟩; exact (τpos a).le)
  have f1 : ∀ q, f q ≤ 1 := fun q => Real.sSup_le (by
    rintro _ ⟨a, -, rfl⟩; exact (τlt1 a).le) (by norm_num)
  have fle : ∀ q (a : A' A), q < (a:Q) → f q ≤ τ a := by
    intro q a hqa
    apply Real.sSup_le _ (τpos a).le
    rintro _ ⟨c, hc, rfl⟩
    exact (τmono (Subtype.coe_lt_coe.1 (lt_of_le_of_lt hc hqa))).le
  have gef : ∀ q (a : A' A), (a:Q) ≤ q → τ a ≤ f q := by
    intro q a h
    exact le_csSup (Lbdd q) ⟨a, h, rfl⟩
  have fmono : StrictMono f := by
    intro q q' h
    obtain ⟨a, ha1, ha2⟩ := strict_dense' hD hA h
    obtain ⟨b, hb1, hb2⟩ := strict_dense' hD hA ha2
    calc f q ≤ τ a := fle q a ha1
      _ < τ b := τmono (show a < b from hb1)
      _ ≤ f q' := gef q' b hb2.le
  refine ⟨f, fmono, ⟨?_⟩⟩
  rintro _ ⟨x1, rfl⟩ _ ⟨x2, rfl⟩ y ⟨hy1, hy2⟩
  rcases eq_or_lt_of_le hy1 with e | hy1
  · exact ⟨x1, e⟩
  rcases eq_or_lt_of_le hy2 with e | hy2
  · exact ⟨x2, e.symm⟩
  have ypos : 0 < y := lt_of_le_of_lt (f0 x1) hy1
  have ylt : y < 1 := lt_of_lt_of_le hy2 (f1 x2)
  let C : Set Q := {c | ∃ a : A' A, (a:Q) = c ∧ τ a < y}
  have Cne : C.Nonempty := by
    obtain ⟨a, -, ha⟩ := τdense 0 y le_rfl ypos ylt.le
    exact ⟨a, a, rfl, ha⟩
  have Cbdd : BddAbove C := ⟨x2, by
    rintro _ ⟨a, rfl, ha⟩
    by_contra hc
    push Not at hc
    have := fle x2 a hc
    linarith⟩
  obtain ⟨q, hq⟩ := hC C Cne Cbdd
  refine ⟨q, le_antisymm ?_ ?_⟩
  · by_contra hc
    push Not at hc
    have Lne : (L q).Nonempty := by
      rcases (L q).eq_empty_or_nonempty with e | e
      · exfalso
        have : f q = 0 := by simp only [f, e, Real.sSup_empty]
        linarith
      · exact e
    obtain ⟨_, ⟨a, ha, rfl⟩, hya⟩ := exists_lt_of_lt_csSup Lne hc
    obtain ⟨b, hb1, hb2⟩ := τdense y (τ a) ypos.le hya (τlt1 a).le
    have hba : b < a := τmono.lt_iff_lt.1 hb2
    have hbq : (b:Q) < q := lt_of_lt_of_le hba ha
    obtain ⟨_, ⟨c, rfl, hc⟩, hbc⟩ : ∃ c ∈ C, (b:Q) < c := by
      by_contra hn
      push Not at hn
      exact absurd (hq.2 (fun c hc => hn c hc)) (not_le.2 hbq)
    have := τmono (show b < c from hbc)
    linarith
  · by_contra hc
    push Not at hc
    obtain ⟨a, h1, h2⟩ := τdense (f q) y (f0 q) hc ylt.le
    have : (a:Q) ≤ q := hq.1 ⟨a, rfl, h2⟩
    have := gef q a this
    linarith

lemma backward {Q : Type*} [LinearOrder Q] (S : Set ℝ) (hS : S.OrdConnected) (e : Q ≃o S) :
    IsDenseOrder Q ∧ IsCompleteOrder Q ∧ ∃ A : Set Q, A.Countable ∧ IsDenseSubset A := by
  have key : ∀ q q' : Q, q ≤ q' ↔ ((e q : S) : ℝ) ≤ ((e q' : S) : ℝ) := by
    intro q q'
    rw [← e.le_iff_le]; rfl
  have keylt : ∀ q q' : Q, q < q' ↔ ((e q : S) : ℝ) < ((e q' : S) : ℝ) := by
    intro q q'
    rw [← e.lt_iff_lt]; rfl
  have pull : ∀ x : ℝ, (hx : x ∈ S) → ((e (e.symm ⟨x, hx⟩) : S) : ℝ) = x := by
    intro x hx; simp
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    have hlt := (keylt a b).1 hab
    apply Set.Infinite.of_image (fun q => ((e q : S) : ℝ))
    apply (Set.Icc_infinite hlt).mono
    intro x hx
    have xS : x ∈ S := hS.out (e a).2 (e b).2 hx
    refine ⟨e.symm ⟨x, xS⟩, ⟨?_, ?_⟩, pull x xS⟩
    · rw [key, pull]; exact hx.1
    · rw [key, pull]; exact hx.2
  · intro A hne hbdd
    obtain ⟨u, hu⟩ := hbdd
    obtain ⟨a0, ha0⟩ := hne
    let B : Set ℝ := (fun q => ((e q : S) : ℝ)) '' A
    have Bbdd : BddAbove B := ⟨(e u : ℝ), by
      rintro _ ⟨a, ha, rfl⟩; exact (key a u).1 (hu ha)⟩
    have Bne : B.Nonempty := ⟨_, a0, ha0, rfl⟩
    have s1 : ((e a0 : S) : ℝ) ≤ sSup B := le_csSup Bbdd ⟨a0, ha0, rfl⟩
    have s2 : sSup B ≤ (e u : ℝ) := csSup_le Bne (by
      rintro _ ⟨a, ha, rfl⟩; exact (key a u).1 (hu ha))
    have sS : sSup B ∈ S := hS.out (e a0).2 (e u).2 ⟨s1, s2⟩
    refine ⟨e.symm ⟨sSup B, sS⟩, ?_, ?_⟩
    · intro a ha
      rw [key, pull]
      exact le_csSup Bbdd ⟨a, ha, rfl⟩
    · intro b hb
      rw [key, pull]
      exact csSup_le Bne (by rintro _ ⟨a, ha, rfl⟩; exact (key a b).1 (hb ha))
  · refine ⟨(fun q => ((e q : S) : ℝ)) ⁻¹' Set.range ((↑) : ℚ → ℝ), ?_, ?_⟩
    · exact (Set.countable_range _).preimage (Subtype.val_injective.comp e.injective)
    · intro q1 q2 h
      have hlt := (keylt q1 q2).1 h
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlt
      have rS : (r:ℝ) ∈ S := hS.out (e q1).2 (e q2).2 ⟨hr1.le, hr2.le⟩
      refine ⟨e.symm ⟨r, rS⟩, ⟨r, (pull _ rS).symm⟩, ?_, ?_⟩
      · rw [key, pull]; exact hr1.le
      · rw [key, pull]; exact hr2.le

end C9071Aux

theorem C9071Aux.main (Q : Type*) [LinearOrder Q] :
    (IsDenseOrder Q ∧ IsCompleteOrder Q ∧ ∃ A : Set Q, A.Countable ∧ IsDenseSubset A) ↔
      ∃ S : Set ℝ, S.OrdConnected ∧ Nonempty (Q ≃o S) := by
  constructor
  · rintro ⟨hD, hC, A, hAc, hA⟩
    obtain ⟨f, hf, hS⟩ := C9071Aux.forward hD hC A hAc hA
    exact ⟨_, hS, ⟨hf.orderIso f⟩⟩
  · rintro ⟨S, hS, ⟨e⟩⟩
    exact C9071Aux.backward S hS e



open AssumptionsOfPhysics.ExperimentalDomain in
theorem solution {Ω : Type*} (D : ExperimentalDomain Ω) :
    (∃ r : LinearOrder D.Possibility, D.IsNaturalOrder r ∧ @IsDenseOrder _ r.toPreorder ∧
        @IsCompleteOrder _ r.toPreorder ∧
        ∃ A : Set D.Possibility, A.Countable ∧ @IsDenseSubset _ r.toPreorder A) ↔
      ∃ U : Set ℝ, U.OrdConnected ∧
        Nonempty (@Homeomorph D.Possibility U _ (Preorder.topology U)) := by
  constructor
  · rintro ⟨r, hnat, hd, hc, hA⟩
    letI := r
    obtain ⟨S, hS, ⟨e⟩⟩ := (C9071Aux.main D.Possibility).mp ⟨hd, hc, hA⟩
    refine ⟨S, hS, ?_⟩
    letI tS : TopologicalSpace S := Preorder.topology S
    haveI : OrderTopology S := ⟨rfl⟩
    letI tP : TopologicalSpace D.Possibility := Preorder.topology D.Possibility
    haveI : OrderTopology D.Possibility := ⟨rfl⟩
    have h : @Homeomorph D.Possibility S (Preorder.topology D.Possibility) tS :=
      @Homeomorph.mk _ _ tP tS e.toEquiv
        (@OrderIso.continuous _ _ _ _ tP tS ⟨rfl⟩ ⟨rfl⟩ e)
        (@OrderIso.continuous _ _ _ _ tS tP ⟨rfl⟩ ⟨rfl⟩ e.symm)
    have hnat' : Preorder.topology D.Possibility = D.naturalTopology := hnat
    exact ⟨hnat' ▸ h⟩
  · rintro ⟨U, hU, ⟨h⟩⟩
    let g : D.Possibility ≃ U := @Homeomorph.toEquiv _ _ _ (Preorder.topology U) h
    letI r : LinearOrder D.Possibility := LinearOrder.lift' g g.injective
    let f : D.Possibility ≃o U :=
      { toEquiv := g
        map_rel_iff' := Iff.rfl }
    obtain ⟨hd, hc, hA⟩ := (C9071Aux.main D.Possibility).mpr ⟨U, hU, ⟨f⟩⟩
    refine ⟨r, ?_, hd, hc, hA⟩
    letI tU : TopologicalSpace U := Preorder.topology U
    haveI : OrderTopology U := ⟨rfl⟩
    have h2 : D.naturalTopology = TopologicalSpace.induced g tU :=
      (@Homeomorph.isInducing _ _ D.naturalTopology tU h).eq_induced
    letI tP : TopologicalSpace D.Possibility := Preorder.topology D.Possibility
    haveI : OrderTopology D.Possibility := ⟨rfl⟩
    have h1 : Preorder.topology D.Possibility = TopologicalSpace.induced f tU :=
      (@Homeomorph.isInducing _ _ tP tU (@Homeomorph.mk _ _ tP tU f.toEquiv
        (@OrderIso.continuous _ _ _ _ tP tU ⟨rfl⟩ ⟨rfl⟩ f)
        (@OrderIso.continuous _ _ _ _ tU tP ⟨rfl⟩ ⟨rfl⟩ f.symm))).eq_induced
    show Preorder.topology D.Possibility = D.naturalTopology
    rw [h1, h2]
    rfl
