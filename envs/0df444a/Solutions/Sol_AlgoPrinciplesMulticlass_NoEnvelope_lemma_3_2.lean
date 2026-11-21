-- Prove2me | solution 1 for AlgoPrinciplesMulticlass.NoEnvelope.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:15:27.686637+00:00
-- url     : https://prove2.me/submissions/0374ee58-8f4f-4c79-80db-5def01c20603

import Mathlib
import Definitions.Def_AlgoPrinciplesMulticlass_NoEnvelope_PAC
import Definitions.Def_AlgoPrinciplesMulticlass_NoEnvelope_Construction

section
namespace AlgoPrinciplesMulticlass.Dev.L32
open AlgoPrinciplesMulticlass.NoEnvelope

open Classical in
noncomputable def rank (p : Param) (x : Pt) : ℕ∞ :=
  if h : ∃ i : Fin p.ℓ, x = p.publicPoint i then ((h.choose : Fin p.ℓ).val : ℕ∞) else ⊤

theorem pp_v_length (p : Param) (i : Fin p.ℓ) : (p.publicPoint i).v.length = i.val := by
  simp [Param.publicPoint]

theorem pp_inj (p : Param) {i k : Fin p.ℓ} (h : p.publicPoint i = p.publicPoint k) : i = k := by
  have := congrArg (fun x : Pt => x.v.length) h
  simp only [pp_v_length] at this
  exact Fin.ext this

theorem rank_pp (p : Param) (i : Fin p.ℓ) : rank p (p.publicPoint i) = (i.val : ℕ∞) := by
  have h : ∃ k : Fin p.ℓ, p.publicPoint i = p.publicPoint k := ⟨i, rfl⟩
  rw [rank, dif_pos h, pp_inj p h.choose_spec.symm]

theorem hyp_pp (p : Param) (i : Fin p.ℓ) : hyp p (p.publicPoint i) = Label.pub (p.b i (p.u i)) := by
  have h : ∃ k : Fin p.ℓ, p.publicPoint i = p.publicPoint k := ⟨i, rfl⟩
  rw [hyp, dif_pos h, pp_inj p h.choose_spec.symm]

theorem hyp_np (p : Param) (x : Pt) (h : ¬ ∃ i : Fin p.ℓ, x = p.publicPoint i) :
    hyp p x = Label.priv p := by
  rw [hyp, dif_neg h]

theorem rank_np (p : Param) (x : Pt) (h : ¬ ∃ i : Fin p.ℓ, x = p.publicPoint i) :
    rank p x = ⊤ := by
  rw [rank, dif_neg h]

open Classical in
theorem reconstruct_same (d : ℕ) (v v' : List (Fin d → Bool)) (j j' : Fin d) (y : Label) :
    reconstruct ⟨d, v, j⟩ y ⟨d, v', j'⟩ =
      if (⟨d, v', j'⟩ : Pt) = ⟨d, v, j⟩ then y else
      if hp : v' <+: v ∧ v'.length < v.length then Label.pub (v.get ⟨v'.length, hp.2⟩ j')
      else Label.pub false := by
  unfold reconstruct
  simp only [dite_true]

theorem err_subset (p : Param) (m : ℕ) (hm : 1 ≤ m) (xs : Fin m → Pt) :
    {x | refLearner m (labelSample (hyp p) xs) x ≠ hyp p x} ⊆
      {x | Finset.univ.sup (fun k : Fin m => rank p (xs k)) < rank p x} := by
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  by_cases ha : ∃ k, ¬ ∃ i : Fin p.ℓ, xs k = p.publicPoint i
  · exfalso
    obtain ⟨k, hk⟩ := ha
    obtain ⟨q, hq⟩ : ∃ q, (List.finRange m).findSome? (fun i => (labelSample (hyp p) xs i).2.privParam) = some q := by
      rcases h : (List.finRange m).findSome? (fun i => (labelSample (hyp p) xs i).2.privParam) with _ | q
      · rw [List.findSome?_eq_none_iff] at h
        have := h k (List.mem_finRange k)
        simp [labelSample, hyp_np p _ hk, Label.privParam] at this
      · exact ⟨q, rfl⟩
    obtain ⟨a, _, ha⟩ := List.exists_of_findSome?_eq_some hq
    have hqp : q = p := by
      simp only [labelSample] at ha
      by_cases hh : ∃ i : Fin p.ℓ, xs a = p.publicPoint i
      · obtain ⟨i, hi⟩ := hh
        rw [hi, hyp_pp] at ha; simp [Label.privParam] at ha
      · rw [hyp_np p _ hh] at ha; simpa [Label.privParam] using ha.symm
    apply hx
    simp only [refLearner, hq, hqp]
  · push_neg at ha
    choose σ hσ using ha
    have hnone : (List.finRange m).findSome? (fun i => (labelSample (hyp p) xs i).2.privParam) = none := by
      rw [List.findSome?_eq_none_iff]
      intro k _
      simp [labelSample, hσ k, hyp_pp, Label.privParam]
    have hne : (List.finRange m) ≠ [] := by
      intro h
      have := congrArg List.length h
      simp at this; omega
    obtain ⟨i0, hi0⟩ : ∃ i0, (List.finRange m).argmax (fun i => (labelSample (hyp p) xs i).1.v.length) = some i0 := by
      cases h : (List.finRange m).argmax (fun i => (labelSample (hyp p) xs i).1.v.length) with
      | none => exact absurd (List.argmax_eq_none.1 h) hne
      | some i => exact ⟨i, rfl⟩
    have hmax : ∀ k, (xs k).v.length ≤ (xs i0).v.length := fun k =>
      List.le_of_mem_argmax (List.mem_finRange k) hi0
    have hrank : ∀ k, rank p (xs k) = ((σ k).val : ℕ∞) := fun k => by
      rw [hσ k, rank_pp]
    have hsup : Finset.univ.sup (fun k : Fin m => rank p (xs k)) = ((σ i0).val : ℕ∞) := by
      apply le_antisymm
      · apply Finset.sup_le
        intro k _
        rw [hrank k]
        have := hmax k
        rw [hσ k, hσ i0, pp_v_length, pp_v_length] at this
        exact_mod_cast this
      · rw [← hrank i0]; exact Finset.le_sup (f := fun k : Fin m => rank p (xs k)) (Finset.mem_univ i0)
    rw [hsup]
    by_contra hle
    push_neg at hle
    by_cases hp : ∃ t : Fin p.ℓ, x = p.publicPoint t
    · obtain ⟨t, rfl⟩ := hp
      rw [rank_pp] at hle
      have htle : t.val ≤ (σ i0).val := by exact_mod_cast hle
      apply hx
      simp only [refLearner, hnone, hi0]
      simp only [labelSample]
      rw [hσ i0] at *
      generalize hr : σ i0 = s at *
      simp only [hyp_pp]
      rcases htle.eq_or_lt with h | h
      · have h := Fin.ext h; subst h; simp [reconstruct, hyp_pp]
      · have := reconstruct_same p.d ((List.ofFn p.b).take s) ((List.ofFn p.b).take t) (p.u s) (p.u t)
          (Label.pub (p.b s (p.u s)))
        simp only [Param.publicPoint] at *
        rw [this, if_neg, dif_pos]
        · simp [List.getElem_take, List.getElem_ofFn]
        · refine ⟨?_, ?_⟩
          · have : (List.ofFn p.b).take t = ((List.ofFn p.b).take s).take t := by
              rw [List.take_take]; congr 1; exact (min_eq_left htle).symm
            rw [this]; exact List.take_prefix _ _
          · simp; omega
        · intro hh
          have := congrArg (fun x : Pt => x.v.length) hh
          simp at this; omega
    · rw [rank_np p x hp] at hle
      simp at hle

end AlgoPrinciplesMulticlass.Dev.L32
end

section
open MeasureTheory

namespace AlgoPrinciplesMulticlass.Dev.L32

theorem avoid_bound {α : Type*} [Countable α] (D : @Measure α ⊤) (hD : @IsProbabilityMeasure α ⊤ D)
    (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1) (m : ℕ) (A : Set α)
    (hA : ENNReal.ofReal ε ≤ D Aᶜ) :
    (@Measure.pi (Fin m) (fun _ => α) _ (fun _ => ⊤) (fun _ => D))
      {xs : Fin m → α | ∀ k, xs k ∈ A} ≤ ENNReal.ofReal (Real.exp (-((m:ℝ) * ε))) := by
  letI : MeasurableSpace α := ⊤
  haveI : IsProbabilityMeasure D := hD
  have hAm : MeasurableSet A := by
    exact (Set.to_countable A).measurableSet
  have hDA : D A ≤ ENNReal.ofReal (1 - ε) := by
    have : D A = 1 - D Aᶜ := by
      rw [prob_compl_eq_one_sub hAm, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
    rw [this, ENNReal.ofReal_sub _ h0.le, ENNReal.ofReal_one]
    exact tsub_le_tsub_left hA _
  have hset : {xs : Fin m → α | ∀ k, xs k ∈ A} = Set.pi Set.univ (fun _ => A) := by
    ext xs; simp
  rw [hset, Measure.pi_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc D A ^ m ≤ (ENNReal.ofReal (1 - ε)) ^ m := pow_le_pow_left' hDA m
    _ = ENNReal.ofReal ((1 - ε) ^ m) := (ENNReal.ofReal_pow (by linarith) m).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have h2 : 1 - ε ≤ Real.exp (-ε) := by
        have := Real.add_one_le_exp (-ε); linarith
      calc (1 - ε) ^ m ≤ (Real.exp (-ε)) ^ m := pow_le_pow_left₀ (by linarith) h2 m
        _ = _ := by rw [← Real.exp_nat_mul]; ring_nf

theorem tail_bound {α : Type*} [Countable α] (rank : α → ℕ∞) (D : @MeasureTheory.Measure α ⊤) (hD : @MeasureTheory.IsProbabilityMeasure α ⊤ D) (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1) (m : ℕ) (hm : 1 ≤ m) :
  (@MeasureTheory.Measure.pi (Fin m) (fun _ => α) _ (fun _ => ⊤) (fun _ => D)) {xs : Fin m → α | ENNReal.ofReal ε < D {x | Finset.univ.sup (fun k : Fin m => rank (xs k)) < rank x}} ≤ ENNReal.ofReal (Real.exp (-((m:ℝ) * ε))) := by
  letI : MeasurableSpace α := ⊤
  haveI : IsProbabilityMeasure D := hD
  have hmeas : ∀ s : Set α, MeasurableSet s := fun s => Set.to_countable s |>.measurableSet
  by_cases hc : ∃ K : ℕ, D {x | (K : ℕ∞) < rank x} ≤ ENNReal.ofReal ε
  · classical
    set k0 := Nat.find hc with hk0
    have hk0s : D {x | (k0 : ℕ∞) < rank x} ≤ ENNReal.ofReal ε := Nat.find_spec hc
    refine le_trans (measure_mono (t := {xs : Fin m → α | ∀ k, xs k ∈ {x | rank x < k0}}) ?_)
      (avoid_bound D hD ε h0 h1 m {x | rank x < k0} ?_)
    · intro xs hxs k
      simp only [Set.mem_setOf_eq] at hxs ⊢
      by_contra hk
      push_neg at hk
      have : (k0 : ℕ∞) ≤ Finset.univ.sup (fun k : Fin m => rank (xs k)) :=
        hk.trans (Finset.le_sup (f := fun k : Fin m => rank (xs k)) (Finset.mem_univ k))
      have hsub : {x | Finset.univ.sup (fun k : Fin m => rank (xs k)) < rank x}
          ⊆ {x | (k0 : ℕ∞) < rank x} := fun x hx => lt_of_le_of_lt this hx
      exact absurd (lt_of_lt_of_le hxs (measure_mono hsub |>.trans hk0s)) (lt_irrefl _)
    · rcases Nat.eq_zero_or_pos k0 with h | h
      · have : ({x | rank x < k0} : Set α)ᶜ = Set.univ := by
          ext x; simp [h]
        rw [this]; simp; exact h1.le
      · obtain ⟨j, hj⟩ : ∃ j, k0 = j + 1 := ⟨k0 - 1, by omega⟩
        have hlt : j < k0 := by omega
        have hn := Nat.find_min hc hlt
        push_neg at hn
        have : ({x | rank x < k0} : Set α)ᶜ = {x | (j : ℕ∞) < rank x} := by
          ext x
          simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt, hj]
          constructor
          · intro h
            exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self j) h
          · intro h
            push_cast; exact Order.add_one_le_of_lt h
        rw [this]; exact hn.le
  · push_neg at hc
    have hsub : {xs : Fin m → α | ENNReal.ofReal ε < D {x | Finset.univ.sup (fun k : Fin m => rank (xs k)) < rank x}}
        ⊆ {xs : Fin m → α | ∀ k, xs k ∈ {x | rank x ≠ ⊤}} := by
      intro xs hxs k
      simp only [Set.mem_setOf_eq] at hxs ⊢
      intro htop
      have : Finset.univ.sup (fun k : Fin m => rank (xs k)) = ⊤ :=
        top_le_iff.mp (htop ▸ Finset.le_sup (f := fun k : Fin m => rank (xs k)) (Finset.mem_univ k))
      have hemp : {x | Finset.univ.sup (fun k : Fin m => rank (xs k)) < rank x} = ∅ := by
        ext x; simp [this]
      rw [hemp] at hxs; simp at hxs
    refine le_trans (measure_mono hsub) (avoid_bound D hD ε h0 h1 m _ ?_)
    have heq : ({x | rank x ≠ ⊤} : Set α)ᶜ = ⋂ K : ℕ, {x | (K : ℕ∞) < rank x} := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iInter, not_not]
      constructor
      · intro h K; rw [h]; exact ENat.coe_lt_top K
      · intro h
        by_contra hne
        obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
        have h3 := h (n + 1)
        rw [← hn] at h3
        have h2 : n + 1 < n := by exact_mod_cast h3
        omega
    rw [heq]
    have hanti : Antitone (fun K : ℕ => {x | (K : ℕ∞) < rank x}) := by
      intro a b hab x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      exact lt_of_le_of_lt (by exact_mod_cast hab) hx
    rw [hanti.measure_iInter (fun K => (hmeas _).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
    exact le_iInf fun K => (hc K).le

end AlgoPrinciplesMulticlass.Dev.L32
end

section
open MeasureTheory

namespace AlgoPrinciplesMulticlass
open NoEnvelope

instance Dev.L32.instCountPt : Countable Pt := by
  have : Function.Injective (fun x : Pt => (⟨x.d, (x.v, x.j)⟩ : Σ d : ℕ, List (Fin d → Bool) × Fin d)) := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [Sigma.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [heq_eq_eq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  exact this.countable

theorem chk_lemma_3_2 (h : Pt → Label) (hh : h ∈ H) (D : @Measure Pt ⊤)
    (hD : @IsProbabilityMeasure Pt ⊤ D) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (m : ℕ)
    (hm : 1 ≤ m) :
    failProb refLearner h D m ε ≤ ENNReal.ofReal (Real.exp (-((m : ℝ) * ε))) := by
  obtain ⟨p, rfl⟩ := hh
  refine le_trans (measure_mono ?_) (Dev.L32.tail_bound (Dev.L32.rank p) D hD ε hε0 hε1 m hm)
  intro xs hxs
  simp only [Set.mem_setOf_eq] at hxs ⊢
  refine lt_of_lt_of_le hxs (measure_mono ?_)
  exact Dev.L32.err_subset p m hm xs
end AlgoPrinciplesMulticlass
end

theorem solution : type_of% @AlgoPrinciplesMulticlass.chk_lemma_3_2 := @AlgoPrinciplesMulticlass.chk_lemma_3_2
