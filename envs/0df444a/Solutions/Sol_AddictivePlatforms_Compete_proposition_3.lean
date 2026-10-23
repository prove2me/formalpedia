-- Prove2me | solution 1 for AddictivePlatforms.Compete.proposition_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T09:21:24.486874+00:00
-- url     : https://prove2.me/submissions/02c67a22-6d3b-4298-a5ff-eb217caabe08
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AddictivePlatforms_Compete_Model
import Theorems.Thm_AddictivePlatforms_Compete_proposition_1
import Theorems.Thm_AddictivePlatforms_Compete_proposition_2

open Set Filter Topology
open scoped ENNReal

namespace AP1P3
open AddictivePlatforms.Compete

variable {u : ℝ → ℝ → ℝ} {C : ℝ → ℝ}

lemma slice_diffOn (hS : Standing u C) {d : ℝ} (hd : 0 ≤ d) :
    DifferentiableOn ℝ (fun a => u a d) (Ici 0) := by
  have h1 : DifferentiableOn ℝ (fun a : ℝ => (a, d)) (Ici 0) :=
    (differentiableOn_id.prodMk (differentiableOn_const d))
  have h2 : MapsTo (fun a : ℝ => (a, d)) (Ici 0) quadrant := by
    intro a ha; exact ⟨ha, hd⟩
  exact hS.assumption1.differentiableOn.comp h1 h2

lemma sliceD_contOn (hS : Standing u C) {a : ℝ} (ha : 0 ≤ a) :
    ContinuousOn (fun d => u a d) (Ici 0) := by
  have h1 : ContinuousOn (fun d : ℝ => (a, d)) (Ici 0) :=
    (continuousOn_const.prodMk continuousOn_id)
  have h2 : MapsTo (fun d : ℝ => (a, d)) (Ici 0) quadrant := by
    intro d hd; exact ⟨ha, hd⟩
  exact hS.assumption1.differentiableOn.continuousOn.comp h1 h2

lemma hasDeriv_u (hS : Standing u C) {a d : ℝ} (ha : 0 < a) (hd : 0 ≤ d) :
    HasDerivAt (fun a => u a d) (u1 u a d) a := by
  have hn : Ici (0:ℝ) ∈ 𝓝 a := Ici_mem_nhds ha
  have hda : DifferentiableAt ℝ (fun a => u a d) a :=
    ((slice_diffOn hS hd) a (le_of_lt ha)).differentiableAt hn
  have : u1 u a d = deriv (fun a => u a d) a := derivWithin_of_mem_nhds hn
  rw [this]; exact hda.hasDerivAt

lemma hasDeriv_C (hS : Standing u C) {a : ℝ} (ha : 0 < a) :
    HasDerivAt C (Cderiv C a) a := by
  have hn : Ici (0:ℝ) ∈ 𝓝 a := Ici_mem_nhds ha
  have hda : DifferentiableAt ℝ C a :=
    (hS.assumption2.differentiableOn a (le_of_lt ha)).differentiableAt hn
  have : Cderiv C a = deriv C a := derivWithin_of_mem_nhds hn
  rw [this]; exact hda.hasDerivAt

lemma f_contOn (hS : Standing u C) {d : ℝ} (hd : 0 ≤ d) :
    ContinuousOn (fun a => u a d - C a) (Ici 0) :=
  (slice_diffOn hS hd).continuousOn.sub hS.assumption2.differentiableOn.continuousOn

/-- Near `0`, every `f_d = u(·,d) - C` is strictly increasing. -/
lemma eps_mono (hS : Standing u C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ d : ℝ, 0 ≤ d → StrictMonoOn (fun a => u a d - C a) (Icc 0 ε) := by
  have hev : ∀ᶠ a in 𝓝[>] (0:ℝ), 0 < u1 u a 0 - Cderiv C a := by
    rcases hS.assumption2.limit_pos with ⟨L, hL, hT⟩ | hT
    · exact hT.eventually_const_lt hL
    · exact hT.eventually_gt_atTop 0
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨ε, hε, fun d hd => ?_⟩
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 ε)
  · exact (f_contOn hS hd).mono Icc_subset_Ici_self
  · intro a ha
    rw [interior_Icc] at ha
    have ha0 : 0 < a := ha.1
    have hder : HasDerivAt (fun a => u a d - C a) (u1 u a d - Cderiv C a) a :=
      (hasDeriv_u hS ha0 hd).sub (hasDeriv_C hS ha0)
    rw [hder.deriv]
    have h1 : 0 < u1 u a 0 - Cderiv C a := hsub ha
    have h2 : u1 u a 0 ≤ u1 u a d := by
      rcases eq_or_lt_of_le hd with h | h
      · rw [← h]
      · exact le_of_lt (hS.assumption1.strictMonoOn_u1 a (le_of_lt ha0)
          (show (0:ℝ) ∈ Ici 0 from mem_Ici.2 le_rfl) (show d ∈ Ici 0 from hd) h)
    linarith

lemma Aopt_pos (hS : Standing u C) {Aopt : ℝ → ℝ} (hA : IsUncChoice u C Aopt)
    {d : ℝ} (hd : 0 ≤ d) : 0 < Aopt d := by
  obtain ⟨ε, hε, hm⟩ := eps_mono hS
  rcases (hA d hd).1.lt_or_eq with h | h
  · exact h
  · exfalso
    have h1 := hm d hd (show (0:ℝ) ∈ Icc 0 ε from ⟨le_refl _, hε.le⟩)
      (show ε / 2 ∈ Icc 0 ε from ⟨by linarith, by linarith⟩) (by linarith)
    have h2 := (hA d hd).2 (show ε / 2 ∈ Ici (0:ℝ) from by simp; linarith)
    simp only [mem_ofPred_eq] at h2
    rw [← h] at h2
    simp at h1 h2
    linarith

/-- The unconstrained value `W(d) = u(A(d),d) - C(A(d))` at `d = 0` is positive. -/
lemma W0_pos (hS : Standing u C) {Aopt : ℝ → ℝ} (hA : IsUncChoice u C Aopt) :
    0 < u (Aopt 0) 0 - C (Aopt 0) := by
  obtain ⟨ε, hε, hm⟩ := eps_mono hS
  have h1 := hm 0 le_rfl (show (0:ℝ) ∈ Icc 0 ε from ⟨le_refl _, hε.le⟩)
      (show ε ∈ Icc 0 ε from ⟨hε.le, le_rfl⟩) hε
  have h2 := (hA 0 le_rfl).2 (show ε ∈ Ici (0:ℝ) from hε.le)
  simp only [mem_ofPred_eq] at h2
  simp only [hS.C_zero] at h1
  linarith [hS.assumption1.u_zero_zero_nonneg]

lemma CS_nonneg {K : ℕ} {Abar : ℝ≥0∞} {d : Fin K → ℝ} {x : Choice K}
    (h : ConsumerOpt u C Abar d x) : 0 ≤ payoff u C d x := by
  have := h.2 (∅, fun _ => 0) ⟨by simp, by simp⟩
  simpa [payoff] using this

/-- With one platform at addictiveness `x`, if the unconstrained choice `A(x)` is feasible and
gives a positive value, every optimal choice joins and spends exactly `A(x)`. -/
lemma mono_choice (hS : Standing u C) {Aopt : ℝ → ℝ} (hA : IsUncChoice u C Aopt)
    {Abar : ℝ≥0∞} {x : ℝ} (hx : 0 ≤ x) (hfeas : ENNReal.ofReal (Aopt x) ≤ Abar)
    (hW : 0 < u (Aopt x) x - C (Aopt x)) {d : Fin 1 → ℝ} (hd : ∀ k, d k = x)
    {y : Choice 1} (hy : ConsumerOpt u C Abar d y) :
    0 ∈ y.1 ∧ y.2 0 = Aopt x ∧ payoff u C d y = u (Aopt x) x - C (Aopt x) := by
  have hA0 := (hA x hx).1
  have hfe : Feasible Abar (({0} : Finset (Fin 1)), fun _ => Aopt x) :=
    ⟨by simp [hA0], by simpa using hfeas⟩
  have hp := hy.2 _ hfe
  have hp' : payoff u C d (({0} : Finset (Fin 1)), fun _ => Aopt x) =
      u (Aopt x) x - C (Aopt x) := by simp [payoff, hd]
  rw [hp'] at hp
  have hne : y.1 ≠ ∅ := by
    intro h
    have : payoff u C d y = 0 := by simp [payoff, h]
    linarith
  have h0 : (0 : Fin 1) ∈ y.1 := by
    obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.2 hne
    rwa [Subsingleton.elim k 0] at hk
  have hJ : y.1 = {0} := Finset.eq_singleton_iff_unique_mem.2 ⟨h0, fun k _ => Subsingleton.elim _ _⟩
  have hpy : payoff u C d y = u (y.2 0) x - C (y.2 0) := by
    simp [payoff, hJ, hd]
  have ha0 : 0 ≤ y.2 0 := hy.1.1 0 h0
  have hup := (hA x hx).2 (show y.2 0 ∈ Ici (0:ℝ) from ha0)
  simp only [mem_ofPred_eq] at hup
  have heq : payoff u C d y = u (Aopt x) x - C (Aopt x) := by
    rw [hpy] at hp ⊢; linarith
  refine ⟨h0, ?_, heq⟩
  by_contra hneq
  have hsc := (hS.strictConcaveOn_a x hx).2 (show y.2 0 ∈ Ici (0:ℝ) from ha0)
    (show Aopt x ∈ Ici (0:ℝ) from hA0) hneq (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num)
  have hcv := hS.assumption2.convexOn.2 (show y.2 0 ∈ Ici (0:ℝ) from ha0)
    (show Aopt x ∈ Ici (0:ℝ) from hA0) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at hsc hcv
  have hm : (0:ℝ) ≤ 1/2 * y.2 0 + 1/2 * Aopt x := by positivity
  have hmax := (hA x hx).2 (show 1/2 * y.2 0 + 1/2 * Aopt x ∈ Ici (0:ℝ) from hm)
  simp only [mem_ofPred_eq] at hmax
  rw [hpy] at heq
  linarith

/-- Strict monotone comparative statics: `A(·)` is strictly increasing. -/
lemma Aopt_strictMono (hS : Standing u C) {Aopt : ℝ → ℝ} (hA : IsUncChoice u C Aopt)
    {d0 x : ℝ} (hd0 : 0 ≤ d0) (hlt : d0 < x) : Aopt d0 < Aopt x := by
  have hx : 0 ≤ x := le_trans hd0 hlt.le
  by_contra hle
  rw [not_lt] at hle
  set a0 := Aopt d0 with ha0def
  set b := Aopt x with hbdef
  have ha0 : 0 < a0 := Aopt_pos hS hA hd0
  have hb : 0 ≤ b := (hA x hx).1
  have hg : StrictMonoOn (fun a => u a x - u a d0) (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact (slice_diffOn hS hx).continuousOn.sub (slice_diffOn hS hd0).continuousOn
    · intro a ha
      rw [interior_Ici] at ha
      have hder : HasDerivAt (fun a => u a x - u a d0) (u1 u a x - u1 u a d0) a :=
        (hasDeriv_u hS ha hx).sub (hasDeriv_u hS ha hd0)
      rw [hder.deriv]
      have := hS.assumption1.strictMonoOn_u1 a (le_of_lt ha) (show d0 ∈ Ici 0 from hd0)
        (show x ∈ Ici 0 from hx) hlt
      simp only at this
      linarith
  have o1 := (hA x hx).2 (show a0 ∈ Ici (0:ℝ) from ha0.le)
  have o2 := (hA d0 hd0).2 (show b ∈ Ici (0:ℝ) from hb)
  simp only [mem_ofPred_eq] at o1 o2
  have hba : b = a0 := by
    rcases lt_or_eq_of_le hle with h | h
    · have := hg (show b ∈ Ici (0:ℝ) from hb) (show a0 ∈ Ici (0:ℝ) from ha0.le) h
      simp only at this
      linarith
    · exact h
  have hn : Ici (0:ℝ) ∈ 𝓝 a0 := Ici_mem_nhds ha0
  have m1 : IsLocalMax (fun a => u a x - C a) a0 := by
    have := (hA x hx).2
    rw [← hbdef, hba] at this
    exact this.isLocalMax hn
  have m2 : IsLocalMax (fun a => u a d0 - C a) a0 := (hA d0 hd0).2.isLocalMax hn
  have e1 := m1.deriv_eq_zero
  have e2 := m2.deriv_eq_zero
  have q1 : HasDerivAt (fun a => u a x - C a) (u1 u a0 x - Cderiv C a0) a0 :=
    (hasDeriv_u hS ha0 hx).sub (hasDeriv_C hS ha0)
  have q2 : HasDerivAt (fun a => u a d0 - C a) (u1 u a0 d0 - Cderiv C a0) a0 :=
    (hasDeriv_u hS ha0 hd0).sub (hasDeriv_C hS ha0)
  rw [q1.deriv] at e1
  rw [q2.deriv] at e2
  have := hS.assumption1.strictMonoOn_u1 a0 ha0.le (show d0 ∈ Ici 0 from hd0)
    (show x ∈ Ici 0 from hx) hlt
  simp only at this
  linarith

lemma sum_fin2 (J : Finset (Fin 2)) (f : Fin 2 → ℝ) :
    ∑ k ∈ J, f k = (if (0 : Fin 2) ∈ J then f 0 else 0) + (if (1 : Fin 2) ∈ J then f 1 else 0) := by
  have : ∑ k ∈ J, f k = ∑ k, if k ∈ J then f k else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [this, Fin.sum_univ_two]

lemma small_feasible {Abar : ℝ≥0∞} (hAbar : 0 < Abar) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ℝ, 0 < e ∧ e ≤ ε ∧ ENNReal.ofReal e ≤ Abar := by
  by_cases htop : Abar = ⊤
  · exact ⟨ε, hε, le_rfl, by simp [htop]⟩
  · have hpos : 0 < Abar.toReal := ENNReal.toReal_pos (ne_of_gt hAbar) htop
    refine ⟨min ε Abar.toReal, lt_min hε hpos, min_le_left _ _, ?_⟩
    calc ENNReal.ofReal (min ε Abar.toReal) ≤ ENNReal.ofReal Abar.toReal :=
          ENNReal.ofReal_le_ofReal (min_le_right _ _)
      _ = Abar := ENNReal.ofReal_toReal htop

/-- A small attention level on a zero-addictiveness platform gives a value above `u(0,0)`. -/
lemma small_gain (hS : Standing u C) {Abar : ℝ≥0∞} (hAbar : 0 < Abar) :
    ∃ e : ℝ, 0 < e ∧ ENNReal.ofReal e ≤ Abar ∧ u 0 0 < u e 0 - C e := by
  obtain ⟨ε, hε, hm⟩ := eps_mono hS
  obtain ⟨e, he, heε, hfe⟩ := small_feasible hAbar hε
  refine ⟨e, he, hfe, ?_⟩
  have := hm 0 le_rfl (show (0:ℝ) ∈ Icc 0 ε from ⟨le_rfl, hε.le⟩)
    (show e ∈ Icc 0 ε from ⟨he.le, heε⟩) he
  simp only [hS.C_zero, sub_zero] at this
  exact this

/-- At a symmetric duopoly profile `(ds, ds)`, by (3) any feasible choice joining some platform is
worth at most the single-platform value `u(A_1, ds) - C(A_1)`. -/
lemma duo_bound (hS : Standing u C) {Abar : ℝ≥0∞} {ds : ℝ} (hds : 0 ≤ ds) {AK AK1 : ℝ}
    (h2 : IsPerspMax u C Abar 2 ds AK) (h1 : IsPerspMax u C Abar 1 ds AK1)
    (heq : perspObj u C 2 ds AK = perspObj u C 1 ds AK1)
    {d : Fin 2 → ℝ} (hd : ∀ k, d k = ds) {y : Choice 2} (hy : Feasible Abar y)
    (hne : y.1 ≠ ∅) : payoff u C d y ≤ u AK1 ds - C AK1 := by
  have hv : perspObj u C 1 ds AK1 = u AK1 ds - C AK1 := by simp [perspObj]
  have single : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t ≤ Abar → u t ds - C t ≤ u AK1 ds - C AK1 := by
    intro t ht htA
    have := h1.2.2 t ht htA
    simpa [perspObj] using this
  obtain ⟨hnn, hsum⟩ := hy
  rw [sum_fin2] at hsum
  by_cases h0 : (0 : Fin 2) ∈ y.1 <;> by_cases h1' : (1 : Fin 2) ∈ y.1
  · simp only [h0, h1', if_true] at hsum
    have hp : payoff u C d y = u (y.2 0) ds + u (y.2 1) ds - C (y.2 0 + y.2 1) := by
      simp [payoff, hne, sum_fin2, h0, h1', hd]
    rw [hp]
    have a0 := hnn 0 h0
    have a1 := hnn 1 h1'
    have hc := (hS.assumption1.concaveOn_a ds hds).2 (show y.2 0 ∈ Ici (0:ℝ) from a0)
      (show y.2 1 ∈ Ici (0:ℝ) from a1) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num)
    simp only [smul_eq_mul] at hc
    have hm := h2.2.2 (y.2 0 + y.2 1) (by linarith) hsum
    simp only [perspObj] at hm heq hv
    have : (y.2 0 + y.2 1) / 2 = 1/2 * y.2 0 + 1/2 * y.2 1 := by ring
    rw [this] at hm
    linarith
  · simp only [h0, h1', if_true, if_false, add_zero] at hsum
    have hp : payoff u C d y = u (y.2 0) ds - C (y.2 0) := by
      simp [payoff, hne, sum_fin2, h0, h1', hd]
    rw [hp]; exact single _ (hnn 0 h0) hsum
  · simp only [h0, h1', if_true, if_false, zero_add] at hsum
    have hp : payoff u C d y = u (y.2 1) ds - C (y.2 1) := by
      simp [payoff, hne, sum_fin2, h0, h1', hd]
    rw [hp]; exact single _ (hnn 1 h1') hsum
  · exfalso; apply hne
    ext k; fin_cases k <;> simp [h0, h1']

/-- In a duopoly SPE at `(ds, ds)` satisfying (3), the single-platform value is nonnegative:
otherwise the consumer joins nobody and a platform gains by deviating to `0`. -/
lemma duo_participation (hS : Standing u C) {Abar : ℝ≥0∞} (hAbar : 0 < Abar) {ds : ℝ}
    (hds : 0 ≤ ds) {AK AK1 : ℝ}
    (h2 : IsPerspMax u C Abar 2 ds AK) (h1 : IsPerspMax u C Abar 1 ds AK1)
    (heq : perspObj u C 2 ds AK = perspObj u C 1 ds AK1)
    {σ : ConsumerStrategy 2} (hspe : IsSPE u C Abar (fun _ => ds) σ) :
    0 ≤ u AK1 ds - C AK1 := by
  by_contra hv
  rw [not_le] at hv
  have single : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t ≤ Abar → u t ds - C t ≤ u AK1 ds - C AK1 := by
    intro t ht htA
    have := h1.2.2 t ht htA
    simpa [perspObj] using this
  have hopt := hspe.2.1 (fun _ => ds) (fun _ => hds)
  have hcs := CS_nonneg hopt
  have hemp : (σ (fun _ => ds)).1 = ∅ := by
    by_contra hne
    have := duo_bound hS hds h2 h1 heq (fun _ => rfl) hopt.1 hne
    linarith
  have hpp : platformPayoff (0 : Fin 2) (σ (fun _ => ds)) = 0 := by
    simp [platformPayoff, hemp]
  have hdev := hspe.2.2 0 0 le_rfl
  rw [hpp] at hdev
  set d' : Fin 2 → ℝ := Function.update (fun _ => ds) 0 0 with hd'
  have hd0 : d' 0 = 0 := by simp [hd']
  have hd1 : d' 1 = ds := by simp [hd']
  have hopt' := hspe.2.1 d' (by intro k; fin_cases k <;> simp [hd0, hd1, hds])
  obtain ⟨e, he, hfe, hgain⟩ := small_gain hS hAbar
  have hfeas : Feasible Abar (({0} : Finset (Fin 2)), fun _ => e) := ⟨by simp [he.le], by simpa using hfe⟩
  have hge := hopt'.2 _ hfeas
  have hpe : payoff u C d' (({0} : Finset (Fin 2)), fun _ => e) = u e 0 - C e := by
    simp [payoff, hd0]
  rw [hpe] at hge
  have hu00 := hS.assumption1.u_zero_zero_nonneg
  set y := σ d' with hy
  obtain ⟨hnn, hsum⟩ := hopt'.1
  rw [sum_fin2] at hsum
  by_cases h0 : (0 : Fin 2) ∈ y.1 <;> by_cases h1' : (1 : Fin 2) ∈ y.1
  · have hne : y.1 ≠ ∅ := Finset.ne_empty_of_mem h0
    have hz : y.2 0 = 0 := by
      have : platformPayoff (0 : Fin 2) y = y.2 0 := by simp [platformPayoff, h0]
      have := hnn 0 h0
      linarith
    simp only [h0, h1', if_true, hz, zero_add] at hsum
    have hp : payoff u C d' y = u 0 0 + (u (y.2 1) ds - C (y.2 1)) := by
      simp [payoff, hne, sum_fin2, h0, h1', hd0, hd1, hz]; ring
    have := single _ (hnn 1 h1') hsum
    linarith
  · have hne : y.1 ≠ ∅ := Finset.ne_empty_of_mem h0
    have hz : y.2 0 = 0 := by
      have : platformPayoff (0 : Fin 2) y = y.2 0 := by simp [platformPayoff, h0]
      have := hnn 0 h0
      linarith
    have hp : payoff u C d' y = u 0 0 := by
      simp [payoff, hne, sum_fin2, h0, h1', hd0, hz, hS.C_zero]
    linarith
  · have hne : y.1 ≠ ∅ := Finset.ne_empty_of_mem h1'
    simp only [h0, h1', if_true, if_false, zero_add] at hsum
    have hp : payoff u C d' y = u (y.2 1) ds - C (y.2 1) := by
      simp [payoff, hne, sum_fin2, h0, h1', hd1]
    have := single _ (hnn 1 h1') hsum
    linarith
  · have hemp' : y.1 = ∅ := by ext k; fin_cases k <;> simp [h0, h1']
    have hp : payoff u C d' y = 0 := by simp [payoff, hemp']
    linarith

lemma fin1_J {J : Finset (Fin 1)} (h : (0 : Fin 1) ∈ J) : J = {0} :=
  Finset.eq_singleton_iff_unique_mem.2 ⟨h, fun k _ => Subsingleton.elim _ _⟩

lemma upd1 (d : Fin 1 → ℝ) (x : ℝ) : ∀ k, Function.update d 0 x k = x := by
  intro k; rw [Subsingleton.elim k 0]; simp

/-- The monopolist's payoff is at most the cap. -/
lemma mono_pp_le {Abar : ℝ≥0∞} {B : ℝ} (hB : 0 ≤ B) (hAb : Abar = ENNReal.ofReal B)
    {y : Choice 1} (hy : Feasible Abar y) : platformPayoff (0 : Fin 1) y ≤ B := by
  by_cases h0 : (0 : Fin 1) ∈ y.1
  · have hpp : platformPayoff (0 : Fin 1) y = y.2 0 := by simp [platformPayoff, h0]
    rw [hpp]
    have hs := hy.2
    rw [fin1_J h0, hAb] at hs
    simp only [Finset.sum_singleton] at hs
    exact (ENNReal.ofReal_le_ofReal_iff hB).1 hs
  · simp [platformPayoff, h0, hB]

/-- If the unconstrained value `W(x)` is positive then `A(x) ≤ Ā^M`: at the cap `A(x)` a monopoly
equilibrium (it exists) must leave the consumer the positive payoff `W(x)` by the tie-break. -/
lemma le_AbarM (hS : Standing u C) {Aopt : ℝ → ℝ} (hA : IsUncChoice u C Aopt)
    (hex : ∀ Abar : ℝ≥0∞, 0 < Abar →
      ∃ (d : Fin 1 → ℝ) (σ : ConsumerStrategy 1), IsMonopolyEq u C Abar d σ)
    {x : ℝ} (hx : 0 ≤ x) (hW : 0 < u (Aopt x) x - C (Aopt x)) :
    ENNReal.ofReal (Aopt x) ≤ AbarM u C := by
  by_contra h
  rw [not_le] at h
  obtain ⟨s, hs, hslt⟩ := sInf_lt_iff.1 h
  have hApos := Aopt_pos hS hA hx
  obtain ⟨d', σ', hM⟩ := hex (ENNReal.ofReal (Aopt x)) (by simpa using hApos)
  have hcs : consumerSurplus u C d' σ' = 0 := hs _ hslt.le d' σ' hM
  have hopt := hM.1.2.1 (Function.update d' 0 x) (fun k => by rw [upd1]; exact hx)
  obtain ⟨hj, ha, hpay⟩ := mono_choice hS hA hx le_rfl hW (upd1 d' x) hopt
  have hdevpp : platformPayoff (0 : Fin 1) (σ' (Function.update d' 0 x)) = Aopt x := by
    simp [platformPayoff, hj, ha]
  have hdev := hM.1.2.2 0 x hx
  have hle := mono_pp_le (hA x hx).1 rfl (hM.1.2.1 d' hM.1.1).1
  rw [hdevpp] at hdev
  have htie := hM.2 x hx (by rw [hdevpp]; linarith)
  unfold consumerSurplus at htie hcs
  rw [hpay, hcs] at htie
  linarith

/-- Proposition 1, zero part, at the threshold itself: for every cap `Ā ≥ Ā^M` every monopoly
equilibrium leaves the consumer zero. -/
lemma mono_zero (hS : Standing u C) {Aopt : ℝ → ℝ} (hA : IsUncChoice u C Aopt)
    (hex : ∀ Abar : ℝ≥0∞, 0 < Abar →
      ∃ (d : Fin 1 → ℝ) (σ : ConsumerStrategy 1), IsMonopolyEq u C Abar d σ)
    {Abar : ℝ≥0∞} (hAb : AbarM u C ≤ Abar) {dM : Fin 1 → ℝ} {σM : ConsumerStrategy 1}
    (hM : IsMonopolyEq u C Abar dM σM) : consumerSurplus u C dM σM = 0 := by
  have hopt := hM.1.2.1 dM hM.1.1
  have hnn := CS_nonneg hopt
  by_contra hne
  have hc : 0 < payoff u C dM (σM dM) := lt_of_le_of_ne hnn (Ne.symm hne)
  set d0 := dM 0 with hd0def
  have hd0 : 0 ≤ d0 := hM.1.1 0
  have hdk : ∀ k, dM k = d0 := fun k => by rw [Subsingleton.elim k 0]
  set y := σM dM with hydef
  have hyne : y.1 ≠ ∅ := by
    intro h; simp [payoff, h] at hc
  have h0 : (0 : Fin 1) ∈ y.1 := by
    obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.2 hyne
    rwa [Subsingleton.elim k 0] at hk
  have hpy : payoff u C dM y = u (y.2 0) d0 - C (y.2 0) := by
    simp [payoff, fin1_J h0, hdk]
  have hW0 : 0 < u (Aopt d0) d0 - C (Aopt d0) := by
    have := (hA d0 hd0).2 (show y.2 0 ∈ Ici (0:ℝ) from hopt.1.1 0 h0)
    simp only [mem_ofPred_eq] at this
    linarith
  suffices hx : ∃ x : ℝ, 0 ≤ x ∧ 0 < u (Aopt x) x - C (Aopt x) ∧
      ¬ ENNReal.ofReal (Aopt x) ≤ Abar by
    obtain ⟨x, hx, hWx, hnot⟩ := hx
    exact hnot (le_trans (le_AbarM hS hA hex hx hWx) hAb)
  by_cases hcap : ENNReal.ofReal (Aopt d0) ≤ Abar
  · obtain ⟨-, hya, -⟩ := mono_choice hS hA hd0 hcap hW0 hdk hopt
    have hpp : platformPayoff (0 : Fin 1) y = Aopt d0 := by
      simp [platformPayoff, h0, hya]
    -- continuity of `u(A(d0), ·)` at `d0`
    have hcont : ContinuousWithinAt (fun d => u (Aopt d0) d) (Ioi d0) d0 :=
      ((sliceD_contOn hS (hA d0 hd0).1) d0 hd0).mono (fun z hz => le_trans hd0 (le_of_lt hz))
    have hev : ∀ᶠ z in 𝓝[>] d0, C (Aopt d0) < u (Aopt d0) z :=
      hcont.eventually_const_lt (by linarith)
    obtain ⟨x, hxv, hxgt⟩ := (hev.and self_mem_nhdsWithin).exists
    have hxgt' : d0 < x := hxgt
    have hx : 0 ≤ x := le_trans hd0 hxgt'.le
    have hWx : 0 < u (Aopt x) x - C (Aopt x) := by
      have := (hA x hx).2 (show Aopt d0 ∈ Ici (0:ℝ) from (hA d0 hd0).1)
      simp only [mem_ofPred_eq] at this
      linarith
    refine ⟨x, hx, hWx, fun hcx => ?_⟩
    have hopt' := hM.1.2.1 (Function.update dM 0 x) (fun k => by rw [upd1]; exact hx)
    obtain ⟨hj, ha, -⟩ := mono_choice hS hA hx hcx hWx (upd1 dM x) hopt'
    have hdev := hM.1.2.2 0 x hx
    have hdevpp : platformPayoff (0 : Fin 1) (σM (Function.update dM 0 x)) = Aopt x := by
      simp [platformPayoff, hj, ha]
    rw [hdevpp, ← hydef, hpp] at hdev
    have := Aopt_strictMono hS hA hd0 hxgt'
    linarith
  · exact ⟨d0, hd0, hW0, hcap⟩

end AP1P3

open AddictivePlatforms.Compete AP1P3 in
theorem solution (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Aopt : ℝ → ℝ)
    (hS : Standing u C) (hE : UncOptExists u C 2) (hA : IsUncChoice u C Aopt) :
    (∀ Abar : ℝ≥0∞, 0 < Abar → Abar ≤ ENNReal.ofReal (Aopt 0) →
      ∀ (dM : Fin 1 → ℝ) (σM : ConsumerStrategy 1), IsMonopolyEq u C Abar dM σM →
      ∀ (d : Fin 2 → ℝ) (σ : ConsumerStrategy 2), IsSPE u C Abar d σ →
        (∀ k, dM 0 < d k) ∧ consumerSurplus u C d σ < consumerSurplus u C dM σM) ∧
    (∀ Abar : ℝ≥0∞, AbarM u C ≤ Abar →
      ∀ (dM : Fin 1 → ℝ) (σM : ConsumerStrategy 1), IsMonopolyEq u C Abar dM σM →
      ∀ (d : Fin 2 → ℝ) (σ : ConsumerStrategy 2), IsSPE u C Abar d σ →
        (∀ k, d k ≤ dM 0) ∧ consumerSurplus u C dM σM ≤ consumerSurplus u C d σ) := by
  -- the existence pin for two platforms gives the one for a single platform
  have hE1 : UncOptExists u C 1 := by
    intro d hd J hJ
    obtain ⟨k0, hk0⟩ := hJ
    have hJ0 : J = {0} := fin1_J (by rwa [Subsingleton.elim k0 0] at hk0)
    obtain ⟨a, ha, hmax⟩ := hE (fun _ => d 0) (fun _ => hd 0) {0} (by simp)
    refine ⟨fun _ => a 0, fun k _ => ha 0 (by simp), fun a' ha' => ?_⟩
    have h0 : 0 ≤ a' 0 := ha' 0 (by simp [hJ0])
    have := hmax (fun _ => a' 0) (fun _ _ => by simpa using h0)
    simpa [payoff, hJ0] using this
  obtain ⟨hP1a, hP1b, -, -⟩ := proposition_1 u C Aopt hS hE1 hA
  have hex : ∀ Abar : ℝ≥0∞, 0 < Abar →
      ∃ (d : Fin 1 → ℝ) (σ : ConsumerStrategy 1), IsMonopolyEq u C Abar d σ := by
    intro Abar h
    obtain ⟨dP, hdP⟩ := hP1a Abar
    obtain ⟨d, σ, hM, -⟩ := (hP1b Abar h dP hdP).1
    exact ⟨d, σ, hM⟩
  have duo : ∀ Abar : ℝ≥0∞, 0 < Abar → ∀ (d : Fin 2 → ℝ) (σ : ConsumerStrategy 2),
      IsSPE u C Abar d σ → ∃ ds AK AK1 : ℝ, 0 < ds ∧ (∀ k, d k = ds) ∧
        IsPerspMax u C Abar 2 ds AK ∧ IsPerspMax u C Abar 1 ds AK1 ∧
        perspObj u C 2 ds AK = perspObj u C 1 ds AK1 := by
    intro Abar h d σ hspe
    obtain ⟨ds, hpos, ⟨AK, AK1, h2, h1, heq⟩, -, huniq⟩ :=
      proposition_2 u C hS 2 le_rfl hE Abar h
    have e2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    have e1 : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
    rw [e1, e2] at heq
    rw [e2] at h2
    rw [e1] at h1
    exact ⟨ds, AK, AK1, hpos, huniq d σ hspe, h2, h1, heq⟩
  -- a lower bound for the monopoly surplus
  have monoLB : ∀ {Abar : ℝ≥0∞} {dM : Fin 1 → ℝ} {σM : ConsumerStrategy 1},
      IsMonopolyEq u C Abar dM σM → ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t ≤ Abar →
        u t (dM 0) - C t ≤ consumerSurplus u C dM σM := by
    intro Abar dM σM hM t ht htA
    have := (hM.1.2.1 dM hM.1.1).2 (({0} : Finset (Fin 1)), fun _ => t)
      ⟨by simp [ht], by simpa using htA⟩
    simpa [payoff, consumerSurplus] using this
  constructor
  · intro Abar hpos hle dM σM hM d σ hspe
    obtain ⟨dP, hdP⟩ := hP1a Abar
    have hchar := (hP1b Abar hpos dP hdP).2 dM σM hM
    have hdA : dA Aopt Abar = 0 :=
      le_antisymm (sInf_le ⟨0, le_rfl, by simp, hle⟩) zero_le
    rw [hdA, zero_min] at hchar
    have hdM0 : dM 0 = 0 := le_antisymm (ENNReal.ofReal_eq_zero.1 hchar) (hM.1.1 0)
    obtain ⟨ds, AK, AK1, hds, hdk, h2, h1, heq⟩ := duo Abar hpos d σ hspe
    refine ⟨fun k => by rw [hdk k, hdM0]; exact hds, ?_⟩
    have hopt := hspe.2.1 d hspe.1
    unfold consumerSurplus
    by_cases hne : (σ d).1 = ∅
    · have h0 : payoff u C d (σ d) = 0 := by simp [payoff, hne]
      obtain ⟨e, he, hfe, hgain⟩ := small_gain hS hpos
      have := monoLB hM e he.le hfe
      rw [hdM0] at this
      unfold consumerSurplus at this
      linarith [hS.assumption1.u_zero_zero_nonneg]
    · have hb := duo_bound hS hds.le h2 h1 heq hdk hopt.1 hne
      have hanti := hS.assumption1.strictAntiOn_d AK1 h1.1 (show (0:ℝ) ∈ Ici 0 from mem_Ici.2 le_rfl)
        (show ds ∈ Ici 0 from hds.le) hds
      simp only at hanti
      have := monoLB hM AK1 h1.1 h1.2.1
      rw [hdM0] at this
      unfold consumerSurplus at this
      linarith
  · intro Abar hAb dM σM hM d σ hspe
    have hpos : 0 < Abar :=
      lt_of_lt_of_le (ENNReal.ofReal_pos.2 (Aopt_pos hS hA le_rfl))
        (le_trans (le_AbarM hS hA hex le_rfl (W0_pos hS hA)) hAb)
    obtain ⟨ds, AK, AK1, hds, hdk, h2, h1, heq⟩ := duo Abar hpos d σ hspe
    have hz := mono_zero hS hA hex hAb hM
    have hdfun : d = fun _ => ds := funext hdk
    have hpart := duo_participation hS hpos hds.le h2 h1 heq (hdfun ▸ hspe)
    refine ⟨fun k => ?_, ?_⟩
    · rw [hdk k]
      by_contra hlt
      rw [not_le] at hlt
      have hanti := hS.assumption1.strictAntiOn_d AK1 h1.1 (show dM 0 ∈ Ici 0 from hM.1.1 0)
        (show ds ∈ Ici 0 from hds.le) hlt
      simp only at hanti
      have := monoLB hM AK1 h1.1 h1.2.1
      linarith
    · rw [hz]
      exact CS_nonneg (hspe.2.1 d hspe.1)
