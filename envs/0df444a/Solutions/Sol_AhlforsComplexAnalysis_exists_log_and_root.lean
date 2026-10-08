-- Prove2me | solution 1 for AhlforsComplexAnalysis.exists_log_and_root
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-06T11:21:52.175009+00:00
-- url     : https://prove2.me/submissions/4f415aae-b69b-4d0d-8ac0-55b3e6824006

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Defs


open Complex Set Metric Filter Topology

namespace RMA

/-! ## Segments and polygonal paths -/

/-- The point `a + t (b - a)` of the segment from `a` to `b`. -/
noncomputable def sp (a b : ℂ) (t : ℝ) : ℂ := a + (t : ℂ) * (b - a)

/-- The segment `[a, b]`. -/
def sset (a b : ℂ) : Set ℂ := sp a b '' Icc 0 1

/-- `∫_{[a,b]} f(w) dw`. -/
noncomputable def sint (f : ℂ → ℂ) (a b : ℂ) : ℂ :=
  (b - a) * ∫ t in (0:ℝ)..1, f (sp a b t)

/-- Integral along the polygonal path starting at `a` through the vertices `l`. -/
noncomputable def pint (f : ℂ → ℂ) : ℂ → List ℂ → ℂ
  | _, [] => 0
  | a, b :: l => sint f a b + pint f b l

/-- The trace of the polygonal path. -/
def pset : ℂ → List ℂ → Set ℂ
  | a, [] => {a}
  | a, b :: l => sset a b ∪ pset b l

/-- The endpoint of the polygonal path. -/
def pend : ℂ → List ℂ → ℂ
  | a, [] => a
  | _, b :: l => pend b l

lemma continuous_sp (a b : ℂ) : Continuous (sp a b) := by
  unfold sp; fun_prop

lemma sp_zero (a b : ℂ) : sp a b 0 = a := by simp [sp]

lemma sp_one (a b : ℂ) : sp a b 1 = b := by simp [sp]

lemma sp_mem {a b : ℂ} {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : sp a b t ∈ sset a b :=
  ⟨t, ht, rfl⟩

lemma left_mem_sset (a b : ℂ) : a ∈ sset a b := by
  simpa [sp_zero] using sp_mem (a := a) (b := b) (t := 0) ⟨le_rfl, zero_le_one⟩

lemma right_mem_sset (a b : ℂ) : b ∈ sset a b := by
  simpa [sp_one] using sp_mem (a := a) (b := b) (t := 1) ⟨zero_le_one, le_rfl⟩

lemma isCompact_sset (a b : ℂ) : IsCompact (sset a b) :=
  isCompact_Icc.image (continuous_sp a b)

lemma sset_subset_of_convex {s : Set ℂ} (hs : Convex ℝ s) {a b : ℂ} (ha : a ∈ s)
    (hb : b ∈ s) : sset a b ⊆ s := by
  rintro _ ⟨t, ht, rfl⟩
  have := hs.add_smul_sub_mem ha hb ht
  simpa [sp, Complex.real_smul] using this

lemma sset_symm (a b : ℂ) : sset a b = sset b a := by
  ext w; constructor
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
    exact ⟨1 - t, ⟨by linarith, by linarith⟩, by simp [sp]; ring⟩
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
    exact ⟨1 - t, ⟨by linarith, by linarith⟩, by simp [sp]; ring⟩

lemma isCompact_pset : ∀ (a : ℂ) (l : List ℂ), IsCompact (pset a l)
  | a, [] => isCompact_singleton
  | a, b :: l => (isCompact_sset a b).union (isCompact_pset b l)

lemma start_mem_pset : ∀ (a : ℂ) (l : List ℂ), a ∈ pset a l
  | a, [] => rfl
  | a, b :: l => Or.inl (left_mem_sset a b)

lemma pend_mem_pset : ∀ (a : ℂ) (l : List ℂ), pend a l ∈ pset a l
  | a, [] => rfl
  | a, b :: l => Or.inr (pend_mem_pset b l)

lemma sset_subset_pset (a b : ℂ) (l : List ℂ) : sset a b ⊆ pset a (b :: l) :=
  subset_union_left

lemma pset_tail_subset (a b : ℂ) (l : List ℂ) : pset b l ⊆ pset a (b :: l) :=
  subset_union_right

/-! ## Basic properties of segment integrals -/

lemma intervalIntegrable_comp_sp {f : ℂ → ℂ} {a b : ℂ} (hf : ContinuousOn f (sset a b)) :
    IntervalIntegrable (fun t : ℝ => f (sp a b t)) MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le zero_le_one]
  exact hf.comp (continuous_sp a b).continuousOn (fun t ht => sp_mem ht)

/-- Fundamental theorem of calculus along a segment. -/
lemma sint_eq_sub {f F : ℂ → ℂ} {a b : ℂ} (hF : ∀ w ∈ sset a b, HasDerivAt F (f w) w)
    (hf : ContinuousOn f (sset a b)) : sint f a b = F b - F a := by
  have hd : ∀ t ∈ uIcc (0:ℝ) 1, HasDerivAt (fun t : ℝ => F (sp a b t))
      (f (sp a b t) * (b - a)) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have h1 : HasDerivAt (fun t : ℝ => sp a b t) (b - a) t := by
      have := ((hasDerivAt_id (t : ℂ)).comp_ofReal (z := t)).mul_const (b - a)
      simpa [sp] using this.const_add a
    exact (hF _ (sp_mem ht)).comp t h1
  have hint : IntervalIntegrable (fun t : ℝ => f (sp a b t) * (b - a)) MeasureTheory.volume 0 1 :=
    (intervalIntegrable_comp_sp hf).mul_const _
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [sp_one, sp_zero] at this
  rw [sint, ← this, intervalIntegral.integral_mul_const, mul_comm]

lemma sint_congr {f g : ℂ → ℂ} {a b : ℂ} (h : EqOn f g (sset a b)) :
    sint f a b = sint g a b := by
  unfold sint
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  exact h (sp_mem ht)

lemma sint_sub {f g : ℂ → ℂ} {a b : ℂ} (hf : ContinuousOn f (sset a b))
    (hg : ContinuousOn g (sset a b)) :
    sint (fun w => f w - g w) a b = sint f a b - sint g a b := by
  unfold sint
  rw [intervalIntegral.integral_sub (intervalIntegrable_comp_sp hf)
    (intervalIntegrable_comp_sp hg), mul_sub]

lemma sint_const_mul (c : ℂ) (f : ℂ → ℂ) (a b : ℂ) :
    sint (fun w => c * f w) a b = c * sint f a b := by
  unfold sint
  rw [intervalIntegral.integral_const_mul]; ring

lemma norm_sint_le {f : ℂ → ℂ} {a b : ℂ} {C : ℝ} (h : ∀ w ∈ sset a b, ‖f w‖ ≤ C) :
    ‖sint f a b‖ ≤ ‖b - a‖ * C := by
  unfold sint
  rw [norm_mul]
  gcongr
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (f := fun t : ℝ => f (sp a b t)) (C := C) (fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      exact h _ (sp_mem ⟨ht.1.le, ht.2⟩))
  simpa using this

lemma sint_symm (f : ℂ → ℂ) (a b : ℂ) : sint f b a = - sint f a b := by
  unfold sint
  have h1 : (∫ t in (0:ℝ)..1, f (sp b a t)) = ∫ t in (0:ℝ)..1, f (sp a b t) := by
    have := intervalIntegral.integral_comp_sub_left (fun t : ℝ => f (sp a b t)) (a := (0:ℝ))
      (b := 1) (d := 1)
    simp only [sub_zero, sub_self] at this
    rw [← this]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [sp]; push_cast; ring_nf
  rw [h1]; ring

/-! ## Polygonal integrals -/

lemma pint_eq_sub {f F : ℂ → ℂ} : ∀ {a : ℂ} {l : List ℂ},
    (∀ w ∈ pset a l, HasDerivAt F (f w) w) → ContinuousOn f (pset a l) →
    pint f a l = F (pend a l) - F a
  | a, [], _, _ => by simp [pint, pend]
  | a, b :: l, hF, hf => by
    rw [pint, pend, sint_eq_sub (fun w hw => hF w (sset_subset_pset a b l hw))
      (hf.mono (sset_subset_pset a b l)),
      pint_eq_sub (fun w hw => hF w (pset_tail_subset a b l hw))
        (hf.mono (pset_tail_subset a b l))]
    ring

/-- A polygonal loop integral of a function with a primitive vanishes. -/
lemma pint_loop_eq_zero {f F : ℂ → ℂ} {a : ℂ} {l : List ℂ} (hl : pend a l = a)
    (hF : ∀ w ∈ pset a l, HasDerivAt F (f w) w) (hf : ContinuousOn f (pset a l)) :
    pint f a l = 0 := by
  rw [pint_eq_sub hF hf, hl, sub_self]

lemma pint_congr {f g : ℂ → ℂ} : ∀ {a : ℂ} {l : List ℂ}, EqOn f g (pset a l) →
    pint f a l = pint g a l
  | a, [], _ => rfl
  | a, b :: l, h => by
    rw [pint, pint, sint_congr (h.mono (sset_subset_pset a b l)),
      pint_congr (h.mono (pset_tail_subset a b l))]

lemma pint_sub {f g : ℂ → ℂ} : ∀ {a : ℂ} {l : List ℂ}, ContinuousOn f (pset a l) →
    ContinuousOn g (pset a l) → pint (fun w => f w - g w) a l = pint f a l - pint g a l
  | a, [], _, _ => by simp [pint]
  | a, b :: l, hf, hg => by
    rw [pint, pint, pint, sint_sub (hf.mono (sset_subset_pset a b l))
      (hg.mono (sset_subset_pset a b l)),
      pint_sub (hf.mono (pset_tail_subset a b l)) (hg.mono (pset_tail_subset a b l))]
    ring

lemma pint_const_mul (c : ℂ) (f : ℂ → ℂ) : ∀ (a : ℂ) (l : List ℂ),
    pint (fun w => c * f w) a l = c * pint f a l
  | a, [] => by simp [pint]
  | a, b :: l => by rw [pint, pint, sint_const_mul, pint_const_mul c f b l]; ring

/-- Total length of a polygonal path. -/
noncomputable def plen : ℂ → List ℂ → ℝ
  | _, [] => 0
  | a, b :: l => ‖b - a‖ + plen b l

lemma norm_pint_le {f : ℂ → ℂ} {C : ℝ} : ∀ {a : ℂ} {l : List ℂ},
    (∀ w ∈ pset a l, ‖f w‖ ≤ C) → ‖pint f a l‖ ≤ plen a l * C
  | a, [], _ => by simp [pint, plen]
  | a, b :: l, h => by
    rw [pint, plen, add_mul]
    exact (norm_add_le _ _).trans (add_le_add
      (norm_sint_le fun w hw => h w (sset_subset_pset a b l hw))
      (norm_pint_le fun w hw => h w (pset_tail_subset a b l hw)))

lemma pend_append : ∀ (a : ℂ) (l₁ l₂ : List ℂ), pend a (l₁ ++ l₂) = pend (pend a l₁) l₂
  | a, [], l₂ => rfl
  | a, b :: l₁, l₂ => pend_append b l₁ l₂

lemma pint_append (f : ℂ → ℂ) : ∀ (a : ℂ) (l₁ l₂ : List ℂ),
    pint f a (l₁ ++ l₂) = pint f a l₁ + pint f (pend a l₁) l₂
  | a, [], l₂ => by simp [pint, pend]
  | a, b :: l₁, l₂ => by
    rw [List.cons_append, pint, pint, pint_append f b l₁ l₂, pend]; ring

lemma pset_append : ∀ (a : ℂ) (l₁ l₂ : List ℂ),
    pset a (l₁ ++ l₂) = pset a l₁ ∪ pset (pend a l₁) l₂
  | a, [], l₂ => by
    simp only [List.nil_append, pset, pend]
    exact (union_eq_right.mpr (singleton_subset_iff.mpr (start_mem_pset a l₂))).symm
  | a, b :: l₁, l₂ => by
    rw [List.cons_append, pset, pset, pset_append b l₁ l₂, pend, union_assoc]

/-- Vertices of the reversed path (which starts at `pend a l`). -/
def revl (a : ℂ) (l : List ℂ) : List ℂ := ((a :: l).reverse).tail

lemma revl_cons (a b : ℂ) (l : List ℂ) : revl a (b :: l) = revl b l ++ [a] := by
  unfold revl
  rw [List.reverse_cons (a := a), List.tail_append_of_ne_nil]
  simp

lemma pend_revl : ∀ (a : ℂ) (l : List ℂ), pend (pend a l) (revl a l) = a
  | a, [] => rfl
  | a, b :: l => by
    rw [revl_cons, pend, pend_append, pend_revl b l]; rfl

lemma pint_revl (f : ℂ → ℂ) : ∀ (a : ℂ) (l : List ℂ),
    pint f (pend a l) (revl a l) = - pint f a l
  | a, [] => by simp [pint, revl, pend]
  | a, b :: l => by
    rw [revl_cons, pend, pint_append, pint_revl f b l, pend_revl, pint, pint, pint,
      sint_symm]
    simp

lemma pset_revl : ∀ (a : ℂ) (l : List ℂ), pset (pend a l) (revl a l) = pset a l
  | a, [] => by simp [pset, revl, pend]
  | a, b :: l => by
    rw [revl_cons, pend, pset_append, pset_revl b l, pend_revl]
    simp only [pset]
    rw [sset_symm b a]
    have ha : a ∈ sset a b := left_mem_sset a b
    ext w
    simp only [mem_union, mem_singleton_iff]
    constructor
    · rintro (h | h | h)
      · exact Or.inr h
      · exact Or.inl h
      · exact Or.inl (h ▸ ha)
    · rintro (h | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h

end RMA


open Complex Set Metric Filter Topology

namespace RMA

/-! ## Parametric integrals and Morera's theorem -/

/-- Continuity of a parametric interval integral with an integrand continuous on
`T × [c, d]`. -/
lemma param_cont {X : Type*} [TopologicalSpace X] {T : Set X} {G : X → ℝ → ℂ} {c d : ℝ}
    (hG : ContinuousOn (Function.uncurry G) (T ×ˢ uIcc c d)) :
    ContinuousOn (fun x => ∫ s in c..d, G x s) T := by
  rw [continuousOn_iff_continuous_domRestrict]
  set G' : T → ℝ → ℂ := fun x s => G x (projIcc (c ⊓ d) (c ⊔ d) inf_le_sup s) with hG'
  have hc : Continuous (Function.uncurry G') := by
    have h1 : Continuous fun p : T × ℝ => ((p.1 : X), ((projIcc (c ⊓ d) (c ⊔ d) inf_le_sup p.2 : ℝ))) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd))
    refine hG.comp_continuous h1 (fun p => ⟨p.1.2, ?_⟩)
    exact (projIcc (c ⊓ d) (c ⊔ d) inf_le_sup p.2).2
  have := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := MeasureTheory.volume) hc c d
  convert this using 1
  funext x
  apply intervalIntegral.integral_congr
  intro s hs
  simp only [hG', projIcc_of_mem _ hs]

lemma swap_ii {G : ℝ → ℝ → ℂ} {c d e f : ℝ}
    (hG : ContinuousOn (Function.uncurry G) (uIcc c d ×ˢ uIcc e f)) :
    ∫ x in c..d, ∫ t in e..f, G x t = ∫ t in e..f, ∫ x in c..d, G x t := by
  apply MeasureTheory.intervalIntegral_intervalIntegral_swap
  exact (hG.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
    (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)

/-- Morera: a segment integral of a family of holomorphic functions, continuous in both
variables, is holomorphic in the parameter. -/
lemma diffOn_sint_param {U : Set ℂ} (hU : IsOpen U) {Φ : ℂ → ℂ → ℂ} {a b : ℂ}
    (hc : ContinuousOn (Function.uncurry Φ) (U ×ˢ sset a b))
    (hd : ∀ w ∈ sset a b, DifferentiableOn ℂ (fun z => Φ z w) U) :
    DifferentiableOn ℂ (fun z => sint (Φ z) a b) U := by
  set J : ℂ → ℂ := fun z => ∫ t in (0:ℝ)..1, Φ z (sp a b t) with hJ
  suffices h : DifferentiableOn ℂ J U by
    exact (h.const_mul (b - a)).congr (fun z _ => rfl)
  -- joint continuity along lines
  have hcomp : ∀ {S : Set ℂ} (_ : S ⊆ U), ContinuousOn (fun p : ℂ × ℝ => Φ p.1 (sp a b p.2))
      (S ×ˢ uIcc 0 1) := by
    intro S hS
    refine hc.comp ((continuous_fst.prodMk ((continuous_sp a b).comp continuous_snd)).continuousOn)
      ?_
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    rw [uIcc_of_le zero_le_one] at ht
    exact ⟨hS hz, sp_mem ht⟩
  rw [← isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU]
  refine ⟨?_, param_cont (G := fun z t => Φ z (sp a b t)) (hcomp subset_rfl)⟩
  intro z w hR
  rw [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq]
  -- a line inside the rectangle
  have hline : ∀ (L : ℝ → ℂ) (c d : ℝ), Continuous L → (∀ x ∈ uIcc c d, L x ∈ U) →
      (∫ x in c..d, J (L x)) = ∫ t in (0:ℝ)..1, ∫ x in c..d, Φ (L x) (sp a b t) ∧
      ContinuousOn (fun t => ∫ x in c..d, Φ (L x) (sp a b t)) (uIcc 0 1) := by
    intro L c d hL hLU
    have hj : ContinuousOn (Function.uncurry fun x t => Φ (L x) (sp a b t))
        (uIcc c d ×ˢ uIcc 0 1) := by
      have := (hcomp (S := U) subset_rfl).comp
        ((hL.comp continuous_fst).prodMk continuous_snd).continuousOn
        (fun p hp => ⟨hLU _ (mem_prod.1 hp).1, (mem_prod.1 hp).2⟩)
      exact this
    refine ⟨swap_ii hj, ?_⟩
    have hj' : ContinuousOn (Function.uncurry fun t x => Φ (L x) (sp a b t))
        (uIcc 0 1 ×ˢ uIcc c d) := by
      have := hj.comp (continuous_snd.prodMk continuous_fst).continuousOn
        (fun p hp => ⟨(mem_prod.1 hp).2, (mem_prod.1 hp).1⟩)
      exact this
    exact param_cont hj'
  have hRe : ∀ x ∈ uIcc z.re w.re, ∀ k ∈ uIcc z.im w.im, (x : ℂ) + k * I ∈ U := by
    intro x hx k hk
    apply hR
    rw [Rectangle, mem_reProdIm]
    simp [hx, hk]
  have hIm : ∀ y ∈ uIcc z.im w.im, ∀ k ∈ uIcc z.re w.re, (k : ℂ) + y * I ∈ U := by
    intro y hy k hk
    apply hR
    rw [Rectangle, mem_reProdIm]
    simp [hy, hk]
  obtain ⟨e1, c1⟩ := hline (fun x : ℝ => (x : ℂ) + z.im * I) z.re w.re (by fun_prop)
    (fun x hx => hRe x hx _ left_mem_uIcc)
  obtain ⟨e2, c2⟩ := hline (fun x : ℝ => (x : ℂ) + w.im * I) z.re w.re (by fun_prop)
    (fun x hx => hRe x hx _ right_mem_uIcc)
  obtain ⟨e3, c3⟩ := hline (fun y : ℝ => (w.re : ℂ) + y * I) z.im w.im (by fun_prop)
    (fun y hy => hIm y hy _ right_mem_uIcc)
  obtain ⟨e4, c4⟩ := hline (fun y : ℝ => (z.re : ℂ) + y * I) z.im w.im (by fun_prop)
    (fun y hy => hIm y hy _ left_mem_uIcc)
  simp only [hJ] at e1 e2 e3 e4 ⊢
  simp only [smul_eq_mul]
  rw [e1, e2, e3, e4]
  have i1 := c1.intervalIntegrable (μ := MeasureTheory.volume)
  have i2 := c2.intervalIntegrable (μ := MeasureTheory.volume)
  have i3 := c3.intervalIntegrable (μ := MeasureTheory.volume)
  have i4 := c4.intervalIntegrable (μ := MeasureTheory.volume)
  rw [← intervalIntegral.integral_sub i1 i2, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (i1.sub i2)
      (i3.const_mul I), ← intervalIntegral.integral_sub ((i1.sub i2).add (i3.const_mul I))
      (i4.const_mul I)]
  refine (intervalIntegral.integral_congr (g := fun _ => (0:ℂ)) ?_).trans (by simp)
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  have hcons := (hd _ (sp_mem ht)).isConservativeOn z w hR
  rw [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq] at hcons
  simp only [smul_eq_mul] at hcons
  simpa using hcons

lemma diffOn_pint_param {U : Set ℂ} (hU : IsOpen U) {Φ : ℂ → ℂ → ℂ} : ∀ {a : ℂ} {l : List ℂ},
    ContinuousOn (Function.uncurry Φ) (U ×ˢ pset a l) →
    (∀ w ∈ pset a l, DifferentiableOn ℂ (fun z => Φ z w) U) →
    DifferentiableOn ℂ (fun z => pint (Φ z) a l) U
  | a, [], _, _ => by simp only [pint]; exact differentiableOn_const 0
  | a, b :: l, hc, hd => by
    simp only [pint]
    exact (diffOn_sint_param hU (hc.mono (prod_mono subset_rfl (sset_subset_pset a b l)))
      (fun w hw => hd w (sset_subset_pset a b l hw))).add
      (diffOn_pint_param hU (hc.mono (prod_mono subset_rfl (pset_tail_subset a b l)))
      (fun w hw => hd w (pset_tail_subset a b l hw)))

end RMA


open Complex Set Metric Filter Topology

namespace RMA

/-! ## Winding numbers of polygonal loops -/

/-- `∫_γ dw / (w - z)` (the winding number times `2πi`). -/
noncomputable def wn (a : ℂ) (l : List ℂ) (z : ℂ) : ℂ := pint (fun w => (w - z)⁻¹) a l

lemma continuousOn_inv_sub {S : Set ℂ} {z : ℂ} (hz : z ∉ S) :
    ContinuousOn (fun w => (w - z)⁻¹) S := by
  apply ContinuousOn.inv₀ (by fun_prop)
  intro w hw h
  exact hz (by rw [sub_eq_zero] at h; exact h ▸ hw)

/-- The winding number is locally constant off the loop. -/
lemma wn_eq_of_near {a : ℂ} {l : List ℂ} (hl : pend a l = a) {z z' : ℂ}
    (hz : z ∉ pset a l) (hzz : ‖z' - z‖ < infDist z (pset a l) / 4) :
    wn a l z' = wn a l z := by
  set δ := infDist z (pset a l) with hδ
  have hδpos : 0 < δ := ((isCompact_pset a l).isClosed.notMem_iff_infDist_pos
    ⟨a, start_mem_pset a l⟩).1 hz
  have hfar : ∀ w ∈ pset a l, δ ≤ ‖w - z‖ := by
    intro w hw
    have := infDist_le_dist_of_mem (x := z) hw
    rwa [dist_comm, dist_eq_norm] at this
  have hz' : z' ∉ pset a l := by
    intro h
    have := hfar z' h
    linarith [norm_nonneg (z' - z)]
  have key : pint (fun w => (w - z')⁻¹ - (w - z)⁻¹) a l = 0 := by
    apply pint_loop_eq_zero hl (F := fun w => log ((w - z') / (w - z)))
    · intro w hw
      have hwz : w - z ≠ 0 := by
        intro h; have := hfar w hw; rw [h, norm_zero] at this; linarith
      have hwz' : w - z' ≠ 0 := by
        intro h; exact hz' (by rw [sub_eq_zero] at h; exact h ▸ hw)
      have hq : (w - z') / (w - z) ∈ slitPlane := by
        have : (w - z') / (w - z) = 1 + (z - z') / (w - z) := by field_simp; ring
        rw [this]
        apply mem_slitPlane_of_norm_lt_one
        rw [norm_div, div_lt_one (norm_pos_iff.2 hwz)]
        have := hfar w hw
        have h2 : ‖z - z'‖ = ‖z' - z‖ := norm_sub_rev _ _
        linarith
      have hd : HasDerivAt (fun w => (w - z') / (w - z))
          ((1 * (w - z) - (w - z') * 1) / (w - z) ^ 2) w :=
        ((hasDerivAt_id w).sub_const z').div ((hasDerivAt_id w).sub_const z) hwz
      convert hd.clog hq using 1
      field_simp
    · exact (continuousOn_inv_sub hz').sub (continuousOn_inv_sub hz)
  rw [pint_sub (continuousOn_inv_sub hz') (continuousOn_inv_sub hz), sub_eq_zero] at key
  exact key

/-- The winding number vanishes far away from the loop. -/
lemma wn_eq_zero_of_far {a : ℂ} {l : List ℂ} (hl : pend a l = a) {R : ℝ}
    (hR : ∀ w ∈ pset a l, ‖w‖ ≤ R) {z : ℂ} (hz : 2 * R < ‖z‖) : wn a l z = 0 := by
  have hR0 : 0 ≤ R := (norm_nonneg a).trans (hR a (start_mem_pset a l))
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith
  have hzn : z ∉ pset a l := fun h => by linarith [hR z h]
  apply pint_loop_eq_zero hl (F := fun w => log (1 + (-w / z)))
  · intro w hw
    have hwz : w - z ≠ 0 := by
      intro h; exact hzn (by rw [sub_eq_zero] at h; exact h ▸ hw)
    have hq : 1 + (-w / z) ∈ slitPlane := by
      apply mem_slitPlane_of_norm_lt_one
      rw [norm_div, norm_neg, div_lt_one (norm_pos_iff.2 hz0)]
      linarith [hR w hw]
    have hd : HasDerivAt (fun w => 1 + (-w / z)) (-1 / z) w := by
      have := ((hasDerivAt_id w).neg.div_const z).const_add 1
      simpa using this
    convert hd.clog hq using 1
    have h1 : 1 + -w / z ≠ 0 := slitPlane_ne_zero hq
    field_simp
    ring_nf
    have h2 : -w + z ≠ 0 := by intro h; apply hwz; linear_combination -h
    field_simp
    try ring
  · exact continuousOn_inv_sub hzn

/-- If the complement of `Ω` in the Riemann sphere is connected, the winding number of a
polygonal loop in `Ω` vanishes at every point outside `Ω`. -/
lemma wn_eq_zero_of_not_mem {Ω : Set ℂ}
    (hK : IsConnected (((↑) : ℂ → OnePoint ℂ) '' Ω)ᶜ) {a : ℂ} {l : List ℂ}
    (hl : pend a l = a) (hlΩ : pset a l ⊆ Ω) {z : ℂ} (hz : z ∉ Ω) : wn a l z = 0 := by
  obtain ⟨R, hR⟩ : ∃ R, ∀ w ∈ pset a l, ‖w‖ ≤ R := by
    obtain ⟨R, hR⟩ := (isCompact_pset a l).isBounded.subset_closedBall 0
    exact ⟨R, fun w hw => by simpa using hR hw⟩
  set K := (((↑) : ℂ → OnePoint ℂ) '' Ω)ᶜ with hKdef
  set N : OnePoint ℂ → ℂ := fun x => x.elim 0 (wn a l) with hN
  have hloc : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, N y = N x := by
    intro x hx
    induction x using OnePoint.rec with
    | infty =>
      rw [OnePoint.nhds_infty_eq, Filter.coclosedCompact_eq_cocompact]
      refine Filter.eventually_sup.2 ⟨?_, Filter.eventually_pure.2 rfl⟩
      rw [Filter.eventually_map]
      filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop (2 * R)] with w hw
      exact wn_eq_zero_of_far hl hR hw
    | coe z =>
      have hzΩ : z ∉ Ω := fun h => hx ⟨z, h, rfl⟩
      have hzl : z ∉ pset a l := fun h => hzΩ (hlΩ h)
      have hδ : 0 < infDist z (pset a l) := ((isCompact_pset a l).isClosed.notMem_iff_infDist_pos
        ⟨a, start_mem_pset a l⟩).1 hzl
      rw [OnePoint.nhds_coe_eq, Filter.eventually_map]
      filter_upwards [ball_mem_nhds z (by positivity : 0 < infDist z (pset a l) / 4)] with w hw
      rw [mem_ball, dist_eq_norm] at hw
      exact wn_eq_of_near hl hzl hw
  haveI : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hK.isPreconnected
  have hlc : IsLocallyConstant (fun x : K => N x) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    rw [nhds_subtype_eq_comap]
    exact ((hloc x x.2).comap _)
  have hinf : (OnePoint.infty : OnePoint ℂ) ∈ K := by
    rintro ⟨w, _, hw⟩
    exact OnePoint.coe_ne_infty w hw
  have hzK : ((z : ℂ) : OnePoint ℂ) ∈ K := by
    rintro ⟨w, hw, hwz⟩
    exact hz (OnePoint.coe_injective hwz ▸ hw)
  have := hlc.apply_eq_of_preconnectedSpace ⟨_, hzK⟩ ⟨_, hinf⟩
  simpa [hN] using this

end RMA


open Complex Set Metric Filter Topology

namespace RMA

/-! ## Dixon's proof of Cauchy's theorem for polygonal loops -/

lemma dslope_symm (g : ℂ → ℂ) (z w : ℂ) : dslope g z w = dslope g w z := by
  rcases eq_or_ne z w with rfl | h
  · rfl
  · rw [dslope_of_ne _ h.symm, dslope_of_ne _ h, slope_comm]

/-- `dslope g z w = ∫₀¹ g'(z + t(w - z)) dt` when the segment lies in a domain of
holomorphy. -/
lemma dslope_eq_integral {g : ℂ → ℂ} {B : Set ℂ} (hB : IsOpen B) (hBc : Convex ℝ B)
    (hg : DifferentiableOn ℂ g B) {z w : ℂ} (hz : z ∈ B) (hw : w ∈ B) :
    dslope g z w = ∫ t in (0:ℝ)..1, deriv g (sp z w t) := by
  rcases eq_or_ne w z with rfl | hne
  · simp [sp]
  have hs : sset z w ⊆ B := sset_subset_of_convex hBc hz hw
  have hftc := sint_eq_sub (f := deriv g) (F := g) (a := z) (b := w)
    (fun u hu => ((hg u (hs hu)).differentiableAt (hB.mem_nhds (hs hu))).hasDerivAt)
    ((hg.deriv hB).continuousOn.mono hs)
  rw [sint] at hftc
  rw [dslope_of_ne _ hne, slope_def_field]
  have hwz : w - z ≠ 0 := sub_ne_zero.2 hne
  rw [← hftc]
  field_simp

lemma continuousOn_dslope {g : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) :
    ContinuousOn (fun p : ℂ × ℂ => dslope g p.1 p.2) (Ω ×ˢ Ω) := by
  rintro ⟨z₀, w₀⟩ ⟨hz₀, hw₀⟩
  apply ContinuousAt.continuousWithinAt
  have hgc : ContinuousOn g Ω := hg.continuousOn
  rcases eq_or_ne z₀ w₀ with rfl | hne
  · obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 hΩ z₀ hz₀
    have hcont : ContinuousOn (fun p : ℂ × ℂ => ∫ t in (0:ℝ)..1, deriv g (sp p.1 p.2 t))
        (ball z₀ r ×ˢ ball z₀ r) := by
      apply param_cont (G := fun (p : ℂ × ℂ) t => deriv g (sp p.1 p.2 t))
      have hd : ContinuousOn (deriv g) (ball z₀ r) :=
        ((hg.mono hrΩ).deriv isOpen_ball).continuousOn
      refine hd.comp (by unfold sp; fun_prop) ?_
      rintro ⟨⟨z, w⟩, t⟩ ⟨⟨hz, hw⟩, ht⟩
      rw [uIcc_of_le zero_le_one] at ht
      exact sset_subset_of_convex (convex_ball z₀ r) hz hw (sp_mem ht)
    have hmem : ball z₀ r ×ˢ ball z₀ r ∈ 𝓝 (z₀, z₀) :=
      prod_mem_nhds (ball_mem_nhds z₀ hr) (ball_mem_nhds z₀ hr)
    refine ((hcont (z₀, z₀) (mem_of_mem_nhds hmem)).continuousAt hmem).congr ?_
    filter_upwards [hmem] with p hp
    exact (dslope_eq_integral isOpen_ball (convex_ball z₀ r) (hg.mono hrΩ) hp.1 hp.2).symm
  · have hev : ∀ᶠ p : ℂ × ℂ in 𝓝 (z₀, w₀), dslope g p.1 p.2 = (p.2 - p.1)⁻¹ * (g p.2 - g p.1) := by
      have : {p : ℂ × ℂ | p.2 ≠ p.1} ∈ 𝓝 (z₀, w₀) :=
        (isOpen_ne_fun continuous_snd continuous_fst).mem_nhds hne.symm
      filter_upwards [this] with p hp
      rw [dslope_of_ne _ hp, slope_def_field, div_eq_inv_mul]
    have hc : ContinuousAt (fun p : ℂ × ℂ => (p.2 - p.1)⁻¹ * (g p.2 - g p.1)) (z₀, w₀) := by
      have h1 : ContinuousAt (fun p : ℂ × ℂ => g p.2) (z₀, w₀) :=
        (hgc.continuousAt (hΩ.mem_nhds hw₀)).comp continuous_snd.continuousAt
      have h2 : ContinuousAt (fun p : ℂ × ℂ => g p.1) (z₀, w₀) :=
        (hgc.continuousAt (hΩ.mem_nhds hz₀)).comp continuous_fst.continuousAt
      exact ((continuous_snd.sub continuous_fst).continuousAt.inv₀
        (sub_ne_zero.2 hne.symm)).mul (h1.sub h2)
    exact hc.congr (hev.mono fun p hp => hp.symm)

section Dixon

variable {Ω : Set ℂ} (hΩ : IsOpen Ω) (hK : IsConnected (((↑) : ℂ → OnePoint ℂ) '' Ω)ᶜ)
  {a : ℂ} {l : List ℂ} (hl : pend a l = a) (hlΩ : pset a l ⊆ Ω)
  {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g Ω)

include hΩ hK hl hlΩ hg in
/-- Dixon: `∫_γ (g(w) - g(z))/(w - z) dw = 0` for every `z ∈ Ω`. -/
lemma pint_dslope_eq_zero {z : ℂ} (hz : z ∈ Ω) : pint (dslope g z) a l = 0 := by
  classical
  set P := pset a l with hP
  have hPc : IsCompact P := isCompact_pset a l
  set h : ℂ → ℂ := fun z => pint (dslope g z) a l with hh
  set h₁ : ℂ → ℂ := fun z => pint (fun w => g w * (w - z)⁻¹) a l with hh₁
  have hgc : ContinuousOn g Ω := hg.continuousOn
  -- `h` is holomorphic on `Ω`
  have hhd : DifferentiableOn ℂ h Ω := by
    apply diffOn_pint_param hΩ
    · exact (continuousOn_dslope hΩ hg).mono (prod_mono subset_rfl hlΩ)
    · intro w hw
      have : (fun z => dslope g z w) = dslope g w := funext fun z => dslope_symm g z w
      rw [this]
      exact (differentiableOn_dslope (hΩ.mem_nhds (hlΩ hw))).2 hg
  -- `h₁` is holomorphic off the loop
  have hh₁d : DifferentiableOn ℂ h₁ Pᶜ := by
    apply diffOn_pint_param hPc.isClosed.isOpen_compl
    · rintro ⟨z, w⟩ ⟨hz, hw⟩
      apply ContinuousWithinAt.mul
      · exact ((hgc.mono hlΩ) w hw).comp continuousWithinAt_snd (fun p hp => hp.2)
      · apply ContinuousWithinAt.inv₀ (continuous_snd.sub continuous_fst).continuousWithinAt
        intro h0; apply hz; simp only [Pi.sub_apply, sub_eq_zero] at h0
        simp only at h0 hw ⊢; rw [h0] at hw; exact hw
    · intro w hw
      apply DifferentiableOn.const_mul
      apply DifferentiableOn.inv (by fun_prop)
      intro z hz h0; apply hz; rw [sub_eq_zero] at h0; simpa [← h0] using hw
  -- relation between `h` and `h₁`
  have hrel : ∀ z, z ∉ P → h z = h₁ z - g z * wn a l z := by
    intro z hzP
    simp only [hh, hh₁, wn]
    rw [← pint_const_mul, ← pint_sub]
    · apply pint_congr
      intro w hw
      have hne : w ≠ z := fun h0 => hzP (h0 ▸ hw)
      rw [dslope_of_ne _ hne, slope_def_field]
      have : w - z ≠ 0 := sub_ne_zero.2 hne
      field_simp
    · exact ContinuousOn.mul (hgc.mono hlΩ) (continuousOn_inv_sub hzP)
    · exact continuousOn_const.mul (continuousOn_inv_sub hzP)
  -- the glued entire function
  set H : ℂ → ℂ := fun z => if z ∈ Ω then h z else h₁ z with hH
  have hHd : Differentiable ℂ H := by
    intro z
    by_cases hzΩ : z ∈ Ω
    · apply ((hhd z hzΩ).differentiableAt (hΩ.mem_nhds hzΩ)).congr_of_eventuallyEq
      filter_upwards [hΩ.mem_nhds hzΩ] with w hw
      simp [hH, hw]
    · have hzP : z ∉ P := fun h0 => hzΩ (hlΩ h0)
      have hδ : 0 < infDist z P := (hPc.isClosed.notMem_iff_infDist_pos
        ⟨a, start_mem_pset a l⟩).1 hzP
      have hball : ∀ w ∈ ball z (infDist z P / 4), w ∉ P ∧ wn a l w = 0 := by
        intro w hw
        rw [mem_ball, dist_eq_norm] at hw
        refine ⟨fun hwP => ?_, ?_⟩
        · have := infDist_le_dist_of_mem (x := z) hwP
          rw [dist_comm, dist_eq_norm] at this
          linarith
        · rw [wn_eq_of_near hl hzP hw]
          exact wn_eq_zero_of_not_mem hK hl hlΩ hzΩ
      have hmem : ball z (infDist z P / 4) ∈ 𝓝 z := ball_mem_nhds z (by positivity)
      apply ((hh₁d z hzP).differentiableAt (hPc.isClosed.isOpen_compl.mem_nhds hzP)).congr_of_eventuallyEq
      filter_upwards [hmem] with w hw
      obtain ⟨hwP, hw0⟩ := hball w hw
      by_cases hwΩ : w ∈ Ω
      · simp [hH, hwΩ, hrel w hwP, hw0]
      · simp [hH, hwΩ]
  -- bounds
  obtain ⟨R, hR⟩ : ∃ R, ∀ w ∈ P, ‖w‖ ≤ R := by
    obtain ⟨R, hR⟩ := hPc.isBounded.subset_closedBall 0
    exact ⟨R, fun w hw => by simpa using hR hw⟩
  have hR0 : 0 ≤ R := (norm_nonneg a).trans (hR a (start_mem_pset a l))
  obtain ⟨M, hM⟩ := hPc.exists_bound_of_continuousOn (hgc.mono hlΩ)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a (start_mem_pset a l))
  set L := plen a l with hL
  have hL0 : 0 ≤ L := by
    have := norm_pint_le (f := fun _ => (1:ℂ)) (a := a) (l := l) (C := 1) (fun _ _ => by simp)
    have h2 := norm_nonneg (pint (fun _ => (1:ℂ)) a l)
    nlinarith
  have hfar : ∀ z : ℂ, 2 * R < ‖z‖ → ‖H z‖ ≤ L * (M / (‖z‖ - R)) := by
    intro z hz
    have hzP : z ∉ P := fun h0 => by linarith [hR z h0]
    have hHz : H z = h₁ z := by
      by_cases hzΩ : z ∈ Ω
      · simp [hH, hzΩ, hrel z hzP, wn_eq_zero_of_far hl hR hz]
      · simp [hH, hzΩ]
    rw [hHz]
    apply norm_pint_le
    intro w hw
    have hwR := hR w hw
    have hpos : 0 < ‖z‖ - R := by linarith
    have hd : ‖z‖ - R ≤ ‖w - z‖ := by
      have := norm_sub_norm_le z w
      rw [norm_sub_rev] at this
      linarith
    rw [norm_mul, norm_inv]
    calc ‖g w‖ * ‖w - z‖⁻¹ ≤ M * (‖z‖ - R)⁻¹ := by
          apply mul_le_mul (hM w hw) _ (by positivity) hM0
          exact inv_anti₀ hpos hd
      _ = M / (‖z‖ - R) := by rw [div_eq_mul_inv]
  have hbdd : Bornology.IsBounded (range H) := by
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0:ℂ) (2 * R + 1)).exists_bound_of_continuousOn
      hHd.continuous.continuousOn
    rw [isBounded_iff_forall_norm_le]
    refine ⟨max C (L * (M / (R + 1))), ?_⟩
    rintro _ ⟨z, rfl⟩
    by_cases hz : ‖z‖ ≤ 2 * R + 1
    · exact (hC z (by simpa using hz)).trans (le_max_left _ _)
    · push Not at hz
      refine (hfar z (by linarith)).trans (le_trans ?_ (le_max_right _ _))
      apply mul_le_mul_of_nonneg_left _ hL0
      apply div_le_div_of_nonneg_left hM0 (by linarith) (by linarith)
  have hH0 : ∀ z, H z = 0 := by
    intro z
    by_contra hne
    set ε := ‖H z‖ with hε
    have hεpos : 0 < ε := norm_pos_iff.2 hne
    set T : ℝ := 2 * R + 1 + L * M / ε with hT
    have hLM : 0 ≤ L * M := mul_nonneg hL0 hM0
    have hT0 : 0 ≤ T := by positivity
    have hnT : ‖(T : ℂ)‖ = T := by simp [abs_of_nonneg hT0]
    have h1 := hfar (T : ℂ) (by rw [hnT]; have : 0 ≤ L * M / ε := (by positivity); linarith [hT])
    rw [hHd.apply_eq_apply_of_bounded hbdd (T : ℂ) z, hnT] at h1
    have hpos : 0 < T - R := by have : 0 ≤ L * M / ε := (by positivity); linarith [hT]
    have h2 : L * (M / (T - R)) < ε := by
      rw [← mul_div_assoc, div_lt_iff₀ hpos, hT]
      have : ε * (2 * R + 1 + L * M / ε - R) = ε * (R + 1) + L * M := by
        field_simp; ring
      rw [this]; nlinarith
    linarith
  have := hH0 z
  simpa [hH, hz] using this

include hΩ hK hl hlΩ hg in
/-- **Cauchy's theorem** for polygonal loops in a region whose complement in the Riemann
sphere is connected. -/
theorem pint_eq_zero_of_loop : pint g a l = 0 := by
  have ha : a ∈ Ω := hlΩ (start_mem_pset a l)
  set G : ℂ → ℂ := fun w => (w - a) * g w with hG
  have hGd : DifferentiableOn ℂ G Ω := ((differentiableOn_id.sub_const a).mul hg)
  have := pint_dslope_eq_zero hΩ hK hl hlΩ hGd ha
  rw [← this]
  apply pint_congr
  intro w _
  rcases eq_or_ne w a with rfl | hne
  · rw [dslope_same]
    have hd : HasDerivAt G (1 * g w + (w - w) * deriv g w) w :=
      ((hasDerivAt_id w).sub_const w).mul
        ((hg w ha).differentiableAt (hΩ.mem_nhds ha)).hasDerivAt
    rw [hd.deriv]; ring
  · rw [dslope_of_ne _ hne, slope_def_field]
    have : w - a ≠ 0 := sub_ne_zero.2 hne
    simp only [hG, sub_self, zero_mul, sub_zero]
    field_simp

end Dixon

end RMA


open Complex Set Metric Filter Topology

namespace RMA

/-! ## Global primitives, logarithms and roots -/

lemma pend_snoc (a : ℂ) (l : List ℂ) (w : ℂ) : pend a (l ++ [w]) = w := by
  rw [pend_append]; rfl

lemma pset_snoc (a : ℂ) (l : List ℂ) (w : ℂ) :
    pset a (l ++ [w]) = pset a l ∪ (sset (pend a l) w ∪ {w}) := by
  rw [pset_append]; rfl

/-- Every point of a region can be reached from `a` by a polygonal path in the region. -/
lemma exists_path {Ω : Set ℂ} (hΩ : IsOpen Ω) (hc : IsPreconnected Ω) {a : ℂ} (ha : a ∈ Ω) :
    ∀ z ∈ Ω, ∃ l : List ℂ, pend a l = z ∧ pset a l ⊆ Ω := by
  set Q : ℂ → Prop := fun z => ∃ l : List ℂ, pend a l = z ∧ pset a l ⊆ Ω with hQ
  have hext : ∀ z w, Q z → sset z w ⊆ Ω → Q w := by
    rintro z w ⟨l, hl, hlΩ⟩ hs
    refine ⟨l ++ [w], pend_snoc a l w, ?_⟩
    rw [pset_snoc, hl]
    exact union_subset hlΩ (union_subset hs (singleton_subset_iff.2 (hs (right_mem_sset z w))))
  have hcover : Ω ⊆ interior {z | Q z} ∪ interior {z | ¬ Q z} := by
    intro z hz
    obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 hΩ z hz
    by_cases hQz : Q z
    · left
      rw [mem_interior_iff_mem_nhds]
      filter_upwards [ball_mem_nhds z hr] with w hw
      exact hext z w hQz ((sset_subset_of_convex (convex_ball z r) (mem_ball_self hr) hw).trans hrΩ)
    · right
      rw [mem_interior_iff_mem_nhds]
      filter_upwards [ball_mem_nhds z hr] with w hw hQw
      exact hQz (hext w z hQw ((sset_subset_of_convex (convex_ball z r) hw (mem_ball_self hr)).trans
        hrΩ))
  have hdisj : Disjoint (interior {z | Q z}) (interior {z | ¬ Q z}) := by
    rw [Set.disjoint_left]
    intro z h1 h2
    exact (interior_subset (s := {z | ¬ Q z}) h2 : ¬ Q z) (interior_subset (s := {z | Q z}) h1)
  have hQa : a ∈ interior {z | Q z} := by
    obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 hΩ a ha
    rw [mem_interior_iff_mem_nhds]
    filter_upwards [ball_mem_nhds a hr] with w hw
    exact hext a w ⟨[], rfl, by simpa [pset] using ha⟩
      ((sset_subset_of_convex (convex_ball a r) (mem_ball_self hr) hw).trans hrΩ)
  have := hc.subset_left_of_subset_union isOpen_interior isOpen_interior hdisj hcover ⟨a, ha, hQa⟩
  intro z hz
  exact (interior_subset (s := {z | Q z}) (this hz) : Q z)

/-- A holomorphic function on a region whose complement in the Riemann sphere is connected
has a primitive. -/
theorem exists_primitive {Ω : Set ℂ} (hΩ : IsOpen Ω) (hc : IsPreconnected Ω)
    (hK : IsConnected (((↑) : ℂ → OnePoint ℂ) '' Ω)ᶜ) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g Ω) : ∃ F : ℂ → ℂ, ∀ z ∈ Ω, HasDerivAt F (g z) z := by
  classical
  rcases Ω.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact ⟨0, fun z hz => hz.elim⟩
  have hp := exists_path hΩ hc ha
  set F : ℂ → ℂ := fun z => if hz : z ∈ Ω then pint g a (hp z hz).choose else 0 with hF
  have hstep : ∀ z w, z ∈ Ω → w ∈ Ω → sset z w ⊆ Ω → F w = F z + sint g z w := by
    intro z w hz hw hs
    obtain ⟨hlz, hlzΩ⟩ := (hp z hz).choose_spec
    obtain ⟨hlw, hlwΩ⟩ := (hp w hw).choose_spec
    set lz := (hp z hz).choose
    set lw := (hp w hw).choose
    have hend1 : pend a (lz ++ [w]) = pend a lw := by rw [pend_snoc, hlw]
    have hloop : pend a ((lz ++ [w]) ++ revl a lw) = a := by
      rw [pend_append, hend1, pend_revl]
    have hsub : pset a ((lz ++ [w]) ++ revl a lw) ⊆ Ω := by
      rw [pset_append, hend1, pset_revl, pset_snoc, hlz]
      exact union_subset (union_subset hlzΩ (union_subset hs (singleton_subset_iff.2 hw))) hlwΩ
    have h0 := pint_eq_zero_of_loop hΩ hK hloop hsub hg
    rw [pint_append, hend1, pint_revl, pint_append, hlz] at h0
    simp only [pint, add_zero] at h0
    simp only [hF, dif_pos hz, dif_pos hw]
    linear_combination -h0
  refine ⟨F, fun z hz => ?_⟩
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 hΩ z hz
  obtain ⟨P, hP⟩ := (hg.mono hrΩ).isExactOn_ball
  have hev : ∀ᶠ w in 𝓝 z, F w = P w + (F z - P z) := by
    filter_upwards [ball_mem_nhds z hr] with w hw
    have hs : sset z w ⊆ ball z r := sset_subset_of_convex (convex_ball z r) (mem_ball_self hr) hw
    rw [hstep z w hz (hrΩ hw) (hs.trans hrΩ),
      sint_eq_sub (fun u hu => hP u (hs hu)) (hg.continuousOn.mono (hs.trans hrΩ))]
    ring
  exact ((hP z (mem_ball_self hr)).add_const (F z - P z)).congr_of_eventuallyEq hev

theorem exists_log {Ω : Set ℂ} (hΩ : IsOpen Ω) (hc : IsPreconnected Ω)
    (hK : IsConnected (((↑) : ℂ → OnePoint ℂ) '' Ω)ᶜ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Ω) (hf0 : ∀ z ∈ Ω, f z ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L Ω ∧ ∀ z ∈ Ω, exp (L z) = f z := by
  rcases Ω.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact ⟨0, differentiableOn_empty, fun z hz => hz.elim⟩
  have hg : DifferentiableOn ℂ (fun z => deriv f z / f z) Ω :=
    (hf.deriv hΩ).div hf hf0
  obtain ⟨F, hF⟩ := exists_primitive hΩ hc hK hg
  have hfd : ∀ z ∈ Ω, HasDerivAt f (deriv f z) z := fun z hz =>
    ((hf z hz).differentiableAt (hΩ.mem_nhds hz)).hasDerivAt
  set u : ℂ → ℂ := fun z => f z * exp (-F z) with hu
  have hud : ∀ z ∈ Ω, HasDerivAt u 0 z := by
    intro z hz
    have := (hfd z hz).mul ((hF z hz).neg.cexp)
    refine this.congr_deriv ?_
    have h : f z * (deriv f z / f z) = deriv f z := mul_div_cancel₀ _ (hf0 z hz)
    linear_combination (-exp (-F z)) * h
  have hconst : ∀ z ∈ Ω, u z = u a := by
    intro z hz
    exact hΩ.is_const_of_deriv_eq_zero hc (fun w hw => (hud w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hud w hw).deriv) hz ha
  have hua : u a ≠ 0 := mul_ne_zero (hf0 a ha) (exp_ne_zero _)
  refine ⟨fun z => F z + log (u a), ?_, fun z hz => ?_⟩
  · exact (fun z hz => ((hF z hz).differentiableAt.add_const _).differentiableWithinAt)
  · rw [exp_add, exp_log hua, ← hconst z hz, hu]
    simp only
    rw [mul_comm (f z), ← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]

end RMA

open AhlforsComplexAnalysis in
theorem RMA.exists_log_and_root_main {Ω : Set ℂ}
    (hΩ : IsSimplyConnectedRegion Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    (hf0 : ∀ z ∈ Ω, f z ≠ 0) :
    (∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L Ω ∧ ∀ z ∈ Ω, Complex.exp (L z) = f z) ∧
    ∀ n : ℕ, 0 < n → ∃ R : ℂ → ℂ, AnalyticOnNhd ℂ R Ω ∧ ∀ z ∈ Ω, R z ^ n = f z := by
  obtain ⟨⟨hΩo, hΩc⟩, hK⟩ := hΩ
  obtain ⟨L, hLd, hL⟩ := RMA.exists_log hΩo hΩc.isPreconnected hK hf.differentiableOn hf0
  refine ⟨⟨L, hLd.analyticOnNhd hΩo, hL⟩, fun n hn => ?_⟩
  refine ⟨fun z => Complex.exp (L z / n), ?_, fun z hz => ?_⟩
  · exact ((hLd.div_const (n : ℂ)).cexp).analyticOnNhd hΩo
  · rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hn.ne')]
    exact hL z hz

open AhlforsComplexAnalysis

theorem solution {Ω : Set ℂ}
    (hΩ : IsSimplyConnectedRegion Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    (hf0 : ∀ z ∈ Ω, f z ≠ 0) :
    (∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L Ω ∧ ∀ z ∈ Ω, Complex.exp (L z) = f z) ∧
    ∀ n : ℕ, 0 < n → ∃ R : ℂ → ℂ, AnalyticOnNhd ℂ R Ω ∧ ∀ z ∈ Ω, R z ^ n = f z :=
  RMA.exists_log_and_root_main hΩ hf hf0
