-- Prove2me | solution 1 for Aumann1974.TwoPerson.mimic_payoff_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T07:07:57.600537+00:00
-- url     : https://prove2.me/submissions/0d2c8441-f47f-4b75-b40f-695549c616ae

import Mathlib
import Definitions.Def_Aumann1974_TwoPerson_RandomizingStructure
import Definitions.Def_Aumann1974_TwoPerson_Payoffs

set_option autoImplicit false

open MeasureTheory in
/-- Integral of a function of a finitely-valued map with measurable level sets. -/
theorem aumanne25e92e4_integral_fintype {Ω T : Type*} [MeasurableSpace Ω] [Fintype T]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → T)
    (hf : ∀ t, MeasurableSet {ω | f ω = t}) (φ : T → ℝ) :
    ∫ ω, φ (f ω) ∂μ = ∑ t, μ.real {ω | f ω = t} * φ t := by
  classical
  have hfun : (fun ω => φ (f ω)) =
      fun ω => ∑ t, Set.indicator {ω | f ω = t} (fun _ => φ t) ω := by
    funext ω
    rw [Finset.sum_eq_single (f ω)]
    · simp
    · intro b _ hb
      simp [Set.indicator, Ne.symm hb]
    · simp
  rw [hfun, integral_finset_sum]
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [integral_indicator_const _ (hf t), smul_eq_mul]
  · intro t _
    exact (integrable_const (φ t)).indicator (hf t)

open MeasureTheory Aumann1974.TwoPerson in
/-- Player 0's payoff after replacing `s 0` by a `𝒥₀`-measurable `σ` is the
`p₀`-average over `σ`'s values of the payoffs of the pure deviations. -/
theorem aumanne25e92e4_avg {Ω X : Type*} {mΩ : MeasurableSpace Ω}
    {S : Fin 2 → Type*} [∀ i, Fintype (S i)]
    (R : RandomizingStructure (Fin 2) Ω mΩ)
    (g : (∀ i, S i) → X) (u : Fin 2 → X → ℝ)
    (s : ∀ i, Ω → S i) (hs1 : ∀ b, MeasurableSet {ω | s 1 ω = b})
    (hmix1 : IsMixed R 1 (s 1))
    (σ : Ω → S 0) (hσ : ∀ a, MeasurableSet[R.J 0] {ω | σ ω = a}) :
    H R u g (Function.update s 0 σ) 0 =
      ∑ a : S 0, (R.p 0).real {ω | σ ω = a} * H R u g (Function.update s 0 (fun _ => a)) 0 := by
  classical
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  -- general finite-sum formula
  have hH : ∀ t : ∀ k, Ω → S k, (∀ k b, MeasurableSet {ω | t k ω = b}) →
      H R u g t 0 = ∑ c : (∀ k, S k),
        (R.p 0).real ({ω | t 0 ω = c 0} ∩ {ω | t 1 ω = c 1}) * payoffFn u g 0 c := by
    intro t ht
    have hset : ∀ c : (∀ k, S k),
        {ω | (fun k => t k ω) = c} = {ω | t 0 ω = c 0} ∩ {ω | t 1 ω = c 1} := by
      intro c
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      constructor
      · intro h
        exact ⟨congrFun h 0, congrFun h 1⟩
      · rintro ⟨h1, h2⟩
        funext k
        fin_cases k
        · exact h1
        · exact h2
    have hmeas : ∀ c : (∀ k, S k), MeasurableSet {ω | (fun k => t k ω) = c} := by
      intro c
      rw [hset c]
      exact (ht 0 (c 0)).inter (ht 1 (c 1))
    have e : H R u g t 0 = ∑ c : (∀ k, S k),
        (R.p 0).real {ω | (fun k => t k ω) = c} * payoffFn u g 0 c :=
      aumanne25e92e4_integral_fintype (R.p 0) (fun ω k => t k ω) hmeas (payoffFn u g 0)
    rw [e]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hset c]
  set Q : S 1 → ℝ := fun b => (R.p 0).real {ω | s 1 ω = b} with hQ
  -- formula for any J₀-measurable replacement
  have hG : ∀ τ : Ω → S 0, (∀ a, MeasurableSet[R.J 0] {ω | τ ω = a}) →
      H R u g (Function.update s 0 τ) 0 =
        ∑ c : (∀ k, S k), (R.p 0).real {ω | τ ω = c 0} * Q (c 1) * payoffFn u g 0 c := by
    intro τ hτ
    have h0 : ∀ ω, Function.update s 0 τ 0 ω = τ ω := by
      intro ω; rw [Function.update_self]
    have h1 : ∀ ω, Function.update s 0 τ 1 ω = s 1 ω := by
      intro ω; rw [Function.update_of_ne h10]
    have hmt : ∀ k b, MeasurableSet {ω | Function.update s 0 τ k ω = b} := by
      intro k b
      fin_cases k
      · simp only [Fin.zero_eta, h0]
        exact R.J_le 0 _ (hτ b)
      · simp only [Fin.mk_one, h1]
        exact hs1 b
    rw [hH _ hmt]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [h0, h1]
    have hB : MeasurableSet[⨆ (k : Fin 2) (_ : k ≠ 1), R.J k] {ω | τ ω = c 0} :=
      (le_iSup₂ (f := fun (k : Fin 2) (_ : k ≠ 1) => R.J k) 0 h10.symm) _ (hτ (c 0))
    have := (hmix1 (c 1)).2 0 h10.symm _ hB
    rw [Set.inter_comm, measureReal_def, measureReal_def, hQ, this, ENNReal.toReal_mul]
    simp only [measureReal_def]
    ring
  have hconst : ∀ a : S 0, ∀ b : S 0, MeasurableSet[R.J 0] {ω : Ω | (fun _ => a) ω = b} := by
    intro a b
    by_cases hb : a = b
    · simp [hb]
    · simp [hb]
  have hD : ∀ a : S 0, H R u g (Function.update s 0 (fun _ => a)) 0 =
      ∑ c : (∀ k, S k), (if c 0 = a then Q (c 1) * payoffFn u g 0 c else 0) := by
    intro a
    rw [hG _ (hconst a)]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : c 0 = a
    · have : {ω : Ω | a = c 0} = Set.univ := by
        ext ω; simp [hc]
      simp only [this, if_pos hc, probReal_univ, one_mul]
    · have : {ω : Ω | a = c 0} = ∅ := by
        ext ω; simp [Ne.symm hc]
      simp only [this, if_neg hc, measureReal_empty, zero_mul]
  rw [hG σ hσ]
  simp_rw [hD, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  have : ∀ a' : S 0, (R.p 0).real {ω | σ ω = a'} *
      (if c 0 = a' then Q (c 1) * payoffFn u g 0 c else 0) =
      if c 0 = a' then (R.p 0).real {ω | σ ω = c 0} * Q (c 1) * payoffFn u g 0 c else 0 := by
    intro a'
    by_cases hc : c 0 = a'
    · subst hc; simp [mul_assoc]
    · simp [hc]
  simp_rw [this]
  rw [Finset.sum_ite_eq]
  simp

open MeasureTheory Aumann1974.TwoPerson in
theorem solution {Ω X : Type*} {mΩ : MeasurableSpace Ω}
    {S : Fin 2 → Type*} [∀ i, Fintype (S i)] [Fintype X]
    (R : RandomizingStructure (Fin 2) Ω mΩ) (hII : AssumptionII R)
    (g : (∀ i, S i) → X) (u : Fin 2 → X → ℝ)
    (h52 : ∀ B : Set Ω, MeasurableSet[mΩ] B → (R.p 0 B = 0 ↔ R.p 1 B = 0))
    (s : ∀ i, Ω → S i) (hs : IsEquilibrium R u g s) (hmix : ∀ i, IsMixed R i (s i))
    (t₁ : Ω → S 0) (hobj : IsObjectiveStrategy R t₁) (hmix₁ : IsMixed R 0 t₁)
    (hmimic : ∀ a : S 0, R.p 1 {ω | t₁ ω = a} = R.p 1 {ω | s 0 ω = a}) :
    H R u g (fun i => if h : i = 0 then h ▸ t₁ else s i) 0 = H R u g s 0 := by
  classical
  have hprof : (fun i => if h : i = 0 then h ▸ t₁ else s i) = Function.update s 0 t₁ := by
    funext k
    fin_cases k
    · simp
    · simp
  rw [hprof]
  have hs1 : ∀ b, MeasurableSet {ω | s 1 ω = b} := fun b => R.J_le 1 _ (hs.1 1 b)
  have hs0 : ∀ a, MeasurableSet[R.J 0] {ω | s 0 ω = a} := hs.1 0
  have ht0 : ∀ a, MeasurableSet[R.J 0] {ω | t₁ ω = a} := fun a => (hmix₁ a).1
  set D : S 0 → ℝ := fun a => H R u g (Function.update s 0 (fun _ => a)) 0 with hDdef
  set v := H R u g s 0 with hv
  have hAs : v = ∑ a : S 0, (R.p 0).real {ω | s 0 ω = a} * D a := by
    have := aumanne25e92e4_avg R g u s hs1 (hmix 1) (s 0) hs0
    rw [Function.update_eq_self] at this
    exact this
  have hAt := aumanne25e92e4_avg R g u s hs1 (hmix 1) t₁ ht0
  have hsum : ∀ τ : Ω → S 0, (∀ a, MeasurableSet {ω | τ ω = a}) →
      ∑ a : S 0, (R.p 0).real {ω | τ ω = a} = 1 := by
    intro τ hτ
    have := aumanne25e92e4_integral_fintype (R.p 0) τ hτ (fun _ => (1 : ℝ))
    simp only [mul_one] at this
    rw [← this]
    simp
  have hle : ∀ a : S 0, D a ≤ v := by
    intro a
    apply hs.2 0 (fun _ => a)
    intro b
    by_cases hb : a = b
    · simp [hb]
    · simp [hb]
  have hzero : ∑ a : S 0, (R.p 0).real {ω | s 0 ω = a} * (v - D a) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← hAs, ← Finset.sum_mul,
      hsum (s 0) (fun a => R.J_le 0 _ (hs0 a)), one_mul, sub_self]
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
    mul_nonneg measureReal_nonneg (sub_nonneg.mpr (hle a)))).1 hzero
  have hkey : ∀ a : S 0, (R.p 0).real {ω | t₁ ω = a} * D a =
      (R.p 0).real {ω | t₁ ω = a} * v := by
    intro a
    by_cases hz : R.p 0 {ω | t₁ ω = a} = 0
    · simp [measureReal_def, hz]
    · have h1 : R.p 1 {ω | s 0 ω = a} ≠ 0 := by
        rw [← hmimic a, ← hobj a 0 1]; exact hz
      have h0 : R.p 0 {ω | s 0 ω = a} ≠ 0 := by
        intro h; exact h1 ((h52 _ (R.J_le 0 _ (hs0 a))).1 h)
      have hP : (R.p 0).real {ω | s 0 ω = a} ≠ 0 := by
        rw [measureReal_def, ENNReal.toReal_ne_zero]
        exact ⟨h0, measure_ne_top _ _⟩
      have := (mul_eq_zero.1 (hterm a (Finset.mem_univ a))).resolve_left hP
      rw [show D a = v by linarith]
  rw [hAt]
  calc _ = ∑ a : S 0, (R.p 0).real {ω | t₁ ω = a} * v :=
        Finset.sum_congr rfl fun a _ => hkey a
    _ = v := by rw [← Finset.sum_mul, hsum t₁ (fun a => R.J_le 0 _ (ht0 a)), one_mul]
