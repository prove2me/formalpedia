-- Prove2me | solution 1 for Aumann1974.TwoPerson.objective_best_response_transfer
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T03:40:19.788075+00:00
-- url     : https://prove2.me/submissions/51e29a34-effe-4670-8c64-60ae10c85899

import Mathlib
import Definitions.Def_Aumann1974_TwoPerson_RandomizingStructure
import Definitions.Def_Aumann1974_TwoPerson_Payoffs

set_option autoImplicit false

section HelpersE29
open Aumann1974.TwoPerson MeasureTheory Set

/-- Lebesgue measure on `[0,1]`. -/
noncomputable def e29nu : Measure ℝ := volume.restrict (Icc (0:ℝ) 1)

instance e29nu_prob : IsProbabilityMeasure e29nu := ⟨by simp [e29nu]⟩

/-- Product of two copies of Lebesgue measure on `[0,1]`. -/
noncomputable def e29mu : Measure (ℝ × ℝ) := e29nu.prod e29nu

instance e29mu_prob : IsProbabilityMeasure e29mu := by
  unfold e29mu; infer_instance

/-- Player 0 observes the first coordinate, player 1 the second. -/
def e29J : Fin 2 → MeasurableSpace (ℝ × ℝ) :=
  ![MeasurableSpace.comap Prod.fst inferInstance, MeasurableSpace.comap Prod.snd inferInstance]

noncomputable def e29R : RandomizingStructure (Fin 2) (ℝ × ℝ) inferInstance where
  J := e29J
  J_le := by
    intro i
    fin_cases i
    · exact measurable_fst.comap_le
    · exact measurable_snd.comap_le
  p := fun _ => e29mu
  isProb := fun _ => e29mu_prob

/-- Non-atomic splitting for Lebesgue measure on `[0,1]` (via the intermediate value theorem). -/
theorem e29_split (A0 : Set ℝ) (hA : MeasurableSet A0) (hpos : 0 < e29nu A0) :
    ∃ B0, MeasurableSet B0 ∧ B0 ⊆ A0 ∧ 0 < e29nu B0 ∧ e29nu B0 < e29nu A0 := by
  set f : ℝ → ℝ := fun x => e29nu.real (A0 ∩ Iic x) with hf
  have hlip : LipschitzWith 1 f := by
    apply LipschitzWith.of_le_add
    intro x y
    have h1 : A0 ∩ Iic x ⊆ (A0 ∩ Iic y) ∪ Ioc y x := by
      rintro z ⟨hz1, hz2⟩
      by_cases hzy : z ≤ y
      · exact Or.inl ⟨hz1, hzy⟩
      · exact Or.inr ⟨not_le.mp hzy, hz2⟩
    have h2 : e29nu.real (Ioc y x) ≤ dist x y := by
      have h3 : e29nu (Ioc y x) ≤ volume (Ioc y x) :=
        Measure.le_iff'.1 Measure.restrict_le_self _
      rw [Real.volume_Ioc] at h3
      calc e29nu.real (Ioc y x) = (e29nu (Ioc y x)).toReal := rfl
        _ ≤ (ENNReal.ofReal (x - y)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h3
        _ = max (x - y) 0 := ENNReal.toReal_ofReal'
        _ ≤ dist x y := by
          rw [Real.dist_eq]; exact max_le (le_abs_self _) (abs_nonneg _)
    calc f x ≤ e29nu.real ((A0 ∩ Iic y) ∪ Ioc y x) := measureReal_mono h1
      _ ≤ e29nu.real (A0 ∩ Iic y) + e29nu.real (Ioc y x) := measureReal_union_le _ _
      _ ≤ f y + dist x y := by simp only [hf]; linarith
  have hcont := hlip.continuous
  have hf0 : f 0 = 0 := by
    have h0 : e29nu (A0 ∩ Iic 0) = 0 := by
      rw [e29nu, Measure.restrict_apply (hA.inter measurableSet_Iic)]
      apply measure_mono_null (t := ({0} : Set ℝ)) _ Real.volume_singleton
      rintro z ⟨⟨_, hz0⟩, hz1, _⟩
      exact le_antisymm hz0 hz1
    simp only [hf, Measure.real, h0, ENNReal.toReal_zero]
  have hf1 : f 1 = e29nu.real A0 := by
    have h1 : e29nu (A0 ∩ Iic 1) = e29nu A0 := by
      rw [e29nu, Measure.restrict_apply (hA.inter measurableSet_Iic), Measure.restrict_apply hA]
      congr 1
      ext z
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨⟨h, _⟩, h'⟩; exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩; exact ⟨⟨h, h'.2⟩, h'⟩
    simp only [hf, Measure.real, h1]
  have hfin : e29nu A0 ≠ ⊤ := measure_ne_top _ _
  have hr : 0 < e29nu.real A0 := ENNReal.toReal_pos hpos.ne' hfin
  obtain ⟨c, _, hc⟩ := intermediate_value_Icc zero_le_one hcont.continuousOn
    (show e29nu.real A0 / 2 ∈ Icc (f 0) (f 1) by
      rw [hf0, hf1]; constructor <;> linarith)
  have hB : e29nu (A0 ∩ Iic c) = ENNReal.ofReal (e29nu.real A0 / 2) := by
    rw [← hc]
    simp only [hf, Measure.real]
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  refine ⟨A0 ∩ Iic c, hA.inter measurableSet_Iic, inter_subset_left, ?_, ?_⟩
  · rw [hB]; exact ENNReal.ofReal_pos.2 (by linarith)
  · rw [hB, ← ENNReal.ofReal_toReal hfin]
    exact (ENNReal.ofReal_lt_ofReal_iff hr).2 (by simp only [Measure.real] at *; linarith)

theorem e29mu_fst (A0 : Set ℝ) : e29mu (Prod.fst ⁻¹' A0) = e29nu A0 := by
  rw [← prod_univ, e29mu, Measure.prod_prod, measure_univ, mul_one]

theorem e29mu_snd (A0 : Set ℝ) : e29mu (Prod.snd ⁻¹' A0) = e29nu A0 := by
  rw [← univ_prod, e29mu, Measure.prod_prod, measure_univ, one_mul]

theorem e29mu_box (A0 B0 : Set ℝ) :
    e29mu (Prod.fst ⁻¹' A0 ∩ Prod.snd ⁻¹' B0) = e29nu A0 * e29nu B0 := by
  rw [← prod_eq, e29mu, Measure.prod_prod]

theorem e29_sup0 : (⨆ (k : Fin 2) (_ : k ≠ 0), e29R.J k) ≤ e29J 1 := by
  refine iSup₂_le fun k hk => ?_
  fin_cases k
  · exact absurd rfl hk
  · exact le_rfl

theorem e29_sup1 : (⨆ (k : Fin 2) (_ : k ≠ 1), e29R.J k) ≤ e29J 0 := by
  refine iSup₂_le fun k hk => ?_
  fin_cases k
  · exact le_rfl
  · exact absurd rfl hk

theorem e29_secret0 (A : Set (ℝ × ℝ)) (hA : MeasurableSet[e29J 0] A) : IsSecret e29R 0 A := by
  refine ⟨hA, fun j _ B hB => ?_⟩
  have hB' : MeasurableSet[e29J 1] B := e29_sup0 B hB
  obtain ⟨A0, _, rfl⟩ := (MeasurableSpace.measurableSet_comap).1 hA
  obtain ⟨B0, _, rfl⟩ := (MeasurableSpace.measurableSet_comap).1 hB'
  change e29mu _ = e29mu _ * e29mu _
  rw [e29mu_box, e29mu_fst, e29mu_snd]

theorem e29_secret1 (A : Set (ℝ × ℝ)) (hA : MeasurableSet[e29J 1] A) : IsSecret e29R 1 A := by
  refine ⟨hA, fun j _ B hB => ?_⟩
  have hB' : MeasurableSet[e29J 0] B := e29_sup1 B hB
  obtain ⟨A0, _, rfl⟩ := (MeasurableSpace.measurableSet_comap).1 hA
  obtain ⟨B0, _, rfl⟩ := (MeasurableSpace.measurableSet_comap).1 hB'
  change e29mu _ = e29mu _ * e29mu _
  rw [inter_comm, e29mu_box, e29mu_fst, e29mu_snd, mul_comm]

theorem e29_nonatomic0 (j : Fin 2) : NonAtomicOn (e29R.p j) (e29J 0) := by
  intro A hA hpos
  obtain ⟨A0, hA0, rfl⟩ := (MeasurableSpace.measurableSet_comap).1 hA
  change 0 < e29mu _ at hpos
  rw [e29mu_fst] at hpos
  obtain ⟨B0, hB0, hsub, h1, h2⟩ := e29_split A0 hA0 hpos
  refine ⟨Prod.fst ⁻¹' B0, (MeasurableSpace.measurableSet_comap).2 ⟨B0, hB0, rfl⟩,
    preimage_mono hsub, ?_, ?_⟩
  · change 0 < e29mu _; rw [e29mu_fst]; exact h1
  · change e29mu _ < e29mu _; rw [e29mu_fst, e29mu_fst]; exact h2

theorem e29_nonatomic1 (j : Fin 2) : NonAtomicOn (e29R.p j) (e29J 1) := by
  intro A hA hpos
  obtain ⟨A0, hA0, rfl⟩ := (MeasurableSpace.measurableSet_comap).1 hA
  change 0 < e29mu _ at hpos
  rw [e29mu_snd] at hpos
  obtain ⟨B0, hB0, hsub, h1, h2⟩ := e29_split A0 hA0 hpos
  refine ⟨Prod.snd ⁻¹' B0, (MeasurableSpace.measurableSet_comap).2 ⟨B0, hB0, rfl⟩,
    preimage_mono hsub, ?_, ?_⟩
  · change 0 < e29mu _; rw [e29mu_snd]; exact h1
  · change e29mu _ < e29mu _; rw [e29mu_snd, e29mu_snd]; exact h2

theorem e29_assumptionII : AssumptionII e29R := by
  intro i
  refine ⟨e29R.J i, ?_, ?_⟩
  · fin_cases i
    · exact e29_secret0
    · exact e29_secret1
  · fin_cases i
    · exact e29_nonatomic0
    · exact e29_nonatomic1

/-- The witness profile: both players always play `false`. -/
def e29t : ∀ _ : Fin 2, ℝ × ℝ → Bool := fun _ _ => false

theorem e29_trivial_secret (i : Fin 2) (A : Set (ℝ × ℝ)) (hA : A = ∅ ∨ A = univ) :
    IsSecret e29R i A := by
  rcases hA with rfl | rfl
  · exact ⟨@MeasurableSet.empty _ (e29R.J i), fun j _ B _ => by simp⟩
  · exact ⟨@MeasurableSet.univ _ (e29R.J i), fun j _ B _ => by simp⟩

theorem e29_const_sets (b a : Bool) :
    {ω : ℝ × ℝ | b = a} = ∅ ∨ {ω : ℝ × ℝ | b = a} = univ := by
  by_cases h : b = a
  · right; ext ω; simp [h]
  · left; ext ω; simp [h]

theorem e29_counterexample : ¬ (IsEquilibrium e29R (fun (_ : Fin 2) (x : Bool) => if x then (1:ℝ) else 0)
    (fun a : (∀ _ : Fin 2, Bool) => a 0) e29t) := by
  rintro ⟨_, hdev⟩
  have hstrat : IsStrategy e29R 0 (fun _ : ℝ × ℝ => true) := by
    intro a
    rcases e29_const_sets true a with h | h
    · rw [h]; exact @MeasurableSet.empty _ (e29R.J 0)
    · rw [h]; exact @MeasurableSet.univ _ (e29R.J 0)
  have := hdev 0 (fun _ => true) hstrat
  simp [H, payoffFn, e29t, Function.update] at this
  norm_num at this

end HelpersE29

open Aumann1974.TwoPerson in
theorem solution : ¬ (∀ {Ω X : Type} {mΩ : MeasurableSpace Ω}
    {S : Fin 2 → Type} [∀ i, Fintype (S i)] [Fintype X]
    (R : RandomizingStructure (Fin 2) Ω mΩ) (hII : AssumptionII R)
    (g : (∀ i, S i) → X) (u : Fin 2 → X → ℝ)
    (s t : ∀ i, Ω → S i)
    (hobj : ∀ i, IsObjectiveStrategy R (t i)) (hmix : ∀ i, IsMixed R i (t i))
    (heq : (fun i => H R u g s i) = fun i => H R u g t i)
    (hbr : ∀ i, ∀ σ : Ω → S i, H R u g t i ≤ H R u g (Function.update t i σ) i),
    IsEquilibrium R u g t ∧ (fun i => H R u g s i) = fun i => H R u g t i) := by
  intro h
  have hobj : ∀ i, IsObjectiveStrategy e29R (e29t i) := fun _ _ _ _ => rfl
  have hmix : ∀ i, IsMixed e29R i (e29t i) := fun i a =>
    e29_trivial_secret i _ (e29_const_sets false a)
  have hbr : ∀ i, ∀ σ : ℝ × ℝ → Bool,
      H e29R (fun (_ : Fin 2) (x : Bool) => if x then (1:ℝ) else 0)
        (fun a : (∀ _ : Fin 2, Bool) => a 0) e29t i ≤
      H e29R (fun (_ : Fin 2) (x : Bool) => if x then (1:ℝ) else 0)
        (fun a : (∀ _ : Fin 2, Bool) => a 0) (Function.update e29t i σ) i := by
    intro i σ
    have h0 : H e29R (fun (_ : Fin 2) (x : Bool) => if x then (1:ℝ) else 0)
        (fun a : (∀ _ : Fin 2, Bool) => a 0) e29t i = 0 := by
      simp [H, payoffFn, e29t]
    rw [h0]
    apply MeasureTheory.integral_nonneg
    intro ω
    simp only [payoffFn]
    split <;> norm_num
  exact e29_counterexample
    (@h (ℝ × ℝ) Bool inferInstance (fun _ => Bool) (fun _ => inferInstance) inferInstance
      e29R e29_assumptionII (fun a => a 0) (fun _ x => if x then 1 else 0) e29t e29t
      hobj hmix rfl hbr).1
