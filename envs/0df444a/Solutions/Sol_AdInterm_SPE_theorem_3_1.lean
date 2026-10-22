-- Prove2me | solution 1 for AdInterm.SPE.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T18:34:30.990604+00:00
-- url     : https://prove2.me/submissions/41b23d35-07de-43bf-8c90-df5930f84d59

import Mathlib
import Definitions.Def_AdInterm_SPE_VirtualValue
import Definitions.Def_AdInterm_SPE_Setting
import Theorems.Thm_AdInterm_SPE_theorem_3_1_intermediaries

open MeasureTheory

namespace AdInterm.SPE.Res

open AdInterm.SPE

lemma maxFin_zero (v : Fin 0 → ℝ) : maxFin 0 v = 0 := by
  unfold maxFin; simp; rfl

lemma maxFin_eq_of_max {m : ℕ} (v : Fin m → ℝ) (i : Fin m) (h : ∀ j, v j ≤ v i) :
    maxFin m v = v i := by
  unfold maxFin
  have : (Finset.univ.sup (fun j => (v j : WithBot ℝ))) = (v i : WithBot ℝ) :=
    le_antisymm (Finset.sup_le (fun j _ => WithBot.coe_le_coe.2 (h j)))
      (Finset.le_sup (f := fun j => (v j : WithBot ℝ)) (Finset.mem_univ i))
  rw [this]
  rfl

lemma exists_argmax {m : ℕ} (v : Fin (m + 1) → ℝ) : ∃ i, ∀ j, v j ≤ v i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ v Finset.univ_nonempty
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

lemma le_maxFin {m : ℕ} (v : Fin m → ℝ) (j : Fin m) : v j ≤ maxFin m v := by
  cases m with
  | zero => exact j.elim0
  | succ m =>
    obtain ⟨i, hi⟩ := exists_argmax v
    rw [maxFin_eq_of_max v i hi]; exact hi j

lemma maxFin_le {m : ℕ} (v : Fin m → ℝ) (a : ℝ) (ha : 0 ≤ a) (h : ∀ j, v j ≤ a) :
    maxFin m v ≤ a := by
  cases m with
  | zero => rw [maxFin_zero]; exact ha
  | succ m =>
    obtain ⟨i, hi⟩ := exists_argmax v
    rw [maxFin_eq_of_max v i hi]; exact h i

lemma abs_maxFin_le {m : ℕ} (v : Fin m → ℝ) : |maxFin m v| ≤ ∑ j, |v j| := by
  cases m with
  | zero => simp [maxFin_zero]
  | succ m =>
    obtain ⟨i, hi⟩ := exists_argmax v
    rw [maxFin_eq_of_max v i hi]
    exact Finset.single_le_sum (f := fun j => |v j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)

lemma maxFin_eq_sup' {m : ℕ} (v : Fin (m + 1) → ℝ) :
    maxFin (m + 1) v = Finset.univ.sup' Finset.univ_nonempty v := by
  obtain ⟨i, hi⟩ := exists_argmax v
  rw [maxFin_eq_of_max v i hi]
  exact le_antisymm (Finset.le_sup' v (Finset.mem_univ i))
    (Finset.sup'_le _ _ (fun j _ => hi j))

lemma measurable_maxFin (m : ℕ) : Measurable (maxFin m) := by
  cases m with
  | zero =>
    have : maxFin 0 = fun _ => (0 : ℝ) := by funext v; exact maxFin_zero v
    rw [this]; exact measurable_const
  | succ m =>
    have : maxFin (m + 1) = fun v => Finset.univ.sup' Finset.univ_nonempty
        (fun j (v : Fin (m + 1) → ℝ) => v j) v := by
      funext v; rw [maxFin_eq_sup']; simp [Finset.sup'_apply]
    rw [this]
    have h2 := Finset.measurable_sup' (s := (Finset.univ : Finset (Fin (m + 1))))
      Finset.univ_nonempty (f := fun j (v : Fin (m + 1) → ℝ) => v j)
      (fun j _ => measurable_pi_apply j)
    convert h2 using 1

lemma secondMax_eq {n : ℕ} (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (h : ∀ j, v j ≤ v i) :
    secondMax (n + 1) v = maxFin n (i.removeNth v) := by
  have key : (Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.1 ≠ p.2)).sup
      (fun p => min ((v p.1 : WithBot ℝ)) ((v p.2 : WithBot ℝ))) =
      Finset.univ.sup (fun j => ((i.removeNth v j : ℝ) : WithBot ℝ)) := by
    apply le_antisymm
    · apply Finset.sup_le
      rintro ⟨p1, p2⟩ hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      by_cases h1 : p1 = i
      · subst h1
        obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hp)
        refine le_trans (min_le_right _ _) ?_
        exact Finset.le_sup (f := fun j => ((p1.removeNth v j : ℝ) : WithBot ℝ))
          (Finset.mem_univ j)
      · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq h1
        refine le_trans (min_le_left _ _) ?_
        exact Finset.le_sup (f := fun j => ((i.removeNth v j : ℝ) : WithBot ℝ))
          (Finset.mem_univ j)
    · apply Finset.sup_le
      intro j _
      have hmem : (i, i.succAbove j) ∈ Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.1 ≠ p.2) := by
        simp [(Fin.succAbove_ne i j).symm]
      refine le_trans ?_ (Finset.le_sup (f := fun p : Fin (n + 1) × Fin (n + 1) =>
        min ((v p.1 : WithBot ℝ)) ((v p.2 : WithBot ℝ))) hmem)
      simp only [Fin.removeNth]
      rw [min_eq_right (WithBot.coe_le_coe.2 (h _))]
  unfold secondMax maxFin
  rw [key]

/-- `i` is the lowest-index maximiser of `v`. -/
def LowMax {m : ℕ} (v : Fin m → ℝ) (i : Fin m) : Prop :=
  ∀ j, (j < i → v j < v i) ∧ (i < j → v j ≤ v i)

lemma lowMax_max {m : ℕ} {v : Fin m → ℝ} {i : Fin m} (h : LowMax v i) : ∀ j, v j ≤ v i := by
  intro j
  rcases lt_trichotomy j i with hlt | rfl | hgt
  · exact ((h j).1 hlt).le
  · exact le_rfl
  · exact (h j).2 hgt

lemma lowMax_unique {m : ℕ} {v : Fin m → ℝ} {i i' : Fin m} (h : LowMax v i) (h' : LowMax v i') :
    i = i' := by
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · exact absurd (lt_of_lt_of_le ((h' i).1 hlt) ((h i').2 hlt)) (lt_irrefl _)
  · exact heq
  · exact absurd (lt_of_lt_of_le ((h i').1 hgt) ((h' i).2 hgt)) (lt_irrefl _)

lemma exists_lowMax {n : ℕ} (v : Fin (n + 1) → ℝ) : ∃ i, LowMax v i := by
  classical
  obtain ⟨i0, hi0⟩ := exists_argmax v
  have hne : (Finset.univ.filter (fun i => ∀ j, v j ≤ v i)).Nonempty :=
    ⟨i0, by simp [hi0]⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image _ (fun i => i) hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hmin
  refine ⟨i, fun j => ⟨fun hj => ?_, fun _ => hi j⟩⟩
  rcases lt_or_eq_of_le (hi j) with hlt | heq
  · exact hlt
  · exfalso
    have := hmin j (fun l => heq ▸ hi l)
    exact absurd hj (not_lt.2 this)

/-- The `i`-th summand condition, written on `(v i, removeNth i v)`. -/
def ACond {n : ℕ} (i : Fin (n + 1)) (x : ℝ) (y : Fin n → ℝ) : Prop :=
  ∀ j, (i.succAbove j < i → y j < x) ∧ (i < i.succAbove j → y j ≤ x)

lemma aCond_iff {n : ℕ} (i : Fin (n + 1)) (v : Fin (n + 1) → ℝ) :
    ACond i (v i) (i.removeNth v) ↔ LowMax v i := by
  constructor
  · intro h j
    by_cases hj : j = i
    · subst hj; exact ⟨fun h => absurd h (lt_irrefl _), fun h => absurd h (lt_irrefl _)⟩
    · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
      exact h j'
  · intro h j
    exact h (i.succAbove j)

open scoped Classical in
/-- Everywhere decomposition of the second-price revenue by the identity of the winner. -/
lemma integrand_decomp {n : ℕ} (c δ : ℝ) (v : Fin (n + 1) → ℝ) :
    (if δ ≤ maxFin (n + 1) v then max δ (secondMax (n + 1) v) - c else 0) =
      ∑ i, (if ACond i (v i) (i.removeNth v) ∧ δ ≤ v i then
        max δ (maxFin n (i.removeNth v)) - c else 0) := by
  classical
  obtain ⟨i0, hi0⟩ := exists_lowMax v
  rw [Finset.sum_eq_single i0]
  · rw [maxFin_eq_of_max v i0 (lowMax_max hi0), secondMax_eq v i0 (lowMax_max hi0)]
    simp only [(aCond_iff i0 v).2 hi0, true_and]
  · intro i _ hne
    rw [if_neg]
    rintro ⟨h, _⟩
    exact hne (lowMax_unique ((aCond_iff i v).1 h) hi0)
  · intro h; exact absurd (Finset.mem_univ i0) h

/-- Posted-price profit `(p − c) · P(X > p)`. -/
noncomputable def fval (μ : Measure ℝ) (c p : ℝ) : ℝ := (p - c) * μ.real (Set.Ioi p)

open scoped Classical in
/-- The `i`-th summand on `ℝ × (Fin n → ℝ)`. -/
noncomputable def Fi {n : ℕ} (c δ : ℝ) (i : Fin (n + 1)) (z : ℝ × (Fin n → ℝ)) : ℝ :=
  if ACond i z.1 z.2 ∧ δ ≤ z.1 then max δ (maxFin n z.2) - c else 0

lemma measurable_aCond {n : ℕ} (i : Fin (n + 1)) :
    MeasurableSet {z : ℝ × (Fin n → ℝ) | ACond i z.1 z.2} := by
  apply measurableSet_setOf.2
  unfold ACond
  apply Measurable.forall
  intro j
  apply Measurable.and
  · apply Measurable.imp measurable_const
    exact measurableSet_setOf.1 (measurableSet_lt ((measurable_pi_apply j).comp measurable_snd)
      measurable_fst)
  · apply Measurable.imp measurable_const
    exact measurableSet_setOf.1 (measurableSet_le ((measurable_pi_apply j).comp measurable_snd)
      measurable_fst)

lemma measurableSet_B {n : ℕ} (δ : ℝ) (i : Fin (n + 1)) :
    MeasurableSet {z : ℝ × (Fin n → ℝ) | ACond i z.1 z.2 ∧ δ ≤ z.1} :=
  (measurable_aCond i).inter (measurableSet_le measurable_const measurable_fst)

lemma measurableSet_A {n : ℕ} (δ : ℝ) (i : Fin (n + 1)) (y : Fin n → ℝ) :
    MeasurableSet {x : ℝ | ACond i x y ∧ δ ≤ x} := by
  have := (measurableSet_B (n := n) δ i).preimage (measurable_id.prodMk measurable_const :
    Measurable (fun x : ℝ => (x, y)))
  exact this

lemma Fi_eq_indicator {n : ℕ} (c δ : ℝ) (i : Fin (n + 1)) :
    Fi c δ i = {z : ℝ × (Fin n → ℝ) | ACond i z.1 z.2 ∧ δ ≤ z.1}.indicator
      (fun z => max δ (maxFin n z.2) - c) := by
  classical
  funext z
  simp only [Fi, Set.indicator, Set.mem_setOf_eq]

section integrals

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma integrable_coord {n : ℕ} (hint : Integrable (fun x : ℝ => x) μ) (j : Fin n) :
    Integrable (fun y : Fin n → ℝ => y j) (Measure.pi (fun _ : Fin n => μ)) := by
  have h := measurePreserving_eval (fun _ : Fin n => μ) j
  exact h.integrable_comp_of_integrable hint

lemma integrable_g {n : ℕ} (hint : Integrable (fun x : ℝ => x) μ) (c δ : ℝ) (hδ : 0 ≤ δ) :
    Integrable (fun y : Fin n → ℝ => max δ (maxFin n y) - c)
      (Measure.pi (fun _ : Fin n => μ)) := by
  have hb : Integrable (fun y : Fin n → ℝ => δ + |c| + ∑ j, |y j|)
      (Measure.pi (fun _ : Fin n => μ)) :=
    (integrable_const _).add (integrable_finset_sum _ (fun j _ => (integrable_coord μ hint j).abs))
  refine hb.mono' ?_ ?_
  · exact ((measurable_const.max (measurable_maxFin n)).sub_const c).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun y => ?_)
    rw [Real.norm_eq_abs]
    have h1 := abs_maxFin_le y
    have h2 : |max δ (maxFin n y)| ≤ δ + |maxFin n y| := by
      rw [abs_le]; constructor
      · have := neg_abs_le (maxFin n y)
        have := le_max_right δ (maxFin n y)
        linarith
      · have := le_abs_self (maxFin n y)
        rcases le_total δ (maxFin n y) with h | h
        · rw [max_eq_right h]; linarith [abs_nonneg (maxFin n y)]
        · rw [max_eq_left h]; linarith [abs_nonneg (maxFin n y)]
    calc |max δ (maxFin n y) - c| ≤ |max δ (maxFin n y)| + |c| := abs_sub _ _
      _ ≤ δ + |c| + ∑ j, |y j| := by linarith

lemma integrable_Fi {n : ℕ} (hint : Integrable (fun x : ℝ => x) μ) (c δ : ℝ) (hδ : 0 ≤ δ)
    (i : Fin (n + 1)) :
    Integrable (Fi c δ i) (μ.prod (Measure.pi (fun _ : Fin n => μ))) := by
  rw [Fi_eq_indicator]
  apply Integrable.indicator _ (measurableSet_B δ i)
  have := (measurePreserving_snd (μ := μ) (ν := Measure.pi (fun _ : Fin n => μ))).integrable_comp_of_integrable
    (integrable_g μ hint c δ hδ)
  exact this

lemma inner_Fi {n : ℕ} (c δ : ℝ) (hδ : 0 ≤ δ)
    (hatom : ∀ p, 0 ≤ p → (p - c) * μ.real {p} = 0) (i : Fin (n + 1)) (y : Fin n → ℝ) :
    ∫ x, Fi c δ i (x, y) ∂μ = fval μ c (max δ (maxFin n y)) := by
  set p := max δ (maxFin n y) with hp
  have hfun : (fun x => Fi c δ i (x, y)) =
      {x : ℝ | ACond i x y ∧ δ ≤ x}.indicator (fun _ => p - c) := by
    classical
    funext x
    simp only [Fi, Set.indicator, Set.mem_setOf_eq, hp]
  rw [hfun, integral_indicator_const _ (measurableSet_A δ i y), smul_eq_mul]
  have hsub1 : Set.Ioi p ⊆ {x : ℝ | ACond i x y ∧ δ ≤ x} := by
    intro x hx
    have hx' : p < x := hx
    refine ⟨fun j => ⟨fun _ => ?_, fun _ => ?_⟩, ?_⟩
    · exact lt_of_le_of_lt (le_trans (le_maxFin y j) (le_max_right _ _)) hx'
    · exact (lt_of_le_of_lt (le_trans (le_maxFin y j) (le_max_right _ _)) hx').le
    · exact (lt_of_le_of_lt (le_max_left _ _) hx').le
  have hsub2 : {x : ℝ | ACond i x y ∧ δ ≤ x} ⊆ Set.Ici p := by
    rintro x ⟨hA, hx⟩
    have hy : ∀ j, y j ≤ x := by
      intro j
      rcases lt_or_gt_of_ne (Fin.succAbove_ne i j) with h | h
      · exact ((hA j).1 h).le
      · exact (hA j).2 h
    exact max_le hx (maxFin_le y x (le_trans hδ hx) hy)
  have hp0 : 0 ≤ p := le_trans hδ (le_max_left _ _)
  unfold fval
  by_cases hpc : p - c = 0
  · rw [hpc]; simp
  · have hat : μ.real {p} = 0 := by
      have := hatom p hp0
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hpc
      · exact h
    have h1 : μ.real (Set.Ioi p) ≤ μ.real {x : ℝ | ACond i x y ∧ δ ≤ x} := measureReal_mono hsub1
    have h2 : μ.real {x : ℝ | ACond i x y ∧ δ ≤ x} ≤ μ.real (Set.Ici p) := measureReal_mono hsub2
    have h3 : μ.real (Set.Ici p) ≤ μ.real {p} + μ.real (Set.Ioi p) := by
      rw [← Set.Ioi_insert, Set.insert_eq]
      exact measureReal_union_le _ _
    rw [mul_comm]
    congr 1
    linarith

/-- The second-price revenue with reserve `δ` and cost `c` equals
`m · E[(max(δ, M) − c) P(X > max(δ, M))]`, `M` the maximum of `m − 1` other bids. -/
lemma reserveObj_eq {n : ℕ} (hint : Integrable (fun x : ℝ => x) μ) (c δ : ℝ) (hδ : 0 ≤ δ)
    (hatom : ∀ p, 0 ≤ p → (p - c) * μ.real {p} = 0) :
    reserveObj (n + 1) μ c δ =
      (n + 1) * ∫ y, fval μ c (max δ (maxFin n y)) ∂(Measure.pi (fun _ : Fin n => μ)) := by
  classical
  have hT : ∀ i : Fin (n + 1), ∫ v, Fi c δ i (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i v)
      ∂(Measure.pi (fun _ : Fin (n + 1) => μ)) =
      ∫ y, fval μ c (max δ (maxFin n y)) ∂(Measure.pi (fun _ : Fin n => μ)) := by
    intro i
    have h := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
    rw [h.integral_comp' (Fi c δ i), integral_prod_symm _ (integrable_Fi μ hint c δ hδ i)]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun y => inner_Fi μ c δ hδ hatom i y))
  have hIi : ∀ i : Fin (n + 1), Integrable
      (fun v => Fi c δ i (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i v))
      (Measure.pi (fun _ : Fin (n + 1) => μ)) := by
    intro i
    have h := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
    exact (h.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2
      (integrable_Fi μ hint c δ hδ i)
  have hpt : ∀ v : Fin (n + 1) → ℝ,
      (if δ ≤ maxFin (n + 1) v then max δ (secondMax (n + 1) v) - c else 0) =
        ∑ i, Fi c δ i (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i v) := by
    intro v
    rw [integrand_decomp]
    rfl
  unfold reserveObj
  simp_rw [hpt]
  rw [integral_finset_sum _ (fun i _ => hIi i)]
  simp_rw [hT]
  simp

end integrals

section analysis

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

open Filter Topology

lemma real_Ioi_eq (x : ℝ) : μ.real (Set.Ioi x) = 1 - cdf μ x := by
  unfold cdf
  rw [ProbabilityTheory.cdf_eq_real, ← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

lemma fval_eq (c x : ℝ) : fval μ c x = (x - c) * (1 - cdf μ x) := by
  unfold fval; rw [real_Ioi_eq]

lemma cdf_le_one' (x : ℝ) : cdf μ x ≤ 1 := ProbabilityTheory.cdf_le_one μ x

lemma cdf_mono : Monotone (cdf μ) := ProbabilityTheory.monotone_cdf μ

lemma atom_zero_pos (hR : RegularPos μ) {x : ℝ} (hx : 0 < x) : μ {x} = 0 := by
  have hac := hR.2.2.2.1
  have : μ.restrict (Set.Ioi 0) {x} = 0 := hac (Real.volume_singleton)
  rw [Measure.restrict_apply (measurableSet_singleton x)] at this
  rwa [show ({x} : Set ℝ) ∩ Set.Ioi 0 = {x} from
    Set.inter_eq_left.2 (Set.singleton_subset_iff.2 hx)] at this

lemma cdf_contAt (hR : RegularPos μ) {x : ℝ} (hx : 0 < x) : ContinuousAt (cdf μ) x := by
  have hmono := cdf_mono μ
  rw [continuousAt_iff_continuous_left'_right']
  constructor
  · rw [hmono.continuousWithinAt_Iio_iff_leftLim_eq]
    have h1 := (ProbabilityTheory.cdf μ).measure_singleton x
    rw [ProbabilityTheory.measure_cdf, atom_zero_pos μ hR hx] at h1
    have h2 : cdf μ x - Function.leftLim (cdf μ) x ≤ 0 := by
      have := (ENNReal.ofReal_eq_zero).1 h1.symm
      exact this
    have h3 : Function.leftLim (cdf μ) x ≤ cdf μ x := Monotone.leftLim_le hmono le_rfl
    unfold cdf at *
    linarith
  · exact ((ProbabilityTheory.cdf μ).right_continuous x).mono Set.Ioi_subset_Ici_self

lemma cdf_contWithin (hR : RegularPos μ) {x : ℝ} (hx : 0 ≤ x) (s : Set ℝ) (hs : s ⊆ Set.Ici 0) :
    ContinuousWithinAt (cdf μ) s x := by
  rcases eq_or_lt_of_le hx with h | h
  · subst h
    exact ((ProbabilityTheory.cdf μ).right_continuous 0).mono hs
  · exact (cdf_contAt μ hR h).continuousWithinAt

/-- The posted-price profit as a function of the cdf. -/
noncomputable def fG (c : ℝ) (x : ℝ) : ℝ := (x - c) * (1 - cdf μ x)

lemma fG_hasDeriv (hR : RegularPos μ) (c : ℝ) {x : ℝ} (hx : 0 < x) (hx1 : cdf μ x < 1) :
    HasDerivAt (fG μ c) ((1 - cdf μ x) - (x - c) * deriv (cdf μ) x) x := by
  have hd := (hR.2.2.2.2.1 x hx hx1).1
  have h1 : HasDerivAt (fun p => p - c) 1 x := (hasDerivAt_id x).sub_const c
  have h2 : HasDerivAt (fun p => 1 - cdf μ p) (-deriv (cdf μ) x) x := hd.const_sub 1
  have := h1.mul h2
  exact this.congr_deriv (by ring)

lemma fG_deriv_eq (hR : RegularPos μ) (c : ℝ) {x : ℝ} (hx : 0 < x) (hx1 : cdf μ x < 1) :
    (1 - cdf μ x) - (x - c) * deriv (cdf μ) x = deriv (cdf μ) x * (c - phi μ x) := by
  have hg := (hR.2.2.2.2.1 x hx hx1).2
  unfold phi
  field_simp
  ring

lemma fG_contOn (hR : RegularPos μ) (c : ℝ) {a b : ℝ} (ha : 0 ≤ a) :
    ContinuousOn (fG μ c) (Set.Icc a b) := by
  intro x hx
  have hx0 : 0 ≤ x := le_trans ha hx.1
  unfold fG
  apply ContinuousWithinAt.mul
  · exact (continuous_id.sub continuous_const).continuousWithinAt
  · apply ContinuousWithinAt.sub continuousWithinAt_const
    exact cdf_contWithin μ hR hx0 _ (fun y hy => le_trans ha hy.1)

lemma fG_mono (hR : RegularPos μ) (c : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (h : ∀ x, a < x → x < b → cdf μ x < 1 ∧ phi μ x < c) : fG μ c a ≤ fG μ c b := by
  have hmon : MonotoneOn (fG μ c) (Set.Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (fG_contOn μ hR c ha)
    · rw [interior_Icc]
      intro x hx
      exact (fG_hasDeriv μ hR c (lt_of_le_of_lt ha hx.1) (h x hx.1 hx.2).1).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      have hx0 : 0 < x := lt_of_le_of_lt ha hx.1
      obtain ⟨h1, h2⟩ := h x hx.1 hx.2
      rw [(fG_hasDeriv μ hR c hx0 h1).deriv, fG_deriv_eq μ hR c hx0 h1]
      exact mul_nonneg (hR.2.2.2.2.1 x hx0 h1).2.le (by linarith)
  exact hmon ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

lemma fG_anti (hR : RegularPos μ) (c : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (h : ∀ x, a < x → x < b → cdf μ x < 1 ∧ c < phi μ x) : fG μ c b ≤ fG μ c a := by
  have hmon : AntitoneOn (fG μ c) (Set.Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) (fG_contOn μ hR c ha)
    · rw [interior_Icc]
      intro x hx
      exact (fG_hasDeriv μ hR c (lt_of_le_of_lt ha hx.1) (h x hx.1 hx.2).1).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      have hx0 : 0 < x := lt_of_le_of_lt ha hx.1
      obtain ⟨h1, h2⟩ := h x hx.1 hx.2
      rw [(fG_hasDeriv μ hR c hx0 h1).deriv, fG_deriv_eq μ hR c hx0 h1]
      exact mul_nonpos_of_nonneg_of_nonpos (hR.2.2.2.2.1 x hx0 h1).2.le (by linarith)
  exact hmon ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

lemma tail_tendsto (hR : RegularPos μ) :
    Tendsto (fun x : ℝ => x * μ.real (Set.Ioi x)) atTop (𝓝 0) := by
  have hint : Integrable (fun y : ℝ => y) μ := hR.2.1
  have hI : Tendsto (fun x : ℝ => ∫ y, (Set.Ioi x).indicator (fun y => y) y ∂μ) atTop
      (𝓝 (∫ _y, (0 : ℝ) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun y => |y|)
    · exact Eventually.of_forall (fun x =>
        (aestronglyMeasurable_id.indicator measurableSet_Ioi))
    · exact Eventually.of_forall (fun x => Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs]
        by_cases hy : y ∈ Set.Ioi x
        · rw [Set.indicator_of_mem hy]
        · rw [Set.indicator_of_notMem hy]; simp))
    · exact hint.abs
    · refine Eventually.of_forall (fun y => ?_)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop y] with x hx
      rw [Set.indicator_of_notMem (by simp [hx])]
  simp only [integral_zero] at hI
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hI
  · filter_upwards [eventually_ge_atTop 0] with x hx
    exact mul_nonneg hx measureReal_nonneg
  · filter_upwards [eventually_ge_atTop 0] with x hx
    rw [integral_indicator measurableSet_Ioi]
    have h1 : ∫ _y in Set.Ioi x, x ∂μ = x * μ.real (Set.Ioi x) := by
      rw [setIntegral_const, smul_eq_mul, mul_comm]
    rw [← h1]
    apply setIntegral_mono_on (integrableOn_const) hint.integrableOn measurableSet_Ioi
    intro y hy; exact (le_of_lt hy)

/-- Facts about `p* = φ^{-1}(c)`. -/
lemma below_pstar (c : ℝ) {x : ℝ} (hx : 0 < x) (hxp : x < phiInv μ c) :
    cdf μ x < 1 ∧ phi μ x < c := by
  have hnot : x ∉ {x : ℝ | 0 < x ∧ (cdf μ x < 1 → c ≤ phi μ x)} := by
    intro hmem
    have := csInf_le ⟨0, fun y hy => hy.1.le⟩ hmem
    unfold phiInv at hxp
    linarith
  simp only [Set.mem_setOf_eq, not_and, _root_.not_imp] at hnot
  obtain ⟨h1, h2⟩ := hnot hx
  exact ⟨h1, lt_of_not_ge h2⟩

lemma pstar_set_nonempty (hR : RegularPos μ) (c : ℝ) (hc0 : 0 ≤ c) :
    ({x : ℝ | 0 < x ∧ (cdf μ x < 1 → c ≤ phi μ x)}).Nonempty := by
  by_contra hS
  rw [Set.not_nonempty_iff_eq_empty] at hS
  have hall : ∀ x, 0 < x → cdf μ x < 1 ∧ phi μ x < c := by
    intro x hx
    have : x ∉ {x : ℝ | 0 < x ∧ (cdf μ x < 1 → c ≤ phi μ x)} := by rw [hS]; simp
    simp only [Set.mem_setOf_eq, not_and, _root_.not_imp] at this
    obtain ⟨h1, h2⟩ := this hx
    exact ⟨h1, lt_of_not_ge h2⟩
  set x0 := c + 1
  have hx0 : 0 < x0 := by simp only [x0]; linarith
  have hK : 0 < fG μ c x0 := by
    unfold fG
    have := (hall x0 hx0).1
    apply mul_pos (by simp only [x0]; linarith) (by linarith)
  have hev := (tail_tendsto μ hR).eventually (gt_mem_nhds hK)
  obtain ⟨x, hx⟩ := (hev.and (eventually_ge_atTop x0)).exists
  have hmono := fG_mono μ hR c hx0.le hx.2 (fun y hy _ => hall y (lt_trans hx0 hy))
  have hfx : fG μ c x ≤ x * μ.real (Set.Ioi x) := by
    unfold fG
    rw [real_Ioi_eq]
    have := cdf_le_one' μ x
    apply mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  linarith [hx.1]

lemma pstar_ge (hR : RegularPos μ) (c : ℝ) (hc0 : 0 ≤ c) (hc : ∀ x, x < c → cdf μ x < 1) :
    c ≤ phiInv μ c := by
  apply le_csInf (pstar_set_nonempty μ hR c hc0)
  rintro y ⟨hy0, hy⟩
  by_cases h1 : cdf μ y < 1
  · have h2 := hy h1
    have hg := (hR.2.2.2.2.1 y hy0 h1).2
    have : 0 ≤ (1 - cdf μ y) / deriv (cdf μ) y := div_nonneg (by linarith) hg.le
    unfold phi at h2
    linarith
  · by_contra hlt
    exact h1 (hc y (lt_of_not_ge hlt))

lemma above_pstar (hR : RegularPos μ) (hI : IncVV μ) (c : ℝ) (hc0 : 0 ≤ c) {x : ℝ}
    (hxp : phiInv μ c < x) (hx1 : cdf μ x < 1) : c < phi μ x := by
  obtain ⟨y, ⟨hy0, hy⟩, hyx⟩ := exists_lt_of_csInf_lt (pstar_set_nonempty μ hR c hc0) hxp
  have hx0 : 0 < x := lt_trans hy0 hyx
  by_cases h1 : cdf μ y < 1
  · exact lt_of_le_of_lt (hy h1) (hI ⟨hy0, h1⟩ ⟨hx0, hx1⟩ hyx)
  · exact absurd (lt_of_le_of_lt (cdf_mono μ hyx.le) hx1) (by linarith [cdf_le_one' μ y])

lemma fG_le_pstar_of_ge (hR : RegularPos μ) (hI : IncVV μ) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : ∀ x, x < c → cdf μ x < 1) {a b : ℝ} (ha : phiInv μ c ≤ a) (hab : a ≤ b) :
    fG μ c b ≤ fG μ c a := by
  have hp := pstar_ge μ hR c hc0 hc
  have ha0 : 0 ≤ a := le_trans hc0 (le_trans hp ha)
  by_cases hb : cdf μ b < 1
  · apply fG_anti μ hR c ha0 hab
    intro x hax hxb
    have hx1 : cdf μ x < 1 := lt_of_le_of_lt (cdf_mono μ hxb.le) hb
    exact ⟨hx1, above_pstar μ hR hI c hc0 (lt_of_le_of_lt ha hax) hx1⟩
  · have hb1 : cdf μ b = 1 := le_antisymm (cdf_le_one' μ b) (not_lt.1 hb)
    unfold fG
    rw [hb1, sub_self, mul_zero]
    exact mul_nonneg (by linarith) (by linarith [cdf_le_one' μ a])

lemma fG_le_pstar (hR : RegularPos μ) (hI : IncVV μ) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : ∀ x, x < c → cdf μ x < 1) {a : ℝ} (ha : 0 ≤ a) :
    fG μ c a ≤ fG μ c (phiInv μ c) := by
  rcases le_total a (phiInv μ c) with h | h
  · apply fG_mono μ hR c ha h
    intro x hax hxp
    exact below_pstar μ c (lt_of_le_of_lt ha hax) hxp
  · exact fG_le_pstar_of_ge μ hR hI c hc0 hc le_rfl h

lemma fval_dom (hR : RegularPos μ) (hI : IncVV μ) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : ∀ x, x < c → cdf μ x < 1) {δ : ℝ} (hδ : 0 ≤ δ) (M : ℝ) :
    fval μ c (max δ M) ≤ fval μ c (max (phiInv μ c) M) := by
  rw [fval_eq, fval_eq]
  change fG μ c (max δ M) ≤ fG μ c (max (phiInv μ c) M)
  rcases le_total (phiInv μ c) M with h | h
  · rw [max_eq_right h]
    exact fG_le_pstar_of_ge μ hR hI c hc0 hc h (le_max_right _ _)
  · rw [max_eq_left h]
    exact fG_le_pstar μ hR hI c hc0 hc (le_trans hδ (le_max_left _ _))

end analysis

/-- Core result: in a second-price auction with `m ≥ 1` i.i.d. bidders, cost `c ≤ sup 𝒳` and
values whose only possible atom is at a point where it does not matter, the reserve
`φ^{-1}(c)` is optimal. -/
theorem core (m : ℕ) (hm : 1 ≤ m) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hR : RegularPos μ) (hI : IncVV μ) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : ∀ x, x < c → cdf μ x < 1)
    (hatom : ∀ p, 0 ≤ p → (p - c) * μ.real {p} = 0) :
    0 ≤ phiInv μ c ∧
      ∀ δ : ℝ, 0 ≤ δ → reserveObj m μ c δ ≤ reserveObj m μ c (phiInv μ c) := by
  have hp0 : 0 ≤ phiInv μ c := le_trans hc0 (pstar_ge μ hR c hc0 hc)
  refine ⟨hp0, fun δ hδ => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hint : Integrable (fun x : ℝ => x) μ := hR.2.1
  rw [reserveObj_eq μ hint c δ hδ hatom, reserveObj_eq μ hint c _ hp0 hatom]
  have hintg : ∀ d, 0 ≤ d → Integrable (fun y => fval μ c (max d (maxFin n y)))
      (Measure.pi (fun _ : Fin n => μ)) := by
    intro d hd
    have := (integrable_Fi μ hint c d hd (0 : Fin (n + 1))).integral_prod_right
    refine this.congr (Filter.Eventually.of_forall (fun y => ?_))
    exact inner_Fi μ c d hd hatom (0 : Fin (n + 1)) y
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono (hintg δ hδ) (hintg _ hp0)
  intro y
  exact fval_dom μ hR hI c hc0 hc hδ _

end AdInterm.SPE.Res

open MeasureTheory Filter Topology

namespace AdInterm.SPE.L31

open AdInterm.SPE AdInterm.SPE.Res

section psiFacts

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma T_nonempty (hR : RegularPos μ) (w : ℝ) :
    ({x : ℝ | 0 < x ∧ (cdf μ x < 1 → w ≤ phi μ x)}).Nonempty := by
  obtain ⟨x, hx0, hx⟩ := pstar_set_nonempty μ hR (max w 0) (le_max_right _ _)
  exact ⟨x, hx0, fun h => le_trans (le_max_left _ _) (hx h)⟩

lemma phiInv_mono (hR : RegularPos μ) : Monotone (phiInv μ) := by
  intro w w' hww
  apply csInf_le_csInf ⟨0, fun y hy => hy.1.le⟩ (T_nonempty μ hR w')
  rintro x ⟨hx0, hx⟩
  exact ⟨hx0, fun h => le_trans hww (hx h)⟩

lemma exists_pos_cdf_lt (hR : RegularPos μ) : ∃ x, 0 < x ∧ cdf μ x < 1 := by
  have h1 : ∀ᶠ x in 𝓝[>] (0 : ℝ), cdf μ x < 1 :=
    (((ProbabilityTheory.cdf μ).right_continuous 0).mono Set.Ioi_subset_Ici_self).eventually
      (gt_mem_nhds hR.2.2.1)
  obtain ⟨x, hx1, hx0⟩ := (h1.and self_mem_nhdsWithin).exists
  exact ⟨x, hx0, hx1⟩

lemma zproj_pos (hR : RegularPos μ) (hI : IncVV μ) : 0 < zproj μ := by
  have hz0 : 0 ≤ zproj μ := le_trans le_rfl (pstar_ge μ hR 0 le_rfl (fun x hx =>
    lt_of_le_of_lt (cdf_mono μ hx.le) hR.2.2.1))
  rcases eq_or_lt_of_le hz0 with h | h
  · exfalso
    obtain ⟨x, hx0, hx1⟩ := exists_pos_cdf_lt μ hR
    have hanti := fG_anti μ hR 0 le_rfl hx0.le (fun y hy hyx => by
      have hy1 : cdf μ y < 1 := lt_of_le_of_lt (cdf_mono μ hyx.le) hx1
      refine ⟨hy1, above_pstar μ hR hI 0 le_rfl ?_ hy1⟩
      change phiInv μ 0 < y
      rw [← zproj, ← h]; exact hy)
    unfold fG at hanti
    simp at hanti
    have : 0 < x * (1 - cdf μ x) := mul_pos hx0 (by linarith)
    linarith
  · exact h

lemma phi_contAt (hR : RegularPos μ) {x : ℝ} (hx0 : 0 < x) (hx1 : cdf μ x < 1) :
    ContinuousAt (phi μ) x := by
  have hU : {y : ℝ | 0 < y ∧ cdf μ y < 1} ∈ 𝓝 x := by
    have h1 : ∀ᶠ y in 𝓝 x, 0 < y := lt_mem_nhds hx0
    have h2 : ∀ᶠ y in 𝓝 x, cdf μ y < 1 := (cdf_contAt μ hR hx0).eventually (gt_mem_nhds hx1)
    exact h1.and h2
  have hg : ContinuousAt (deriv (cdf μ)) x := hR.2.2.2.2.2.continuousAt hU
  have hgx := (hR.2.2.2.2.1 x hx0 hx1).2
  unfold phi
  exact continuousAt_id.sub ((continuousAt_const.sub (cdf_contAt μ hR hx0)).div hg hgx.ne')

lemma phi_le_self (hR : RegularPos μ) {x : ℝ} (hx0 : 0 < x) (hx1 : cdf μ x < 1) :
    phi μ x ≤ x := by
  have hg := (hR.2.2.2.2.1 x hx0 hx1).2
  have : 0 ≤ (1 - cdf μ x) / deriv (cdf μ) x := div_nonneg (by linarith) hg.le
  unfold phi; linarith

lemma phi_nonneg_of_ge (hR : RegularPos μ) (hI : IncVV μ) {x : ℝ} (hzx : zproj μ ≤ x)
    (hx1 : cdf μ x < 1) : 0 ≤ phi μ x := by
  rcases eq_or_lt_of_le hzx with h | h
  · subst h
    have hz0 := zproj_pos μ hR hI
    by_contra hneg
    push Not at hneg
    have hev : ∀ᶠ y in 𝓝 (zproj μ), phi μ y < 0 ∧ cdf μ y < 1 :=
      ((phi_contAt μ hR hz0 hx1).eventually (gt_mem_nhds hneg)).and
        ((cdf_contAt μ hR hz0).eventually (gt_mem_nhds hx1))
    obtain ⟨y, ⟨hy1, hy2⟩, hy3⟩ := ((hev.filter_mono
      (nhdsWithin_le_nhds (s := Set.Ioi (zproj μ)))).and
      (self_mem_nhdsWithin : Set.Ioi (zproj μ) ∈ 𝓝[>] (zproj μ))).exists
    have := above_pstar μ hR hI 0 le_rfl hy3 hy2
    linarith
  · exact (above_pstar μ hR hI 0 le_rfl h hx1).le

lemma supX_ge {x : ℝ} (hex : ∃ y, cdf μ y = 1) (hx1 : cdf μ x < 1) : x ≤ supX μ := by
  apply le_csInf hex
  intro y hy
  by_contra h
  push Not at h
  have := cdf_mono μ h.le
  have hy' : cdf μ y = 1 := hy
  linarith

lemma supX_le (hR : RegularPos μ) {x : ℝ} (hx : cdf μ x = 1) : supX μ ≤ x := by
  show sInf {x : ℝ | cdf μ x = 1} ≤ x
  refine csInf_le ⟨0, fun y hy => ?_⟩ (show x ∈ {x : ℝ | cdf μ x = 1} from hx)
  by_contra h
  push Not at h
  have := cdf_mono μ h.le
  have hy' : cdf μ y = 1 := hy
  linarith [hR.2.2.1]

lemma supX_nonneg (hR : RegularPos μ) : 0 ≤ supX μ := by
  apply Real.sInf_nonneg
  intro y hy
  by_contra h
  push Not at h
  have := cdf_mono μ h.le
  have hy' : cdf μ y = 1 := hy
  linarith [hR.2.2.1]

lemma cdf_eq_one_of_not_lt {x : ℝ} (h : ¬ cdf μ x < 1) : cdf μ x = 1 :=
  le_antisymm (cdf_le_one' μ x) (not_lt.1 h)

lemma psi_nonneg (hR : RegularPos μ) (hI : IncVV μ) (x : ℝ) : 0 ≤ psi μ x := by
  unfold psi
  split_ifs with h1 h2
  · exact phi_nonneg_of_ge μ hR hI h2 h1
  · exact le_rfl
  · exact supX_nonneg μ hR

lemma psi_mono (hR : RegularPos μ) (hI : IncVV μ) : Monotone (psi μ) := by
  intro x y hxy
  have hz0 := zproj_pos μ hR hI
  by_cases hy1 : cdf μ y < 1
  · have hx1 : cdf μ x < 1 := lt_of_le_of_lt (cdf_mono μ hxy) hy1
    unfold psi
    rw [if_pos hx1, if_pos hy1]
    split_ifs with hzx hzy hzy
    · exact hI.monotoneOn ⟨lt_of_lt_of_le hz0 hzx, hx1⟩ ⟨lt_of_lt_of_le hz0 hzy, hy1⟩ hxy
    · exact absurd (le_trans hzx hxy) hzy
    · exact phi_nonneg_of_ge μ hR hI hzy hy1
    · exact le_rfl
  · have hex : ∃ y', cdf μ y' = 1 := ⟨y, cdf_eq_one_of_not_lt μ hy1⟩
    unfold psi
    rw [if_neg hy1]
    split_ifs with hx1 hzx
    · exact le_trans (phi_le_self μ hR (lt_of_lt_of_le hz0 hzx) hx1) (supX_ge μ hex hx1)
    · exact supX_nonneg μ hR
    · exact le_rfl

lemma isMech_psi (hR : RegularPos μ) (hI : IncVV μ) : IsMech (zproj μ, psi μ) :=
  ⟨(zproj_pos μ hR hI).le, (psi_mono μ hR hI).monotoneOn _, fun x _ => psi_nonneg μ hR hI x⟩

lemma S_psi_ge (hR : RegularPos μ) (hI : IncVV μ) {P x : ℝ} (hP : 0 < P)
    (hx : 0 ≤ x ∧ P ≤ psi μ x) : P ≤ x := by
  have hz0 := zproj_pos μ hR hI
  obtain ⟨hx0, hPx⟩ := hx
  unfold psi at hPx
  split_ifs at hPx with h1 h2
  · exact le_trans hPx (phi_le_self μ hR (lt_of_lt_of_le hz0 h2) h1)
  · linarith
  · exact le_trans hPx (supX_le μ hR (cdf_eq_one_of_not_lt μ h1))

lemma cost_le_sup_of_win (hR : RegularPos μ) (hI : IncVV μ) {P w : ℝ} (hw0 : 0 ≤ w)
    (hPw : P ≤ psi μ w) : ∀ y, y < P → cdf μ y < 1 := by
  intro y hy
  have hz0 := zproj_pos μ hR hI
  by_cases hw1 : cdf μ w < 1
  · have hpw : psi μ w ≤ w := by
      unfold psi; rw [if_pos hw1]
      split_ifs with hzw
      · exact phi_le_self μ hR (lt_of_lt_of_le hz0 hzw) hw1
      · exact hw0
    exact lt_of_le_of_lt (cdf_mono μ (by linarith)) hw1
  · unfold psi at hPw
    rw [if_neg hw1] at hPw
    by_contra hy1
    have := supX_le μ hR (cdf_eq_one_of_not_lt μ hy1)
    linarith

lemma ginv_psi_eq (hR : RegularPos μ) (hI : IncVV μ) {P : ℝ} (hP0 : 0 ≤ P)
    (hP : ∀ y, y < P → cdf μ y < 1) :
    max (zproj μ) (ginv (psi μ) P) = phiInv μ P := by
  rcases eq_or_lt_of_le hP0 with h | h
  · subst h
    have hS : {x : ℝ | 0 ≤ x ∧ 0 ≤ psi μ x} = Set.Ici 0 := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_Ici]
      exact ⟨fun h => h.1, fun h => ⟨h, psi_nonneg μ hR hI x⟩⟩
    unfold ginv
    rw [hS, csInf_Ici, max_eq_left (zproj_pos μ hR hI).le]
    rfl
  · have hS : {x : ℝ | 0 ≤ x ∧ P ≤ psi μ x} = {x : ℝ | 0 < x ∧ (cdf μ x < 1 → P ≤ phi μ x)} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hx
        have hPx := S_psi_ge μ hR hI h hx
        refine ⟨lt_of_lt_of_le h hPx, fun hx1 => ?_⟩
        have h2 := hx.2
        unfold psi at h2
        rw [if_pos hx1] at h2
        split_ifs at h2
        · exact h2
        · linarith
      · rintro ⟨hx0, hx⟩
        refine ⟨hx0.le, ?_⟩
        unfold psi
        split_ifs with hx1 hzx
        · exact hx hx1
        · exfalso; apply hzx
          apply csInf_le ⟨0, fun y hy => hy.1.le⟩
          exact ⟨hx0, fun _ => le_trans h.le (hx hx1)⟩
        · apply le_csInf ⟨x, cdf_eq_one_of_not_lt μ hx1⟩
          intro y hy
          by_contra hlt
          push Not at hlt
          have := hP y hlt
          simp only [Set.mem_setOf_eq] at hy
          linarith
    unfold ginv
    rw [hS]
    change max (zproj μ) (phiInv μ P) = phiInv μ P
    exact max_eq_right (phiInv_mono μ hR hP0)

end psiFacts

section mech

/-- Realized profit of the one-stage intermediary with mechanism `mech`, cost `P`, values `v`. -/
noncomputable def Imech (m : ℕ) (mech : Mechanism) (P : ℝ) (v : Fin m → ℝ) : ℝ :=
  if mech.1 ≤ maxFin m v ∧ P ≤ mech.2 (maxFin m v) then
    max (max mech.1 (ginv mech.2 P)) (secondMax m v) - P else 0

/-- Second-price revenue integrand with reserve `δ` and cost `P`. -/
noncomputable def Ires (m : ℕ) (P δ : ℝ) (v : Fin m → ℝ) : ℝ :=
  if δ ≤ maxFin m v then max δ (secondMax m v) - P else 0

lemma secondMax_le_maxFin {n : ℕ} (v : Fin (n + 1) → ℝ) (h0 : 0 ≤ maxFin (n + 1) v) :
    secondMax (n + 1) v ≤ maxFin (n + 1) v := by
  obtain ⟨i, hi⟩ := exists_argmax v
  rw [secondMax_eq v i hi]
  rw [maxFin_eq_of_max v i hi] at h0 ⊢
  exact maxFin_le _ _ h0 (fun j => hi _)

lemma ginv_le {Y : ℝ → ℝ} {P w : ℝ} (hw0 : 0 ≤ w) (hw : P ≤ Y w) : ginv Y P ≤ w :=
  csInf_le ⟨0, fun x hx => hx.1⟩ ⟨hw0, hw⟩

lemma charge_le {n : ℕ} {mech : Mechanism} (hm : IsMech mech) {P : ℝ} {v : Fin (n + 1) → ℝ}
    (hwin : mech.1 ≤ maxFin (n + 1) v ∧ P ≤ mech.2 (maxFin (n + 1) v)) :
    max (max mech.1 (ginv mech.2 P)) (secondMax (n + 1) v) ≤ maxFin (n + 1) v := by
  have hw0 : 0 ≤ maxFin (n + 1) v := le_trans hm.1 hwin.1
  exact max_le (max_le hwin.1 (ginv_le hw0 hwin.2)) (secondMax_le_maxFin v hw0)

lemma Imech_eq_Ires {m : ℕ} {mech : Mechanism} (hm : IsMech mech) {P : ℝ}
    (hne : ({x : ℝ | 0 ≤ x ∧ P ≤ mech.2 x}).Nonempty) (v : Fin m → ℝ)
    (hv : maxFin m v ≠ max mech.1 (ginv mech.2 P)) :
    Imech m mech P v = Ires m P (max mech.1 (ginv mech.2 P)) v := by
  unfold Imech Ires
  by_cases hwin : mech.1 ≤ maxFin m v ∧ P ≤ mech.2 (maxFin m v)
  · have hw0 : 0 ≤ maxFin m v := le_trans hm.1 hwin.1
    rw [if_pos hwin, if_pos (max_le hwin.1 (ginv_le hw0 hwin.2))]
  · rw [if_neg hwin, if_neg]
    intro hδ
    have hlt : max mech.1 (ginv mech.2 P) < maxFin m v := lt_of_le_of_ne hδ (Ne.symm hv)
    have hr : mech.1 ≤ maxFin m v := le_trans (le_max_left _ _) hδ
    have hg : ginv mech.2 P < maxFin m v := lt_of_le_of_lt (le_max_right _ _) hlt
    obtain ⟨x, ⟨hx0, hxP⟩, hxw⟩ := exists_lt_of_csInf_lt hne hg
    apply hwin
    refine ⟨hr, le_trans hxP ?_⟩
    exact hm.2.1 (Set.mem_Ici.2 hx0) (Set.mem_Ici.2 (le_trans hx0 hxw.le)) hxw.le

lemma Imech_empty {m : ℕ} {mech : Mechanism} (hm : IsMech mech) {P : ℝ}
    (he : ¬ ({x : ℝ | 0 ≤ x ∧ P ≤ mech.2 x}).Nonempty) (v : Fin m → ℝ) :
    Imech m mech P v = 0 := by
  unfold Imech
  rw [if_neg]
  rintro ⟨h1, h2⟩
  exact he ⟨_, le_trans hm.1 h1, h2⟩

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma null_maxFin_eq {n : ℕ} {δ : ℝ} (hδ : μ {δ} = 0) :
    (Measure.pi (fun _ : Fin (n + 1) => μ)) {v | maxFin (n + 1) v = δ} = 0 := by
  have hsub : {v : Fin (n + 1) → ℝ | maxFin (n + 1) v = δ} ⊆
      ⋃ i, (Function.eval i) ⁻¹' {δ} := by
    intro v hv
    obtain ⟨i, hi⟩ := exists_argmax v
    simp only [Set.mem_setOf_eq] at hv
    rw [maxFin_eq_of_max v i hi] at hv
    exact Set.mem_iUnion.2 ⟨i, hv⟩
  apply measure_mono_null hsub
  apply measure_iUnion_null
  intro i
  rw [(measurePreserving_eval (fun _ : Fin (n + 1) => μ) i).measure_preimage
    (measurableSet_singleton δ).nullMeasurableSet]
  exact hδ

lemma ae_maxFin_le {n : ℕ} {x0 : ℝ} (hx0 : 0 ≤ x0) (h : μ (Set.Ioi x0) = 0) :
    ∀ᵐ v ∂(Measure.pi (fun _ : Fin (n + 1) => μ)), maxFin (n + 1) v ≤ x0 := by
  have hnull : (Measure.pi (fun _ : Fin (n + 1) => μ)) (⋃ i, (Function.eval i) ⁻¹' Set.Ioi x0) = 0 := by
    apply measure_iUnion_null
    intro i
    rw [(measurePreserving_eval (fun _ : Fin (n + 1) => μ) i).measure_preimage
      measurableSet_Ioi.nullMeasurableSet]
    exact h
  rw [ae_iff]
  apply measure_mono_null _ hnull
  intro v hv
  simp only [Set.mem_setOf_eq, not_le] at hv
  by_contra hc
  simp only [Set.mem_iUnion, Set.mem_preimage, Function.eval, Set.mem_Ioi, not_exists,
    not_lt] at hc
  exact absurd (maxFin_le v x0 hx0 hc) (not_le.2 hv)

end mech

section final

lemma secondMax_eq_dite (m : ℕ) (v : Fin m → ℝ) :
    secondMax m v =
      if h : (Finset.univ.filter (fun p : Fin m × Fin m => p.1 ≠ p.2)).Nonempty then
        (Finset.univ.filter (fun p : Fin m × Fin m => p.1 ≠ p.2)).sup' h
          (fun p => min (v p.1) (v p.2)) else 0 := by
  unfold secondMax
  split_ifs with h
  · have : (Finset.univ.filter (fun p : Fin m × Fin m => p.1 ≠ p.2)).sup
        (fun p => min ((v p.1 : WithBot ℝ)) ((v p.2 : WithBot ℝ))) =
        (((Finset.univ.filter (fun p : Fin m × Fin m => p.1 ≠ p.2)).sup' h
          (fun p => min (v p.1) (v p.2)) : ℝ) : WithBot ℝ) := by
      rw [Finset.coe_sup']
      rfl
    rw [this]
    rfl
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h]
    rfl

lemma measurable_secondMax (m : ℕ) : Measurable (secondMax m) := by
  have : secondMax m = fun v => if h : (Finset.univ.filter
      (fun p : Fin m × Fin m => p.1 ≠ p.2)).Nonempty then
        (Finset.univ.filter (fun p : Fin m × Fin m => p.1 ≠ p.2)).sup' h
          (fun p => min (v p.1) (v p.2)) else 0 := by
    funext v; exact secondMax_eq_dite m v
  rw [this]
  by_cases h : (Finset.univ.filter (fun p : Fin m × Fin m => p.1 ≠ p.2)).Nonempty
  · simp only [h, dite_true]
    have h2 := Finset.measurable_sup' h
      (f := fun (p : Fin m × Fin m) (v : Fin m → ℝ) => min (v p.1) (v p.2))
      (fun p _ => (measurable_pi_apply p.1).min (measurable_pi_apply p.2))
    convert h2 using 1
    funext v
    rw [Finset.sup'_apply]
  · simp only [h, dite_false]
    exact measurable_const

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma buyer_atomless (hV : BuyerLaw μ) (p : ℝ) : μ {p} = 0 := by
  rcases lt_or_ge 0 p with h | h
  · exact atom_zero_pos μ hV.1 h
  · have h1 : μ (Set.Iic 0) = 0 := by
      rw [← ProbabilityTheory.ofReal_cdf]
      have : ProbabilityTheory.cdf μ 0 = 0 := hV.2
      rw [this]; simp
    exact measure_mono_null (Set.singleton_subset_iff.2 (Set.mem_Iic.2 h)) h1

lemma Ipsi_nonneg (hR : RegularPos μ) (hI : IncVV μ) {n : ℕ} {P : ℝ} (hP0 : 0 ≤ P)
    (v : Fin (n + 1) → ℝ) : 0 ≤ Imech (n + 1) (zproj μ, psi μ) P v := by
  unfold Imech
  split_ifs with hwin
  · simp only at hwin ⊢
    have hz0 := zproj_pos μ hR hI
    rcases eq_or_lt_of_le hP0 with h | h
    · subst h
      have := le_trans (le_max_left _ _) (le_max_left (max (zproj μ) (ginv (psi μ) 0))
        (secondMax (n + 1) v))
      linarith
    · have hg : P ≤ ginv (psi μ) P := by
        show P ≤ sInf {x : ℝ | 0 ≤ x ∧ P ≤ psi μ x}
        apply le_csInf (⟨maxFin (n + 1) v, le_trans hz0.le hwin.1, hwin.2⟩ :
          ({x : ℝ | 0 ≤ x ∧ P ≤ psi μ x}).Nonempty)
        intro x hx
        exact S_psi_ge μ hR hI h hx
      have := le_trans (le_max_right _ _) (le_max_left (max (zproj μ) (ginv (psi μ) P))
        (secondMax (n + 1) v))
      linarith
  · exact le_rfl

lemma S_psi_nonempty (hR : RegularPos μ) (hI : IncVV μ) {P : ℝ} (hP0 : 0 ≤ P)
    (hP : ∀ y, y < P → cdf μ y < 1) :
    ({x : ℝ | 0 ≤ x ∧ P ≤ psi μ x}).Nonempty := by
  rcases eq_or_lt_of_le hP0 with h | h
  · subst h; exact ⟨0, le_rfl, psi_nonneg μ hR hI 0⟩
  · obtain ⟨x, hx0, hx⟩ := T_nonempty μ hR P
    refine ⟨x, hx0.le, ?_⟩
    unfold psi
    split_ifs with hx1 hzx
    · exact hx hx1
    · exfalso; apply hzx
      apply csInf_le ⟨0, fun y hy => hy.1.le⟩
      exact ⟨hx0, fun _ => le_trans h.le (hx hx1)⟩
    · apply le_csInf ⟨x, cdf_eq_one_of_not_lt μ hx1⟩
      intro y hy
      by_contra hlt
      push Not at hlt
      have := hP y hlt
      have hy' : cdf μ y = 1 := hy
      linarith

lemma integral_Imech_eq {n : ℕ} {mech : Mechanism} (hm : IsMech mech) {P : ℝ}
    (hatom : ∀ p, μ {p} = 0)
    (hne : ({x : ℝ | 0 ≤ x ∧ P ≤ mech.2 x}).Nonempty) :
    ∫ v, Imech (n + 1) mech P v ∂(Measure.pi (fun _ : Fin (n + 1) => μ)) =
      reserveObj (n + 1) μ P (max mech.1 (ginv mech.2 P)) := by
  unfold reserveObj
  apply integral_congr_ae
  have hnull := null_maxFin_eq μ (n := n) (hatom (max mech.1 (ginv mech.2 P)))
  rw [Filter.EventuallyEq, ae_iff]
  apply measure_mono_null _ hnull
  intro v hv
  by_contra hc
  exact hv (Imech_eq_Ires hm hne v hc)

lemma perP (hV : BuyerLaw μ) (hI : IncVV μ) {n : ℕ} {mech : Mechanism} (hm : IsMech mech)
    {P : ℝ} (hP0 : 0 ≤ P) :
    ∫ v, Imech (n + 1) mech P v ∂(Measure.pi (fun _ : Fin (n + 1) => μ)) ≤
      ∫ v, Imech (n + 1) (zproj μ, psi μ) P v ∂(Measure.pi (fun _ : Fin (n + 1) => μ)) := by
  have hR := hV.1
  have hatom := buyer_atomless μ hV
  have hpsi0 : 0 ≤ ∫ v, Imech (n + 1) (zproj μ, psi μ) P v
      ∂(Measure.pi (fun _ : Fin (n + 1) => μ)) :=
    integral_nonneg (fun v => Ipsi_nonneg μ hR hI hP0 v)
  by_cases hP : ∀ y, y < P → cdf μ y < 1
  · have hpsi := integral_Imech_eq μ (n := n) (isMech_psi μ hR hI) hatom
      (S_psi_nonempty μ hR hI hP0 hP)
    simp only at hpsi
    rw [hpsi, ginv_psi_eq μ hR hI hP0 hP]
    by_cases hne : ({x : ℝ | 0 ≤ x ∧ P ≤ mech.2 x}).Nonempty
    · rw [integral_Imech_eq μ hm hatom hne]
      have hcore := core (n + 1) (by omega) μ hR hI P hP0 hP (fun p _ => by
        rw [measureReal_def, hatom p]; simp)
      exact hcore.2 _ (le_trans hm.1 (le_max_left _ _))
    · have : (fun v => Imech (n + 1) mech P v) = fun _ => 0 := by
        funext v; exact Imech_empty hm hne v
      rw [this, integral_zero]
      rw [← ginv_psi_eq μ hR hI hP0 hP, ← hpsi]
      exact hpsi0
  · push Not at hP
    obtain ⟨y, hyP, hy1⟩ := hP
    have hy1' : cdf μ y = 1 := le_antisymm (cdf_le_one' μ y) hy1
    have hy0 : 0 ≤ y := by
      by_contra h
      push Not at h
      have := cdf_mono μ h.le
      linarith [hR.2.2.1]
    have hIoi : μ (Set.Ioi y) = 0 := by
      have h1 : μ.real (Set.Ioi y) = 0 := by rw [real_Ioi_eq, hy1']; ring
      rwa [measureReal_eq_zero_iff] at h1
    refine le_trans ?_ hpsi0
    apply integral_nonpos_of_ae
    filter_upwards [ae_maxFin_le μ (n := n) hy0 hIoi] with v hv
    unfold Imech
    split_ifs with hwin
    · have := charge_le hm hwin
      simp only [Pi.zero_apply]
      linarith
    · exact le_rfl

theorem lemma31 (m : ℕ) (hm : 1 ≤ m)
    (hV : BuyerLaw μ) (hVinc : IncVV μ)
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (rS : ℝ) (hrS0 : 0 ≤ rS) :
    IsMech (zproj μ, psi μ) ∧
      ∀ mech : Mechanism, IsMech mech →
        singleProfit m μ η rS mech ≤ singleProfit m μ η rS (zproj μ, psi μ) := by
  have hR := hV.1
  refine ⟨isMech_psi μ hR hVinc, fun mech hmech => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hsp : ∀ mech' : Mechanism, singleProfit (n + 1) μ η rS mech' =
      ∫ x, Imech (n + 1) mech' (max rS x.2) x.1
        ∂((Measure.pi (fun _ : Fin (n + 1) => μ)).prod η) := fun _ => rfl
  have hint : ∀ i : Fin (n + 1), Integrable (fun v : Fin (n + 1) → ℝ => v i)
      (Measure.pi (fun _ : Fin (n + 1) => μ)) := fun i => integrable_coord μ hR.2.1 i
  -- the psi-integrand, rewritten with `φ^{-1}` to see measurability
  have hH : (fun x : (Fin (n + 1) → ℝ) × ℝ => Imech (n + 1) (zproj μ, psi μ) (max rS x.2) x.1) =
      fun x => if zproj μ ≤ maxFin (n + 1) x.1 ∧ max rS x.2 ≤ psi μ (maxFin (n + 1) x.1) then
        max (phiInv μ (max rS x.2)) (secondMax (n + 1) x.1) - max rS x.2 else 0 := by
    funext x
    unfold Imech
    simp only
    split_ifs with hwin
    · rw [ginv_psi_eq μ hR hVinc (le_trans hrS0 (le_max_left _ _))
        (cost_le_sup_of_win μ hR hVinc (le_trans (zproj_pos μ hR hVinc).le hwin.1) hwin.2)]
    · rfl
  have hmeasH : Measurable (fun x : (Fin (n + 1) → ℝ) × ℝ =>
      Imech (n + 1) (zproj μ, psi μ) (max rS x.2) x.1) := by
    rw [hH]
    have hmf : Measurable (fun x : (Fin (n + 1) → ℝ) × ℝ => maxFin (n + 1) x.1) :=
      (measurable_maxFin (n + 1)).comp measurable_fst
    have hmP : Measurable (fun x : (Fin (n + 1) → ℝ) × ℝ => max rS x.2) :=
      measurable_const.max measurable_snd
    have hpsi : Measurable (psi μ) := (psi_mono μ hR hVinc).measurable
    have hphi : Measurable (phiInv μ) := (phiInv_mono μ hR).measurable
    apply Measurable.ite
    · exact (measurableSet_le measurable_const hmf).inter
        (measurableSet_le hmP (hpsi.comp hmf))
    · exact ((hphi.comp hmP).max ((measurable_secondMax (n + 1)).comp measurable_fst)).sub hmP
    · exact measurable_const
  have hIpsi : Integrable (fun x : (Fin (n + 1) → ℝ) × ℝ =>
      Imech (n + 1) (zproj μ, psi μ) (max rS x.2) x.1)
      ((Measure.pi (fun _ : Fin (n + 1) => μ)).prod η) := by
    have hb : Integrable (fun x : (Fin (n + 1) → ℝ) × ℝ => ∑ i, |x.1 i|)
        ((Measure.pi (fun _ : Fin (n + 1) => μ)).prod η) := by
      have hb0 : Integrable (fun v : Fin (n + 1) → ℝ => ∑ i, |v i|)
          (Measure.pi (fun _ : Fin (n + 1) => μ)) :=
        integrable_finset_sum _ (fun i _ => (hint i).abs)
      exact (measurePreserving_fst (μ := Measure.pi (fun _ : Fin (n + 1) => μ))
        (ν := η)).integrable_comp_of_integrable hb0
    refine hb.mono' hmeasH.aestronglyMeasurable (Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (Ipsi_nonneg μ hR hVinc (le_trans hrS0
      (le_max_left _ _)) x.1)]
    refine le_trans ?_ (abs_maxFin_le x.1)
    unfold Imech
    split_ifs with hwin
    · have := charge_le (isMech_psi μ hR hVinc) hwin
      have h0 : 0 ≤ max rS x.2 := le_trans hrS0 (le_max_left _ _)
      have := le_abs_self (maxFin (n + 1) x.1)
      linarith
    · exact abs_nonneg _
  rw [hsp, hsp]
  by_cases hintm : Integrable (fun x : (Fin (n + 1) → ℝ) × ℝ =>
      Imech (n + 1) mech (max rS x.2) x.1) ((Measure.pi (fun _ : Fin (n + 1) => μ)).prod η)
  · rw [integral_prod_symm _ hintm, integral_prod_symm _ hIpsi]
    apply integral_mono hintm.integral_prod_right hIpsi.integral_prod_right
    intro D
    exact perP μ hV hVinc hmech (le_trans hrS0 (le_max_left _ _))
  · rw [integral_undef hintm]
    exact integral_nonneg (fun x => Ipsi_nonneg μ hR hVinc (le_trans hrS0 (le_max_left _ _)) x.1)

end final

end AdInterm.SPE.L31

open MeasureTheory Filter Topology

namespace AdInterm.SPE.G1

open AdInterm.SPE AdInterm.SPE.Res AdInterm.SPE.L31

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma cdf_zproj_lt (hR : RegularPos μ) (hI : IncVV μ) : cdf μ (zproj μ) < 1 := by
  have hz0 := zproj_pos μ hR hI
  by_contra h
  have hz1 : cdf μ (zproj μ) = 1 := cdf_eq_one_of_not_lt μ h
  obtain ⟨x0, hx00, hx01⟩ := exists_pos_cdf_lt μ hR
  have hx0z : x0 < zproj μ := by
    by_contra hc
    push Not at hc
    have := cdf_mono μ hc
    linarith
  have hev : ∀ᶠ b in 𝓝[<] (zproj μ), fG μ 0 x0 ≤ fG μ 0 b := by
    filter_upwards [Ioo_mem_nhdsLT hx0z] with b hb
    apply fG_mono μ hR 0 hx00.le hb.1.le
    intro x hx hxb
    exact below_pstar μ 0 (lt_trans hx00 hx) (lt_trans hxb hb.2)
  have hcont : ContinuousAt (fG μ 0) (zproj μ) := by
    unfold fG
    exact (continuousAt_id.sub continuousAt_const).mul
      (continuousAt_const.sub (cdf_contAt μ hR hz0))
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (zproj μ)))
  have hle := ge_of_tendsto hlim hev
  unfold fG at hle
  rw [hz1] at hle
  have : 0 < (x0 - 0) * (1 - cdf μ x0) := mul_pos (by linarith) (by linarith)
  linarith

lemma phi_zproj (hR : RegularPos μ) (hI : IncVV μ) : phi μ (zproj μ) = 0 := by
  have hz0 := zproj_pos μ hR hI
  have hz1 := cdf_zproj_lt μ hR hI
  apply le_antisymm
  · by_contra hpos
    push Not at hpos
    have hev : ∀ᶠ y in 𝓝 (zproj μ), 0 < phi μ y :=
      (phi_contAt μ hR hz0 hz1).eventually (lt_mem_nhds hpos)
    obtain ⟨y, hy, hy2⟩ := ((hev.filter_mono (nhdsWithin_le_nhds (s := Set.Iio (zproj μ)))).and
      (Ioo_mem_nhdsLT hz0)).exists
    have := (below_pstar μ 0 hy2.1 hy2.2).2
    linarith
  · exact phi_nonneg_of_ge μ hR hI le_rfl hz1

lemma tendsto_phi_atTop (hR : RegularPos μ) (hI : IncVV μ) (hall : ∀ x, cdf μ x < 1) :
    Tendsto (phi μ) atTop atTop := by
  rw [tendsto_atTop]
  intro L
  obtain ⟨x, hx0, hx⟩ := T_nonempty μ hR L
  filter_upwards [eventually_ge_atTop x] with y hy
  exact le_trans (hx (hall x))
    (hI.monotoneOn ⟨hx0, hall x⟩ ⟨lt_of_lt_of_le hx0 hy, hall y⟩ hy)

lemma cdf_supX (hR : RegularPos μ) (hex : ∃ x, cdf μ x = 1) : cdf μ (supX μ) = 1 := by
  have hev : ∀ᶠ y in 𝓝[>] (supX μ), cdf μ y = 1 := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    obtain ⟨x, hx, hxy⟩ := exists_lt_of_csInf_lt hex hy
    have hx' : cdf μ x = 1 := hx
    exact le_antisymm (cdf_le_one' μ y) (hx' ▸ cdf_mono μ hxy.le)
  have hlim : Tendsto (cdf μ) (𝓝[>] (supX μ)) (𝓝 (cdf μ (supX μ))) :=
    ((ProbabilityTheory.cdf μ).right_continuous (supX μ)).mono Set.Ioi_subset_Ici_self
  have h2 : Tendsto (cdf μ) (𝓝[>] (supX μ)) (𝓝 1) :=
    tendsto_const_nhds.congr' (hev.mono (fun y hy => hy.symm))
  exact tendsto_nhds_unique hlim h2

lemma supX_pos (hR : RegularPos μ) (hex : ∃ x, cdf μ x = 1) : 0 < supX μ := by
  rcases eq_or_lt_of_le (supX_nonneg μ hR) with h | h
  · have := cdf_supX μ hR hex
    rw [← h] at this
    linarith [hR.2.2.1]
  · exact h

lemma cdf_lt_of_lt_supX (hR : RegularPos μ) {y : ℝ} (hy : y < supX μ) : cdf μ y < 1 := by
  by_contra h
  have := supX_le μ hR (cdf_eq_one_of_not_lt μ h)
  linarith

lemma tendsto_phi_supX (hR : RegularPos μ) (hI : IncVV μ) (hex : ∃ x, cdf μ x = 1) :
    Tendsto (phi μ) (𝓝[<] (supX μ)) (𝓝 (supX μ)) := by
  have hs0 := supX_pos μ hR hex
  have hs1 := cdf_supX μ hR hex
  rw [tendsto_order]
  constructor
  · intro a ha
    -- some point of the support has `φ > a`
    have hclaim : ∃ y1, 0 < y1 ∧ y1 < supX μ ∧ a < phi μ y1 := by
      by_contra hno
      push Not at hno
      set s := supX μ
      set κ := (s - a) / 2 with hκ
      have hκ0 : 0 < κ := by rw [hκ]; linarith
      set y0 := max ((a + s) / 2) (s / 2) with hy0
      have hy00 : 0 < y0 := lt_of_lt_of_le (by linarith) (le_max_right _ _)
      have hy0s : y0 < s := max_lt (by linarith) (by linarith)
      have hy0a : s - κ ≤ y0 := by rw [hκ]; exact le_trans (by linarith) (le_max_left _ _)
      let h : ℝ → ℝ := fun y => (1 - cdf μ y) * Real.exp (y / κ)
      have hmono : ∀ b, y0 ≤ b → b < s → h y0 ≤ h b := by
        intro b hb hbs
        have hMon : MonotoneOn h (Set.Icc y0 b) := by
          apply monotoneOn_of_deriv_nonneg (convex_Icc y0 b)
          · intro x hx
            have hx0 : 0 < x := lt_of_lt_of_le hy00 hx.1
            exact (((continuousAt_const.sub (cdf_contAt μ hR hx0)).mul
              ((Real.continuous_exp.comp (continuous_id.div_const κ)).continuousAt))).continuousWithinAt
          · rw [interior_Icc]
            intro x hx
            have hx0 : 0 < x := lt_of_lt_of_le hy00 hx.1.le
            have hx1 : cdf μ x < 1 := cdf_lt_of_lt_supX μ hR (lt_trans hx.2 hbs)
            have hd := (hR.2.2.2.2.1 x hx0 hx1).1
            exact ((hd.const_sub 1).mul ((hasDerivAt_id x).div_const κ).exp).differentiableAt.differentiableWithinAt
          · rw [interior_Icc]
            intro x hx
            have hx0 : 0 < x := lt_of_lt_of_le hy00 hx.1.le
            have hx1 : cdf μ x < 1 := cdf_lt_of_lt_supX μ hR (lt_trans hx.2 hbs)
            have hd := (hR.2.2.2.2.1 x hx0 hx1).1
            have hg := (hR.2.2.2.2.1 x hx0 hx1).2
            have hD : HasDerivAt h ((-deriv (cdf μ) x) * Real.exp (x / κ) +
                (1 - cdf μ x) * (Real.exp (x / κ) * (1 / κ))) x :=
              (hd.const_sub 1).mul ((hasDerivAt_id x).div_const κ).exp
            rw [hD.deriv]
            have hphi := hno x hx0 (lt_trans hx.2 hbs)
            -- (1 - G)/g ≥ κ
            have hratio : κ ≤ (1 - cdf μ x) / deriv (cdf μ) x := by
              unfold phi at hphi
              have : y0 < x := hx.1
              linarith
            have hgk : deriv (cdf μ) x ≤ (1 - cdf μ x) / κ := by
              rw [le_div_iff₀ hκ0]
              rw [le_div_iff₀ hg] at hratio
              linarith
            have he := Real.exp_pos (x / κ)
            have : (-deriv (cdf μ) x) * Real.exp (x / κ) +
                (1 - cdf μ x) * (Real.exp (x / κ) * (1 / κ)) =
                Real.exp (x / κ) * ((1 - cdf μ x) / κ - deriv (cdf μ) x) := by
              field_simp
              ring
            rw [this]
            exact mul_nonneg he.le (by linarith)
        exact hMon ⟨le_rfl, hb⟩ ⟨hb, le_rfl⟩ hb
      have hcont : ContinuousAt h s :=
        (continuousAt_const.sub (cdf_contAt μ hR hs0)).mul
          ((Real.continuous_exp.comp (continuous_id.div_const κ)).continuousAt)
      have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio s))
      have hev : ∀ᶠ b in 𝓝[<] s, h y0 ≤ h b := by
        filter_upwards [Ioo_mem_nhdsLT hy0s] with b hb
        exact hmono b hb.1.le hb.2
      have hle := ge_of_tendsto hlim hev
      have hhs : h s = 0 := by simp only [h, hs1, sub_self, zero_mul]
      rw [hhs] at hle
      have hpos : 0 < h y0 := mul_pos (by linarith [cdf_lt_of_lt_supX μ hR hy0s])
        (Real.exp_pos _)
      linarith
    obtain ⟨y1, hy10, hy1s, hy1a⟩ := hclaim
    filter_upwards [Ioo_mem_nhdsLT hy1s] with y hy
    have hy1c := cdf_lt_of_lt_supX μ hR hy1s
    have hyc := cdf_lt_of_lt_supX μ hR hy.2
    exact lt_trans hy1a (hI ⟨hy10, hy1c⟩ ⟨lt_trans hy10 hy.1, hyc⟩ hy.1)
  · intro a ha
    filter_upwards [Ioo_mem_nhdsLT hs0] with y hy
    exact lt_of_le_of_lt (phi_le_self μ hR hy.1 (cdf_lt_of_lt_supX μ hR hy.2))
      (lt_trans hy.2 ha)

lemma psi_continuous (hR : RegularPos μ) (hI : IncVV μ) : Continuous (psi μ) := by
  have hz0 := zproj_pos μ hR hI
  have hz1 := cdf_zproj_lt μ hR hI
  have hpz : psi μ (zproj μ) = 0 := by
    unfold psi; rw [if_pos hz1, if_pos le_rfl]; exact phi_zproj μ hR hI
  have hbelow : ∀ y, y < zproj μ → psi μ y = 0 := by
    intro y hy
    unfold psi
    rw [if_pos (lt_of_le_of_lt (cdf_mono μ hy.le) hz1), if_neg (not_le.2 hy)]
  have hmid : ∀ y, zproj μ ≤ y → cdf μ y < 1 → psi μ y = phi μ y := by
    intro y hy hy1
    unfold psi
    rw [if_pos hy1, if_pos hy]
  rw [continuous_iff_continuousAt]
  intro x
  rcases lt_trichotomy x (zproj μ) with hxz | hxz | hzx
  · have hev : psi μ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hxz] with y hy
      exact hbelow y hy
    exact continuousAt_const.congr hev.symm
  · subst hxz
    rw [continuousAt_iff_continuous_left'_right']
    constructor
    · have hev : psi μ =ᶠ[𝓝[<] (zproj μ)] fun _ => (0 : ℝ) := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact hbelow y hy
      unfold ContinuousWithinAt
      rw [hpz]
      exact tendsto_const_nhds.congr' hev.symm
    · have hev : psi μ =ᶠ[𝓝[>] (zproj μ)] phi μ := by
        have h1 : ∀ᶠ y in 𝓝 (zproj μ), cdf μ y < 1 :=
          (cdf_contAt μ hR hz0).eventually (gt_mem_nhds hz1)
        filter_upwards [self_mem_nhdsWithin, h1.filter_mono nhdsWithin_le_nhds] with y hy hy1
        exact hmid y (le_of_lt hy) hy1
      exact (phi_contAt μ hR hz0 hz1).continuousWithinAt.congr_of_eventuallyEq hev
        (by rw [hpz, phi_zproj μ hR hI])
  · by_cases hx1 : cdf μ x < 1
    · have hx0 : 0 < x := lt_trans hz0 hzx
      have hev : psi μ =ᶠ[𝓝 x] phi μ := by
        have h1 : ∀ᶠ y in 𝓝 x, cdf μ y < 1 := (cdf_contAt μ hR hx0).eventually (gt_mem_nhds hx1)
        filter_upwards [Ioi_mem_nhds hzx, h1] with y hy hy1
        exact hmid y (le_of_lt hy) hy1
      exact (phi_contAt μ hR hx0 hx1).congr hev.symm
    · have hx1' := cdf_eq_one_of_not_lt μ hx1
      have hex : ∃ y, cdf μ y = 1 := ⟨x, hx1'⟩
      have hsx : supX μ ≤ x := supX_le μ hR hx1'
      have habove : ∀ y, supX μ ≤ y → psi μ y = supX μ := by
        intro y hy
        have : cdf μ y = 1 := le_antisymm (cdf_le_one' μ y)
          ((cdf_supX μ hR hex) ▸ cdf_mono μ hy)
        unfold psi
        rw [if_neg (by rw [this]; exact lt_irrefl 1)]
      rcases eq_or_lt_of_le hsx with hs | hs
      · subst hs
        rw [continuousAt_iff_continuous_left'_right']
        constructor
        · have hzs : zproj μ < supX μ := hzx
          have hev : psi μ =ᶠ[𝓝[<] (supX μ)] phi μ := by
            filter_upwards [Ioo_mem_nhdsLT hzs] with y hy
            exact hmid y hy.1.le (cdf_lt_of_lt_supX μ hR hy.2)
          unfold ContinuousWithinAt
          rw [habove _ le_rfl]
          exact (tendsto_phi_supX μ hR hI hex).congr' hev.symm
        · have hev : psi μ =ᶠ[𝓝[>] (supX μ)] fun _ => supX μ := by
            filter_upwards [self_mem_nhdsWithin] with y hy
            exact habove y (le_of_lt hy)
          unfold ContinuousWithinAt
          rw [habove _ le_rfl]
          exact tendsto_const_nhds.congr' hev.symm
      · have hev : psi μ =ᶠ[𝓝 x] fun _ => supX μ := by
          filter_upwards [Ioi_mem_nhds hs] with y hy
          exact habove y (le_of_lt hy)
        exact continuousAt_const.congr hev.symm

theorem lemmaG1 (hR : RegularPos μ) (hI : IncVV μ) :
    ((∃ x, cdf μ x = 1) → Tendsto (phi μ) (𝓝[<] (supX μ)) (𝓝 (supX μ))) ∧
      ((∀ x, cdf μ x < 1) → Tendsto (phi μ) atTop atTop) ∧
      (0 < zproj μ ∧ cdf μ (zproj μ) < 1 ∧ phi μ (zproj μ) = 0) ∧
      Continuous (psi μ) :=
  ⟨tendsto_phi_supX μ hR hI, tendsto_phi_atTop μ hR hI,
    ⟨zproj_pos μ hR hI, cdf_zproj_lt μ hR hI, phi_zproj μ hR hI⟩, psi_continuous μ hR hI⟩

end AdInterm.SPE.G1

open MeasureTheory

namespace AdInterm.SPE.BI

variable {N K : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] (β : Fin N → Option (Fin K))

/-- Restriction of `v` to the block `c`. -/
def restr (c : Fin K) (v : Fin N → ℝ) : {i // β i = some c} → ℝ := fun i => v i.1

lemma measurable_restr (c : Fin K) : Measurable (restr β c) :=
  measurable_pi_lambda _ (fun i => measurable_pi_apply i.1)

/-- The restriction to all blocks is measure preserving. -/
lemma map_restr :
    (Measure.pi (fun _ : Fin N => μ)).map (fun v c => restr β c v) =
      Measure.pi (fun c : Fin K => Measure.pi (fun _ : {i // β i = some c} => μ)) := by
  classical
  have hmeas : Measurable (fun v : Fin N → ℝ => fun c => restr β c v) :=
    measurable_pi_lambda _ (fun c => measurable_restr β c)
  symm
  refine Measure.pi_eq_generateFrom (C := fun c => Set.pi Set.univ '' Set.pi Set.univ
      (fun _ : {i // β i = some c} => {s : Set ℝ | MeasurableSet s}))
    (fun c => generateFrom_pi) (fun c => isPiSystem_pi)
    (fun c => Measure.FiniteSpanningSetsIn.pi (fun _ => μ.toFiniteSpanningSetsIn)) ?_
  intro s hs
  choose t ht hst using hs
  -- the preimage is a box
  let T : Fin N → Set ℝ := fun i => ⋂ (c : Fin K) (h : β i = some c), t c ⟨i, h⟩
  have hTm : ∀ i, MeasurableSet (T i) := by
    intro i
    exact MeasurableSet.iInter (fun c => MeasurableSet.iInter (fun h => ht c ⟨i, h⟩ trivial))
  have hpre : (fun v : Fin N → ℝ => fun c => restr β c v) ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ T := by
    ext v
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, T, Set.mem_iInter]
    constructor
    · intro h i c hc
      have := h c
      rw [← hst c] at this
      exact this ⟨i, hc⟩ trivial
    · intro h c
      rw [← hst c]
      intro i _
      exact h i.1 c i.2
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi (fun c => by
      rw [← hst c]; exact MeasurableSet.univ_pi (fun i => ht c i trivial))), hpre,
    Measure.pi_pi]
  rw [← Fintype.prod_fiberwise β (fun i => μ (T i)), Fintype.prod_option]
  have hnone : ∏ i : {i // β i = none}, μ (T i) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    have : T i = Set.univ := by
      simp only [T]
      ext x
      simp only [Set.mem_iInter, Set.mem_univ, iff_true]
      intro c hc
      rw [i.2] at hc
      exact absurd hc (by simp)
    rw [this, measure_univ]
  rw [hnone, one_mul]
  apply Finset.prod_congr rfl
  intro c _
  rw [← hst c, Measure.pi_pi]
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  simp only [T]
  ext x
  simp only [Set.mem_iInter]
  constructor
  · intro h; exact h c i.2
  · intro h c' hc'
    have : c' = c := by
      have := i.2
      rw [hc'] at this
      exact (Option.some.inj this)
    subst this
    exact h

/-- Functions of disjoint blocks of i.i.d. coordinates have the product law. -/
theorem block_indep (f : Fin K → (Fin N → ℝ) → ℝ) (hf : ∀ c, Measurable (f c))
    (hloc : ∀ c v v', (∀ i, β i = some c → v i = v' i) → f c v = f c v') :
    (Measure.pi (fun _ : Fin N => μ)).map (fun v c => f c v) =
      Measure.pi (fun c => (Measure.pi (fun _ : Fin N => μ)).map (f c)) := by
  classical
  let g : (c : Fin K) → ({i // β i = some c} → ℝ) → ℝ := fun c w =>
    f c (fun i => if h : β i = some c then w ⟨i, h⟩ else 0)
  have hg : ∀ c, Measurable (g c) := by
    intro c
    apply (hf c).comp
    apply measurable_pi_lambda
    intro i
    by_cases h : β i = some c
    · simp only [h, dite_true]; exact measurable_pi_apply _
    · simp only [h, dite_false]; exact measurable_const
  have hfg : ∀ c v, f c v = g c (restr β c v) := by
    intro c v
    apply hloc
    intro i hi
    simp [restr, hi]
  have hcomp : (fun v c => f c v) = (fun w c => g c (w c)) ∘ (fun v c => restr β c v) := by
    funext v c; exact hfg c v
  have hmeasR : Measurable (fun v : Fin N → ℝ => fun c => restr β c v) :=
    measurable_pi_lambda _ (fun c => measurable_restr β c)
  have hmG : Measurable (fun (w : ∀ c, {i // β i = some c} → ℝ) c => g c (w c)) :=
    measurable_pi_lambda _ (fun c => (hg c).comp (measurable_pi_apply c))
  rw [hcomp, ← Measure.map_map hmG hmeasR, map_restr μ β]
  rw [Measure.pi_map_pi (fun c => (hg c).aemeasurable)]
  congr 1
  funext c
  -- marginal of block `c`
  have hmarg : (Measure.pi (fun _ : Fin N => μ)).map (restr β c) =
      Measure.pi (fun _ : {i // β i = some c} => μ) := by
    have h1 : restr β c = (fun w => w c) ∘ (fun v c => restr β c v) := rfl
    rw [h1, ← Measure.map_map (measurable_pi_apply c) hmeasR, map_restr μ β]
    exact (measurePreserving_eval _ c).map_eq
  have h2 : f c = g c ∘ restr β c := by funext v; exact hfg c v
  rw [h2, ← Measure.map_map (hg c) (measurable_restr β c), hmarg]

end AdInterm.SPE.BI

open MeasureTheory ProbabilityTheory Filter Topology

namespace AdInterm.SPE.ARL

open AdInterm.SPE AdInterm.SPE.Res AdInterm.SPE.L31 AdInterm.SPE.G1

lemma div_child {K p c : ℕ} (hc : c < K) : (p * K + c) / K = p := by
  have hK : 0 < K := by omega
  rw [mul_comm, Nat.mul_add_div hK, Nat.div_eq_of_lt hc, add_zero]

lemma desc_parent {k : ℕ → ℕ} {s i c x : ℕ} (hc : c < k (s + 1))
    (h : DescendantBuyer k s (i * k (s + 1) + c) x) : DescendantBuyer k (s + 1) i x := by
  unfold DescendantBuyer at *
  rw [Finset.prod_Icc_succ_top (by omega), ← Nat.div_div_eq_div_mul, h, div_child hc]

/-- The clean report recursion: `F_0 = values`, `F_{t+1}(j) = ψ_{W_t}(max_c F_t(j k + c))`. -/
noncomputable def F (k : ℕ → ℕ) (μ : Measure ℝ) : ℕ → (ℕ → ℝ) → ℕ → ℝ
  | 0, u, j => u j
  | t + 1, u, j => psi (annLaw k μ t)
      (maxFin (k (t + 1)) (fun c : Fin (k (t + 1)) => F k μ t u (j * k (t + 1) + c)))

lemma F_zero (k : ℕ → ℕ) (μ : Measure ℝ) (u : ℕ → ℝ) (j : ℕ) : F k μ 0 u j = u j := rfl

lemma F_succ (k : ℕ → ℕ) (μ : Measure ℝ) (t : ℕ) (u : ℕ → ℝ) (j : ℕ) :
    F k μ (t + 1) u j = psi (annLaw k μ t)
      (maxFin (k (t + 1)) (fun c : Fin (k (t + 1)) => F k μ t u (j * k (t + 1) + c))) := rfl

lemma bid_zero (k : ℕ → ℕ) (σ : Profile) (u : ℕ → ℝ) (j : ℕ) :
    bid k σ u 0 j = (u j : WithBot ℝ) := by
  simp [bid, bidCore]

lemma bid_succ (k : ℕ → ℕ) (σ : Profile) (u : ℕ → ℝ) (t j : ℕ) :
    bid k σ u (t + 1) j =
      if ((σ (t + 1) j).1 : WithBot ℝ) ≤ (Finset.range (k (t + 1))).sup
          (fun c => bid k σ u t (j * k (t + 1) + c)) then
        (((σ (t + 1) j).2 (((Finset.range (k (t + 1))).sup
          (fun c => bid k σ u t (j * k (t + 1) + c))).getD 0) : ℝ) : WithBot ℝ) else ⊥ := by
  simp [bid, bidCore]

/-- `getD` of the sup of nonnegative-or-absent reports is the max of the reports read as `0`. -/
lemma sup_getD (K : ℕ) (b : ℕ → WithBot ℝ)
    (hb : ∀ c, c < K → b c = ⊥ ∨ ∃ a : ℝ, 0 ≤ a ∧ b c = (a : WithBot ℝ)) :
    ((Finset.range K).sup b).getD 0 = maxFin K (fun c : Fin K => (b c).unbotD 0) := by
  have hle : ∀ c, c < K → 0 ≤ (b c).unbotD 0 := by
    intro c hc
    rcases hb c hc with h | ⟨a, ha, h⟩
    · rw [h]; simp
    · rw [h]; simpa using ha
  rcases hS : (Finset.range K).sup b with _ | a
  · -- all absent
    have hall : ∀ c, c < K → b c = ⊥ := by
      intro c hc
      have := Finset.le_sup (f := b) (Finset.mem_range.2 hc)
      rw [hS] at this
      exact le_bot_iff.1 this
    have : maxFin K (fun c : Fin K => (b c).unbotD 0) = 0 := by
      apply le_antisymm
      · apply maxFin_le _ 0 le_rfl
        intro c
        rw [hall c c.2]; simp
      · cases K with
        | zero => rw [maxFin_zero]
        | succ K =>
          have := le_maxFin (fun c : Fin (K + 1) => (b c).unbotD 0) 0
          refine le_trans ?_ this
          exact hle 0 (Nat.succ_pos K)
    rw [this]; rfl
  · have hne : (Finset.range K).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h, Finset.sup_empty] at hS
      exact absurd hS (by simp)
    obtain ⟨c0, hc0, hc0e⟩ := Finset.exists_mem_eq_sup _ hne b
    rw [hS] at hc0e
    have hc0' := Finset.mem_range.1 hc0
    have ha0 : 0 ≤ a := by
      have := hle c0 hc0'
      rw [← hc0e] at this; exact this
    change a = _
    apply le_antisymm
    · have := le_maxFin (fun c : Fin K => (b c).unbotD 0) ⟨c0, hc0'⟩
      simp only at this
      rw [← hc0e] at this
      exact this
    · apply maxFin_le _ a ha0
      intro c
      have h1 := Finset.le_sup (f := b) (Finset.mem_range.2 c.2)
      rw [hS] at h1
      rcases hb c c.2 with h | ⟨a', _, h⟩
      · rw [h]; simpa using ha0
      · rw [h] at h1 ⊢
        simpa using WithBot.coe_le_coe.1 h1

variable (k : ℕ → ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]

/-- The law hypotheses packaged: `W_t` is regular with increasing virtual value for `t < n`. -/
def LawHyp (n : ℕ) : Prop :=
  ∀ t, t < n → IsProbabilityMeasure (annLaw k μ t) ∧ RegularPos (annLaw k μ t) ∧
    IncVV (annLaw k μ t)

lemma bid_eq_F (n : ℕ) (hL : LawHyp k μ n) (u : ℕ → ℝ) (hu : ∀ i, 0 ≤ u i) :
    ∀ t, t ≤ n → ∀ j,
      (bid k (fun s _ => eqMech k μ s) u t j = ⊥ ∨
        ∃ a : ℝ, 0 ≤ a ∧ bid k (fun s _ => eqMech k μ s) u t j = (a : WithBot ℝ)) ∧
      (bid k (fun s _ => eqMech k μ s) u t j).unbotD 0 = F k μ t u j := by
  intro t
  induction t with
  | zero =>
    intro _ j
    rw [bid_zero]
    exact ⟨Or.inr ⟨u j, hu j, rfl⟩, rfl⟩
  | succ t ih =>
    intro ht j
    obtain ⟨hP, hR, hI⟩ := hL t (by omega)
    have hz0 := zproj_pos (annLaw k μ t) hR hI
    have hz1 := cdf_zproj_lt (annLaw k μ t) hR hI
    have hchild : ∀ c, c < k (t + 1) →
        bid k (fun s _ => eqMech k μ s) u t (j * k (t + 1) + c) = ⊥ ∨
          ∃ a : ℝ, 0 ≤ a ∧ bid k (fun s _ => eqMech k μ s) u t (j * k (t + 1) + c) =
            (a : WithBot ℝ) := fun c _ => (ih (by omega) _).1
    have hsup := sup_getD (k (t + 1))
      (fun c => bid k (fun s _ => eqMech k μ s) u t (j * k (t + 1) + c)) hchild
    have hF : F k μ (t + 1) u j = psi (annLaw k μ t)
        (((Finset.range (k (t + 1))).sup
          (fun c => bid k (fun s _ => eqMech k μ s) u t (j * k (t + 1) + c))).getD 0) := by
      rw [F_succ, hsup]
      congr 1
      congr 1
      funext c
      exact ((ih (by omega) _).2).symm
    have hmech : eqMech k μ (t + 1) = (zproj (annLaw k μ t), psi (annLaw k μ t)) := by
      simp [eqMech]
    rw [bid_succ]
    simp only [hmech]
    rw [hF]
    set w := (Finset.range (k (t + 1))).sup
      (fun c => bid k (fun s _ => eqMech k μ s) u t (j * k (t + 1) + c)) with hw
    split_ifs with hzw
    · refine ⟨Or.inr ⟨_, psi_nonneg (annLaw k μ t) hR hI _, rfl⟩, rfl⟩
    · refine ⟨Or.inl rfl, ?_⟩
      simp only [WithBot.unbotD_bot]
      symm
      -- the report is below the reserve, where `ψ = 0`
      have hlt : w.getD 0 < zproj (annLaw k μ t) := by
        rcases hwc : w with _ | a
        · exact hz0
        · rw [hwc] at hzw
          exact lt_of_not_ge (fun h => hzw (WithBot.coe_le_coe.2 h))
      unfold psi
      rw [if_pos (lt_of_le_of_lt (cdf_mono _ hlt.le) hz1), if_neg (not_le.2 hlt)]

lemma F_local (u u' : ℕ → ℝ) : ∀ t j, (∀ i, DescendantBuyer k t j i → u i = u' i) →
    F k μ t u j = F k μ t u' j := by
  intro t
  induction t with
  | zero =>
    intro j h
    rw [F_zero, F_zero]
    exact h j (by unfold DescendantBuyer; simp)
  | succ t ih =>
    intro j h
    rw [F_succ, F_succ]
    congr 2
    funext c
    exact ih _ (fun i hi => h i (desc_parent c.2 hi))

lemma nodes_succ (n t : ℕ) (ht : t ≤ n) :
    nodes k n t = k (t + 1) * nodes k n (t + 1) := by
  unfold nodes
  rw [Finset.Icc_eq_cons_Ioc (by omega), Finset.prod_cons, ← Finset.Icc_add_one_left_eq_Ioc]

lemma lawHyp_of (n : ℕ) (hV : BuyerLaw μ) (hVinc : IncVV μ)
    (hA : ∀ t, 1 ≤ t → t ≤ n → RegularPos (annLaw k μ t) ∧ IncVV (annLaw k μ t)) :
    LawHyp k μ n := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨by simp only [annLaw]; infer_instance, hV.1, hVinc⟩
  | succ t ih =>
    intro ht
    obtain ⟨hP, hR, hI⟩ := ih (by omega)
    refine ⟨?_, (hA (t + 1) (by omega) (by omega)).1, (hA (t + 1) (by omega) (by omega)).2⟩
    have hmeas : Measurable (fun x : Fin (k (t + 1)) → ℝ =>
        psi (annLaw k μ t) (maxFin (k (t + 1)) x)) :=
      (psi_mono _ hR hI).measurable.comp (measurable_maxFin _)
    show IsProbabilityMeasure ((Measure.pi (fun _ : Fin (k (t + 1)) => annLaw k μ t)).map
      (fun x => psi (annLaw k μ t) (maxFin (k (t + 1)) x)))
    exact Measure.isProbabilityMeasure_map hmeas.aemeasurable

/-- Clean reports as functions of the buyer vector. -/
noncomputable def G (n t j : ℕ) (v : Fin (nodes k n 0) → ℝ) : ℝ := F k μ t (buyerValues k n v) j

omit [IsProbabilityMeasure μ] in
lemma measurable_buyerValues (n i : ℕ) :
    Measurable (fun v : Fin (nodes k n 0) → ℝ => buyerValues k n v i) := by
  unfold buyerValues
  by_cases h : i < nodes k n 0
  · simp only [h, dite_true]; exact measurable_pi_apply _
  · simp only [h, dite_false]; exact measurable_const

lemma measurable_G (n : ℕ) (hL : LawHyp k μ n) :
    ∀ t, t ≤ n → ∀ j, Measurable (G k μ n t j) := by
  intro t
  induction t with
  | zero => intro _ j; exact measurable_buyerValues k n j
  | succ t ih =>
    intro ht j
    obtain ⟨hP, hR, hI⟩ := hL t (by omega)
    unfold G
    simp only [F_succ]
    apply (psi_mono _ hR hI).measurable.comp
    apply (measurable_maxFin _).comp
    exact measurable_pi_lambda _ (fun c => ih (by omega) _)

lemma joint_law (n : ℕ) (hk : ∀ t, 1 ≤ t → t ≤ n + 1 → 1 ≤ k t) (hL : LawHyp k μ n)
    (t : ℕ) (ht : t ≤ n) (hlaw : ∀ j, j < nodes k n t →
      (Measure.pi (fun _ : Fin (nodes k n 0) => μ)).map (G k μ n t j) = annLaw k μ t)
    (p : ℕ) (hp : p < nodes k n (t + 1)) :
    (Measure.pi (fun _ : Fin (nodes k n 0) => μ)).map
        (fun v (c : Fin (k (t + 1))) => G k μ n t (p * k (t + 1) + c) v) =
      Measure.pi (fun _ : Fin (k (t + 1)) => annLaw k μ t) := by
  classical
  have hK : 0 < k (t + 1) := hk (t + 1) (by omega) (by omega)
  set B := ∏ s ∈ Finset.Icc 1 t, k s with hB
  let β : Fin (nodes k n 0) → Option (Fin (k (t + 1))) := fun i =>
    if (i.1 / B) / k (t + 1) = p then some ⟨(i.1 / B) % k (t + 1), Nat.mod_lt _ hK⟩ else none
  have hbi := AdInterm.SPE.BI.block_indep μ β
    (fun c v => G k μ n t (p * k (t + 1) + c) v)
    (fun c => measurable_G k μ n hL t ht _)
    (by
      intro c v v' hvv
      unfold G
      apply F_local
      intro i hi
      unfold buyerValues
      by_cases h : i < nodes k n 0
      · simp only [h, dite_true]
        apply hvv
        unfold DescendantBuyer at hi
        simp only [β]
        rw [← hB] at hi
        rw [hi, div_child c.2, if_pos rfl]
        congr 1
        ext
        simp only
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt c.2]
      · simp only [h, dite_false])
  rw [hbi]
  congr 1
  funext c
  apply hlaw
  rw [nodes_succ k n t ht]
  have := c.2
  nlinarith

theorem laws (n : ℕ) (hk : ∀ t, 1 ≤ t → t ≤ n + 1 → 1 ≤ k t) (hL : LawHyp k μ n) :
    ∀ t, t ≤ n → ∀ j, j < nodes k n t →
      (Measure.pi (fun _ : Fin (nodes k n 0) => μ)).map (G k μ n t j) = annLaw k μ t := by
  intro t
  induction t with
  | zero =>
    intro _ j hj
    have : G k μ n 0 j = fun v => v ⟨j, hj⟩ := by
      funext v; unfold G; rw [F_zero]; unfold buyerValues; simp [hj]
    rw [this]
    exact (measurePreserving_eval (fun _ : Fin (nodes k n 0) => μ) ⟨j, hj⟩).map_eq
  | succ t ih =>
    intro ht j hj
    obtain ⟨hP, hR, hI⟩ := hL t (by omega)
    have hjoint := joint_law k μ n hk hL t (by omega) (ih (by omega)) j hj
    have hcomp : G k μ n (t + 1) j = (fun x => psi (annLaw k μ t) (maxFin (k (t + 1)) x)) ∘
        (fun v (c : Fin (k (t + 1))) => G k μ n t (j * k (t + 1) + c) v) := by
      funext v; rfl
    have hm1 : Measurable (fun x : Fin (k (t + 1)) → ℝ => psi (annLaw k μ t) (maxFin (k (t + 1)) x)) :=
      (psi_mono _ hR hI).measurable.comp (measurable_maxFin _)
    have hm2 : Measurable (fun v (c : Fin (k (t + 1))) => G k μ n t (j * k (t + 1) + c) v) :=
      measurable_pi_lambda _ (fun c => measurable_G k μ n hL t (by omega) _)
    rw [hcomp, ← Measure.map_map hm1 hm2, hjoint]
    rfl

theorem arl (n : ℕ) (hk : ∀ t, 1 ≤ t → t ≤ n + 1 → 1 ≤ k t)
    (hV : BuyerLaw μ) (hVinc : IncVV μ)
    (hA : ∀ t, 1 ≤ t → t ≤ n → RegularPos (annLaw k μ t) ∧ IncVV (annLaw k μ t)) :
    (∀ t, t ≤ n → ∀ j, j < nodes k n t →
      (Measure.pi (fun _ : Fin (nodes k n 0) => μ)).map
          (fun v => (bid k (fun s _ => eqMech k μ s) (buyerValues k n v) t j).unbotD 0) =
        annLaw k μ t) ∧
      (∀ t, t ≤ n → ∀ p, p < nodes k n (t + 1) →
        iIndepFun
          (fun (c : Fin (k (t + 1))) (v : Fin (nodes k n 0) → ℝ) =>
            (bid k (fun s _ => eqMech k μ s) (buyerValues k n v) t
              (p * k (t + 1) + c)).unbotD 0)
          (Measure.pi (fun _ : Fin (nodes k n 0) => μ))) := by
  have hL := lawHyp_of k μ n hV hVinc hA
  have hμpos : ∀ᵐ x ∂μ, 0 ≤ x := by
    rw [ae_iff]
    have : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
    rw [this]; exact hV.1.1
  have hae : ∀ᵐ v ∂(Measure.pi (fun _ : Fin (nodes k n 0) => μ)),
      ∀ i, 0 ≤ buyerValues k n v i := by
    have h1 : ∀ i : Fin (nodes k n 0), ∀ᵐ v ∂(Measure.pi (fun _ : Fin (nodes k n 0) => μ)),
        0 ≤ v i := fun i =>
      (measurePreserving_eval (fun _ : Fin (nodes k n 0) => μ) i).quasiMeasurePreserving.ae
        (p := fun x => 0 ≤ x) hμpos
    filter_upwards [ae_all_iff.2 h1] with v hv i
    unfold buyerValues
    by_cases h : i < nodes k n 0
    · simp only [h, dite_true]; exact hv _
    · simp only [h, dite_false]; exact le_rfl
  have hbidG : ∀ t, t ≤ n → ∀ j,
      (fun v => (bid k (fun s _ => eqMech k μ s) (buyerValues k n v) t j).unbotD 0) =ᵐ[
        Measure.pi (fun _ : Fin (nodes k n 0) => μ)] G k μ n t j := by
    intro t ht j
    filter_upwards [hae] with v hv
    exact (bid_eq_F k μ n hL (buyerValues k n v) hv t ht j).2
  have hlaws := laws k μ n hk hL
  refine ⟨fun t ht j hj => ?_, fun t ht p hp => ?_⟩
  · rw [Measure.map_congr (hbidG t ht j)]
    exact hlaws t ht j hj
  · rw [iIndepFun_iff_map_fun_eq_pi_map (fun c =>
      ((measurable_G k μ n hL t ht _).aemeasurable).congr (hbidG t ht _).symm)]
    have hvec : (fun v (c : Fin (k (t + 1))) =>
        (bid k (fun s _ => eqMech k μ s) (buyerValues k n v) t (p * k (t + 1) + c)).unbotD 0) =ᵐ[
          Measure.pi (fun _ : Fin (nodes k n 0) => μ)]
        (fun v (c : Fin (k (t + 1))) => G k μ n t (p * k (t + 1) + c) v) := by
      filter_upwards [hae] with v hv
      funext c
      exact (bid_eq_F k μ n hL (buyerValues k n v) hv t ht _).2
    rw [Measure.map_congr hvec, joint_law k μ n hk hL t ht (hlaws t ht) p hp]
    congr 1
    funext c
    rw [Measure.map_congr (hbidG t ht _)]
    symm
    apply hlaws t ht
    rw [nodes_succ k n t ht]
    have := c.2
    nlinarith

end AdInterm.SPE.ARL

open MeasureTheory

namespace AdInterm.SPE.L21A

open AdInterm.SPE

variable {k : ℕ → ℕ} {σ : Profile} {v : ℕ → ℝ}

/-- The natural (non-overridden) report of tier-`(s+1)` node `i`. -/
noncomputable def natRep (k : ℕ → ℕ) (σ : Profile) (v : ℕ → ℝ) (ov : BidOverride)
    (s i : ℕ) : WithBot ℝ :=
  if (σ (s + 1) i).1 ≤ (Finset.range (k (s + 1))).sup
      (fun c => bidCore k σ v ov s (i * k (s + 1) + c)) then
    ((σ (s + 1) i).2 (((Finset.range (k (s + 1))).sup
      (fun c => bidCore k σ v ov s (i * k (s + 1) + c))).getD 0) : WithBot ℝ) else ⊥

lemma bidCore_zero_of_eq (b : ℝ) (j : ℕ) :
    bidCore k σ v (some (0, j, b)) 0 j = (b : WithBot ℝ) := by
  simp [bidCore]

lemma bidCore_zero_of_ne (ov : BidOverride) (j : ℕ) (h : ∀ b, ov ≠ some (0, j, b)) :
    bidCore k σ v ov 0 j = (v j : WithBot ℝ) := by
  rcases ov with _ | ⟨s, i, b⟩
  · simp [bidCore]
  · cases s with
    | zero =>
      have : i ≠ j := by
        rintro rfl; exact h b rfl
      simp [bidCore, this]
    | succ s => simp [bidCore]

lemma bidCore_succ_of_eq (b : ℝ) (s j : ℕ) :
    bidCore k σ v (some (s + 1, j, b)) (s + 1) j = (b : WithBot ℝ) := by
  simp [bidCore]

lemma bidCore_succ_of_ne (ov : BidOverride) (s j : ℕ) (h : ∀ b, ov ≠ some (s + 1, j, b)) :
    bidCore k σ v ov (s + 1) j = natRep k σ v ov s j := by
  rcases ov with _ | ⟨s', i, b⟩
  · simp [bidCore, natRep]
  · have : ¬ (s' = s + 1 ∧ i = j) := by
      rintro ⟨rfl, rfl⟩; exact h b rfl
    simp only [bidCore, natRep]
    rw [if_neg this]

lemma bidCore_self (b : ℝ) (t j : ℕ) :
    bidCore k σ v (some (t, j, b)) t j = (b : WithBot ℝ) := by
  cases t with
  | zero => exact bidCore_zero_of_eq b j
  | succ t => exact bidCore_succ_of_eq b t j

lemma bestChild_unique {n : ℕ} {rS : ℝ} {ov : BidOverride} {s p c c' : ℕ}
    (h : IsBestChild k n σ rS v ov s p c) (h' : IsBestChild k n σ rS v ov s p c') :
    c = c' := by
  rcases lt_trichotomy c c' with hlt | heq | hgt
  · exfalso
    have h1 := h'.2.2.2 c h.1
    rw [if_pos hlt] at h1
    have h2 := h.2.2.2 c' h'.1
    rw [if_neg (by omega)] at h2
    exact lt_irrefl _ (lt_of_lt_of_le h1 h2)
  · exact heq
  · exfalso
    have h1 := h.2.2.2 c' h'.1
    rw [if_pos hgt] at h1
    have h2 := h'.2.2.2 c h.1
    rw [if_neg (by omega)] at h2
    exact lt_irrefl _ (lt_of_lt_of_le h1 h2)

lemma chooseChild_some {n : ℕ} {rS : ℝ} {ov : BidOverride} {s p q : ℕ}
    (h : chooseChild k n σ rS v ov s p = some q) :
    ∃ c, IsBestChild k n σ rS v ov s p c ∧ q = p * k (s + 1) + c := by
  classical
  unfold chooseChild at h
  split_ifs at h with hc
  · exact ⟨_, Classical.choose_spec hc, (Option.some.inj h).symm⟩

lemma chooseChild_of_best {n : ℕ} {rS : ℝ} {ov : BidOverride} {s p c : ℕ}
    (h : IsBestChild k n σ rS v ov s p c) :
    chooseChild k n σ rS v ov s p = some (p * k (s + 1) + c) := by
  classical
  have hc : ∃ c, IsBestChild k n σ rS v ov s p c := ⟨c, h⟩
  unfold chooseChild
  rw [dif_pos hc]
  rw [bestChild_unique (Classical.choose_spec hc) h]

lemma chooseChild_none {n : ℕ} {rS : ℝ} {ov : BidOverride} {s p : ℕ}
    (h : ¬ ∃ c, IsBestChild k n σ rS v ov s p c) :
    chooseChild k n σ rS v ov s p = none := by
  classical
  unfold chooseChild
  rw [dif_neg h]

lemma chooseChild_congr {n : ℕ} {rS : ℝ} {v' : ℕ → ℝ} {ov ov' : BidOverride} {s : ℕ}
    (h : bidCore k σ v ov s = bidCore k σ v' ov' s) (p : ℕ) :
    chooseChild k n σ rS v ov s p = chooseChild k n σ rS v' ov' s p := by
  have hb : ∀ c, IsBestChild k n σ rS v ov s p c ↔ IsBestChild k n σ rS v' ov' s p c := by
    intro c; simp only [IsBestChild, h]
  by_cases hc : ∃ c, IsBestChild k n σ rS v ov s p c
  · obtain ⟨c, hc⟩ := hc
    rw [chooseChild_of_best hc, chooseChild_of_best ((hb c).1 hc)]
  · rw [chooseChild_none hc, chooseChild_none (fun ⟨c, hc'⟩ => hc ⟨c, (hb c).2 hc'⟩)]

lemma winnerDepth_congr {n : ℕ} {rS : ℝ} {v' : ℕ → ℝ} {ov ov' : BidOverride} {t : ℕ}
    (h : ∀ s, t ≤ s → bidCore k σ v ov s = bidCore k σ v' ov' s) :
    ∀ d, d ≤ n + 1 - t →
      winnerDepth k n σ rS v ov d = winnerDepth k n σ rS v' ov' d := by
  intro d
  induction d with
  | zero => intro _; simp [winnerDepth]
  | succ d ih =>
    intro hd
    simp only [winnerDepth]
    rw [ih (by omega)]
    congr 1
    funext p
    exact chooseChild_congr (h (n - d) (by omega)) p


/-- `(s, i)` is an ancestor-or-self of `(t, j)` (for `s ≥ t`). -/
def isAnc (k : ℕ → ℕ) (t j s i : ℕ) : Prop := j / ∏ x ∈ Finset.Icc (t + 1) s, k x = i

lemma div_child {K p c : ℕ} (hc : c < K) : (p * K + c) / K = p := by
  have hK : 0 < K := by omega
  rw [mul_comm, Nat.mul_add_div hK, Nat.div_eq_of_lt hc, add_zero]

lemma isAnc_self (t j : ℕ) : isAnc k t j t j := by
  unfold isAnc
  rw [Finset.Icc_eq_empty (by omega)]
  simp

lemma isAnc_self_iff (t j i : ℕ) : isAnc k t j t i ↔ j = i := by
  unfold isAnc
  rw [Finset.Icc_eq_empty (by omega)]
  simp

lemma isAnc_parent {t j s p c : ℕ} (hs : t ≤ s) (hc : c < k (s + 1))
    (h : isAnc k t j s (p * k (s + 1) + c)) : isAnc k t j (s + 1) p := by
  unfold isAnc at *
  rw [Finset.prod_Icc_succ_top (by omega), ← Nat.div_div_eq_div_mul, h, div_child hc]

lemma desc_parent {s i c x : ℕ} (hc : c < k (s + 1))
    (h : DescendantBuyer k s (i * k (s + 1) + c) x) : DescendantBuyer k (s + 1) i x := by
  unfold DescendantBuyer at *
  rw [Finset.prod_Icc_succ_top (by omega), ← Nat.div_div_eq_div_mul, h, div_child hc]

lemma natRep_congr {v' : ℕ → ℝ} {ov ov' : BidOverride} {s i : ℕ}
    (h : ∀ c, c < k (s + 1) →
      bidCore k σ v ov s (i * k (s + 1) + c) = bidCore k σ v' ov' s (i * k (s + 1) + c)) :
    natRep k σ v ov s i = natRep k σ v' ov' s i := by
  unfold natRep
  have : (Finset.range (k (s + 1))).sup (fun c => bidCore k σ v ov s (i * k (s + 1) + c)) =
      (Finset.range (k (s + 1))).sup (fun c => bidCore k σ v' ov' s (i * k (s + 1) + c)) :=
    Finset.sup_congr rfl (fun c hc => h c (Finset.mem_range.1 hc))
  rw [this]

lemma natRep_mono {ov ov' : BidOverride} {s i : ℕ} (hm : IsMech (σ (s + 1) i))
    (h : ∀ c, c < k (s + 1) →
      bidCore k σ v ov s (i * k (s + 1) + c) ≤ bidCore k σ v ov' s (i * k (s + 1) + c)) :
    natRep k σ v ov s i ≤ natRep k σ v ov' s i := by
  unfold natRep
  have hw : (Finset.range (k (s + 1))).sup (fun c => bidCore k σ v ov s (i * k (s + 1) + c)) ≤
      (Finset.range (k (s + 1))).sup (fun c => bidCore k σ v ov' s (i * k (s + 1) + c)) :=
    Finset.sup_mono_fun (fun c hc => h c (Finset.mem_range.1 hc))
  generalize (Finset.range (k (s + 1))).sup (fun c => bidCore k σ v ov s (i * k (s + 1) + c))
    = w at hw ⊢
  generalize (Finset.range (k (s + 1))).sup (fun c => bidCore k σ v ov' s (i * k (s + 1) + c))
    = w' at hw ⊢
  split_ifs with h1 h2
  · obtain ⟨a, rfl⟩ : ∃ a : ℝ, (a : WithBot ℝ) = w :=
      WithBot.ne_bot_iff_exists.1 (fun hb => by rw [hb] at h1; exact absurd h1 (by simp))
    obtain ⟨a', rfl⟩ : ∃ a : ℝ, (a : WithBot ℝ) = w' :=
      WithBot.ne_bot_iff_exists.1 (fun hb => by rw [hb] at h2; exact absurd h2 (by simp))
    have h1' : (σ (s + 1) i).1 ≤ a := WithBot.coe_le_coe.1 h1
    have hw' : a ≤ a' := WithBot.coe_le_coe.1 hw
    exact WithBot.coe_le_coe.2
      (hm.2.1 (Set.mem_Ici.2 (le_trans hm.1 h1')) (Set.mem_Ici.2 (le_trans (le_trans hm.1 h1') hw')) hw')
  · exact absurd (le_trans h1 hw) h2
  all_goals exact bot_le

/-- Nodes not above the overridden node at the same or a lower tier are unaffected. -/
lemma bidCore_low (t' j' : ℕ) (b : ℝ) :
    ∀ s i, (s < t' ∨ (s = t' ∧ i ≠ j')) →
      bidCore k σ v (some (t', j', b)) s i = bidCore k σ v none s i := by
  intro s
  induction s with
  | zero =>
    intro i hi
    rw [bidCore_zero_of_ne _ _ (fun b' h => by
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          omega),
      bidCore_zero_of_ne _ _ (fun b' h => by simp at h)]
  | succ s ih =>
    intro i hi
    rw [bidCore_succ_of_ne _ _ _ (fun b' h => by
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          omega),
      bidCore_succ_of_ne _ _ _ (fun b' h => by simp at h)]
    exact natRep_congr (fun c _ => ih _ (Or.inl (by omega)))

lemma bidCore_unaffected (t j : ℕ) (b : ℝ) :
    ∀ s, t ≤ s → ∀ i, ¬ isAnc k t j s i →
      bidCore k σ v (some (t, j, b)) s i = bidCore k σ v none s i := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base =>
    intro i hi
    rw [isAnc_self_iff] at hi
    exact bidCore_low t j b t i (Or.inr ⟨rfl, fun h => hi h.symm⟩)
  | succ s hs ih =>
    intro i hi
    rw [bidCore_succ_of_ne _ _ _ (fun b' h => by
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          omega),
      bidCore_succ_of_ne _ _ _ (fun b' h => by simp at h)]
    exact natRep_congr (fun c hc => ih _ (fun h => hi (isAnc_parent hs hc h)))

lemma bidCore_mono {n : ℕ} (hσ : ∀ s i, 1 ≤ s → s ≤ n → IsMech (σ s i))
    (t j : ℕ) {b b' : ℝ} (hbb : b ≤ b') :
    ∀ s, t ≤ s → s ≤ n → ∀ i, isAnc k t j s i →
      bidCore k σ v (some (t, j, b)) s i ≤ bidCore k σ v (some (t, j, b')) s i := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base =>
    intro _ i hi
    rw [isAnc_self_iff] at hi
    subst hi
    rw [bidCore_self, bidCore_self]
    exact WithBot.coe_le_coe.2 hbb
  | succ s hs ih =>
    intro hsn i hi
    rw [bidCore_succ_of_ne _ _ _ (fun b' h => by
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          omega),
      bidCore_succ_of_ne _ _ _ (fun b' h => by
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          omega)]
    apply natRep_mono (hσ _ _ (by omega) hsn)
    intro c hc
    by_cases ha : isAnc k t j s (i * k (s + 1) + c)
    · exact ih (by omega) _ ha
    · rw [bidCore_unaffected t j b s hs _ ha, bidCore_unaffected t j b' s hs _ ha]

lemma bidCore_selfEq (t j : ℕ) (b0 : ℝ) (hb0 : (b0 : WithBot ℝ) = bidCore k σ v none t j) :
    ∀ s, bidCore k σ v (some (t, j, b0)) s = bidCore k σ v none s := by
  intro s
  induction s with
  | zero =>
    funext i
    by_cases h : t = 0 ∧ i = j
    · obtain ⟨rfl, rfl⟩ := h
      rw [bidCore_self, hb0]
    · rw [bidCore_zero_of_ne _ _ (fun b' h' => by
            simp only [Option.some.injEq, Prod.mk.injEq] at h'
            omega),
        bidCore_zero_of_ne _ _ (fun b' h => by simp at h)]
  | succ s ih =>
    funext i
    by_cases h : t = s + 1 ∧ i = j
    · obtain ⟨rfl, rfl⟩ := h
      rw [bidCore_self, hb0]
    · rw [bidCore_succ_of_ne _ _ _ (fun b' h' => by
            simp only [Option.some.injEq, Prod.mk.injEq] at h'
            omega),
        bidCore_succ_of_ne _ _ _ (fun b' h => by simp at h)]
      exact natRep_congr (fun c _ => by rw [ih])

lemma bidCore_local {v' : ℕ → ℝ} (ov : BidOverride) :
    ∀ s i, (∀ x, DescendantBuyer k s i x → v x = v' x) →
      bidCore k σ v ov s i = bidCore k σ v' ov s i := by
  intro s
  induction s with
  | zero =>
    intro i hi
    by_cases h : ∃ b, ov = some (0, i, b)
    · obtain ⟨b, rfl⟩ := h
      rw [bidCore_zero_of_eq, bidCore_zero_of_eq]
    · push Not at h
      rw [bidCore_zero_of_ne _ _ h, bidCore_zero_of_ne _ _ h]
      rw [hi i (by unfold DescendantBuyer; simp)]
  | succ s ih =>
    intro i hi
    by_cases h : ∃ b, ov = some (s + 1, i, b)
    · obtain ⟨b, rfl⟩ := h
      rw [bidCore_succ_of_eq, bidCore_succ_of_eq]
    · push Not at h
      rw [bidCore_succ_of_ne _ _ _ h, bidCore_succ_of_ne _ _ _ h]
      exact natRep_congr (fun c hc => ih _ (fun x hx => hi x (desc_parent hc hx)))

lemma bidCore_indep {v' : ℕ → ℝ} (t j : ℕ) (b : ℝ)
    (hv : ∀ i, ¬ DescendantBuyer k t j i → v i = v' i) :
    ∀ s, t ≤ s → bidCore k σ v (some (t, j, b)) s = bidCore k σ v' (some (t, j, b)) s := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base =>
    funext i
    by_cases h : i = j
    · subst h
      rw [bidCore_self, bidCore_self]
    · apply bidCore_local
      intro x hx
      apply hv
      unfold DescendantBuyer at *
      rw [hx]; exact h
  | succ s hs ih =>
    funext i
    rw [bidCore_succ_of_ne _ _ _ (fun b' h' => by
          simp only [Option.some.injEq, Prod.mk.injEq] at h'
          omega),
      bidCore_succ_of_ne _ _ _ (fun b' h' => by
          simp only [Option.some.injEq, Prod.mk.injEq] at h'
          omega)]
    exact natRep_congr (fun c _ => by rw [ih])


lemma winnerDepth_succ_some {n : ℕ} {rS : ℝ} {ov : BidOverride} {d q : ℕ}
    (h : winnerDepth k n σ rS v ov (d + 1) = some q) :
    ∃ p, winnerDepth k n σ rS v ov d = some p ∧
      chooseChild k n σ rS v ov (n - d) p = some q := by
  simp only [winnerDepth] at h
  cases hw : winnerDepth k n σ rS v ov d with
  | none => rw [hw] at h; simp at h
  | some p => rw [hw] at h; exact ⟨p, rfl, h⟩

lemma winner_chain {n : ℕ} {rS : ℝ} {ov : BidOverride} {t j : ℕ} (ht : t ≤ n)
    (hw : winnerDepth k n σ rS v ov (n + 1 - t) = some j) :
    ∀ e d, d + e = n + 1 - t →
      ∃ p, winnerDepth k n σ rS v ov d = some p ∧ isAnc k t j (n + 1 - d) p := by
  intro e
  induction e with
  | zero =>
    intro d hd
    refine ⟨j, by rw [show d = n + 1 - t by omega]; exact hw, ?_⟩
    rw [show n + 1 - d = t by omega]
    exact isAnc_self t j
  | succ e ih =>
    intro d hd
    obtain ⟨q, hq, hqa⟩ := ih (d + 1) (by omega)
    obtain ⟨p, hp, hc⟩ := winnerDepth_succ_some hq
    obtain ⟨c, hbest, rfl⟩ := chooseChild_some hc
    refine ⟨p, hp, ?_⟩
    rw [show n + 1 - (d + 1) = n - d by omega] at hqa
    rw [show n + 1 - d = n - d + 1 by omega]
    exact isAnc_parent (by omega) hbest.1 hqa

lemma winsWith_upset {n : ℕ} (hσ : ∀ s i, 1 ≤ s → s ≤ n → IsMech (σ s i))
    {rS : ℝ} {t j : ℕ} (ht : t ≤ n) {b b' : ℝ} (hbb : b ≤ b')
    (hw : winsWith k n σ rS v t j b) : winsWith k n σ rS v t j b' := by
  unfold winsWith winnerAt at *
  have key : ∀ d, d ≤ n + 1 - t →
      winnerDepth k n σ rS v (some (t, j, b)) d = winnerDepth k n σ rS v (some (t, j, b')) d := by
    intro d
    induction d with
    | zero => intro _; simp [winnerDepth]
    | succ d ih =>
      intro hd
      obtain ⟨p, hp, _⟩ := winner_chain ht hw (n + 1 - t - d) d (by omega)
      obtain ⟨q, hq, hqa⟩ := winner_chain ht hw (n + 1 - t - (d + 1)) (d + 1) (by omega)
      obtain ⟨p', hp', hc⟩ := winnerDepth_succ_some hq
      rw [hp] at hp'
      cases hp'
      obtain ⟨c0, hbest, rfl⟩ := chooseChild_some hc
      rw [show n + 1 - (d + 1) = n - d by omega] at hqa
      have hs1 : t ≤ n - d := by omega
      have hmono := bidCore_mono (v := v) hσ t j hbb (n - d) hs1 (by omega) _ hqa
      have hsib : ∀ d', d' < k (n - d + 1) → d' ≠ c0 →
          bidCore k σ v (some (t, j, b')) (n - d) (p * k (n - d + 1) + d') =
            bidCore k σ v (some (t, j, b)) (n - d) (p * k (n - d + 1) + d') := by
        intro d' _ hne
        have hna : ¬ isAnc k t j (n - d) (p * k (n - d + 1) + d') := by
          intro ha
          unfold isAnc at ha hqa
          rw [ha] at hqa
          omega
        rw [bidCore_unaffected t j b' _ hs1 _ hna, bidCore_unaffected t j b _ hs1 _ hna]
      have hbest' : IsBestChild k n σ rS v (some (t, j, b')) (n - d) p c0 := by
        refine ⟨hbest.1, ?_, ?_, ?_⟩
        · intro hb
          rw [hb] at hmono
          exact hbest.2.1 (le_bot_iff.1 hmono)
        · intro hn
          exact le_trans (hbest.2.2.1 hn) hmono
        · intro d' hd'
          by_cases he : d' = c0
          · subst he
            simp
          · have h0 := hbest.2.2.2 d' hd'
            rw [hsib d' hd' he]
            split_ifs with hlt
            · rw [if_pos hlt] at h0
              exact lt_of_lt_of_le h0 hmono
            · rw [if_neg hlt] at h0
              exact le_trans h0 hmono
      simp only [winnerDepth]
      rw [← ih (by omega), hp]
      simp only [Option.bind_some]
      rw [hc, chooseChild_of_best hbest']
  rw [← key _ le_rfl]
  exact hw

lemma wins_report {n : ℕ} (hσ : ∀ s i, 1 ≤ s → s ≤ n → IsMech (σ s i))
    {rS : ℝ} (hrS : 0 ≤ rS) {t j : ℕ} (ht : t ≤ n)
    (hw : wins k n σ rS v t j) :
    ∃ b0 : ℝ, 0 ≤ b0 ∧ (b0 : WithBot ℝ) = bidCore k σ v none t j := by
  unfold wins winnerAt at hw
  rw [show n + 1 - t = (n - t) + 1 by omega] at hw
  obtain ⟨p, hp, hc⟩ := winnerDepth_succ_some hw
  rw [show n - (n - t) = t by omega] at hc
  obtain ⟨c0, hbest, hj⟩ := chooseChild_some hc
  obtain ⟨b0, hb0⟩ := WithBot.ne_bot_iff_exists.1 hbest.2.1
  rw [← hj] at hb0
  refine ⟨b0, ?_, hb0⟩
  rcases Nat.eq_or_lt_of_le ht with heq | hlt
  · have := hbest.2.2.1 heq
    rw [← hj, ← hb0] at this
    exact le_trans hrS (WithBot.coe_le_coe.1 this)
  · rw [show n - t = (n - t - 1) + 1 by omega] at hp
    obtain ⟨p', _, hc'⟩ := winnerDepth_succ_some hp
    rw [show n - (n - t - 1) = t + 1 by omega] at hc'
    obtain ⟨c1, hbest1, hp'⟩ := chooseChild_some hc'
    have hne := hbest1.2.1
    rw [← hp', bidCore_succ_of_ne _ _ _ (fun b h => by simp at h)] at hne
    unfold natRep at hne
    split_ifs at hne with hr
    · have hsup : (Finset.range (k (t + 1))).sup
          (fun c => bidCore k σ v none t (p * k (t + 1) + c)) ≤ (b0 : WithBot ℝ) := by
        apply Finset.sup_le
        intro c hc
        have h0 := hbest.2.2.2 c (Finset.mem_range.1 hc)
        rw [hb0, hj]
        split_ifs at h0
        · exact h0.le
        · exact h0
      have h2 := WithBot.coe_le_coe.1 (le_trans hr hsup)
      exact le_trans (hσ (t + 1) p (by omega) (by omega)).1 h2
    · exact absurd rfl hne

end AdInterm.SPE.L21A


open MeasureTheory ProbabilityTheory Filter Topology

namespace AdInterm.SPE.Seller

open AdInterm.SPE AdInterm.SPE.Res AdInterm.SPE.L31 AdInterm.SPE.G1 AdInterm.SPE.ARL
  AdInterm.SPE.L21A

lemma sInf_sandwich {S : Set ℝ} {m : ℝ} (h1 : Set.Ioi m ⊆ S) (h2 : S ⊆ Set.Ici m) :
    sInf S = m := by
  apply le_antisymm
  · have hne : (Set.Ioi m).Nonempty := ⟨m + 1, by simp⟩
    have := csInf_le_csInf ⟨m, fun x hx => h2 hx⟩ hne h1
    rwa [csInf_Ioi] at this
  · exact le_csInf ⟨m + 1, h1 (by simp)⟩ (fun x hx => h2 hx)

lemma secondMax_nonneg {K : ℕ} (x : Fin K → ℝ) (hx : ∀ c, 0 ≤ x c) :
    0 ≤ secondMax K x := by
  cases K with
  | zero => unfold secondMax; simp; rfl
  | succ K =>
    obtain ⟨i, hi⟩ := exists_argmax x
    rw [secondMax_eq x i hi]
    cases K with
    | zero => rw [maxFin_zero]
    | succ K => exact le_trans (hx _) (le_maxFin (i.removeNth x) 0)

lemma secondMax_zero_of {K : ℕ} (hK : K = 0) (x : Fin K → ℝ) : secondMax K x = 0 := by
  subst hK; unfold secondMax; simp; rfl

lemma secondMax_spec {K : ℕ} (x : Fin K → ℝ) (i : Fin K) (hi : ∀ j, x j ≤ x i) :
    (∀ d, d ≠ i → x d ≤ secondMax K x) ∧
      (∀ b, 0 ≤ b → (∀ d, d ≠ i → x d ≤ b) → secondMax K x ≤ b) := by
  cases K with
  | zero => exact i.elim0
  | succ K =>
    rw [secondMax_eq x i hi]
    refine ⟨fun d hd => ?_, fun b hb h => ?_⟩
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hd
      exact le_maxFin (i.removeNth x) j
    · exact maxFin_le _ b hb (fun j => h _ (Fin.succAbove_ne i j))

lemma exists_lowMax' {K : ℕ} (hK : 0 < K) (x : Fin K → ℝ) : ∃ i, LowMax x i := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  exact exists_lowMax x

lemma wins_iff_best {k : ℕ → ℕ} {n : ℕ} {σ : Profile} {rS : ℝ} {u : ℕ → ℝ} {c : ℕ} :
    wins k n σ rS u n c ↔ IsBestChild k n σ rS u none n 0 c := by
  unfold wins winnerAt
  rw [show n + 1 - n = 0 + 1 by omega, winnerDepth, winnerDepth, Option.bind_some, Nat.sub_zero]
  constructor
  · intro h
    obtain ⟨c', hb, hc⟩ := chooseChild_some h
    simp only [zero_mul, zero_add] at hc
    subst hc; exact hb
  · intro h
    rw [chooseChild_of_best h]
    simp

lemma winsWith_iff {k : ℕ → ℕ} {n : ℕ} {σ : Profile} {rS : ℝ} {u : ℕ → ℝ} {c : ℕ} {b : ℝ} :
    winsWith k n σ rS u n c b ↔
      c < k (n + 1) ∧ (rS : WithBot ℝ) ≤ b ∧
        ∀ d, d < k (n + 1) → (d < c → bid k σ u n d < b) ∧ (c < d → bid k σ u n d ≤ b) := by
  have hother : ∀ d, d ≠ c → bidCore k σ u (some (n, c, b)) n d = bid k σ u n d := by
    intro d hd
    exact bidCore_low n c b n d (Or.inr ⟨rfl, hd⟩)
  have hself : bidCore k σ u (some (n, c, b)) n c = (b : WithBot ℝ) := bidCore_self b n c
  unfold winsWith winnerAt
  rw [show n + 1 - n = 0 + 1 by omega, winnerDepth, winnerDepth, Option.bind_some, Nat.sub_zero]
  constructor
  · intro h
    obtain ⟨c', hb, hc⟩ := chooseChild_some h
    simp only [zero_mul, zero_add] at hc
    subst hc
    simp only [IsBestChild, zero_mul, zero_add] at hb
    refine ⟨hb.1, by rw [← hself]; exact hb.2.2.1 trivial, fun d hd => ⟨fun hdc => ?_, fun hcd => ?_⟩⟩
    · have := hb.2.2.2 d hd
      rw [if_pos hdc, hother d (by omega), hself] at this
      exact this
    · have := hb.2.2.2 d hd
      rw [if_neg (by omega), hother d (by omega), hself] at this
      exact this
  · rintro ⟨hc, hr, hd⟩
    have hb : IsBestChild k n σ rS u (some (n, c, b)) n 0 c := by
      simp only [IsBestChild, zero_mul, zero_add]
      refine ⟨hc, by rw [hself]; simp, fun _ => by rw [hself]; exact hr, fun d hdK => ?_⟩
      by_cases hdc : d = c
      · subst hdc; simp
      · split_ifs with hlt
        · rw [hother d hdc, hself]; exact (hd d hdK).1 hlt
        · rw [hother d hdc, hself]; exact (hd d hdK).2 (by omega)
    rw [chooseChild_of_best hb]
    simp

/-- The seller's realized revenue is that of a second-price auction with reserve `rS` among the
tier-`n` reports (absent reports read as `0`). -/
lemma sellerRev_eq {k : ℕ → ℕ} {n : ℕ} {σ : Profile} {rS : ℝ} (hrS : 0 ≤ rS) {u : ℕ → ℝ}
    (hb : ∀ c, c < k (n + 1) → bid k σ u n c = ⊥ ∨ ∃ a : ℝ, 0 ≤ a ∧ bid k σ u n c = (a : WithBot ℝ)) :
    sellerRev k n σ rS u =
      (fun x : Fin (k (n + 1)) → ℝ => if rS ≤ maxFin (k (n + 1)) x then
        max rS (secondMax (k (n + 1)) x) - 0 else 0)
        (fun c => (bid k σ u n c).unbotD 0) := by
  classical
  set K := k (n + 1) with hK
  set x : Fin K → ℝ := fun c => (bid k σ u n c).unbotD 0 with hx
  have hx0 : ∀ c : Fin K, 0 ≤ x c := by
    intro c
    rcases hb c c.2 with h | ⟨a, ha, h⟩
    · simp [hx, h]
    · simp only [hx, h]; exact ha
  have hbx : ∀ c : Fin K, bid k σ u n c ≤ (x c : WithBot ℝ) := by
    intro c
    rcases hb c c.2 with h | ⟨a, _, h⟩
    · rw [h]; exact bot_le
    · simp only [hx, h]; exact le_rfl
  simp only [sub_zero]
  unfold sellerRev
  by_cases hwin : ∃ c, IsBestChild k n σ rS u none n 0 c
  · obtain ⟨c0, hc0⟩ := hwin
    have hc0K : c0 < K := hc0.1
    have hc0f := hc0
    have hbidC : ∀ d, bidCore k σ u none n d = bid k σ u n d := fun _ => rfl
    simp only [IsBestChild, zero_mul, zero_add, hbidC] at hc0
    obtain ⟨a0, ha0⟩ := WithBot.ne_bot_iff_exists.1 hc0.2.1
    have hxc0 : x ⟨c0, hc0K⟩ = a0 := by simp only [hx]; rw [← ha0]; rfl
    have hrS0 : rS ≤ a0 := by
      have := hc0.2.2.1 trivial
      rw [← ha0] at this
      exact WithBot.coe_le_coe.1 this
    have hargmax : ∀ d : Fin K, x d ≤ x ⟨c0, hc0K⟩ := by
      intro d
      rw [hxc0]
      rcases hb d d.2 with h | ⟨a, _, h⟩
      · simp only [hx, h, WithBot.unbotD_bot]
        exact le_trans hrS hrS0
      · have h1 := hc0.2.2.2 d d.2
        simp only [hx, h]
        split_ifs at h1
        · rw [h, ← ha0] at h1; exact (WithBot.coe_lt_coe.1 h1).le
        · rw [h, ← ha0] at h1; exact WithBot.coe_le_coe.1 h1
    have hmaxx : maxFin K x = a0 := by rw [maxFin_eq_of_max x _ hargmax, hxc0]
    obtain ⟨hsp1, hsp2⟩ := secondMax_spec x ⟨c0, hc0K⟩ hargmax
    rw [Finset.sum_eq_single c0]
    · rw [if_pos (wins_iff_best.2 hc0f), if_pos (by rw [hmaxx]; exact hrS0)]
      unfold pay
      apply sInf_sandwich
      · intro b hbm
        have hbm' : max rS (secondMax K x) < b := hbm
        have hb0 : 0 ≤ b := le_trans hrS (le_trans (le_max_left _ _) hbm'.le)
        refine ⟨hb0, winsWith_iff.2 ⟨hc0K, WithBot.coe_le_coe.2 (le_trans (le_max_left _ _) hbm'.le),
          fun d hd => ⟨fun hdc => ?_, fun hcd => ?_⟩⟩⟩
        · have hne : (⟨d, hd⟩ : Fin K) ≠ ⟨c0, hc0K⟩ := by
            intro h; simp at h; omega
          refine lt_of_le_of_lt (hbx ⟨d, hd⟩) (WithBot.coe_lt_coe.2 ?_)
          exact lt_of_le_of_lt (le_trans (hsp1 _ hne) (le_max_right _ _)) hbm'
        · have hne : (⟨d, hd⟩ : Fin K) ≠ ⟨c0, hc0K⟩ := by
            intro h; simp at h; omega
          refine le_trans (hbx ⟨d, hd⟩) (WithBot.coe_le_coe.2 ?_)
          exact (lt_of_le_of_lt (le_trans (hsp1 _ hne) (le_max_right _ _)) hbm').le
      · rintro b ⟨hb0, hw⟩
        obtain ⟨_, hr, hd⟩ := winsWith_iff.1 hw
        apply max_le (WithBot.coe_le_coe.1 hr)
        apply hsp2 b hb0
        intro d hne
        have hne' : (d : ℕ) ≠ c0 := fun h => hne (Fin.ext h)
        have hbd : bid k σ u n d ≤ (b : WithBot ℝ) := by
          rcases lt_or_gt_of_ne hne' with h | h
          · exact ((hd d d.2).1 h).le
          · exact (hd d d.2).2 h
        rcases hb d d.2 with h | ⟨a, _, h⟩
        · simp only [hx, h, WithBot.unbotD_bot]; exact hb0
        · simp only [hx, h]; rw [h] at hbd; exact WithBot.coe_le_coe.1 hbd
    · intro c _ hne
      rw [if_neg]
      intro hw
      exact hne (bestChild_unique (wins_iff_best.1 hw) hc0f)
    · intro h; exact absurd (Finset.mem_range.2 hc0K) h
  · rw [Finset.sum_eq_zero (fun c _ => by
      rw [if_neg (fun hw => hwin ⟨c, wins_iff_best.1 hw⟩)])]
    split_ifs with hr
    · symm
      rcases Nat.eq_zero_or_pos K with hK0 | hKpos
      · have hm : maxFin K x = 0 := by
          apply le_antisymm (maxFin_le x 0 le_rfl (fun c => absurd c.2 (by omega)))
          exact le_trans hrS hr
        have hs : secondMax K x = 0 := secondMax_zero_of hK0 x
        rw [hs]
        have : rS = 0 := le_antisymm (hm ▸ hr) hrS
        rw [this, max_self]
      · obtain ⟨c, hc⟩ := exists_lowMax' hKpos x
        have hcm : maxFin K x = x c := maxFin_eq_of_max x c (lowMax_max hc)
        by_cases hbc : bid k σ u n c = ⊥
        · have hxc : x c = 0 := by simp [hx, hbc]
          have hrs : rS = 0 := le_antisymm (by rw [hcm, hxc] at hr; exact hr) hrS
          obtain ⟨_, hsp2⟩ := secondMax_spec x c (lowMax_max hc)
          have hs : secondMax K x = 0 := le_antisymm
            (hsp2 0 le_rfl (fun d _ => by rw [← hxc]; exact lowMax_max hc d))
            (secondMax_nonneg x hx0)
          rw [hs, hrs, max_self]
        · exfalso
          apply hwin
          refine ⟨c, ?_⟩
          obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.1 hbc
          have hxc : x c = a := by simp only [hx]; rw [← ha]; rfl
          have hbid : ∀ d, bidCore k σ u none n d = bid k σ u n d := fun _ => rfl
          simp only [IsBestChild, zero_mul, zero_add, hbid]
          refine ⟨c.2, hbc, fun _ => by rw [← ha, ← hxc, ← hcm]; exact WithBot.coe_le_coe.2 hr,
            fun d hd => ?_⟩
          split_ifs with hlt
          · rw [← ha, ← hxc]
            exact lt_of_le_of_lt (hbx ⟨d, hd⟩) (WithBot.coe_lt_coe.2 ((hc ⟨d, hd⟩).1 hlt))
          · rw [← ha, ← hxc]
            exact le_trans (hbx ⟨d, hd⟩) (WithBot.coe_le_coe.2 (lowMax_max hc ⟨d, hd⟩))
    · rfl

section clause

variable (k : ℕ → ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma ae_buyer_nonneg (n : ℕ) (hV : BuyerLaw μ) :
    ∀ᵐ v ∂(Measure.pi (fun _ : Fin (nodes k n 0) => μ)), ∀ i, 0 ≤ buyerValues k n v i := by
  have hμpos : ∀ᵐ x ∂μ, 0 ≤ x := by
    rw [ae_iff]
    have : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
    rw [this]; exact hV.1.1
  have h1 : ∀ i : Fin (nodes k n 0), ∀ᵐ v ∂(Measure.pi (fun _ : Fin (nodes k n 0) => μ)),
      0 ≤ v i := fun i =>
    (measurePreserving_eval (fun _ : Fin (nodes k n 0) => μ) i).quasiMeasurePreserving.ae
      (p := fun x => 0 ≤ x) hμpos
  filter_upwards [ae_all_iff.2 h1] with v hv i
  unfold buyerValues
  by_cases h : i < nodes k n 0
  · simp only [h, dite_true]; exact hv _
  · simp only [h, dite_false]; exact le_rfl

lemma vec_law (n : ℕ) (hk : ∀ t, 1 ≤ t → t ≤ n + 1 → 1 ≤ k t) (hV : BuyerLaw μ)
    (hL : LawHyp k μ n) (t : ℕ) (ht : t ≤ n) (p : ℕ) (hp : p < nodes k n (t + 1)) :
    (Measure.pi (fun _ : Fin (nodes k n 0) => μ)).map
        (fun v (c : Fin (k (t + 1))) =>
          (bid k (fun s _ => eqMech k μ s) (buyerValues k n v) t (p * k (t + 1) + c)).unbotD 0) =
      Measure.pi (fun _ : Fin (k (t + 1)) => annLaw k μ t) := by
  have hvec : (fun v (c : Fin (k (t + 1))) =>
      (bid k (fun s _ => eqMech k μ s) (buyerValues k n v) t (p * k (t + 1) + c)).unbotD 0) =ᵐ[
        Measure.pi (fun _ : Fin (nodes k n 0) => μ)]
      (fun v (c : Fin (k (t + 1))) => G k μ n t (p * k (t + 1) + c) v) := by
    filter_upwards [ae_buyer_nonneg k μ n hV] with v hv
    funext c
    exact (bid_eq_F k μ n hL (buyerValues k n v) hv t ht _).2
  rw [Measure.map_congr hvec, joint_law k μ n hk hL t ht (laws k μ n hk hL t ht) p hp]

lemma lawN (n : ℕ) (hV : BuyerLaw μ) (hVinc : IncVV μ)
    (hA : ∀ t, 1 ≤ t → t ≤ n → RegularPos (annLaw k μ t) ∧ IncVV (annLaw k μ t)) :
    IsProbabilityMeasure (annLaw k μ n) ∧ RegularPos (annLaw k μ n) ∧ IncVV (annLaw k μ n) := by
  cases n with
  | zero => exact ⟨by simp only [annLaw]; infer_instance, hV.1, hVinc⟩
  | succ n =>
    have hL := lawHyp_of k μ (n + 1) hV hVinc hA
    obtain ⟨hP, hR, hI⟩ := hL n (by omega)
    refine ⟨?_, (hA (n + 1) (by omega) le_rfl).1, (hA (n + 1) (by omega) le_rfl).2⟩
    have hmeas : Measurable (fun x : Fin (k (n + 1)) → ℝ =>
        psi (annLaw k μ n) (maxFin (k (n + 1)) x)) :=
      (psi_mono _ hR hI).measurable.comp (measurable_maxFin _)
    show IsProbabilityMeasure ((Measure.pi (fun _ : Fin (k (n + 1)) => annLaw k μ n)).map
      (fun x => psi (annLaw k μ n) (maxFin (k (n + 1)) x)))
    exact Measure.isProbabilityMeasure_map hmeas.aemeasurable

theorem seller_clause (n : ℕ) (hk : ∀ t, 1 ≤ t → t ≤ n + 1 → 1 ≤ k t)
    (hV : BuyerLaw μ) (hVinc : IncVV μ)
    (hA : ∀ t, 1 ≤ t → t ≤ n → RegularPos (annLaw k μ t) ∧ IncVV (annLaw k μ t))
    (rS : ℝ) (hrS : 0 ≤ rS) :
    Pi_S k n μ (fun s _ => eqMech k μ s) rS ≤
      Pi_S k n μ (fun s _ => eqMech k μ s) (zproj (annLaw k μ n)) := by
  have hL := lawHyp_of k μ n hV hVinc hA
  obtain ⟨hPn, hRn, hIn⟩ := lawN k μ n hV hVinc hA
  set K := k (n + 1)
  have hK : 1 ≤ K := hk (n + 1) (by omega) le_rfl
  have hp0 : (0 : ℕ) < nodes k n (n + 1) := by
    unfold nodes; rw [Finset.Icc_eq_empty (by omega)]; simp
  have hlaw := vec_law k μ n hk hV hL n le_rfl 0 hp0
  simp only [zero_mul, zero_add] at hlaw
  have hPi : ∀ r, 0 ≤ r → Pi_S k n μ (fun s _ => eqMech k μ s) r = sellerObj K (annLaw k μ n) r := by
    intro r hr
    unfold Pi_S
    have hae : (fun v => sellerRev k n (fun s _ => eqMech k μ s) r (buyerValues k n v)) =ᵐ[
        Measure.pi (fun _ : Fin (nodes k n 0) => μ)]
        (fun x : Fin K → ℝ => if r ≤ maxFin K x then max r (secondMax K x) - 0 else 0) ∘
          (fun v (c : Fin K) =>
            (bid k (fun s _ => eqMech k μ s) (buyerValues k n v) n c).unbotD 0) := by
      filter_upwards [ae_buyer_nonneg k μ n hV] with v hv
      exact sellerRev_eq hr (fun c _ => (bid_eq_F k μ n hL (buyerValues k n v) hv n le_rfl c).1)
    rw [integral_congr_ae hae]
    have hmeasΦ : Measurable (fun x : Fin K → ℝ =>
        if r ≤ maxFin K x then max r (secondMax K x) - 0 else 0) :=
      Measurable.ite (measurableSet_le measurable_const (measurable_maxFin K))
        ((measurable_const.max (measurable_secondMax K)).sub_const 0) measurable_const
    have hvecm : AEMeasurable (fun v (c : Fin K) =>
        (bid k (fun s _ => eqMech k μ s) (buyerValues k n v) n c).unbotD 0)
        (Measure.pi (fun _ : Fin (nodes k n 0) => μ)) := by
      apply aemeasurable_pi_lambda
      intro c
      refine ((measurable_G k μ n hL n le_rfl c).aemeasurable).congr ?_
      filter_upwards [ae_buyer_nonneg k μ n hV] with v hv
      exact ((bid_eq_F k μ n hL (buyerValues k n v) hv n le_rfl c).2).symm
    have hmap := integral_map hvecm hmeasΦ.aestronglyMeasurable
    rw [hlaw] at hmap
    rw [Function.comp_def, ← hmap]
    rfl
  rw [hPi rS hrS, hPi _ (le_trans le_rfl (zproj_pos _ hRn hIn).le)]
  exact (core K hK (annLaw k μ n) hRn hIn 0 le_rfl
    (fun x hx => lt_of_le_of_lt (cdf_mono _ hx.le) hRn.2.2.1)
    (fun p hp => by
      rcases eq_or_lt_of_le hp with h | h
      · subst h; simp
      · rw [measureReal_def, atom_zero_pos _ hRn h]; simp)).2 rS hrS

end clause

end AdInterm.SPE.Seller

open AdInterm.SPE MeasureTheory

theorem solution (n : ℕ) (k : ℕ → ℕ)
    (hk : ∀ t, 1 ≤ t → t ≤ n + 1 → 1 ≤ k t)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hV : BuyerLaw μ) (hVinc : IncVV μ)
    (hA : ∀ t, 1 ≤ t → t ≤ n →
      RegularPos (annLaw k μ t) ∧ IncVV (annLaw k μ t)) :
    (∀ t, 1 ≤ t → t ≤ n → IsMech (eqMech k μ t)) ∧
      IsSPE k n μ (eqMech k μ) (zproj (annLaw k μ n)) := by
  have hL := AdInterm.SPE.ARL.lawHyp_of k μ n hV hVinc hA
  obtain ⟨hPn, hRn, hIn⟩ := AdInterm.SPE.Seller.lawN k μ n hV hVinc hA
  refine ⟨fun t h1 h2 => ?_, (AdInterm.SPE.L31.zproj_pos _ hRn hIn).le,
    AdInterm.SPE.theorem_3_1_intermediaries n k hk μ hV hVinc hA,
    fun rS hrS => AdInterm.SPE.Seller.seller_clause k μ n hk hV hVinc hA rS hrS⟩
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  obtain ⟨hP, hR, hI⟩ := hL t' (by omega)
  have : eqMech k μ (t' + 1) = (zproj (annLaw k μ t'), psi (annLaw k μ t')) := by
    simp [eqMech]
  rw [this]
  exact AdInterm.SPE.L31.isMech_psi _ hR hI
