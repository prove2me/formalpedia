-- Prove2me | solution 1 for AdInterm.SPE.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T18:04:23.063066+00:00
-- url     : https://prove2.me/submissions/a877b4d2-b0e2-486e-a506-46e38ec8ba49

import Mathlib
import Definitions.Def_AdInterm_SPE_Setting

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
    (hatom : ∀ p, δ ≤ p → (p - c) * μ.real {p} = 0) (i : Fin (n + 1)) (y : Fin n → ℝ) :
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
      have := hatom p (le_max_left _ _)
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
    (hatom : ∀ p, δ ≤ p → (p - c) * μ.real {p} = 0) :
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
theorem core_ineq (n : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hR : RegularPos μ) (hI : IncVV μ) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : ∀ x, x < c → cdf μ x < 1) (δ : ℝ) (hδ : 0 ≤ δ)
    (hA1 : ∀ p, δ ≤ p → (p - c) * μ.real {p} = 0)
    (hA2 : ∀ p, phiInv μ c ≤ p → (p - c) * μ.real {p} = 0) :
    reserveObj (n + 1) μ c δ ≤ reserveObj (n + 1) μ c (phiInv μ c) := by
  have hp0 : 0 ≤ phiInv μ c := le_trans hc0 (pstar_ge μ hR c hc0 hc)
  have hint : Integrable (fun x : ℝ => x) μ := hR.2.1
  rw [reserveObj_eq μ hint c δ hδ hA1, reserveObj_eq μ hint c _ hp0 hA2]
  have hintg : ∀ d, 0 ≤ d → (∀ p, d ≤ p → (p - c) * μ.real {p} = 0) →
      Integrable (fun y => fval μ c (max d (maxFin n y)))
      (Measure.pi (fun _ : Fin n => μ)) := by
    intro d hd hA
    have := (integrable_Fi μ hint c d hd (0 : Fin (n + 1))).integral_prod_right
    refine this.congr (Filter.Eventually.of_forall (fun y => ?_))
    exact inner_Fi μ c d hd hA (0 : Fin (n + 1)) y
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono (hintg δ hδ hA1) (hintg _ hp0 hA2)
  intro y
  exact fval_dom μ hR hI c hc0 hc hδ _

theorem core (m : ℕ) (hm : 1 ≤ m) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hR : RegularPos μ) (hI : IncVV μ) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : ∀ x, x < c → cdf μ x < 1)
    (hatom : ∀ p, 0 ≤ p → (p - c) * μ.real {p} = 0) :
    0 ≤ phiInv μ c ∧
      ∀ δ : ℝ, 0 ≤ δ → reserveObj m μ c δ ≤ reserveObj m μ c (phiInv μ c) := by
  have hp0 : 0 ≤ phiInv μ c := le_trans hc0 (pstar_ge μ hR c hc0 hc)
  refine ⟨hp0, fun δ hδ => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  exact core_ineq n μ hR hI c hc0 hc δ hδ (fun p hp => hatom p (le_trans hδ hp))
    (fun p hp => hatom p (le_trans hp0 hp))

lemma reserve_integrable (n : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : ℝ => x) μ) (c δ : ℝ) (hδ : 0 ≤ δ) :
    Integrable (fun v : Fin (n + 1) → ℝ =>
      if δ ≤ maxFin (n + 1) v then max δ (secondMax (n + 1) v) - c else 0)
      (Measure.pi (fun _ : Fin (n + 1) => μ)) := by
  classical
  have hpt : (fun v : Fin (n + 1) → ℝ =>
      if δ ≤ maxFin (n + 1) v then max δ (secondMax (n + 1) v) - c else 0) =
        fun v => ∑ i, Fi c δ i (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i v) := by
    funext v
    rw [integrand_decomp]
    rfl
  rw [hpt]
  apply integrable_finset_sum
  intro i _
  have h := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
  exact (h.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2
    (integrable_Fi μ hint c δ hδ i)

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
    (hδ0 : μ {max mech.1 (ginv mech.2 P)} = 0)
    (hne : ({x : ℝ | 0 ≤ x ∧ P ≤ mech.2 x}).Nonempty) :
    ∫ v, Imech (n + 1) mech P v ∂(Measure.pi (fun _ : Fin (n + 1) => μ)) =
      reserveObj (n + 1) μ P (max mech.1 (ginv mech.2 P)) := by
  unfold reserveObj
  apply integral_congr_ae
  have hnull := null_maxFin_eq μ (n := n) hδ0
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
  · have hpsi := integral_Imech_eq μ (n := n) (isMech_psi μ hR hI) (hatom _)
      (S_psi_nonempty μ hR hI hP0 hP)
    simp only at hpsi
    rw [hpsi, ginv_psi_eq μ hR hI hP0 hP]
    by_cases hne : ({x : ℝ | 0 ≤ x ∧ P ≤ mech.2 x}).Nonempty
    · rw [integral_Imech_eq μ hm (hatom _) hne]
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


lemma core_gen (hR : RegularPos μ) (hI : IncVV μ) (hpos : ∀ p, 0 < p → μ {p} = 0)
    (n : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : ∀ x, x < c → cdf μ x < 1) (δ : ℝ) (hδ : 0 ≤ δ) :
    reserveObj (n + 1) μ c δ ≤ reserveObj (n + 1) μ c (phiInv μ c) := by
  have hreal : ∀ p, 0 < p → μ.real {p} = 0 := fun p hp => by
    rw [measureReal_def, hpos p hp]; simp
  rcases eq_or_lt_of_le hc0 with hc0' | hcpos
  · subst hc0'
    exact (core (n + 1) (by omega) μ hR hI 0 le_rfl hc (fun p hp => by
      rcases eq_or_lt_of_le hp with h | h
      · subst h; simp
      · rw [hreal p h, mul_zero])).2 δ hδ
  · have hp : c ≤ phiInv μ c := pstar_ge μ hR c hc0 hc
    have hA : ∀ d, 0 < d → ∀ p, d ≤ p → (p - c) * μ.real {p} = 0 := fun d hd p hp =>
      by rw [hreal p (lt_of_lt_of_le hd hp), mul_zero]
    have hstar := hA _ (lt_of_lt_of_le hcpos hp)
    rcases eq_or_lt_of_le hδ with hδ0 | hδpos
    · subst hδ0
      refine le_trans ?_ (core_ineq n μ hR hI c hc0 hc c hc0 (hA c hcpos) hstar)
      unfold reserveObj
      apply integral_mono (reserve_integrable n μ hR.2.1 c 0 le_rfl)
        (reserve_integrable n μ hR.2.1 c c hc0)
      intro v
      simp only
      by_cases h1 : c ≤ maxFin (n + 1) v
      · rw [if_pos (le_trans hc0 h1), if_pos h1]
        have := max_le_max_right (secondMax (n + 1) v) hc0
        linarith
      · rw [if_neg h1]
        split_ifs with h0
        · have h2 := secondMax_le_maxFin v h0
          have : max 0 (secondMax (n + 1) v) ≤ maxFin (n + 1) v := max_le h0 h2
          push Not at h1
          linarith
        · exact le_rfl
    · exact core_ineq n μ hR hI c hc0 hc δ hδ (hA δ hδpos) hstar

lemma Imech_le_Ires_self {n : ℕ} {mech : Mechanism} (hm : IsMech mech) {P : ℝ}
    (hδP : max mech.1 (ginv mech.2 P) ≤ P) (v : Fin (n + 1) → ℝ) :
    Imech (n + 1) mech P v ≤ Ires (n + 1) P P v := by
  unfold Imech Ires
  split_ifs with hwin hPw hPw
  · have := max_le_max_right (secondMax (n + 1) v) hδP
    linarith
  · have := charge_le hm hwin
    push Not at hPw
    linarith
  · have := le_max_left P (secondMax (n + 1) v)
    linarith
  · exact le_rfl

lemma perP_gen (hR : RegularPos μ) (hI : IncVV μ) (hpos : ∀ p, 0 < p → μ {p} = 0)
    {n : ℕ} {mech : Mechanism} (hm : IsMech mech) {P : ℝ} (hP0 : 0 ≤ P) :
    ∫ v, Imech (n + 1) mech P v ∂(Measure.pi (fun _ : Fin (n + 1) => μ)) ≤
      ∫ v, Imech (n + 1) (zproj μ, psi μ) P v ∂(Measure.pi (fun _ : Fin (n + 1) => μ)) := by
  have hpsi0 : 0 ≤ ∫ v, Imech (n + 1) (zproj μ, psi μ) P v
      ∂(Measure.pi (fun _ : Fin (n + 1) => μ)) :=
    integral_nonneg (fun v => Ipsi_nonneg μ hR hI hP0 v)
  by_cases hP : ∀ y, y < P → cdf μ y < 1
  · have hδpsi : μ {max (zproj μ, psi μ).1 (ginv (zproj μ, psi μ).2 P)} = 0 := by
      simp only
      rw [ginv_psi_eq μ hR hI hP0 hP]
      exact hpos _ (lt_of_lt_of_le (zproj_pos μ hR hI) ((phiInv_mono μ hR) hP0))
    have hpsi := integral_Imech_eq μ (n := n) (isMech_psi μ hR hI) hδpsi
      (S_psi_nonempty μ hR hI hP0 hP)
    simp only at hpsi
    rw [hpsi, ginv_psi_eq μ hR hI hP0 hP]
    by_cases hne : ({x : ℝ | 0 ≤ x ∧ P ≤ mech.2 x}).Nonempty
    · have hδ0 : 0 ≤ max mech.1 (ginv mech.2 P) := le_trans hm.1 (le_max_left _ _)
      rcases eq_or_lt_of_le hδ0 with hδ | hδ
      · -- the mechanism's effective reserve is `0`
        by_cases hint : Integrable (fun v => Imech (n + 1) mech P v)
            (Measure.pi (fun _ : Fin (n + 1) => μ))
        · refine le_trans (integral_mono hint (reserve_integrable n μ hR.2.1 P P hP0)
            (fun v => Imech_le_Ires_self hm (by rw [← hδ]; exact hP0) v)) ?_
          exact core_gen μ hR hI hpos n P hP0 hP P hP0
        · rw [integral_undef hint]
          rw [← ginv_psi_eq μ hR hI hP0 hP, ← hpsi]
          exact hpsi0
      · rw [integral_Imech_eq μ hm (hpos _ hδ) hne]
        exact core_gen μ hR hI hpos n P hP0 hP _ hδ0
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

theorem lemmaB1 (m : ℕ) (hm : 1 ≤ m)
    (hV : RegularPos μ) (hpos : ∀ p, 0 < p → μ {p} = 0) (hVinc : IncVV μ)
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (rS : ℝ) (hrS0 : 0 ≤ rS) :
    IsMech (zproj μ, psi μ) ∧
      ∀ mech : Mechanism, IsMech mech →
        singleProfit m μ η rS mech ≤ singleProfit m μ η rS (zproj μ, psi μ) := by
  have hR := hV
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
    exact perP_gen μ hR hVinc hpos hmech (le_trans hrS0 (le_max_left _ _))
  · rw [integral_undef hintm]
    exact integral_nonneg (fun x => Ipsi_nonneg μ hR hVinc (le_trans hrS0 (le_max_left _ _)) x.1)

end final

end AdInterm.SPE.L31

open AdInterm.SPE

theorem solution (m : ℕ) (hm : 1 ≤ m)
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ]
    (hV : RegularPos μ) (hatom : 0 < μ {0}) (hVinc : IncVV μ)
    (η : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure η]
    (hη : η (Set.Iio 0) = 0)
    (rS : ℝ) (hrS0 : 0 ≤ rS)
    (hrS : ∀ x, x < rS → cdf μ x < 1) :
    IsMech (zproj μ, psi μ) ∧
      ∀ mech : Mechanism, IsMech mech →
        singleProfit m μ η rS mech ≤
          singleProfit m μ η rS (zproj μ, psi μ) :=
  AdInterm.SPE.L31.lemmaB1 μ m hm hV (fun p hp => AdInterm.SPE.Res.atom_zero_pos μ hV hp)
    hVinc η rS hrS0
