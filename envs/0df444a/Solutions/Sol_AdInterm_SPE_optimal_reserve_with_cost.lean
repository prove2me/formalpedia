-- Prove2me | solution 1 for AdInterm.SPE.optimal_reserve_with_cost
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T17:48:43.221919+00:00
-- url     : https://prove2.me/submissions/7ae89c09-d439-42a5-af3e-b5554ce7b9a3

import Mathlib
import Definitions.Def_AdInterm_SPE_VirtualValue

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

open AdInterm.SPE AdInterm.SPE.Res

theorem solution (m : ℕ) (hm : 1 ≤ m)
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ]
    (hV : BuyerLaw μ) (hVinc : IncVV μ)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : ∀ x, x < c → cdf μ x < 1) :
    0 ≤ phiInv μ c ∧
      ∀ δ : ℝ, 0 ≤ δ → reserveObj m μ c δ ≤ reserveObj m μ c (phiInv μ c) := by
  apply core m hm μ hV.1 hVinc c hc0 hc
  intro p hp
  have h0 : μ.real {p} = 0 := by
    rcases eq_or_lt_of_le hp with h | h
    · subst h
      have h1 : μ.real (Set.Iic 0) = 0 := by
        rw [← ProbabilityTheory.cdf_eq_real]; exact hV.2
      have h2 : μ.real {(0 : ℝ)} ≤ μ.real (Set.Iic 0) :=
        MeasureTheory.measureReal_mono (by simp)
      have h3 : 0 ≤ μ.real {(0 : ℝ)} := MeasureTheory.measureReal_nonneg
      linarith
    · rw [MeasureTheory.measureReal_def, atom_zero_pos μ hV.1 h]; simp
  rw [h0, mul_zero]
