-- Prove2me | solution 1 for AGT.external_to_swap_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-12T18:09:04.090469+00:00
-- url     : https://prove2.me/submissions/1659b984-3dde-49eb-9be3-40446a33046b

import Definitions.Def_agt_regret
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Continuity

open Finset Filter Topology AGT

namespace BM

/-- Every row-stochastic matrix on a nonempty finite index type has a
stationary distribution.  Mathlib has neither Brouwer's fixed point theorem
nor Perron–Frobenius, so this is proved by the Cesàro/compactness argument:
the averages of the orbit of any distribution are almost fixed, and the
simplex is compact. -/
theorem exists_stationary {M : Type*} [Fintype M] [Nonempty M] [DecidableEq M]
    (Q : M → M → ℝ) (hQ0 : ∀ j i, 0 ≤ Q j i) (hQ1 : ∀ j, ∑ i, Q j i = 1) :
    ∃ p : M → ℝ, (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧
      (∀ i, ∑ j, p j * Q j i = p i) := by
  classical
  -- the one-step map on distributions
  set S : (M → ℝ) → (M → ℝ) := fun p i => ∑ j, p j * Q j i with hSdef
  have hScont : Continuous S := by
    refine continuous_pi fun i => continuous_finsetSum _ fun j _ => ?_
    exact (continuous_apply j).mul continuous_const
  have hSmaps : ∀ p ∈ stdSimplex ℝ M, S p ∈ stdSimplex ℝ M := by
    rintro p ⟨hp0, hp1⟩
    refine ⟨fun i => Finset.sum_nonneg fun j _ => mul_nonneg (hp0 j) (hQ0 j i), ?_⟩
    show ∑ i, ∑ j, p j * Q j i = 1
    rw [Finset.sum_comm]
    calc ∑ j, ∑ i, p j * Q j i = ∑ j, p j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.mul_sum, hQ1 j, mul_one]
      _ = 1 := hp1
  -- the orbit of a point mass
  obtain ⟨i₀⟩ := ‹Nonempty M›
  set v : M → ℝ := fun i => if i = i₀ then 1 else 0 with hvdef
  have hv : v ∈ stdSimplex ℝ M := by
    constructor
    · intro i; by_cases h : i = i₀ <;> simp [hvdef, h]
    · simp [hvdef]
  set x : ℕ → (M → ℝ) := fun m => S^[m] v with hxdef
  have hxsucc : ∀ m, x (m + 1) = S (x m) := fun m =>
    Function.iterate_succ_apply' S m v
  have hx : ∀ m, x m ∈ stdSimplex ℝ M := by
    intro m
    induction m with
    | zero => simpa [hxdef] using hv
    | succ m ih => rw [hxsucc m]; exact hSmaps _ ih
  have hx01 : ∀ m i, x m i ∈ Set.Icc (0 : ℝ) 1 := by
    intro m i
    refine ⟨(hx m).1 i, ?_⟩
    rw [← (hx m).2]
    exact Finset.single_le_sum (fun j _ => (hx m).1 j) (Finset.mem_univ i)
  -- Cesàro averages
  set a : ℕ → (M → ℝ) := fun m i => (∑ r ∈ range (m + 1), x r i) / ((m : ℝ) + 1)
    with hadef
  have hmpos : ∀ m : ℕ, (0 : ℝ) < (m : ℝ) + 1 := fun m => by positivity
  have ha : ∀ m, a m ∈ stdSimplex ℝ M := by
    intro m
    constructor
    · intro i
      exact div_nonneg (Finset.sum_nonneg fun r _ => (hx r).1 i) (hmpos m).le
    · show ∑ i, (∑ r ∈ range (m + 1), x r i) / ((m : ℝ) + 1) = 1
      rw [← Finset.sum_div, Finset.sum_comm]
      rw [Finset.sum_congr rfl (fun r _ => (hx r).2), Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, mul_one]
      push_cast
      exact div_self (hmpos m).ne'
  -- the averages are almost fixed
  have hdiff : ∀ m i, S (a m) i - a m i = (x (m + 1) i - x 0 i) / ((m : ℝ) + 1) := by
    intro m i
    have hstep : ∀ r, ∑ j, x r j * Q j i = x (r + 1) i := by
      intro r; rw [hxsucc r]
    have hSam : S (a m) i = (∑ r ∈ range (m + 1), x (r + 1) i) / ((m : ℝ) + 1) := by
      show ∑ j, a m j * Q j i = _
      rw [eq_div_iff (hmpos m).ne', Finset.sum_mul]
      calc ∑ j, a m j * Q j i * ((m : ℝ) + 1)
          = ∑ j, ∑ r ∈ range (m + 1), x r j * Q j i := by
            refine Finset.sum_congr rfl fun j _ => ?_
            show (∑ r ∈ range (m + 1), x r j) / ((m : ℝ) + 1) * Q j i * ((m : ℝ) + 1) = _
            field_simp
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun r _ => by ring
        _ = ∑ r ∈ range (m + 1), ∑ j, x r j * Q j i := Finset.sum_comm
        _ = ∑ r ∈ range (m + 1), x (r + 1) i :=
            Finset.sum_congr rfl fun r _ => hstep r
    rw [hSam]
    show _ = _
    rw [hadef, div_sub_div_same, ← Finset.sum_sub_distrib,
      Finset.sum_range_sub (fun r => x r i) (m + 1)]
  have htend0 : Tendsto (fun m => S (a m) - a m) atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro i
    have hz : (0 : M → ℝ) i = 0 := rfl
    rw [hz]
    have hb2 : ∀ m : ℕ, (S (a m) - a m) i ≤ 1 / ((m : ℝ) + 1) := by
      intro m
      have h2 : (S (a m) - a m) i = (x (m + 1) i - x 0 i) / ((m : ℝ) + 1) := hdiff m i
      rw [h2, div_le_div_iff_of_pos_right (hmpos m)]
      linarith [(hx01 (m + 1) i).2, (hx01 0 i).1]
    have hb1 : ∀ m : ℕ, -(1 / ((m : ℝ) + 1)) ≤ (S (a m) - a m) i := by
      intro m
      have h2 : (S (a m) - a m) i = (x (m + 1) i - x 0 i) / ((m : ℝ) + 1) := hdiff m i
      rw [h2, neg_div' , div_le_div_iff_of_pos_right (hmpos m)]
      linarith [(hx01 (m + 1) i).1, (hx01 0 i).2]
    have hlim0 : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using hlim0.neg) hlim0 hb1 hb2
  -- compactness of the simplex
  obtain ⟨p, hp, φ, hφ, hlim⟩ :=
    (isCompact_stdSimplex ℝ M).tendsto_subseq ha
  have hSlim : Tendsto (fun k => S (a (φ k))) atTop (𝓝 (S p)) :=
    (hScont.tendsto p).comp hlim
  have hdlim : Tendsto (fun k => S (a (φ k)) - a (φ k)) atTop (𝓝 0) :=
    htend0.comp hφ.tendsto_atTop
  have hback : Tendsto (fun k => a (φ k)) atTop (𝓝 (S p - 0)) := by
    have := hSlim.sub hdlim
    simpa using this
  have hSp : S p = p := by
    have := tendsto_nhds_unique hback hlim
    simpa using this
  exact ⟨p, hp.1, hp.2, fun i => congrFun hSp i⟩


/-- Existence of a stationary distribution, in the junk-value-tolerant form
used to define `stat`. -/
theorem exists_stat {n : ℕ} (Q : Fin (n + 1) → Fin (n + 1) → ℝ) :
    ∃ p : Fin (n + 1) → ℝ, (∀ j, IsLottery (Q j)) →
      (IsLottery p ∧ ∀ i, ∑ j, p j * Q j i = p i) := by
  classical
  by_cases h : ∀ j, IsLottery (Q j)
  · obtain ⟨p, hp0, hp1, hps⟩ :=
      exists_stationary Q (fun j i => (h j).1 i) (fun j => (h j).2)
    exact ⟨p, fun _ => ⟨⟨hp0, hp1⟩, hps⟩⟩
  · exact ⟨fun _ => 0, fun hc => absurd hc h⟩

/-- A stationary distribution of `Q`, chosen once and for all. -/
noncomputable def stat {n : ℕ} (Q : Fin (n + 1) → Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ := (exists_stat Q).choose

theorem stat_spec {n : ℕ} {Q : Fin (n + 1) → Fin (n + 1) → ℝ}
    (h : ∀ j, IsLottery (Q j)) :
    IsLottery (stat Q) ∧ ∀ i, ∑ j, stat Q j * Q j i = stat Q i :=
  (exists_stat Q).choose_spec h

/-- The reversed history of the `j`-th copy of `A` inside the master
procedure, as a function of the master's own reversed history.  Recursing on
the reversed history makes the mutual dependence (the master's play scales
what the copies see, and the copies' plays determine the master's play)
structurally well founded. -/
noncomputable def copyHistR {n : ℕ} (A : OnlineAlgorithm (n + 1)) :
    List (Fin (n + 1) → ℝ) → Fin (n + 1) → List (Fin (n + 1) → ℝ)
  | [], _ => []
  | ℓ :: r, j =>
      (fun i => stat (fun b => A ((copyHistR A r b).reverse)) j * ℓ i) ::
        copyHistR A r j

/-- The master procedure of Blum–Mansour. -/
noncomputable def master {n : ℕ} (A : OnlineAlgorithm (n + 1)) :
    OnlineAlgorithm (n + 1) :=
  fun h => stat (fun j => A ((copyHistR A h.reverse j).reverse))

/-- The loss sequence the `j`-th copy of `A` is fed: the true losses scaled
by the probability the master puts on that copy. -/
noncomputable def scaled {n : ℕ} (A : OnlineAlgorithm (n + 1))
    (ℓ : ℕ → Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℕ → Fin (n + 1) → ℝ :=
  fun u i => algPlay (master A) ℓ u j * ℓ u i

/-- The recursively defined copy histories are exactly the histories of the
scaled loss sequences. -/
theorem copyHistR_range {n : ℕ} (A : OnlineAlgorithm (n + 1))
    (ℓ : ℕ → Fin (n + 1) → ℝ) :
    ∀ (t : ℕ) (j : Fin (n + 1)),
      copyHistR A (((List.range t).map ℓ).reverse) j
        = ((List.range t).map (scaled A ℓ j)).reverse := by
  intro t
  induction t with
  | zero => intro j; simp [copyHistR]
  | succ t ih =>
      intro j
      have hrev : ((List.range (t + 1)).map ℓ).reverse
          = ℓ t :: ((List.range t).map ℓ).reverse := by
        rw [List.range_succ, List.map_append]; simp
      have hP : algPlay (master A) ℓ t
          = stat (fun b =>
              A ((copyHistR A (((List.range t).map ℓ).reverse) b).reverse)) := rfl
      rw [hrev]
      simp only [copyHistR, ← hP]
      rw [ih j, List.range_succ, List.map_append]
      simp
      rfl

/-- The master's play is a stationary distribution of the matrix of the
copies' plays. -/
theorem master_stationary {n : ℕ} (A : OnlineAlgorithm (n + 1))
    (hAdist : ∀ h, IsLottery (A h)) (ℓ : ℕ → Fin (n + 1) → ℝ) (t : ℕ) :
    IsLottery (algPlay (master A) ℓ t) ∧
      ∀ i, ∑ j, algPlay (master A) ℓ t j * algPlay A (scaled A ℓ j) t i
        = algPlay (master A) ℓ t i := by
  have h1 : algPlay (master A) ℓ t
      = stat (fun j => algPlay A (scaled A ℓ j) t) := by
    show stat (fun b =>
      A ((copyHistR A (((List.range t).map ℓ).reverse) b).reverse)) = _
    congr 1
    funext b
    rw [copyHistR_range A ℓ t b, List.reverse_reverse]
    rfl
  rw [h1]
  exact stat_spec (fun _ => hAdist _)

theorem master_lottery {n : ℕ} (A : OnlineAlgorithm (n + 1))
    (hAdist : ∀ h, IsLottery (A h)) (h : List (Fin (n + 1) → ℝ)) :
    IsLottery (master A h) :=
  (stat_spec (fun _ => hAdist _)).1

end BM

open AGT BM Finset in
theorem solution {n : ℕ} (T : ℕ) (R : ℝ)
    (A : OnlineAlgorithm (n + 1)) (hAdist : ∀ h, IsLottery (A h))
    (hA : ∀ ℓ : ℕ → Fin (n + 1) → ℝ, (∀ t i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ k, algLoss A ℓ T ≤ actionLoss ℓ k T + R) :
    ∃ H : OnlineAlgorithm (n + 1), (∀ h, IsLottery (H h)) ∧
      ∀ ℓ : ℕ → Fin (n + 1) → ℝ, (∀ t i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) →
        ∀ F : Fin (n + 1) → Fin (n + 1),
          algLoss H ℓ T ≤ swapLoss H ℓ F T + (n + 1) * R := by
  classical
  refine ⟨master A, fun h => master_lottery A hAdist h, ?_⟩
  intro ℓ hℓ F
  -- the master's play is a distribution, so its entries lie in `[0,1]`
  have hlot : ∀ t, IsLottery (algPlay (master A) ℓ t) :=
    fun t => (master_stationary A hAdist ℓ t).1
  have hstat : ∀ t i, ∑ j, algPlay (master A) ℓ t j * algPlay A (scaled A ℓ j) t i
      = algPlay (master A) ℓ t i := fun t => (master_stationary A hAdist ℓ t).2
  have hp01 : ∀ t j, algPlay (master A) ℓ t j ∈ Set.Icc (0 : ℝ) 1 := by
    intro t j
    refine ⟨(hlot t).1 j, ?_⟩
    rw [← (hlot t).2]
    exact Finset.single_le_sum (fun b _ => (hlot t).1 b) (Finset.mem_univ j)
  -- the scaled loss sequences are still `[0,1]`-valued
  have hsc : ∀ j, ∀ t i, scaled A ℓ j t i ∈ Set.Icc (0 : ℝ) 1 := by
    intro j t i
    refine ⟨mul_nonneg (hp01 t j).1 (hℓ t i).1, ?_⟩
    show algPlay (master A) ℓ t j * ℓ t i ≤ 1
    nlinarith [(hp01 t j).1, (hp01 t j).2, (hℓ t i).1, (hℓ t i).2]
  -- the master's loss splits into the losses of the copies
  have hinner : ∀ t, ∑ i, algPlay (master A) ℓ t i * ℓ t i
      = ∑ j, ∑ i, algPlay A (scaled A ℓ j) t i * scaled A ℓ j t i := by
    intro t
    calc ∑ i, algPlay (master A) ℓ t i * ℓ t i
        = ∑ i, ∑ j, algPlay (master A) ℓ t j * algPlay A (scaled A ℓ j) t i * ℓ t i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← hstat t i, Finset.sum_mul]
      _ = ∑ j, ∑ i, algPlay A (scaled A ℓ j) t i * scaled A ℓ j t i := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ =>
            Finset.sum_congr rfl fun i _ => by simp only [scaled]; ring
  have hdecomp : algLoss (master A) ℓ T = ∑ j, algLoss A (scaled A ℓ j) T := by
    simp only [algLoss]
    rw [Finset.sum_congr rfl (fun t _ => hinner t)]
    exact Finset.sum_comm
  -- each copy's external regret bound, against the action `F j`
  have hbound : ∀ j : Fin (n + 1), algLoss A (scaled A ℓ j) T
      ≤ (∑ t ∈ range T, scaled A ℓ j t (F j)) + R := by
    intro j
    exact hA (scaled A ℓ j) (hsc j) (F j)
  calc algLoss (master A) ℓ T = ∑ j, algLoss A (scaled A ℓ j) T := hdecomp
    _ ≤ ∑ j, ((∑ t ∈ range T, scaled A ℓ j t (F j)) + R) :=
        Finset.sum_le_sum fun j _ => hbound j
    _ = swapLoss (master A) ℓ F T + (n + 1) * R := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        congr 1
        rw [swapLoss, Finset.sum_comm]
        exact Finset.sum_congr rfl fun t _ =>
          Finset.sum_congr rfl fun j _ => rfl
