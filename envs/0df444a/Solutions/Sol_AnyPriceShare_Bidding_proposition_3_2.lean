-- Prove2me | solution 1 for AnyPriceShare.Bidding.proposition_3_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T02:23:53.086056+00:00
-- url     : https://prove2.me/submissions/eec24741-1b2a-4354-b4d5-89cb1c8ccda8

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic

open AnyPriceShare.Bidding

namespace APSP32Sol

/-- The packing set of Definition 3.1. -/
def Zset {m : ℕ} (β : ℝ) (w : Finset (Fin m) → ℝ) (S : Finset (Fin m)) : Set ℝ :=
  {z : ℝ | ∃ lam : Finset (Fin m) → ℝ,
    (∑ T ∈ S.powerset, lam T = 1) ∧
    (∀ T ∈ S.powerset, 0 ≤ lam T) ∧
    (∀ T ∈ S.powerset, w T < z → lam T = 0) ∧
    (∀ j ∈ S, ∑ T ∈ S.powerset with j ∈ T, lam T ≤ β)}

theorem dual_eq {m : ℕ} (β : ℝ) (w : Finset (Fin m) → ℝ) (S : Finset (Fin m)) :
    anyPriceDual β w S = sSup (Zset β w S) := rfl

theorem zero_mem {m : ℕ} (β : ℝ) (hβ : 0 ≤ β) (w : Finset (Fin m) → ℝ) (hmono : Monotone w)
    (hnorm : w ∅ = 0) (S : Finset (Fin m)) : (0 : ℝ) ∈ Zset β w S := by
  classical
  refine ⟨fun T => if T = ∅ then 1 else 0, ?_, ?_, ?_, ?_⟩
  · rw [Finset.sum_ite_eq']; simp
  · intro T _; dsimp only; split_ifs <;> norm_num
  · intro T _ hT
    have : w ∅ ≤ w T := hmono (Finset.empty_subset T)
    exfalso; linarith
  · intro j _
    rw [Finset.sum_eq_zero]
    · exact hβ
    · intro T hT
      simp only [Finset.mem_filter] at hT
      rw [if_neg]; rintro rfl; simp at hT

theorem mem_of_le {m : ℕ} (β : ℝ) (w : Finset (Fin m) → ℝ) (S : Finset (Fin m)) (z z' : ℝ)
    (hz : z ∈ Zset β w S) (hz' : z' ≤ z) : z' ∈ Zset β w S := by
  obtain ⟨lam, h1, h2, h3, h4⟩ := hz
  exact ⟨lam, h1, h2, fun T hT hlt => h3 T hT (lt_of_lt_of_le hlt hz'), h4⟩

/-- A packing has a bundle of positive weight; it is worth at least `z`. -/
theorem exists_pos {m : ℕ} (β : ℝ) (w : Finset (Fin m) → ℝ) (S : Finset (Fin m)) (z : ℝ)
    (lam : Finset (Fin m) → ℝ) (h1 : ∑ T ∈ S.powerset, lam T = 1)
    (h2 : ∀ T ∈ S.powerset, 0 ≤ lam T) (h3 : ∀ T ∈ S.powerset, w T < z → lam T = 0)
    (p : Fin m → ℝ) (hp0 : ∀ j ∈ S, 0 ≤ p j) (hp1 : ∑ j ∈ S, p j = 1)
    (h4 : ∀ j ∈ S, ∑ T ∈ S.powerset with j ∈ T, lam T ≤ β) :
    ∃ T ∈ S.powerset, ∑ j ∈ T, p j ≤ β ∧ z ≤ w T := by
  classical
  -- `∑_T λ_T p(T) = ∑_j p_j load_j ≤ β`
  have hpT : ∀ T ∈ S.powerset, ∑ j ∈ T, p j = ∑ j ∈ S, if j ∈ T then p j else 0 := by
    intro T hT
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.2 (Finset.mem_powerset.1 hT)]
  have hswap : ∑ T ∈ S.powerset, lam T * ∑ j ∈ T, p j =
      ∑ j ∈ S, p j * ∑ T ∈ S.powerset with j ∈ T, lam T := by
    rw [Finset.sum_congr rfl (fun T hT => by rw [hpT T hT]), ]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl; intro T _
    split_ifs <;> ring
  have hle : ∑ T ∈ S.powerset, lam T * ∑ j ∈ T, p j ≤ β := by
    rw [hswap]
    calc ∑ j ∈ S, p j * ∑ T ∈ S.powerset with j ∈ T, lam T ≤ ∑ j ∈ S, p j * β :=
          Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (h4 j hj) (hp0 j hj)
      _ = β := by rw [← Finset.sum_mul, hp1, one_mul]
  by_contra hcon
  push Not at hcon
  have hgood : ∀ T ∈ S.powerset, 0 < lam T → β < ∑ j ∈ T, p j := by
    intro T hT hpos
    by_contra hc
    push Not at hc
    have hzT := hcon T hT hc
    have := h3 T hT hzT
    linarith
  have hex : ∃ T ∈ S.powerset, 0 < lam T := by
    by_contra hc
    push Not at hc
    have : ∑ T ∈ S.powerset, lam T ≤ 0 := Finset.sum_nonpos hc
    linarith
  have hpos : 0 < ∑ T ∈ S.powerset, lam T * (∑ j ∈ T, p j - β) := by
    apply Finset.sum_pos'
    · intro T hT
      rcases (h2 T hT).eq_or_lt with h0 | hp
      · rw [← h0, zero_mul]
      · exact (mul_pos hp (sub_pos.2 (hgood T hT hp))).le
    · obtain ⟨T, hT, hp⟩ := hex
      exact ⟨T, hT, mul_pos hp (sub_pos.2 (hgood T hT hp))⟩
  have : ∑ T ∈ S.powerset, lam T * (∑ j ∈ T, p j - β) =
      ∑ T ∈ S.powerset, lam T * ∑ j ∈ T, p j - β := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, h1, one_mul]
  linarith

/-- Indicator vector of a bundle. -/
def ind {m : ℕ} (T : Finset (Fin m)) : Fin m → ℝ := fun j => if j ∈ T then 1 else 0

theorem ind_inj {m : ℕ} {T T' : Finset (Fin m)} (h : ind T = ind T') : T = T' := by
  ext j
  have := congrFun h j
  simp only [ind] at this
  by_cases h1 : j ∈ T <;> by_cases h2 : j ∈ T' <;> simp_all

/-- Linear functionals on `Fin m → ℝ` are given by their coefficients. -/
theorem dual_apply {m : ℕ} (f : StrongDual ℝ (Fin m → ℝ)) (y : Fin m → ℝ) :
    f y = ∑ j, y j * f (fun j' => if j = j' then 1 else 0) := by
  conv_lhs => rw [pi_eq_sum_univ y]
  rw [map_sum]
  simp [map_smul, smul_eq_mul]

/-- Farkas-type alternative: either some convex combination of the bundles of `F` loads every
item of `S` by at most `β`, or there are non-negative item weights `d` on `S` under which every
bundle of `F` weighs more than `β · d(S)`. -/
theorem alternative {m : ℕ} (S : Finset (Fin m)) (F : Finset (Finset (Fin m)))
    (hF : ∀ T ∈ F, T ⊆ S) (β : ℝ) :
    (∃ y ∈ convexHull ℝ (↑(F.image ind) : Set (Fin m → ℝ)), ∀ j ∈ S, y j ≤ β) ∨
    (∃ d : Fin m → ℝ, (∀ j ∈ S, 0 ≤ d j) ∧ ∀ T ∈ F, β * ∑ j ∈ S, d j < ∑ j ∈ T, d j) := by
  classical
  set K := convexHull ℝ (↑(F.image ind) : Set (Fin m → ℝ))
  set C : Set (Fin m → ℝ) := {y | ∀ j ∈ S, y j ≤ β}
  by_cases hdisj : Disjoint K C
  · right
    have hKc : IsCompact K := (F.image ind).finite_toSet.isCompact_convexHull ℝ
    have hKv : Convex ℝ K := convex_convexHull ℝ _
    have hCc : IsClosed C := by
      have : C = ⋂ j ∈ S, {y : Fin m → ℝ | y j ≤ β} := by ext y; simp [C]
      rw [this]
      exact isClosed_biInter fun j _ => isClosed_le (continuous_apply j) continuous_const
    have hCv : Convex ℝ C := by
      intro y hy y' hy' a a' ha ha' haa j hj
      show a * y j + a' * y' j ≤ β
      have e : a * β + a' * β = β := by rw [← add_mul, haa, one_mul]
      linarith [mul_le_mul_of_nonneg_left (hy j hj) ha, mul_le_mul_of_nonneg_left (hy' j hj) ha']
    obtain ⟨f, u, v, hfK, huv, hfC⟩ := geometric_hahn_banach_compact_closed hKv hKc hCv hCc hdisj
    set c : Fin m → ℝ := fun j => f (fun j' => if j = j' then 1 else 0) with hc
    have hf : ∀ y, f y = ∑ j, y j * c j := dual_apply f
    set one : Fin m → ℝ := fun _ => β
    have hone : one ∈ C := fun j _ => le_rfl
    have hfone := hfC one hone
    -- coefficients vanish off `S` and are non-positive on `S`
    have hcS : ∀ j ∈ S, c j ≤ 0 := by
      intro j hj
      by_contra hpos
      push Not at hpos
      set t := (f one - v) / c j + 1
      have ht : 0 ≤ t := by
        have : 0 ≤ (f one - v) / c j := div_nonneg (by linarith) hpos.le
        linarith
      set yt : Fin m → ℝ := fun j' => β - t * (if j = j' then 1 else 0)
      have hyt : yt ∈ C := by
        intro j' _; simp only [yt]; split_ifs <;> nlinarith
      have h1 := hfC yt hyt
      have h2 : f yt = f one - t * c j := by
        rw [hf, hf]
        simp only [yt, one, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
        rw [Finset.sum_boole_mul]; simp
      have h3 : t * c j = f one - v + c j := by
        simp only [t]; field_simp
      linarith
    have hcnS : ∀ j ∉ S, c j = 0 := by
      intro j hj
      by_contra hne
      set t := -(f one - v + 1) / c j
      set yt : Fin m → ℝ := fun j' => β + t * (if j = j' then 1 else 0)
      have hyt : yt ∈ C := by
        intro j' hj'; simp only [yt]
        have : j ≠ j' := fun h => hj (h ▸ hj')
        simp [this]
      have h1 := hfC yt hyt
      have h2 : f yt = f one + t * c j := by
        rw [hf, hf]
        simp only [yt, one, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
        rw [Finset.sum_boole_mul]; simp
      have h3 : t * c j = -(f one - v + 1) := by
        simp only [t]; field_simp
      linarith
    have hsumS : ∀ T ⊆ S, ∑ j, ind T j * c j = ∑ j ∈ T, c j := by
      intro T _
      simp only [ind, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    refine ⟨fun j => - c j, fun j hj => by linarith [hcS j hj], fun T hT => ?_⟩
    have hTK : ind T ∈ K := subset_convexHull ℝ _ (Finset.mem_coe.2 (Finset.mem_image_of_mem ind hT))
    have h1 := hfK _ hTK
    rw [hf, hsumS T (hF T hT)] at h1
    have h2 : f one = β * ∑ j ∈ S, c j := by
      rw [hf, Finset.mul_sum]
      rw [← Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => by rw [hcnS j hj, mul_zero])]
    simp only [Finset.sum_neg_distrib, mul_neg]
    linarith
  · left
    rw [Set.not_disjoint_iff] at hdisj
    obtain ⟨y, hyK, hyC⟩ := hdisj
    exact ⟨y, hyK, hyC⟩

end APSP32Sol

open APSP32Sol in
theorem solution {m : ℕ} (w : Finset (Fin m) → ℝ) (hmono : Monotone w) (hnorm : w ∅ = 0)
    (β : ℝ) (hβ : 0 < β) (S : Finset (Fin m)) :
    anyPriceDual β w S = anyPrice β w S := by
  classical
  have hw0 : ∀ T, 0 ≤ w T := fun T => hnorm ▸ hmono (Finset.empty_subset T)
  -- index types of the price form
  have hAne : ∀ p : {p : Fin m → ℝ // (∀ j ∈ S, 0 ≤ p j) ∧ ∑ j ∈ S, p j = 1},
      Nonempty {T : Finset (Fin m) // T ⊆ S ∧ ∑ j ∈ T, p.1 j ≤ β} :=
    fun p => ⟨⟨∅, Finset.empty_subset _, by simpa using hβ.le⟩⟩
  have hbddA : ∀ p : {p : Fin m → ℝ // (∀ j ∈ S, 0 ≤ p j) ∧ ∑ j ∈ S, p j = 1},
      BddAbove (Set.range fun T : {T : Finset (Fin m) // T ⊆ S ∧ ∑ j ∈ T, p.1 j ≤ β} =>
        w T.1) := fun p => (Set.finite_range _).bddAbove
  have hbddP : BddBelow (Set.range fun p : {p : Fin m → ℝ // (∀ j ∈ S, 0 ≤ p j) ∧
      ∑ j ∈ S, p j = 1} => ⨆ T : {T : Finset (Fin m) // T ⊆ S ∧ ∑ j ∈ T, p.1 j ≤ β}, w T.1) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨p, rfl⟩
    haveI := hAne p
    exact le_ciSup_of_le (hbddA p) (Classical.arbitrary _) (hw0 _)
  -- packings exist only below `w S`
  have hbdd : BddAbove (Zset β w S) := by
    refine ⟨w S, fun z hz => ?_⟩
    obtain ⟨lam, h1, h2, h3, _⟩ := hz
    by_contra hc
    push Not at hc
    have : ∀ T ∈ S.powerset, lam T = 0 := fun T hT =>
      h3 T hT (lt_of_le_of_lt (hmono (Finset.mem_powerset.1 hT)) hc)
    rw [Finset.sum_eq_zero this] at h1
    norm_num at h1
  have hzero : (0 : ℝ) ∈ Zset β w S := zero_mem β hβ.le w hmono hnorm S
  rw [dual_eq]
  apply le_antisymm
  · -- weak duality
    apply csSup_le ⟨0, hzero⟩
    intro z hz
    obtain ⟨lam, h1, h2, h3, h4⟩ := hz
    rcases S.eq_empty_or_nonempty with rfl | ⟨j0, hj0⟩
    · have hE : anyPrice β w (∅ : Finset (Fin m)) = 0 := by
        unfold anyPrice
        haveI : IsEmpty {p : Fin m → ℝ // (∀ j ∈ (∅ : Finset (Fin m)), 0 ≤ p j) ∧
            ∑ j ∈ (∅ : Finset (Fin m)), p j = 1} := ⟨fun q => by simpa using q.2.2⟩
        exact Real.iInf_of_isEmpty _
      rw [hE]
      by_contra hc
      push Not at hc
      have := h3 ∅ (by simp) (by rw [hnorm]; exact hc)
      simp only [Finset.powerset_empty, Finset.sum_singleton] at h1
      linarith
    · unfold anyPrice
      haveI : Nonempty {p : Fin m → ℝ // (∀ j ∈ S, 0 ≤ p j) ∧ ∑ j ∈ S, p j = 1} :=
        ⟨⟨fun j => if j = j0 then 1 else 0, fun j _ => by dsimp only; split_ifs <;> norm_num,
          by simp [hj0]⟩⟩
      apply le_ciInf
      intro p
      obtain ⟨T, hT, hTp, hzT⟩ := exists_pos β w S z lam h1 h2 h3 p.1 p.2.1 p.2.2 h4
      exact le_ciSup_of_le (hbddA p) ⟨T, Finset.mem_powerset.1 hT, hTp⟩ hzT
  · -- strong duality
    set z := anyPrice β w S with hzdef
    apply le_csSup hbdd
    by_cases hz0 : z ≤ 0
    · exact mem_of_le β w S 0 z hzero hz0
    push Not at hz0
    set F := S.powerset.filter (fun T => z ≤ w T) with hFdef
    have hFsub : ∀ T ∈ F, T ⊆ S := fun T hT => Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1
    have hindinj : Set.InjOn ind (↑F : Set (Finset (Fin m))) :=
      fun T _ T' _ h => ind_inj h
    rcases alternative S F hFsub β with ⟨y, hyK, hyC⟩ | ⟨d, hd0, hdF⟩
    · -- a convex combination of good bundles loads every item by at most `β`
      rw [Finset.mem_convexHull] at hyK
      obtain ⟨μ, hμ0, hμ1, hμc⟩ := hyK
      have hy : ∀ j, y j = ∑ T ∈ F, μ (ind T) * ind T j := by
        intro j
        rw [← hμc, Finset.centerMass, hμ1, inv_one, one_smul, Finset.sum_apply,
          Finset.sum_image hindinj]
        simp
      refine ⟨fun T => if T ∈ F then μ (ind T) else 0, ?_, ?_, ?_, ?_⟩
      · rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (Finset.filter_subset _ _),
          ← Finset.sum_image hindinj, hμ1]
      · intro T _
        dsimp only
        split_ifs with hT
        · exact hμ0 _ (Finset.mem_image_of_mem ind hT)
        · exact le_rfl
      · intro T hT hlt
        dsimp only
        rw [if_neg]
        intro hTF
        exact absurd (Finset.mem_filter.1 hTF).2 (not_le.2 hlt)
      · intro j hj
        rw [Finset.sum_filter]
        have : ∑ T ∈ S.powerset, (if j ∈ T then (if T ∈ F then μ (ind T) else 0) else 0) =
            ∑ T ∈ S.powerset, (if T ∈ F then μ (ind T) * ind T j else 0) := by
          apply Finset.sum_congr rfl; intro T _
          simp only [ind]
          split_ifs <;> simp
        rw [this, Finset.sum_ite_mem, Finset.inter_eq_right.2 (Finset.filter_subset _ _), ← hy]
        exact hyC j hj
    · -- otherwise a price vector makes every good bundle unaffordable
      exfalso
      have hSne : S.Nonempty := by
        rcases S.eq_empty_or_nonempty with hS | hS
        · exfalso
          have hE : z = 0 := by
            rw [hzdef, hS]
            unfold anyPrice
            haveI : IsEmpty {p : Fin m → ℝ // (∀ j ∈ (∅ : Finset (Fin m)), 0 ≤ p j) ∧
                ∑ j ∈ (∅ : Finset (Fin m)), p j = 1} := ⟨fun q => by simpa using q.2.2⟩
            exact Real.iInf_of_isEmpty _
          linarith
        · exact hS
      obtain ⟨j0, hj0⟩ := hSne
      obtain ⟨p, hp0, hp1, hpF⟩ : ∃ p : Fin m → ℝ, (∀ j ∈ S, 0 ≤ p j) ∧ ∑ j ∈ S, p j = 1 ∧
          ∀ T ∈ F, β < ∑ j ∈ T, p j := by
        by_cases hFne : F.Nonempty
        · obtain ⟨T0, hT0⟩ := hFne
          have hD0 : 0 ≤ ∑ j ∈ S, d j := Finset.sum_nonneg hd0
          have hTD : ∑ j ∈ T0, d j ≤ ∑ j ∈ S, d j :=
            Finset.sum_le_sum_of_subset_of_nonneg (hFsub T0 hT0) fun j hj _ => hd0 j hj
          have hDpos : 0 < ∑ j ∈ S, d j := by
            rcases hD0.eq_or_lt with h | h
            · have := hdF T0 hT0; rw [← h] at this hTD; linarith
            · exact h
          refine ⟨fun j => d j / ∑ j ∈ S, d j, fun j hj => div_nonneg (hd0 j hj) hD0, ?_, ?_⟩
          · rw [← Finset.sum_div, div_self hDpos.ne']
          · intro T hT
            rw [← Finset.sum_div, lt_div_iff₀ hDpos]
            exact hdF T hT
        · refine ⟨fun j => if j = j0 then 1 else 0, fun j _ => by dsimp only; split_ifs <;> norm_num,
            by simp [hj0], fun T hT => absurd ⟨T, hT⟩ hFne⟩
      have hle : z ≤ ⨆ T : {T : Finset (Fin m) // T ⊆ S ∧ ∑ j ∈ T, p j ≤ β}, w T.1 := by
        rw [hzdef]; unfold anyPrice
        exact ciInf_le hbddP ⟨p, hp0, hp1⟩
      haveI := hAne ⟨p, hp0, hp1⟩
      obtain ⟨T, hT⟩ := exists_eq_ciSup_of_finite
        (f := fun T : {T : Finset (Fin m) // T ⊆ S ∧ ∑ j ∈ T, p j ≤ β} => w T.1)
      rw [← hT] at hle
      have hTF : T.1 ∉ F := fun hTF => absurd T.2.2 (not_le.2 (hpF T.1 hTF))
      have : w T.1 < z := by
        by_contra hc
        push Not at hc
        exact hTF (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 T.2.1, hc⟩)
      linarith
