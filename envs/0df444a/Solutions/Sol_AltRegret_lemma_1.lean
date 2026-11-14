-- Prove2me | solution 1 for AltRegret.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @Weiqiang
-- created : 2026-11-13T19:29:53.613138+00:00
-- url     : https://prove2.me/submissions/8aa072f8-0556-4b68-9c0c-965066772b0c

import Definitions.Def_AltRegret_play

namespace AAMaximizer
open Set
private noncomputable def mass {d : ℕ} (b v : Fin d → ℝ) (β y : ℝ) (i : Fin d) : ℝ :=
  Real.exp (b i - β*(v i-y)^2)

private lemma partition_pos {d : ℕ} [Nonempty (Fin d)] (b v : Fin d → ℝ) (β y : ℝ) :
    0 < ∑ i, mass b v β y i :=
  Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

private lemma clip_partition {d : ℕ} (b v : Fin d → ℝ) (hv : ∀ i, v i ∈ Icc (-1 : ℝ) 1)
    (β : ℝ) (hβ : 0 ≤ β) (y : ℝ) :
    ∃ z ∈ Icc (-1 : ℝ) 1, ∑ i, mass b v β y i ≤ ∑ i, mass b v β z i := by
  have compare (z : ℝ) (hz : ∀ i, (v i-z)^2 ≤ (v i-y)^2) :
      ∑ i, mass b v β y i ≤ ∑ i, mass b v β z i :=
    Finset.sum_le_sum fun i _ => Real.exp_le_exp.mpr (sub_le_sub_left (mul_le_mul_of_nonneg_left (hz i) hβ) _)
  by_cases hlo : y < -1
  · refine ⟨-1,⟨le_rfl,by norm_num⟩,compare _ fun i => ?_⟩
    have := (hv i).1
    nlinarith [mul_nonneg (show 0 ≤ -1-y by linarith) (show 0 ≤ 2*v i+1-y by linarith)]
  by_cases hhi : 1 < y
  · refine ⟨1,⟨by norm_num,le_rfl⟩,compare _ fun i => ?_⟩
    have := (hv i).2
    nlinarith [mul_nonneg (show 0 ≤ y-1 by linarith) (show 0 ≤ y+1-2*v i by linarith)]
  exact ⟨y,⟨le_of_not_gt hlo,le_of_not_gt hhi⟩,le_rfl⟩

private lemma partition_max {d : ℕ} (b v : Fin d → ℝ) (hv : ∀ i, v i ∈ Icc (-1 : ℝ) 1)
    (β : ℝ) (hβ : 0 ≤ β) :
    ∃ y : ℝ, ∀ z : ℝ, ∑ i, mass b v β z i ≤ ∑ i, mass b v β y i := by
  let F := fun y : ℝ => ∑ i, mass b v β y i
  have hF : Continuous F := by dsimp [F,mass]; fun_prop
  obtain ⟨y,_,hy⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (show (-1:ℝ) ≤ 1 by norm_num)) hF.continuousOn
  refine ⟨y,fun z => ?_⟩
  obtain ⟨z',hz',hle⟩ := clip_partition b v hv β hβ z
  exact hle.trans (isMaxOn_iff.mp hy z' hz')

private lemma center_properties {d : ℕ} [Nonempty (Fin d)] (b v : Fin d → ℝ)
    (hv : ∀ i, v i ∈ Icc (-1 : ℝ) 1) (β m : ℝ) (hβ : 0 < β)
    (hm : ∀ y, ∑ i, mass b v β y i ≤ ∑ i, mass b v β m i) :
    let p := fun i => mass b v β m i / ∑ j, mass b v β m j
    (∑ i, p i = 1) ∧ (∑ i, p i * (v i-m) = 0) ∧ m ∈ Icc (-1 : ℝ) 1 := by
  intro p
  have hZ := partition_pos b v β m
  have hsum : ∑ i, p i = 1 := by dsimp [p]; rw [← Finset.sum_div,div_self hZ.ne']
  have hp (i) : 0 ≤ p i := div_nonneg (Real.exp_pos _).le hZ.le
  have hlocal : IsLocalMax (fun y : ℝ => ∑ i, mass b v β y i) m :=
    Filter.Eventually.of_forall hm
  have hd (i : Fin d) : HasDerivAt (fun y => mass b v β y i)
      (mass b v β m i * (2*β*(v i-m))) m := by
    dsimp [mass]
    convert ((hasDerivAt_const m (b i)).sub ((((hasDerivAt_const m (v i)).sub (hasDerivAt_id m)).pow 2).const_mul β)).exp using 1 <;> simp <;> ring
  have hder := hlocal.hasDerivAt_eq_zero (HasDerivAt.fun_sum fun i _ => hd i)
  have hraw : 2*β * (∑ i, mass b v β m i * (v i-m)) = 0 := by
    rw [Finset.mul_sum, ← hder]
    apply Finset.sum_congr rfl
    intro i _; ring
  have hzero := (mul_eq_zero.mp hraw).resolve_left (by positivity)
  have hcent : ∑ i, p i*(v i-m) = 0 := by
    dsimp [p]
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div,hzero,zero_div]
  refine ⟨hsum,hcent,?_,?_⟩
  · have h := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      mul_le_mul_of_nonneg_left (sub_le_sub_right (hv i).1 m) (hp i)
    rw [← Finset.sum_mul, hsum, one_mul, hcent] at h
    linarith
  · have h := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      mul_le_mul_of_nonneg_left (sub_le_sub_right (hv i).2 m) (hp i)
    rw [← Finset.sum_mul, hsum, one_mul, hcent] at h
    linarith

end AAMaximizer

namespace AAMaximizer
open Set

/-- The weighted mean minus the proposed center is strictly decreasing. -/
private lemma strict_center {d : ℕ} [Nonempty (Fin d)] (b v : Fin d → ℝ)
    (hv : ∀ i, v i ∈ Icc (-1 : ℝ) 1) (β : ℝ) (hβ0 : 0 < β) (hβ : β < 1/2) :
    StrictAnti (fun y : ℝ => (∑ i, mass b v β y i * v i) / (∑ i, mass b v β y i) - y) := by
  let W := mass b v β
  let Z := fun y : ℝ => ∑ i, W y i
  let N := fun y : ℝ => ∑ i, W y i * v i
  let Q := fun y : ℝ => ∑ i, W y i * (v i)^2
  have pos (y) : 0 < Z y := partition_pos b v β y
  have hd (i : Fin d) (y : ℝ) : HasDerivAt (fun s => W s i) (W y i*(2*β*(v i-y))) y := by
    dsimp [W,mass]
    convert ((hasDerivAt_const y (b i)).sub ((((hasDerivAt_const y (v i)).sub
      (hasDerivAt_id y)).pow 2).const_mul β)).exp using 1 <;> simp <;> ring
  have hZ (y) : HasDerivAt Z (2*β*(N y-y*Z y)) y := by
    apply (HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hd i y).congr_deriv
    simp only [N,Z, Finset.mul_sum, ← Finset.sum_sub_distrib, mul_sub]
    apply Finset.sum_congr rfl
    intro i _; ring
  have hN (y) : HasDerivAt N (2*β*(Q y-y*N y)) y := by
    apply (HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hd i y).mul_const (v i)).congr_deriv
    simp only [Q,N, Finset.mul_sum, ← Finset.sum_sub_distrib, mul_sub]
    apply Finset.sum_congr rfl
    intro i _; ring
  apply strictAnti_of_deriv_neg
  intro y
  have derivG : HasDerivAt (fun s => N s / Z s - s)
      (2*β*(Q y/Z y-(N y/Z y)^2)-1) y := by
    apply (((hN y).div (hZ y) (pos y).ne').sub (hasDerivAt_id y)).congr_deriv
    field_simp [(pos y).ne']
    ring
  change deriv (fun s => N s/Z s-s) y < 0
  rw [derivG.deriv]
  have hQ : Q y ≤ Z y := by
    apply Finset.sum_le_sum
    intro i _
    calc
      W y i*(v i)^2 ≤ W y i*1 := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        nlinarith [mul_nonneg (sub_nonneg.mpr (hv i).2) (show 0 ≤ v i+1 by linarith [(hv i).1])]
      _ = _ := mul_one _
  have hVar : Q y/Z y-(N y/Z y)^2 ≤ 1 := by
    have : Q y/Z y ≤ 1 := (div_le_one (pos y)).mpr hQ
    linarith [sq_nonneg (N y/Z y)]
  have hfac := mul_le_mul_of_nonneg_left hVar (show 0 ≤ 2*β by positivity)
  linarith

end AAMaximizer

open AltRegret AAMaximizer

theorem solution {d : ℕ} (hd : 0 < d) (η β : ℝ) (hβ0 : 0 < β) (hβ : β < 1 / 2)
    (c : ℕ → Fin d → ℝ) (t : ℕ) (ht : 1 ≤ t)
    (hc : ∀ i, lossAt c (t - 1) i ∈ Set.Icc (-1 : ℝ) 1) :
    (∃! θ : ℝ, ∀ θ' : ℝ, thetaObjective η β c t θ' ≤ thetaObjective η β c t θ) ∧
    (∀ θ' : ℝ, thetaObjective η β c t θ' ≤ thetaObjective η β c t (theta η β c t)) ∧
    theta η β c t = ∑ i, weights η β c t i * lossAt c (t - 1) i ∧
    play η β c t ∈ stdSimplex ℝ (Fin d) := by
  classical
  let : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let b := fun i => -η * effCumLoss c (t-1) i
  let v := lossAt c (t-1)
  let W := mass b v β
  let Z := fun y => ∑ i, W y i
  let N := fun y => ∑ i, W y i * v i
  let m := theta η β c t
  let p := weights η β c t
  have hpos (y) : 0 < Z y := partition_pos b v β y
  obtain ⟨s,hs⟩ := partition_max b v hc β hβ0.le
  have hex : ∃ y, ∀ z, thetaObjective η β c t z ≤ thetaObjective η β c t y :=
    ⟨s,fun z => Real.log_le_log (hpos z) (hs z)⟩
  have hmax (z) : thetaObjective η β c t z ≤ thetaObjective η β c t m := by
    dsimp only [m,theta]; rw [dif_pos hex]
    exact Classical.choose_spec hex z
  have to_mass (y : ℝ) (hy : ∀ z, thetaObjective η β c t z ≤ thetaObjective η β c t y) :
      ∀ z, Z z ≤ Z y := fun z => (Real.log_le_log_iff (hpos z) (hpos y)).mp (hy z)
  have prop (y : ℝ) (hy : ∀ z, thetaObjective η β c t z ≤ thetaObjective η β c t y) :=
    center_properties b v hc β y hβ0 (to_mass y hy)
  have mean_eq (y : ℝ) (hy : ∀ z, thetaObjective η β c t z ≤ thetaObjective η β c t y) :
      N y / Z y = y := by
    obtain ⟨hsum,hcent,_⟩ := prop y hy
    change ∑ i, (W y i/Z y)*(v i-y) = 0 at hcent
    change ∑ i, W y i/Z y = 1 at hsum
    simp_rw [mul_sub] at hcent
    rw [Finset.sum_sub_distrib,← Finset.sum_mul,hsum,one_mul] at hcent
    simp_rw [div_mul_eq_mul_div] at hcent
    rw [← Finset.sum_div] at hcent
    exact sub_eq_zero.mp hcent
  have hpdef (i) : p i = W m i / Z m := rfl
  have hanti := strict_center b v hc β hβ0 hβ
  have hchosen := mean_eq m hmax
  obtain ⟨hsum,hcent,hmrange⟩ := prop m hmax
  refine ⟨⟨m,hmax,?_⟩,hmax,?_,?_,?_⟩
  · intro y hy
    apply hanti.injective
    change N y / Z y - y = N m / Z m - m
    rw [mean_eq y hy,hchosen,sub_self,sub_self]
  · change m = ∑ i, p i*v i
    simp_rw [hpdef,div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    exact hchosen.symm
  · intro i
    change 0 ≤ p i*(1-(v i-m)/2)
    apply mul_nonneg (div_nonneg (Real.exp_pos _).le (hpos m).le)
    linarith [(hc i).2,hmrange.1]
  · change ∑ i, p i*(1-(v i-m)/2) = 1
    have hn : ∑ i, p i = 1 := hsum
    have hc' : ∑ i, p i*(v i-m) = 0 := hcent
    simp_rw [show ∀ i, p i*(1-(v i-m)/2) = p i-(p i*(v i-m))/2 by intro i; ring]
    rw [Finset.sum_sub_distrib,← Finset.sum_div,hc',hn]; norm_num
