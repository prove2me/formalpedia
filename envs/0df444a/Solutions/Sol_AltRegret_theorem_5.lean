-- Prove2me | solution 1 for AltRegret.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @Weiqiang
-- created : 2026-11-13T19:14:51.832916+00:00
-- url     : https://prove2.me/submissions/02805720-72f5-4f91-9d78-38680afc9207

import Definitions.Def_AltRegret_potential

namespace AltRegretProof5
open Set

/-- A tangent-line bound for a single exponential term on the loss interval. -/
private lemma scalar_bound (η β a z : ℝ) (hη : 0 ≤ η) (hη' : η ≤ 1/8) (hβ : β = η/4)
    (ha : a ∈ Icc (-2 : ℝ) 2) (hz : z ∈ Icc (-2 : ℝ) 2) :
    Real.exp (-η * (a+z) + β*(a^2-z^2)) ≤ 1 - η*(1-a/2)*(a+z) := by
  let f := fun y : ℝ => Real.exp (-η*y - β*y^2)
  let k := fun y : ℝ => -η - 2*β*y
  have hf (y : ℝ) : HasDerivAt f (f y * k y) y := by
    dsimp [f,k]
    convert (((hasDerivAt_id y).const_mul (-η)).sub
      (((hasDerivAt_id y).pow 2).const_mul β)).exp using 1 <;> simp <;> ring
  have hk (y : ℝ) : HasDerivAt k (-2*β) y := by
    dsimp [k]
    convert (hasDerivAt_const y (-η)).sub ((hasDerivAt_id y).const_mul (2*β)) using 1 <;> first | rfl | ring
  have hf' (y : ℝ) : HasDerivAt (fun w => f w * k w) (f y * (k y ^ 2 - 2*β)) y := by
    exact ((hf y).mul (hk y)).congr_deriv (by ring)
  have hconc : ConcaveOn ℝ (Icc (-2 : ℝ) 2) f := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
      (fun y _ => (hf y).continuousAt.continuousWithinAt)
      (fun y _ => (hf y).hasDerivWithinAt) (fun y _ => (hf' y).hasDerivWithinAt)
    intro y hy
    obtain ⟨hy₁,hy₂⟩ := interior_subset hy
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    have hb : 0 ≤ β := by linarith
    have h₁ : -2*η ≤ k y := by dsimp [k]; nlinarith [mul_nonneg hb (sub_nonneg.mpr hy₂)]
    have h₂ : k y ≤ 0 := by dsimp [k]; nlinarith [mul_nonneg hb (sub_nonneg.mpr hy₁)]
    nlinarith [mul_nonneg (sub_nonneg.mpr h₁) (neg_nonneg.mpr h₂),
      mul_nonneg hη (sub_nonneg.mpr hη'), mul_nonneg hη (sub_nonneg.mpr h₁)]
  have hma : -a ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [ha.2], by linarith [ha.1]⟩
  have hline : f z ≤ f (-a) + (f (-a)*k (-a))*(z-(-a)) := by
    rcases lt_trichotomy (-a) z with h|h|h
    · have hsl := hconc.slope_le_of_hasDerivAt hma hz h (hf (-a))
      rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h)] at hsl
      linarith
    · rw [← h]; ring_nf; rfl
    · have hsl := hconc.le_slope_of_hasDerivAt hz hma h (hf (-a))
      rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at hsl
      linarith
  have hid : Real.exp (-η*(a+z)+β*(a^2-z^2)) * f (-a) = f z := by
    dsimp [f]; rw [← Real.exp_add]; congr 1; ring
  apply le_of_mul_le_mul_right (a := f (-a)) _ (Real.exp_pos _)
  rw [hid]
  calc
    _ ≤ _ := hline
    _ = _ := by dsimp [k]; rw [hβ]; ring

/-- Average the tangent bounds, then absorb the common scalar shift. -/
private lemma weighted_bound {d : ℕ} (η β : ℝ) (hη : 0 ≤ η) (hη' : η ≤ 1/8) (hβ : β = η/4)
    (p a z : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (ha : ∀ i, a i ∈ Icc (-2 : ℝ) 2) (hz : ∀ i, z i ∈ Icc (-2 : ℝ) 2) :
    let M := ∑ i, p i * (1-a i/2) * (a i+z i)
    ∑ i, p i * Real.exp (η*(M-a i-z i)+β*((a i)^2-(z i)^2)) ≤ 1 := by
  intro M
  let g := fun i => -η*(a i+z i)+β*((a i)^2-(z i)^2)
  have hsum : (∑ i, p i * Real.exp (g i)) ≤ 1-η*M := by
    calc
      _ ≤ ∑ i, p i*(1-η*(1-a i/2)*(a i+z i)) := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (scalar_bound η β _ _ hη hη' hβ (ha i) (hz i)) (hp i)
      _ = _ := by
        dsimp [M]
        rw [Finset.mul_sum]
        simp_rw [show ∀ i, p i*(1-η*(1-a i/2)*(a i+z i)) =
          p i - η*(p i*(1-a i/2)*(a i+z i)) by intro i; ring]
        rw [Finset.sum_sub_distrib,hs]
  calc
    _ = (∑ i, p i*Real.exp (g i))*Real.exp (η*M) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [g]; ring
    _ ≤ Real.exp (-(η*M))*Real.exp (η*M) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact hsum.trans (by linarith [Real.add_one_le_exp (-(η*M))])
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

end AltRegretProof5

namespace AltRegretProof5
open Set
/-- One unnormalized weight at a candidate center. -/
private noncomputable def mass {d : ℕ} (b v : Fin d → ℝ) (β y : ℝ) (i : Fin d) : ℝ :=
  Real.exp (b i - β*(v i-y)^2)

/-- In positive dimension the normalizer is strictly positive. -/
private lemma partition_pos {d : ℕ} [Nonempty (Fin d)] (b v : Fin d → ℝ) (β y : ℝ) :
    0 < ∑ i, mass b v β y i :=
  Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

/-- Moving a candidate center into the loss interval reduces every squared distance. -/
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

/-- The compact interval therefore contains a global maximizer. -/
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

/-- At a maximizing center the derivative of the normalizer vanishes. -/
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

end AltRegretProof5

namespace AltRegretProof5
open AltRegret Set

/-- Cumulative effective loss of the plays through round n. -/
private noncomputable def learnerLoss {d : ℕ} (η β : ℝ) (c : ℕ → Fin d → ℝ) (n : ℕ) : ℝ :=
  ∑ s ∈ Finset.Icc 1 n, ∑ i, (lossAt c (s-1) i + lossAt c s i) * play η β c s i

/-- Bound the next potential by the current potential for two consecutive bounded losses. -/
private lemma round_bound {d : ℕ} [Nonempty (Fin d)] (η β : ℝ) (hη : 0 < η) (hη' : η ≤ 1/8)
    (hβ : β = η/4) (c : ℕ → Fin d → ℝ) (n : ℕ)
    (hv : ∀ i, lossAt c n i ∈ Icc (-1 : ℝ) 1)
    (hw : ∀ i, lossAt c (n+1) i ∈ Icc (-1 : ℝ) 1) :
    potential η β c (n+1+1) ≤ potential η β c (n+1) := by
  classical
  let v := lossAt c n
  let w := lossAt c (n+1)
  let b := fun i => -η * effCumLoss c n i
  let m := theta η β c (n+1)
  let p := weights η β c (n+1)
  let x := play η β c (n+1)
  let a := fun i => v i-m
  let Z := ∑ i, mass b v β m i
  let B := η * learnerLoss η β c n
  have hbpos : 0 < β := by linarith
  have hθ (y : ℝ) : thetaObjective η β c (n+1) y = Real.log (∑ i, mass b v β y i) := by
    simp only [thetaObjective, Nat.add_sub_cancel, b,v,mass]
  obtain ⟨s,hs⟩ := partition_max b v hv β hbpos.le
  have hex : ∃ y, ∀ z, thetaObjective η β c (n+1) z ≤ thetaObjective η β c (n+1) y :=
    ⟨s,fun z => by rw [hθ,hθ]; exact Real.log_le_log (partition_pos ..) (hs z)⟩
  have hm (z) : ∑ i, mass b v β z i ≤ Z := by
    apply (Real.log_le_log_iff (partition_pos ..) (partition_pos ..)).mp
    rw [← hθ,show Real.log Z = thetaObjective η β c (n+1) m from (hθ m).symm]
    dsimp only [m,theta]
    rw [dif_pos hex]
    exact Classical.choose_spec hex z
  have hpdef (i) : p i = mass b v β m i / Z := by
    simp only [p,weights,Nat.add_sub_cancel,b,v,mass,Z,m]
  have hcenter := center_properties b v hv β m hbpos hm
  change (∑ i, mass b v β m i / Z = 1) ∧ _ at hcenter
  have hsum : ∑ i, p i = 1 := by simp only [hpdef]; exact hcenter.1
  have hmean : ∑ i, p i * a i = 0 := by simp only [hpdef]; exact hcenter.2.1
  have hp (i) : 0 ≤ p i := by rw [hpdef]; exact div_nonneg (Real.exp_pos _).le (partition_pos ..).le
  have ha (i) : a i ∈ Icc (-2 : ℝ) 2 := by
    dsimp only [a]; exact ⟨by linarith [(hv i).1,hcenter.2.2.2],by linarith [(hv i).2,hcenter.2.2.1]⟩
  have hx (i) : x i = p i*(1-a i/2) := by simp only [x,p,play,a,v,m,Nat.add_sub_cancel]
  have hxs : ∑ i, x i = 1 := by
    simp_rw [hx,show ∀ i, p i*(1-a i/2) = p i - (p i*a i)/2 by intro i; ring]
    rw [Finset.sum_sub_distrib,← Finset.sum_div,hmean,hsum]; norm_num
  have hR (i) : η * regretVector η β c n i = B + b i := by
    dsimp only [regretVector, learnerLoss,effCumLoss,B,b]; ring
  have hstep (i) : regretVector η β c (n+1) i =
      regretVector η β c n i + (∑ j, (v j+w j)*x j) - (v i+w i) := by
    simp only [regretVector,Finset.sum_Icc_succ_top (Nat.le_add_left 1 n),Nat.add_sub_cancel,x,v,w]
    ring
  have ho (y) : potentialObjective η β c (n+1) y =
      Real.log (Real.exp B * ∑ i, mass b v β y i) := by
    simp only [potentialObjective,Nat.add_sub_cancel,v,mass,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← Real.exp_add,hR]; congr 1; ring
  have hcur : potential η β c (n+1) = Real.log (Real.exp B * Z) := by
    apply ciSup_eq_of_forall_le_of_forall_lt_exists_gt
    · intro y
      rw [ho]
      apply Real.log_le_log (mul_pos (Real.exp_pos _) (partition_pos ..))
      exact mul_le_mul_of_nonneg_left (hm y) (Real.exp_pos _).le
    · intro l hl; exact ⟨m,by rwa [ho]⟩
  rw [hcur]
  apply ciSup_le
  intro y
  let b' := fun i => η * regretVector η β c (n+1) i
  obtain ⟨q,hq,hclip⟩ := clip_partition b' w hw β hbpos.le y
  have hnext (r : ℝ) : potentialObjective η β c (n+1+1) r =
      Real.log (∑ i, mass b' w β r i) := by
    simp only [potentialObjective,Nat.add_sub_cancel,mass,b',w]
  rw [hnext]
  apply (Real.log_le_log (partition_pos ..) hclip).trans
  let z := fun i => w i-q
  have hz (i) : z i ∈ Icc (-2 : ℝ) 2 := by
    dsimp only [z]; exact ⟨by linarith [(hw i).1,hq.2],by linarith [(hw i).2,hq.1]⟩
  let M := ∑ i, p i*(1-a i/2)*(a i+z i)
  have hM : (∑ j, (v j+w j)*x j) = M+(m+q) := by
    calc
      _ = ∑ j, (p j*(1-a j/2)*(a j+z j) + (m+q)*x j) := by
        apply Finset.sum_congr rfl; intro j _; rw [hx]; dsimp [a,z]; ring
      _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum,hxs,mul_one]
  let D := fun i => η*(M-a i-z i)+β*((a i)^2-(z i)^2)
  have hWeighted : (∑ i, p i * Real.exp (D i)) ≤ 1 :=
    weighted_bound η β hη.le hη' hβ p a z hp hsum ha hz
  have hpart (i) : mass b' w β q i = Real.exp B * Z * (p i * Real.exp (D i)) := by
    have hZ : Z ≠ 0 := (partition_pos b v β m).ne'
    rw [hpdef,show Real.exp B * Z * (mass b v β m i / Z * Real.exp (D i))
      = Real.exp B * mass b v β m i * Real.exp (D i) by field_simp [hZ]]
    dsimp only [mass,b']
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    rw [hstep,hM]
    dsimp only [D,a,z]
    linear_combination hR i
  apply Real.log_le_log (partition_pos ..)
  simp_rw [hpart]
  rw [← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left hWeighted (mul_pos (Real.exp_pos _) (partition_pos ..)).le).trans_eq (mul_one _)

end AltRegretProof5

open AltRegret
open AltRegretProof5

theorem solution (η β : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 8) (hβ : β = η / 4) {d : ℕ}
    (c : ℕ → Fin d → ℝ) (t : ℕ) (ht : 1 ≤ t)
    (hc : ∀ s, 1 ≤ s → s ≤ t → ∀ i, c s i ∈ Set.Icc (-1 : ℝ) 1) :
    potential η β c (t + 1) ≤ potential η β c t ∧ potential η β c t ≤ Real.log d := by
  classical
  rcases eq_or_lt_of_le hη0 with hzero|hpos
  · subst η
    have : β = 0 := by simpa using hβ
    subst β
    simp [potential,potentialObjective,ciSup_const]
  cases d with
  | zero => simp [potential,potentialObjective,ciSup_const]
  | succ d =>
    have hb : 0 ≤ β := by linarith
    have hinit : potential η β c 1 ≤ Real.log (d+1 : ℕ) := by
      apply ciSup_le
      intro y
      have he : Real.exp (-(β*(0-y)^2)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hb (sq_nonneg _)))
      simp [potentialObjective,regretVector,lossAt]
      first
      | exact Real.log_le_log (by positivity) (by nlinarith)
      | apply Real.log_le_log (by positivity); simpa using mul_le_mul_of_nonneg_left he (show (0:ℝ) ≤ d+1 by positivity)
    have hbox (s : ℕ) (hs : s ≤ t) : ∀ i, lossAt c s i ∈ Set.Icc (-1 : ℝ) 1 := by
      cases s with
      | zero => simp [lossAt]
      | succ s => simpa [lossAt] using hc (s+1) (by omega) hs
    have hmono (s : ℕ) (hs : s+1 ≤ t) :
        potential η β c (s+1+1) ≤ potential η β c (s+1) :=
      round_bound η β hpos hη hβ c s (hbox s (by omega)) (hbox (s+1) hs)
    cases t with
    | zero => omega
    | succ k =>
      refine ⟨hmono k le_rfl,?_⟩
      have bound (j : ℕ) (hj : j ≤ k) : potential η β c (j+1) ≤ Real.log (d+1 : ℕ) := by
        induction j with
        | zero => exact hinit
        | succ j ih => exact (hmono j (by omega)).trans (ih (by omega))
      exact bound k le_rfl
