-- Prove2me | solution 1 for AugLagLLC.Penalty.theorem_5_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T10:45:47.852972+00:00
-- url     : https://prove2.me/submissions/d2745f15-198a-4688-9d36-b63e15e68476

import Mathlib
import Definitions.Def_AugLagLLC_Penalty_SecondOrder

open Filter
open scoped Topology

set_option autoImplicit false

namespace AugLagPenAux

open InnerProductSpace

section Grad

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma hg_add {f g : E → ℝ} {a b x : E} (hf : HasGradientAt f a x) (hg : HasGradientAt g b x) :
    HasGradientAt (fun y => f y + g y) (a + b) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  rw [map_add]; exact hf.add hg

lemma hg_const_mul {f : E → ℝ} {a x : E} (c : ℝ) (hf : HasGradientAt f a x) :
    HasGradientAt (fun y => c * f y) (c • a) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  rw [map_smulₛₗ, conj_trivial]; exact hf.const_mul c

lemma hg_sum {ι : Type*} (s : Finset ι) {f : ι → E → ℝ} {a : ι → E} {x : E}
    (hf : ∀ i ∈ s, HasGradientAt (f i) (a i) x) :
    HasGradientAt (fun y => ∑ i ∈ s, f i y) (∑ i ∈ s, a i) x := by
  simp only [hasGradientAt_iff_hasFDerivAt] at *
  rw [map_sum]; exact HasFDerivAt.fun_sum hf

lemma hg_comp {f : E → ℝ} {a x : E} {q : ℝ → ℝ} {q' : ℝ} (hq : HasDerivAt q q' (f x))
    (hf : HasGradientAt f a x) : HasGradientAt (fun y => q (f y)) (q' • a) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  rw [map_smulₛₗ, conj_trivial]; exact hq.comp_hasFDerivAt x hf

lemma hg_sq_shift {s : E → ℝ} {a x : E} (c : ℝ) (hs : HasGradientAt s a x) :
    HasGradientAt (fun y => (s y + c) ^ 2) ((2 * (s x + c)) • a) x := by
  have hq : HasDerivAt (fun t : ℝ => (t + c) ^ 2) (2 * (s x + c)) (s x) := by
    have := ((hasDerivAt_id (s x)).add_const c).pow 2
    exact this.congr_deriv (by simp)
  exact hg_comp hq hs

lemma hgC1 {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x : E) : HasGradientAt f (gradient f x) x :=
  (hf.differentiable one_ne_zero x).hasGradientAt

lemma hgcont {f : E → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (gradient f) :=
  (toDual ℝ E).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)

/-- `ℝ`-linear version of `(toDual ℝ E).symm`. -/
noncomputable def dualSymmL : StrongDual ℝ E →ₗ[ℝ] E where
  toFun f := (toDual ℝ E).symm f
  map_add' f g := map_add _ f g
  map_smul' c f := by rw [map_smulₛₗ, conj_trivial]; rfl

noncomputable def dualSymmCL : StrongDual ℝ E →L[ℝ] E :=
  LinearMap.mkContinuous dualSymmL 1 (fun f => by
    simp [dualSymmL])

lemma grad_diffAt {φ : E → ℝ} {x : E} (h : ContDiffAt ℝ 2 φ x) :
    DifferentiableAt ℝ (gradient φ) x := by
  have e : gradient φ = fun y => (dualSymmCL : StrongDual ℝ E →L[ℝ] E) (fderiv ℝ φ y) := rfl
  rw [e]
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact dualSymmCL.differentiableAt.comp x hd

end Grad

section Lin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The KKT block map at `π = 0`. -/
noncomputable def kmap {m1 m2 : ℕ} (H : E →L[ℝ] E) (g1 : Fin m1 → E) (g2 : Fin m2 → E) :
    (E × (Fin m1 → ℝ) × (Fin m2 → ℝ)) →ₗ[ℝ] (E × (Fin m1 → ℝ) × (Fin m2 → ℝ)) where
  toFun w := (H w.1 + ∑ i, w.2.1 i • g1 i + ∑ j, w.2.2 j • g2 j,
    fun i => inner ℝ (g1 i) w.1, fun j => inner ℝ (g2 j) w.1)
  map_add' w w' := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, add_smul,
        Finset.sum_add_distrib]
      abel
    · funext i; simp [inner_add_right]
    · funext j; simp [inner_add_right]
  map_smul' c w := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul, smul_eq_mul, mul_smul,
        ← Finset.smul_sum, RingHom.id_apply, smul_add]
    · funext i; simp [inner_smul_right]
    · funext j; simp [inner_smul_right]

lemma kmap_apply {m1 m2 : ℕ} (H : E →L[ℝ] E) (g1 : Fin m1 → E) (g2 : Fin m2 → E)
    (w : E × (Fin m1 → ℝ) × (Fin m2 → ℝ)) :
    kmap H g1 g2 w = (H w.1 + ∑ i, w.2.1 i • g1 i + ∑ j, w.2.2 j • g2 j,
      fun i => inner ℝ (g1 i) w.1, fun j => inner ℝ (g2 j) w.1) := rfl

lemma kmap_inj {m1 m2 : ℕ} (H : E →L[ℝ] E) (g1 : Fin m1 → E) (g2 : Fin m2 → E)
    (hpos : ∀ z : E, z ≠ 0 → (∀ i, inner ℝ (g1 i) z = 0) → (∀ j, inner ℝ (g2 j) z = 0) →
      0 < inner ℝ (H z) z)
    (hli : LinearIndependent ℝ (Sum.elim g1 g2)) : Function.Injective (kmap H g1 g2) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨d, a, b⟩ hw
  rw [kmap_apply] at hw
  simp only [Prod.mk_eq_zero] at hw
  obtain ⟨h1, h2, h3⟩ := hw
  have h2' : ∀ i, inner ℝ (g1 i) d = 0 := fun i => congrFun h2 i
  have h3' : ∀ j, inner ℝ (g2 j) d = 0 := fun j => congrFun h3 j
  have hHd : inner ℝ (H d) d = (0 : ℝ) := by
    have := congrArg (fun y => inner ℝ y d) h1
    simp only [inner_add_left, sum_inner, real_inner_smul_left, h2', h3', mul_zero,
      Finset.sum_const_zero, add_zero, inner_zero_left] at this
    exact this
  have hd : d = 0 := by
    by_contra hne
    have := hpos d hne h2' h3'
    linarith
  subst hd
  simp only [map_zero, zero_add] at h1
  have hall := Fintype.linearIndependent_iff.mp hli (Sum.elim a b) (by
    rw [Fintype.sum_sum_type]; simpa using h1)
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext i; simpa using hall (Sum.inl i)
  · funext j; simpa using hall (Sum.inr j)

end Lin

lemma antilip {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : V →ₗ[ℝ] V) (hf : Function.Injective f) : ∃ C > 0, ∀ w, ‖w‖ ≤ C * ‖f w‖ := by
  set e := LinearEquiv.ofInjectiveEndo f hf
  set L : V →L[ℝ] V := LinearMap.toContinuousLinearMap (e.symm : V →ₗ[ℝ] V)
  refine ⟨‖L‖ + 1, by positivity, fun w => ?_⟩
  have hw : w = L (f w) := by
    have : f w = e w := by simp [e, LinearEquiv.coe_ofInjectiveEndo]
    rw [this]; simp [L]
  calc ‖w‖ = ‖L (f w)‖ := by rw [← hw]
    _ ≤ ‖L‖ * ‖f w‖ := L.le_opNorm _
    _ ≤ (‖L‖ + 1) * ‖f w‖ := by nlinarith [norm_nonneg (f w)]

section Problem

open AugLagLLC.Penalty

variable {n m1 m2 : ℕ}

lemma grad_augLag0 (P : Problem n m1 0 m2 0) (hP : P.IsC1) (x : EuclideanSpace ℝ (Fin n))
    (lam : Fin m1 → ℝ) (mu : Fin 0 → ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    gradient (fun y => P.augLag y lam mu ρ) x =
      gradient P.f x + ∑ i, (lam i + ρ * P.h1 i x) • gradient (P.h1 i) x := by
  obtain ⟨hf, hh1, -, -, -⟩ := hP
  have hG : HasGradientAt (fun y => P.augLag y lam mu ρ)
      (gradient P.f x + (ρ / 2) • ∑ i, (2 * (P.h1 i x + lam i / ρ)) • gradient (P.h1 i) x
        + (ρ / 2) • ∑ i : Fin 0, (0 : EuclideanSpace ℝ (Fin n))) x := by
    unfold Problem.augLag
    exact hg_add (hg_add (hgC1 hf x) (hg_const_mul _ (hg_sum _ fun i _ =>
      hg_sq_shift _ (hgC1 (hh1 i) x)))) (hg_const_mul _ (hg_sum _ fun i _ => i.elim0))
  rw [hG.gradient]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, smul_zero, add_zero, Finset.smul_sum,
    smul_smul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1; field_simp; ring

lemma grad_lagr0 (P : Problem n m1 0 m2 0) (hP : P.IsC1) (lam : Fin m1 → ℝ) (v : Fin m2 → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (P.lagr0 lam v) x = gradient P.f x + ∑ i, lam i • gradient (P.h1 i) x
      + ∑ j, v j • gradient (P.h2 j) x := by
  obtain ⟨hf, hh1, -, hh2, -⟩ := hP
  refine HasGradientAt.gradient ?_
  unfold Problem.lagr0
  exact hg_add (hg_add (hgC1 hf x) (hg_sum _ fun i _ => hg_const_mul _ (hgC1 (hh1 i) x)))
    (hg_sum _ fun j _ => hg_const_mul _ (hgC1 (hh2 j) x))

lemma lagr0_C2 (P : Problem n m1 0 m2 0) (lam : Fin m1 → ℝ) (v : Fin m2 → ℝ)
    (xs : EuclideanSpace ℝ (Fin n)) (hC2 : P.IsC2At xs) : ContDiffAt ℝ 2 (P.lagr0 lam v) xs := by
  obtain ⟨hf, hh1, -, hh2, -⟩ := hC2
  unfold Problem.lagr0
  exact (hf.add (ContDiffAt.sum fun i _ => contDiffAt_const.mul (hh1 i))).add
    (ContDiffAt.sum fun j _ => contDiffAt_const.mul (hh2 j))

set_option maxHeartbeats 1000000 in
lemma key_est (P : Problem n m1 0 m2 0) (hP : P.IsC1)
    {τ γ ρ1 : ℝ} {lamMin lamMax : Fin m1 → ℝ} {muMax : Fin 0 → ℝ} {ε : ℕ → ℝ}
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {ρ : ℕ → ℝ} {lamBar : ℕ → Fin m1 → ℝ}
    {muBar : ℕ → Fin 0 → ℝ} {v : ℕ → Fin m2 → ℝ} {u : ℕ → Fin 0 → ℝ}
    (hrun : P.IsRun τ γ ρ1 lamMin lamMax muMax ε x ρ lamBar muBar v u)
    {xs : EuclideanSpace ℝ (Fin n)} (hlim : Tendsto x atTop (𝓝 xs))
    (hfeas : xs ∈ P.Omega1 ∩ P.Omega2)
    (hLI : LinearIndependent ℝ
      (Sum.elim (fun i => gradient (P.h1 i) xs) (fun i => gradient (P.h2 i) xs)))
    (hC2 : P.IsC2At xs)
    (lamS : Fin m1 → ℝ) (vS : Fin m2 → ℝ) (hSOSC : P.SOSC0 lamS vS xs)
    (hρpos : ∀ k, 1 ≤ k → 0 < ρ k) (hρ : Tendsto ρ atTop atTop) :
    ∃ C > 0, ∀ᶠ k in atTop,
      ‖P.lamNext x ρ lamBar k - lamS‖ ≤ C * (ε k + ‖lamBar k - lamS‖ / ρ k) := by
  set g1 : Fin m1 → EuclideanSpace ℝ (Fin n) := fun i => gradient (P.h1 i) xs with hg1
  set g2 : Fin m2 → EuclideanSpace ℝ (Fin n) := fun j => gradient (P.h2 j) xs with hg2
  set G := gradient (P.lagr0 lamS vS) with hG
  set H := hess (P.lagr0 lamS vS) xs with hH
  have hinj := kmap_inj H g1 g2 hSOSC.2 hLI
  obtain ⟨C0, hC0, hC0w⟩ := antilip (kmap H g1 g2) hinj
  set N : ℝ := 3 + m1 + m2 with hN
  have hNpos : 0 < N := by positivity
  set c : ℝ := 1 / (4 * C0 * N) with hc
  have hcpos : 0 < c := by positivity
  obtain ⟨hf, hh1, -, hh2, -⟩ := hP
  -- Taylor remainder of the gradient of the Lagrangian
  have hHd : HasFDerivAt G H xs := (grad_diffAt (lagr0_C2 P lamS vS xs hC2)).hasFDerivAt
  have e1 : ∀ᶠ k in atTop, ‖G (x k) - G xs - H (x k - xs)‖ ≤ c * ‖x k - xs‖ :=
    hlim.eventually (hHd.isLittleO.def hcpos)
  have e2 : ∀ᶠ k in atTop, ∀ i, |P.h1 i (x k) - P.h1 i xs - inner ℝ (g1 i) (x k - xs)|
      ≤ c * ‖x k - xs‖ := by
    rw [eventually_all]; intro i
    have := (hasGradientAt_iff_isLittleO.mp (hgC1 (hh1 i) xs)).def hcpos
    exact hlim.eventually (this.mono fun y hy => by rw [Real.norm_eq_abs] at hy; exact hy)
  have e3 : ∀ᶠ k in atTop, ∀ j, |P.h2 j (x k) - P.h2 j xs - inner ℝ (g2 j) (x k - xs)|
      ≤ c * ‖x k - xs‖ := by
    rw [eventually_all]; intro j
    have := (hasGradientAt_iff_isLittleO.mp (hgC1 (hh2 j) xs)).def hcpos
    exact hlim.eventually (this.mono fun y hy => by rw [Real.norm_eq_abs] at hy; exact hy)
  have e4 : ∀ᶠ k in atTop, ∀ i, ‖gradient (P.h1 i) (x k) - g1 i‖ ≤ c := by
    rw [eventually_all]; intro i
    have ht : Tendsto (fun k => gradient (P.h1 i) (x k)) atTop (𝓝 (g1 i)) :=
      ((hgcont (hh1 i)).tendsto xs).comp hlim
    exact (ht.eventually (Metric.closedBall_mem_nhds _ hcpos)).mono fun k hk => by
      rw [dist_eq_norm] at hk; exact hk
  have e5 : ∀ᶠ k in atTop, ∀ j, ‖gradient (P.h2 j) (x k) - g2 j‖ ≤ c := by
    rw [eventually_all]; intro j
    have ht : Tendsto (fun k => gradient (P.h2 j) (x k)) atTop (𝓝 (g2 j)) :=
      ((hgcont (hh2 j)).tendsto xs).comp hlim
    exact (ht.eventually (Metric.closedBall_mem_nhds _ hcpos)).mono fun k hk => by
      rw [dist_eq_norm] at hk; exact hk
  have e6 : ∀ᶠ k in atTop, 4 * C0 ≤ ρ k := hρ.eventually (eventually_ge_atTop _)
  refine ⟨4 * C0, by positivity, ?_⟩
  filter_upwards [e1, e2, e3, e4, e5, e6, eventually_ge_atTop 1] with k h1k h2k h3k h4k h5k h6k hk
  have hρk : 0 < ρ k := hρpos k hk
  obtain ⟨⟨ε1, ε2, ε3, hε1, hε1k, -, -, -, hε3k, h31, -, -, h34⟩, -⟩ := hrun.2.2.2 k hk
  have hεk : 0 ≤ ε k := hε1.trans hε1k
  set d := x k - xs with hd
  set a : Fin m1 → ℝ := P.lamNext x ρ lamBar k - lamS with ha
  set b : Fin m2 → ℝ := v k - vS with hb
  set w : EuclideanSpace ℝ (Fin n) × (Fin m1 → ℝ) × (Fin m2 → ℝ) := (d, a, b) with hw
  set B := ‖lamBar k - lamS‖ with hB
  have hda : ‖d‖ ≤ ‖w‖ := norm_fst_le w
  have haw : ‖a‖ ≤ ‖w‖ := (norm_fst_le w.2).trans (norm_snd_le w)
  have hbw : ‖b‖ ≤ ‖w‖ := (norm_snd_le w.2).trans (norm_snd_le w)
  have hwn : 0 ≤ ‖w‖ := norm_nonneg _
  -- residual of (3.1)
  set R0 := gradient (fun y => P.augLag y (lamBar k) (muBar k) (ρ k)) (x k)
      + ∑ j, v k j • gradient (P.h2 j) (x k) + ∑ j, u k j • gradient (P.g2 j) (x k) with hR0
  have hR0n : ‖R0‖ ≤ ε k := h31.trans hε1k
  have hR0e : R0 = gradient P.f (x k)
      + ∑ i, (lamBar k i + ρ k * P.h1 i (x k)) • gradient (P.h1 i) (x k)
      + ∑ j, v k j • gradient (P.h2 j) (x k) := by
    rw [hR0, grad_augLag0 P ⟨hf, hh1, fun i => i.elim0, hh2, fun i => i.elim0⟩ _ _ _ hρk.ne']
    simp
  have hGxs : G xs = 0 := hSOSC.1
  have hGx : G (x k) = gradient P.f (x k) + ∑ i, lamS i • gradient (P.h1 i) (x k)
      + ∑ j, vS j • gradient (P.h2 j) (x k) :=
    grad_lagr0 P ⟨hf, hh1, fun i => i.elim0, hh2, fun i => i.elim0⟩ lamS vS (x k)
  -- first block
  have hT1 : H d + ∑ i, a i • g1 i + ∑ j, b j • g2 j = R0 - (G (x k) - G xs - H d)
      - ∑ i, a i • (gradient (P.h1 i) (x k) - g1 i)
      - ∑ j, b j • (gradient (P.h2 j) (x k) - g2 j) := by
    rw [hR0e, hGxs, hGx]
    simp only [ha, hb, Pi.sub_apply, Problem.lamNext, smul_sub, sub_smul,
      Finset.sum_sub_distrib]
    abel
  have hsum1 : ‖∑ i, a i • (gradient (P.h1 i) (x k) - g1 i)‖ ≤ m1 * c * ‖w‖ := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ i ∈ Finset.univ, ‖a i • (gradient (P.h1 i) (x k) - g1 i)‖ ≤ c * ‖w‖ := by
      intro i _
      rw [norm_smul]
      have := (norm_le_pi_norm a i).trans haw
      nlinarith [h4k i, norm_nonneg (a i), norm_nonneg (gradient (P.h1 i) (x k) - g1 i)]
    refine (Finset.sum_le_sum this).trans ?_
    simp
    nlinarith
  have hsum2 : ‖∑ j, b j • (gradient (P.h2 j) (x k) - g2 j)‖ ≤ m2 * c * ‖w‖ := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ j ∈ Finset.univ, ‖b j • (gradient (P.h2 j) (x k) - g2 j)‖ ≤ c * ‖w‖ := by
      intro j _
      rw [norm_smul]
      have := (norm_le_pi_norm b j).trans hbw
      nlinarith [h5k j, norm_nonneg (b j), norm_nonneg (gradient (P.h2 j) (x k) - g2 j)]
    refine (Finset.sum_le_sum this).trans ?_
    simp
    nlinarith
  have hn1 : ‖H d + ∑ i, a i • g1 i + ∑ j, b j • g2 j‖
      ≤ ε k + c * ‖d‖ + m1 * c * ‖w‖ + m2 * c * ‖w‖ := by
    rw [hT1]
    have i1 := norm_sub_le (R0 - (G (x k) - G xs - H d)
      - ∑ i, a i • (gradient (P.h1 i) (x k) - g1 i)) (∑ j, b j • (gradient (P.h2 j) (x k) - g2 j))
    have i2 := norm_sub_le (R0 - (G (x k) - G xs - H d))
      (∑ i, a i • (gradient (P.h1 i) (x k) - g1 i))
    have i3 := norm_sub_le R0 (G (x k) - G xs - H d)
    linarith [h1k]
  -- second block
  have hn2 : ‖(fun i => inner ℝ (g1 i) d : Fin m1 → ℝ)‖ ≤ (‖w‖ + B) / ρ k + c * ‖d‖ := by
    have hnn : 0 ≤ (‖w‖ + B) / ρ k + c * ‖d‖ :=
      add_nonneg (div_nonneg (add_nonneg hwn (norm_nonneg _)) hρk.le)
        (mul_nonneg hcpos.le (norm_nonneg _))
    refine (pi_norm_le_iff_of_nonneg hnn).2 fun i => ?_
    rw [Real.norm_eq_abs]
    have hz : P.h1 i xs = 0 := hfeas.1.1 i
    have hai : |a i| ≤ ‖w‖ := (Real.norm_eq_abs _ ▸ norm_le_pi_norm a i).trans haw
    have hbi : |lamBar k i - lamS i| ≤ B :=
      (Real.norm_eq_abs _ ▸ norm_le_pi_norm (lamBar k - lamS) i)
    have hh : P.h1 i (x k) = (a i - (lamBar k i - lamS i)) / ρ k := by
      simp only [ha, Pi.sub_apply, Problem.lamNext]; field_simp; ring
    have hhb : |P.h1 i (x k)| ≤ (‖w‖ + B) / ρ k := by
      rw [hh, abs_div, abs_of_pos hρk]
      exact div_le_div_of_nonneg_right ((abs_sub _ _).trans (add_le_add hai hbi)) hρk.le
    have := h2k i
    rw [hz, sub_zero (P.h1 i (x k))] at this
    calc |inner ℝ (g1 i) d| = |P.h1 i (x k) - (P.h1 i (x k) - inner ℝ (g1 i) d)| := by ring_nf
      _ ≤ |P.h1 i (x k)| + |P.h1 i (x k) - inner ℝ (g1 i) d| := abs_sub _ _
      _ ≤ _ := add_le_add hhb this
  -- third block
  have hn3 : ‖(fun j => inner ℝ (g2 j) d : Fin m2 → ℝ)‖ ≤ ε k + c * ‖d‖ := by
    have hnn : 0 ≤ ε k + c * ‖d‖ := add_nonneg hεk (mul_nonneg hcpos.le (norm_nonneg _))
    refine (pi_norm_le_iff_of_nonneg hnn).2 fun j => ?_
    rw [Real.norm_eq_abs]
    have hz : P.h2 j xs = 0 := hfeas.2.1 j
    have hhj : |P.h2 j (x k)| ≤ ε k :=
      ((Real.norm_eq_abs _ ▸ norm_le_pi_norm (P.h2vec (x k)) j)).trans (h34.trans
        (by linarith))
    have := h3k j
    rw [hz, sub_zero (P.h2 j (x k))] at this
    calc |inner ℝ (g2 j) d| = |P.h2 j (x k) - (P.h2 j (x k) - inner ℝ (g2 j) d)| := by ring_nf
      _ ≤ |P.h2 j (x k)| + |P.h2 j (x k) - inner ℝ (g2 j) d| := abs_sub _ _
      _ ≤ _ := add_le_add hhj this
  have hK : ‖kmap H g1 g2 w‖ ≤ 2 * ε k + B / ρ k + ‖w‖ / ρ k + N * c * ‖w‖ := by
    rw [kmap_apply, Prod.norm_def, Prod.norm_def]
    have hBn : 0 ≤ B := norm_nonneg _
    have : (‖w‖ + B) / ρ k = ‖w‖ / ρ k + B / ρ k := add_div _ _ _
    have hcd : c * ‖d‖ ≤ c * ‖w‖ := mul_le_mul_of_nonneg_left hda hcpos.le
    have hmm : 0 ≤ ((m1 : ℝ) + m2) * (c * ‖w‖) := by positivity
    have hcw : 0 ≤ c * ‖w‖ := by positivity
    have hBr : 0 ≤ B / ρ k := div_nonneg hBn hρk.le
    have hwr : 0 ≤ ‖w‖ / ρ k := div_nonneg hwn hρk.le
    have hNe : N * c * ‖w‖ = 3 * (c * ‖w‖) + ((m1 : ℝ) + m2) * (c * ‖w‖) := by rw [hN]; ring
    have hm1 : (m1 : ℝ) * c * ‖w‖ + m2 * c * ‖w‖ = ((m1 : ℝ) + m2) * (c * ‖w‖) := by ring
    refine max_le (hn1.trans ?_) (max_le (hn2.trans ?_) (hn3.trans ?_))
    · linarith
    · linarith
    · linarith
  have hw1 := hC0w w
  have hq1 : C0 * (‖w‖ / ρ k) ≤ ‖w‖ / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ hρk (by norm_num)]
    nlinarith
  have hq2 : C0 * (N * c * ‖w‖) = ‖w‖ / 4 := by
    rw [hc]; field_simp
  have hmain : ‖w‖ ≤ 2 * C0 * (2 * ε k + B / ρ k) := by
    nlinarith
  calc ‖P.lamNext x ρ lamBar k - lamS‖ = ‖a‖ := rfl
    _ ≤ ‖w‖ := haw
    _ ≤ 2 * C0 * (2 * ε k + B / ρ k) := hmain
    _ ≤ 4 * C0 * (ε k + B / ρ k) := by
      have : 0 ≤ B / ρ k := by positivity
      nlinarith

end Problem

lemma contraction {A' A ε' η' t' ρ' C δ : ℝ} (hest : A' ≤ C * (ε' + A / ρ'))
    (hεη : ε' ≤ η' * t') (ht : t' * ρ' ≤ A' + A) (hη : C * |η'| ≤ 1 / 2) (hρ1 : 1 ≤ ρ')
    (hρδ : (1 + 2 * C) ≤ δ * ρ') (hA : 0 ≤ A) (hA' : 0 ≤ A') (hC : 0 < C) (ht0 : 0 ≤ t') :
    A' ≤ δ * A := by
  have hρ : 0 < ρ' := by linarith
  have h1 : ρ' * A' ≤ C * (ρ' * ε') + C * A := by
    have := mul_le_mul_of_nonneg_left hest hρ.le
    have e : ρ' * (C * (ε' + A / ρ')) = C * (ρ' * ε') + C * A := by field_simp
    linarith
  have h2 : ε' ≤ |η'| * t' := hεη.trans (mul_le_mul_of_nonneg_right (le_abs_self _) ht0)
  have h3 : ρ' * ε' ≤ |η'| * (A' + A) := by
    have := mul_le_mul_of_nonneg_left h2 hρ.le
    have h4 : |η'| * (t' * ρ') ≤ |η'| * (A' + A) := mul_le_mul_of_nonneg_left ht (abs_nonneg _)
    nlinarith
  have h5 : C * (ρ' * ε') ≤ (A' + A) / 2 := by
    have := mul_le_mul_of_nonneg_left h3 hC.le
    have h6 : C * (|η'| * (A' + A)) ≤ (1 / 2) * (A' + A) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hη (by linarith)
    linarith
  have h7 : ρ' * A' ≤ (1 + 2 * C) * A := by nlinarith
  have h8 : ρ' * A' ≤ ρ' * (δ * A) := by nlinarith
  exact le_of_mul_le_mul_left h8 hρ

lemma ratio_step {A0 A1 A2 D1 D2 r1 r2 δ τ : ℝ} (hδ : δ * (1 + δ + τ) ≤ τ) (hτ : 0 < τ)
    (hδ0 : 0 ≤ δ) (h1 : A2 ≤ δ * A1) (h0 : A1 ≤ δ * A0) (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hD2 : D2 ≤ A2 + A1) (hD1 : A0 - A1 ≤ D1) (hr : 0 < r1) (hr12 : r1 ≤ r2) :
    D2 / r2 ≤ τ * (D1 / r1) := by
  have hr2 : 0 < r2 := hr.trans_le hr12
  have k1 : D2 ≤ (1 + δ) * A1 := by nlinarith
  have k2 : (1 + δ + τ) * A1 ≤ τ * A0 := by nlinarith
  have k3 : D2 ≤ τ * D1 := by nlinarith
  have hD1n : 0 ≤ D1 := by nlinarith
  calc D2 / r2 ≤ (τ * D1) / r2 := div_le_div_of_nonneg_right k3 hr2.le
    _ ≤ (τ * D1) / r1 := div_le_div_of_nonneg_left (mul_nonneg hτ.le hD1n) hr hr12
    _ = τ * (D1 / r1) := mul_div_assoc _ _ _

end AugLagPenAux

set_option maxHeartbeats 1000000 in
open Filter Topology AugLagLLC.Penalty in
theorem solution
    {n m1 m2 : ℕ} (P : Problem n m1 0 m2 0) (hP : P.IsC1)
    {τ γ ρ1 : ℝ} {lamMin lamMax : Fin m1 → ℝ} {muMax : Fin 0 → ℝ} {ε : ℕ → ℝ}
    (hpar : Problem.IsParams τ γ ρ1 lamMin lamMax muMax ε)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {ρ : ℕ → ℝ} {lamBar : ℕ → Fin m1 → ℝ}
    {muBar : ℕ → Fin 0 → ℝ} {v : ℕ → Fin m2 → ℝ} {u : ℕ → Fin 0 → ℝ}
    -- Assumption 1: a run of Algorithm 3.1 on (5.1), with the safeguard Definition of §5.1
    (hrun : P.IsProjRun τ γ ρ1 lamMin lamMax muMax ε x ρ lamBar muBar v u)
    {xs : EuclideanSpace ℝ (Fin n)} (hlim : Tendsto x atTop (𝓝 xs))
    -- Assumption 2
    (hfeas : xs ∈ P.Omega1 ∩ P.Omega2)
    -- Assumption 3
    (hLI : LinearIndependent ℝ
      (Sum.elim (fun i => gradient (P.h1 i) xs) (fun i => gradient (P.h2 i) xs)))
    -- Assumption 4
    (hC2 : P.IsC2At xs)
    -- Assumption 5
    (lamS : Fin m1 → ℝ) (vS : Fin m2 → ℝ) (hSOSC : P.SOSC0 lamS vS xs)
    -- Assumption 6
    (hbox : ∀ i, lamMin i < lamS i ∧ lamS i < lamMax i)
    -- added: `τ > 0`
    (hτ : 0 < τ)
    (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0))
    (hεη : ∀ k, 1 ≤ k → ε k ≤ η k * ‖P.h1vec (x k)‖)
    :
    BddAbove (Set.range ρ) := by
  obtain ⟨hτ0, hτ1, hγ, hρ1, -, -, hε0, hεt⟩ := hpar
  obtain ⟨hr, hproj⟩ := hrun
  obtain ⟨hρ1eq, hbox1, -, hstep⟩ := id hr
  have hpos : ∀ k, 1 ≤ k → 0 < ρ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rw [hρ1eq]; exact hρ1
    | succ k hk ih =>
      rw [(hstep k hk).2.2.2]
      split_ifs
      · exact ih
      · exact mul_pos (by linarith) ih
  have hmono : ∀ k, 1 ≤ k → ρ k ≤ ρ (k + 1) := by
    intro k hk
    rw [(hstep k hk).2.2.2]
    split_ifs
    · exact le_rfl
    · nlinarith [hpos k hk]
  have hmono' : ∀ k, 1 ≤ k → ∀ j, k ≤ j → ρ k ≤ ρ j := by
    intro k hk j hj
    induction j, hj using Nat.le_induction with
    | base => exact le_rfl
    | succ j hj ih => exact ih.trans (hmono j (hk.trans hj))
  by_contra hB
  have hρ : Tendsto ρ atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    rw [not_bddAbove_iff] at hB
    obtain ⟨_, ⟨k, rfl⟩, hk⟩ := hB (max b (ρ 0))
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; exact absurd hk (not_lt.2 (le_max_right _ _))
      · exact h
    exact ⟨k, fun j hj => (le_max_left _ _).trans (hk.le.trans (hmono' k hk1 j hj))⟩
  obtain ⟨C, hC, hest⟩ :=
    AugLagPenAux.key_est P hP hr hlim hfeas hLI hC2 lamS vS hSOSC hpos hρ
  have hboxk : ∀ k, 1 ≤ k → ∀ i, lamMin i ≤ lamBar k i ∧ lamBar k i ≤ lamMax i := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; exact hbox1
    · exact (hstep j h).2.1
  set Bd : ℝ := ‖lamMin - lamS‖ + ‖lamMax - lamS‖ with hBd
  have hBk : ∀ k, 1 ≤ k → ‖lamBar k - lamS‖ ≤ Bd := by
    intro k hk
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    have h1 : |lamMin i - lamS i| ≤ ‖lamMin - lamS‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (lamMin - lamS) i
    have h2 : |lamMax i - lamS i| ≤ ‖lamMax - lamS‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (lamMax - lamS) i
    rw [Real.norm_eq_abs, Pi.sub_apply, abs_le]
    have := hboxk k hk i
    constructor
    · linarith [neg_abs_le (lamMin i - lamS i), norm_nonneg (lamMax - lamS)]
    · linarith [le_abs_self (lamMax i - lamS i), norm_nonneg (lamMin - lamS)]
  set L := P.lamNext x ρ lamBar with hL
  have hLt : Tendsto L atTop (𝓝 lamS) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hR : Tendsto (fun k => C * (ε k + Bd / ρ k)) atTop (𝓝 0) := by
      have : Tendsto (fun k => Bd / ρ k) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hρ
      simpa using (hεt.add this).const_mul C
    refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_ hR
    filter_upwards [hest, eventually_ge_atTop 1] with k hk hk1
    exact hk.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (div_le_div_of_nonneg_right (hBk k hk1) (hpos k hk1).le)) hC.le)
  have hin : ∀ᶠ k in atTop, ∀ i, lamMin i < L k i ∧ L k i < lamMax i := by
    rw [eventually_all]; intro i
    have hi : Tendsto (fun k => L k i) atTop (𝓝 (lamS i)) :=
      ((continuous_apply i).tendsto lamS).comp hLt
    exact (hi.eventually (Ioo_mem_nhds (hbox i).1 (hbox i).2)).mono fun k hk => hk
  have hPr : ∀ᶠ k in atTop, 1 ≤ k ∧ lamBar (k + 1) = L k := by
    filter_upwards [hin, eventually_ge_atTop 1] with k hk hk1
    refine ⟨hk1, funext fun i => ?_⟩
    rw [(hproj k hk1).1 i, min_eq_right (hk i).2.le, max_eq_right (hk i).1.le]
  have ht : ∀ k, 1 ≤ k → ‖P.h1vec (x k)‖ * ρ k = ‖L k - lamBar k‖ := by
    intro k hk
    have e : L k - lamBar k = ρ k • P.h1vec (x k) := by
      funext i; simp [hL, Problem.lamNext, Problem.h1vec]
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (hpos k hk), mul_comm]
  set δ : ℝ := τ / 3 with hδdef
  have hδpos : 0 < δ := by positivity
  have hδ : δ * (1 + δ + τ) ≤ τ := by rw [hδdef]; nlinarith
  have hcond : ∀ᶠ k in atTop, C * |η k| ≤ 1 / 2 ∧ 1 ≤ ρ k ∧ 1 + 2 * C ≤ δ * ρ k := by
    have h1 : ∀ᶠ k in atTop, C * |η k| ≤ 1 / 2 := by
      have : Tendsto (fun k => C * |η k|) atTop (𝓝 0) := by
        simpa using (hη.abs).const_mul C
      exact this.eventually (ge_mem_nhds (by norm_num))
    have h2 := hρ.eventually (eventually_ge_atTop 1)
    have h3 := hρ.eventually (eventually_ge_atTop ((1 + 2 * C) / δ))
    filter_upwards [h1, h2, h3] with k a b c
    refine ⟨a, b, ?_⟩
    rw [div_le_iff₀ hδpos] at c; linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hPr.and (hest.and hcond))
  have hcontr : ∀ k, N ≤ k → ‖L (k + 1) - lamS‖ ≤ δ * ‖L k - lamS‖ := by
    intro k hk
    obtain ⟨⟨hk1, hpk⟩, -, -⟩ := hN k hk
    obtain ⟨-, hest1, hη1, hρ1', hρδ⟩ := hN (k + 1) (by omega)
    have hk1' : 1 ≤ k + 1 := by omega
    rw [hpk] at hest1
    refine AugLagPenAux.contraction hest1 (hεη (k + 1) hk1') ?_ hη1 hρ1' hρδ (norm_nonneg _)
      (norm_nonneg _) hC (norm_nonneg _)
    rw [ht (k + 1) hk1', hpk]
    calc ‖L (k + 1) - L k‖ = ‖(L (k + 1) - lamS) - (L k - lamS)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have hσ : ∀ j, ‖P.sigma x ρ muBar j‖ = 0 := fun j => by
    rw [Subsingleton.elim (P.sigma x ρ muBar j) 0, norm_zero]
  have hconst : ∀ k, N + 1 ≤ k → ρ (k + 1 + 1) = ρ (k + 1) := by
    intro k hk
    obtain ⟨⟨hk1, hpk⟩, -, -⟩ := hN k (by omega)
    obtain ⟨⟨hk1', hpk'⟩, -, -⟩ := hN (k - 1) (by omega)
    have hk1eq : k - 1 + 1 = k := by omega
    rw [hk1eq] at hpk'
    have hA1 := hcontr k (by omega)
    have hA0 := hcontr (k - 1) (by omega)
    rw [hk1eq] at hA0
    have hdec : ‖P.h1vec (x (k + 1))‖ ≤ τ * ‖P.h1vec (x k)‖ := by
      have e2 : ‖P.h1vec (x (k + 1))‖ = ‖L (k + 1) - L k‖ / ρ (k + 1) := by
        rw [eq_div_iff (hpos (k + 1) (by omega)).ne', ht (k + 1) (by omega), hpk]
      have e1 : ‖P.h1vec (x k)‖ = ‖L k - L (k - 1)‖ / ρ k := by
        rw [eq_div_iff (hpos k hk1).ne', ht k hk1, hpk']
      rw [e1, e2]
      refine AugLagPenAux.ratio_step hδ hτ hδpos.le hA1 hA0 (norm_nonneg _) (norm_nonneg _)
        ?_ ?_ (hpos k hk1) (hmono k hk1)
      · calc ‖L (k + 1) - L k‖ = ‖(L (k + 1) - lamS) - (L k - lamS)‖ := by congr 1; abel
          _ ≤ _ := norm_sub_le _ _
      · calc ‖L (k - 1) - lamS‖ - ‖L k - lamS‖ ≤ ‖(L (k - 1) - lamS) - (L k - lamS)‖ :=
            norm_sub_norm_le _ _
          _ = ‖L k - L (k - 1)‖ := by rw [← norm_neg]; congr 1; abel
    have hs := (hstep (k + 1) (by omega)).2.2.2
    have hk11 : k + 1 - 1 = k := by omega
    rw [hk11, hσ, hσ, max_eq_left (norm_nonneg _), max_eq_left (norm_nonneg _),
      if_pos hdec] at hs
    exact hs
  have hfin : ∀ j, N + 2 ≤ j → ρ j = ρ (N + 2) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => rfl
    | succ j hj ih =>
      have h := hconst (j - 1) (by omega)
      have e : j - 1 + 1 = j := by omega
      rw [e] at h
      rw [h, ih]
  obtain ⟨M, hM⟩ := tendsto_atTop_atTop.1 hρ (ρ (N + 2) + 1)
  have := hM (max M (N + 2)) (le_max_left _ _)
  rw [hfin _ (le_max_right _ _)] at this
  linarith
