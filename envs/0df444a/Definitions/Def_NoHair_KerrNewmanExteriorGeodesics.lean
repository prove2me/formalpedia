-- Prove2me | Definitions.Def_NoHair_KerrNewmanExteriorGeodesics
-- name    : NoHair_KerrNewmanExteriorGeodesics
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-22T21:58:04.057204+00:00
-- url     : https://prove2.me/theorems/4b104752-1b97-4923-bf03-1abf2493030c
-- title:
--   Radial normal geodesics and the time orientation in the Kerr–Newman exterior
-- statement:
--   The position and velocity of the geodesic in a local exterior normal chart. Nonpositive signed energy and the correct ordering in Kerr–Schild coordinate time suffice to connect its endpoints by a regular future causal curve in the exterior. The representative is defined and continuously differentiable on the entire real line.
-- source:
--   B. O’Neill, Semi-Riemannian Geometry, chapter 3, normal coordinates. E. Minguzzi, Lorentzian causality theory, https://doi.org/10.1007/s41114-019-0019-x, causal cones in normal neighborhoods.

import Definitions.Def_NoHair_KerrNewmanEinstein_Base
import Definitions.Def_NoHair_PseudoRiemannianNormalCoordinates
import Theorems.Thm_NoHair_kerrNewman_regularTensors

open NoHair NoHair.KNE Set Filter
open OAI.WeakMTWGlobalSupport OAI.WeakMTWGlobalSupport.CoordinateGeometry
open OAI.WeakMTWGlobalSupport.NormalNeighborhood NoHair.PseudoNormal
open scoped ContDiff Manifold BigOperators Topology

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 270000

/-! The time and signed-energy tests for regular normal geodesics in the Kerr–Newman exterior. -/
namespace NoHair.ExteriorGeodesics
noncomputable section

abbrev U (a : ℝ) := kerrNewmanSpacetime a
abbrev D (m a e : ℝ) := (Subtype.val : U a → E4) ⁻¹' kerrNewmanDOC m a e
abbrev I4 := 𝓘(ℝ, E4)
abbrev G (m a e : ℝ) := kerrNewmanMetricField m a e
def timeComponent (v : E4) : ℝ := v 0
private def kEval (a : ℝ) (z u : E4) := ∑ i, ksNull a z i * u i

private theorem metric_formula (m a e : ℝ) (x : U a) (v w : E4) :
    G m a e x v w = -(v 0*w 0) + v 1*w 1 + v 2*w 2 + v 3*w 3
      + ksProfile m a e x.val * kEval a x.val v * kEval a x.val w := by
  change Matrix.toLinearMap₂' ℝ (kerrNewmanMetric m a e x.val) (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul, kerrNewmanMetric, kEval, Fin.sum_univ_four]
  simp [minkowski] <;> ring

theorem exterior_profile (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (x : U a) (hx : x ∈ D m a e) : 0 ≤ ksProfile m a e x.val := by
  obtain ⟨hm, he⟩ := hp
  change m + Real.sqrt (m^2 - a^2 - e^2) < ksRadius a x.val at hx
  have hm' : m ≤ ksRadius a x.val := by linarith [Real.sqrt_nonneg (m^2-a^2-e^2)]
  have hnum : 0 ≤ 2*m*ksRadius a x.val - e^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hm' hm.le, he, sq_nonneg a, sq_nonneg m]
  unfold ksProfile
  exact div_nonneg (mul_nonneg (sq_nonneg _) hnum) (by positivity)

private theorem spatial_squares (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v : E4) (hv : G m a e x v v ≤ 0) :
    (v 1)^2 + (v 2)^2 + (v 3)^2 ≤ (v 0)^2 := by
  rw [metric_formula] at hv
  nlinarith only [hv, mul_nonneg hf (sq_nonneg (kEval a x.val v))]

private theorem spatial_kernel (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v : E4) (h0 : v 0 = 0) : 0 ≤ G m a e x v v := by
  rw [metric_formula, h0]
  nlinarith only [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3),
    mul_nonneg hf (sq_nonneg (kEval a x.val v))]

theorem cone_estimates (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v w : E4) (hv : v ≠ 0) (hvv : G m a e x v v ≤ 0) (hvw : G m a e x v w < 0)
    (hww : G m a e x w w < 0) :
    (∀ i, |v i| ≤ |v 0|) ∧ 0 < (v 0)*(w 0) := by
  have hs := spatial_squares m a e x hf v hvv
  have hb (i : Fin 4) : |v i| ≤ |v 0| := by
    apply (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
    rw [sq_abs, sq_abs]
    fin_cases i <;> simp <;> nlinarith only [hs, sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
  have hv0 : v 0 ≠ 0 := by
    intro h
    apply hv
    ext i
    exact abs_nonpos_iff.mp (by simpa only [h, abs_zero] using hb i)
  refine ⟨hb, ?_⟩
  by_contra! hprod
  have hkernel := spatial_kernel m a e x hf ((w 0) • v - (v 0) • w)
    (by simp [smul_eq_mul, mul_comm])
  have hsym : G m a e x w v = G m a e x v w := by rw [metric_formula, metric_formula]; ring
  let A := matrixBilin (kerrNewmanMetric m a e x.val)
  change 0 ≤ A ((w 0) • v - (v 0) • w) ((w 0) • v - (v 0) • w) at hkernel
  change A w v = A v w at hsym
  change A w w < 0 at hww
  change A v v ≤ 0 at hvv
  change A v w < 0 at hvw
  simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, hsym] at hkernel
  nlinarith only [hkernel, mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (w 0)) hvv,
    mul_neg_of_pos_of_neg (sq_pos_iff.mpr hv0) hww, mul_nonneg_of_nonpos_of_nonpos hprod hvw.le]

private theorem matrix_eval (A : Matrix (Fin 4) (Fin 4) ℝ) (v w : E4) :
    matrixBilin A v w = ∑ i, ∑ j, v i * (w j * A i j) := by
  change Matrix.toLinearMap₂' ℝ A (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul]

private theorem radius_smooth (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    ContDiffAt ℝ ∞ (ksRadius a) z := by
  have hD := (ks_D_pos a z hz).ne'
  have hQ := (ks_Q_pos a z hz).ne'
  rw [ksRadius_eq']
  fun_prop (disch := assumption)

private theorem null_smooth (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (i : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => ksNull a w i) z := by
  have hr := radius_smooth a z hz
  have hne : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hne' := hz.ne'
  fin_cases i
  · simp only [Fin.zero_eta, ksNull_zero]; fun_prop
  · simp only [Fin.mk_one, ksNull_one]; fun_prop (disch := assumption)
  · change ContDiffAt ℝ ∞ (fun w => ksNull a w 2) z
    simp only [ksNull_two]; fun_prop (disch := assumption)
  · change ContDiffAt ℝ ∞ (fun w => ksNull a w 3) z
    simp only [ksNull_three]; fun_prop (disch := assumption)

theorem ambient_velocity (a : ℝ) (γ : ℝ → U a) (hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ)
    (s : ℝ) (v : E4) (hd : HasDerivAt (fun t => (γ t).val) v s) : (velocity γ s : E4) = v := by
  have hval : ContMDiff I4 I4 1 (Subtype.val : U a → E4) := contMDiff_subtype_val
  have hcomp := mfderiv_comp s (hval.mdifferentiableAt (by simp) (x := γ s)) (hγ.mdifferentiableAt (by simp))
  have hinc : (mfderiv I4 I4 (Subtype.val : U a → E4) (γ s) : E4 →L[ℝ] E4) =
      ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := I4) (x := γ s)
  rw [hinc] at hcomp
  have h : fderiv ℝ (fun t => (γ t).val) s = (mfderiv 𝓘(ℝ,ℝ) I4 γ s : ℝ →L[ℝ] E4) := by
    rw [← mfderiv_eq_fderiv]
    exact hcomp
  exact (congrArg (fun A : ℝ →L[ℝ] E4 => A 1) h).symm.trans hd.deriv

abbrev J := Icc (0:ℝ) 1
abbrev F (m a e : ℝ) (z : E4) := matrixBilin (kerrNewmanMetric m a e z)
noncomputable def W (a : ℝ) (T : VecField (U a)) (z : E4) : E4 := by
  classical
  exact if h : z ∈ U a then (T ⟨z,h⟩ : E4) else 0

theorem W_on (a : ℝ) (T : VecField (U a)) (x : U a) :
    W a T x.val = (T x : E4) := by
  classical
  unfold W
  rw [dif_pos x.property]

theorem W_cont (m a e : ℝ) (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T)
    (x : U a) : ContinuousAt (W a T) x.val := by
  apply (U a).isOpen.isOpenEmbedding_subtypeVal.continuousAt_iff.mp
  have h := hT.1.continuousAt (x := x)
  rw [FiberBundle.continuousAt_section] at h
  have htr (y : U a) : (trivializationAt E4 (TangentSpace I4) x ⟨y,T y⟩).2 = (T y : E4) := by
    change tangentCoordChange I4 y y y (T y) = _
    exact tangentCoordChange_self (mem_extChartAt_source y)
  change ContinuousAt (fun y : U a => W a T y.val) x
  rw [show (fun y : U a => W a T y.val) = (fun y : U a => (T y : E4)) from funext (W_on a T)]
  simpa only [htr] using h

abbrev S (m a e : ℝ) := kerrNewmanDOC m a e
theorem openS (m a e : ℝ) : IsOpen (S m a e) := isOpen_lt continuous_const (continuous_ksRadius a)
theorem inU (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) {z : E4}
    (h : z∈S m a e) : z∈U a := by
  change m+Real.sqrt (m^2-a^2-e^2) < ksRadius a z at h
  change 0 < ksRadius a z
  linarith only [hp.1,h,Real.sqrt_nonneg (m^2-a^2-e^2)]

private theorem smooth_scalar_multiple {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → ℝ} {x : X} (hf : ContDiffAt ℝ ∞ f x) (v : Y) :
    ContDiffAt ℝ ∞ (fun z => f z • v) x := hf.smul_const v

set_option backward.defeqAttrib.useBackward true in
theorem field_smooth (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) :
    ContDiffOn ℝ ∞ (F m a e) (S m a e) := by
  let P (i : Fin 4) := EuclideanSpace.proj (𝕜:=ℝ) i
  have heP (i : Fin 4) (v : E4) : P i v = v i := rfl
  let B (i j : Fin 4) := (P i).smulRight (P j)
  have he (y : E4) : F m a e y = ∑ i, ∑ j, (kerrNewmanMetric m a e y i j) • B i j := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    simp only [F,matrix_eval,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
      smul_eq_mul,B,ContinuousLinearMap.smulRight_apply,heP]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  intro y hy
  have hy' : 0 < ksRadius a y := inU m a e hp hy
  apply ContDiffAt.contDiffWithinAt
  rw [show F m a e = fun z => ∑ i, ∑ j, (kerrNewmanMetric m a e z i j) • B i j from funext he]
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  have hcoeff : ContDiffAt ℝ ∞ (fun z : E4 => kerrNewmanMetric m a e z i j) y := by
    have hR := radius_smooth a y hy'
    have hi := null_smooth a y hy' i
    have hj := null_smooth a y hy' j
    have hd := (ks_den_pos a y hy').ne'
    unfold kerrNewmanMetric ksProfile
    fun_prop (disch := assumption)
  first
  | exact smooth_scalar_multiple (Y:=MetricTensor E4) hcoeff (B i j)
  | convert! smooth_scalar_multiple (Y:=MetricTensor E4) hcoeff (B i j) using 1
  | let L : ℝ →L[ℝ] MetricTensor E4 := ContinuousLinearMap.toSpanSingleton ℝ (B i j)
    have hL := ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=ℝ) (F:=MetricTensor E4) (n:=∞) L
    exact hL.contDiffAt.comp (f:=fun z : E4 => kerrNewmanMetric m a e z i j) y hcoeff

theorem field_sym (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) {z : E4}
    (hz : z∈S m a e) (v w : E4) : F m a e z v w=F m a e z w v := by
  let x : U a := ⟨z,inU m a e hp hz⟩
  change G m a e x v w=G m a e x w v
  rw [metric_formula,metric_formula]; ring

theorem field_inv (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) {z : E4}
    (hz : z∈S m a e) : (F m a e z).IsInvertible := by
  let x : U a := ⟨z,inU m a e hp hz⟩
  obtain ⟨b,hb⟩ := (kerrNewman_regularTensors m a e).1 x
  let M := F m a e z
  change ∀ i j, M (b i) (b j) = minkowski i j at hb
  have hi : Function.Injective M := by
    apply (injective_iff_map_eq_zero M).mpr
    intro v hv
    have hs : (∑ i, b.repr v i • b i) = v := b.sum_repr v
    have hw (j : Fin 4) : (∑ i, b.repr v i * minkowski i j)=0 := by
      have eq := congrArg (fun L : E4 →L[ℝ] ℝ => L (b j)) hv
      change M v (b j)=0 at eq
      rw [←hs] at eq
      simpa only [map_sum,map_smul,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,hb] using eq
    have h0 (i : Fin 4) : b.repr v i = 0 := by
      have h := hw i
      fin_cases i <;> simpa [minkowski,Fin.sum_univ_four] using h
    rw [←hs]
    simp [h0]
  have hdim : Module.finrank ℝ E4=Module.finrank ℝ (E4→L[ℝ]ℝ) := (InnerProductSpace.toDual ℝ E4).toLinearEquiv.finrank_eq
  have hs : Function.Surjective M := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi
  exact ⟨ContinuousLinearEquiv.ofBijective M (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs),rfl⟩

theorem nonzero_time (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) {z v : E4}
    (hz : z∈S m a e) (hn : v≠0) (h : F m a e z v v ≤ 0) : v 0≠0 := by
  let x : U a := ⟨z,inU m a e hp hz⟩
  have hs := spatial_squares m a e x (exterior_profile m a e hp x hz) v h
  intro h0
  rw [h0] at hs
  apply hn
  ext i
  fin_cases i
  · exact h0
  · change v 1=0
    apply sq_eq_zero_iff.mp
    nlinarith only [hs,sq_nonneg (v 1),sq_nonneg (v 2),sq_nonneg (v 3)]
  · change v 2=0
    apply sq_eq_zero_iff.mp
    nlinarith only [hs,sq_nonneg (v 1),sq_nonneg (v 2),sq_nonneg (v 3)]
  · change v 3=0
    apply sq_eq_zero_iff.mp
    nlinarith only [hs,sq_nonneg (v 1),sq_nonneg (v 2),sq_nonneg (v 3)]

theorem cone_pair_negative (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    {z v w : E4} (hz : z∈S m a e) (hvv : F m a e z v v ≤ 0) (hww : F m a e z w w < 0)
    (hvw : 0 < v 0*w 0) : F m a e z v w < 0 := by
  let x : U a := ⟨z,inU m a e hp hz⟩
  have hk := spatial_kernel m a e x (exterior_profile m a e hp x hz) ((w 0) • v - (v 0) • w)
    (by simp [smul_eq_mul,mul_comm])
  let A := F m a e z
  change 0 ≤ A ((w 0) • v - (v 0) • w) ((w 0) • v - (v 0) • w) at hk
  have he : A w v = A v w := field_sym m a e hp hz w v
  simp only [map_sub,map_smul,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,he] at hk
  by_contra! h
  change 0 ≤ A v w at h
  have hn := (mul_ne_zero_iff.mp hvw.ne').1
  nlinarith only [hk,mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (w 0)) hvv,
    mul_neg_of_pos_of_neg (sq_pos_iff.mpr hn) hww, mul_nonneg hvw.le h]

theorem sign_prop {L : ℝ} {f : ℝ→ℝ} (hc : ContinuousOn f (Icc 0 L))
    (hne : ∀ s∈Icc 0 L, f s≠0) {u : ℝ} (hu : u∈Icc 0 L) (hpos : 0 < f u) :
    ∀ t∈Icc 0 L, 0 < f t := by
  intro t ht
  by_contra! h
  obtain ⟨r,hr,he⟩ := isPreconnected_Icc.intermediate_value ht hu hc (show (0:ℝ)∈Icc (f t) (f u) from ⟨h,hpos.le⟩)
  exact hne _ hr he

theorem time_deriv {c : ℝ→E4} {v : E4} {t : ℝ} (h : HasDerivAt c v t) :
    HasDerivAt (fun s => c s 0) (v 0) t := by
  let P : E4 →L[ℝ] ℝ := EuclideanSpace.proj 0
  have hh : HasDerivAt (P ∘ c) (P v) t := P.hasFDerivAt.comp_hasDerivAt t h
  exact hh

theorem clock_positive {L o : ℝ} (hL : 0 < L) (c v : ℝ→E4)
    (hc : ∀ t∈Icc 0 L, HasDerivAt c (v t) t) (hv : ContinuousOn v (Icc 0 L))
    (hne : ∀ t∈Icc 0 L, v t 0≠0) (hdisp : 0 < o*(c L 0-c 0 0)) :
    ∀ t∈Icc 0 L, 0 < o*v t 0 := by
  let d (t : ℝ) := o*(c t 0)
  have hd (t : ℝ) (ht : t∈Icc 0 L) : HasDerivAt d (o*v t 0) t :=
    (time_deriv (hc t ht)).const_mul o
  have hco : ContinuousOn d (Icc 0 L) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope d (fun s => o*v s 0) hL hco (fun s hs => hd s (Ioo_subset_Icc_self hs))
  have htd : 0 < o*v t 0 := by
    rw [he]
    exact div_pos (by dsimp [d]; linarith only [hdisp]) (sub_pos.mpr hL)
  have ho := (mul_ne_zero_iff.mp hdisp.ne').1
  exact sign_prop (continuousOn_const.mul ((EuclideanSpace.proj (𝕜:=ℝ) 0).continuous.comp_continuousOn hv))
    (fun s hs => mul_ne_zero ho (hne s hs)) (Ioo_subset_Icc_self ht) htd

theorem common_sign {o u v : ℝ} (h1 : 0 < o*u) (h2 : 0 < o*v) : 0 < u*v := by
  rcases mul_pos_iff.mp h1 with h|h <;> rcases mul_pos_iff.mp h2 with k|k
  · exact mul_pos h.2 k.2
  · linarith [h.1,k.1]
  · linarith [h.1,k.1]
  · exact mul_pos_of_neg_of_neg h.2 k.2

private theorem fit_clock {A : Set ℝ} (hA : IsOpen A) {L : ℝ} (hL : 0 < L) (hS : Icc 0 L⊆A) :
    ∃ f : ℝ→ℝ, ContDiff ℝ 1 f ∧ (∀ t, f t∈A) ∧ ∀ t∈Icc 0 L, f=ᶠ[𝓝 t] id := by
  obtain ⟨r₁,hr₁,h₁⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds (hS (left_mem_Icc.mpr hL.le)))
  obtain ⟨r₂,hr₂,h₂⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds (hS (right_mem_Icc.mpr hL.le)))
  let r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  let m := L/2
  let b : ContDiffBump m := ⟨m+r/2,m+r,by dsimp [m]; linarith,by linarith⟩
  let f (t : ℝ) := m+b t*(t-m)
  refine ⟨f,?_,?_,?_⟩
  · exact contDiff_const.add (b.contDiff.mul (contDiff_id.sub contDiff_const))
  · intro t
    have hb : |f t-m| < m+r := by
      by_cases h : b t=0
      · simp [f,h]; dsimp [m]; linarith
      · have hh : t∈Function.support b := h
        rw [b.support_eq,Metric.mem_ball,Real.dist_eq] at hh
        have he : f t-m=b t*(t-m) := by dsimp [f]; ring
        rw [he,abs_mul,abs_of_nonneg b.nonneg]
        exact (mul_le_mul_of_nonneg_right b.le_one (abs_nonneg _)).trans_lt (by simpa using hh)
    have hl := (abs_lt.mp hb).1
    have hu := (abs_lt.mp hb).2
    by_cases h0 : f t < 0
    · apply h₁
      rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_neg h0]
      dsimp [m] at hl; linarith only [hl,min_le_left r₁ r₂]
    · by_cases h1 : L < f t
      · apply h₂
        rw [Metric.mem_ball,Real.dist_eq,abs_of_pos (sub_pos.mpr h1)]
        dsimp [m] at hu; linarith only [hu,min_le_right r₁ r₂]
      · exact hS ⟨le_of_not_gt h0,le_of_not_gt h1⟩
  · intro t ht
    have hh : t∈Metric.ball m b.rIn := by
      rw [Metric.mem_ball,Real.dist_eq,abs_lt]
      change -(L/2+r/2) < t-L/2 ∧ t-L/2 < L/2+r/2
      constructor <;> linarith [ht.1,ht.2]
    filter_upwards [b.eventuallyEq_one_of_mem_ball hh] with z hz
    change b z=1 at hz
    simp [f,hz]

abbrev NF (m a e : ℝ) (x₀ : E4) := NormalFlow (F m a e) (S m a e) x₀
abbrev span {m a e : ℝ} {x₀ : E4} (N : NF m a e x₀) := Icc (0:ℝ) N.time
abbrev Z {m a e : ℝ} {x₀ : E4} (N : NF m a e x₀) (p v : E4) (t : ℝ) := (N.flow (t,(p,v))).1
abbrev Velo {m a e : ℝ} {x₀ : E4} (N : NF m a e x₀) (p v : E4) (t : ℝ) := (N.flow (t,(p,v))).2

theorem radial_data {m a e : ℝ} {x₀ : E4} (N : NF m a e x₀) {p v : E4}
    (hv : (p,v)∈N.normal.source) :
    (∀ t∈span N, Z N p v t∈S m a e ∧ HasDerivAt (Z N p v) (Velo N p v t) t) ∧
    ContinuousOn (Velo N p v) (span N) ∧ Z N p v 0=p ∧ Velo N p v 0=v := by
  have h0 := N.initial (p,v) (N.source_stays (p,v) hv 0 ⟨le_rfl,N.time_pos.le⟩)
  refine ⟨fun t ht => ⟨(N.ode _ (N.source_stays _ hv t ht)).1,?_⟩,?_,congrArg Prod.fst h0,congrArg Prod.snd h0⟩
  · exact (N.ode _ (N.source_stays _ hv t ht)).2.fst
  · exact (N.flow_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (N.source_stays (p,v) hv)).snd

private theorem radial_nonzero {m a e : ℝ} (hp : IsKerrNewmanBlackHoleParams m a e) {x₀ : E4}
    (N : NF m a e x₀) {p v : E4} (hv : (p,v)∈N.normal.source) (hn : v≠0) {t : ℝ} (ht : t∈span N) :
    Velo N p v t≠0 := by
  intro hbad
  let f := geodesicSpray (F m a e)
  let u (s : ℝ) := N.flow (t-s,(p,v))
  let y := N.flow (t,(p,v))
  have htime {s : ℝ} (hs : s∈Icc 0 t) : t-s∈span N := ⟨sub_nonneg.mpr hs.2,by linarith [ht.2,hs.1]⟩
  have hdu (s : ℝ) (hs : s∈Icc 0 t) : HasDerivAt u (-f (u s)) s := by
    simpa [u,f,Function.comp_def] using ((N.ode _ (N.source_stays (p,v) hv _ (htime hs))).2.scomp s ((hasDerivAt_id s).const_sub t))
  have hy : f y=0 := by
    change (y.2,-OAI.WeakMTWGlobalSupport.CoordinateGeometry.christoffel (F m a e) y.1 y.2 y.2) = 0
    change y.2=0 at hbad
    simp [hbad]
  have hsmooth := contDiffOn_geodesicSpray_of_invertible (openS m a e) (field_smooth m a e hp) (fun z hz => field_inv m a e hp hz)
  have hz : EqOn u (fun _=>y) (Icc 0 t) := by
    apply FlowLinearization.unique_Icc (f:=fun z => -f z) (fun s hs => (hdu s hs).continuousAt.continuousWithinAt) continuousOn_const
    · intro z hz
      have hz' : z∈(S m a e) ×ˢ (univ : Set E4) := by
        rcases hz with ⟨s,hs,rfl⟩|⟨_,_,rfl⟩
        · exact ⟨(N.ode _ (N.source_stays (p,v) hv _ (htime hs))).1,mem_univ _⟩
        · exact ⟨(N.ode _ (N.source_stays (p,v) hv t ht)).1,mem_univ _⟩
      exact (((hsmooth z hz').contDiffAt (((openS m a e).prod isOpen_univ).mem_nhds hz')).of_le (by simp)).neg
    · exact fun s hs => (hdu s hs).hasDerivWithinAt
    · intro s _
      simpa only [hy,neg_zero] using hasDerivWithinAt_const s (Icc (0:ℝ) t) y
    · simp [u,y]
  have h := congrArg Prod.snd (hz (right_mem_Icc.mpr ht.1))
  have h0 := (radial_data N hv).2.2.2
  apply hn
  calc
    v = Velo N p v 0 := h0.symm
    _ = Velo N p v t := by simpa only [u,y,sub_self] using h
    _ = 0 := hbad

theorem radial_future (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T) {x₀ : E4} (N : NF m a e x₀)
    (p q : U a) (htarget : (p.val,q.val)∈N.normal.target)
    (hE : initialEnergy N p.val q.val ≤ 0)
    (ho : 0 ≤ (q.val 0-p.val 0)*timeComponent (T p)) : q∈causalFuture (G m a e) T (D m a e) p := by
  by_cases hdiag : q=p
  · exact Or.inl (mem_singleton_iff.mpr hdiag)
  let v := logVec N p.val q.val
  let R := Z N p.val v
  let d := Velo N p.val v
  let o := timeComponent (T p)
  have hv : (p.val,v)∈N.normal.source := (N.normalAt p.val).map_target htarget
  have hlast : R N.time = q.val := by
    simpa only [N.normalAt_apply,R,Z,v,logVec] using (N.normalAt p.val).right_inv htarget
  have hvne : v≠0 := by
    intro hv0
    have hh : (p.val,(0:E4))∈N.normal.source := hv0 ▸ hv
    have he := normalAt_zero_of_invertible N (openS m a e) (field_smooth m a e hp)
      (fun z hz => field_inv m a e hp hz) hh
    apply hdiag
    apply Subtype.ext
    calc
      q.val = N.normalAt p.val v := ((N.normalAt p.val).right_inv htarget).symm
      _ = p.val := hv0 ▸ he
  obtain ⟨hR,hdc,hfirst,_⟩ := radial_data N hv
  have henergy (t : ℝ) (ht : t∈span N) : F m a e (R t) (d t) (d t) ≤ 0 :=
    (flow_energy N (openS m a e) (field_smooth m a e hp) (fun _ hz => field_sym m a e hp hz)
      (fun _ hz => field_inv m a e hp hz) hv ht).trans_le hE
  have hdn (t : ℝ) (ht : t∈span N) := radial_nonzero hp N hv hvne ht
  have hdt (t : ℝ) (ht : t∈span N) : d t 0≠0 := nonzero_time m a e hp (hR _ ht).1 (hdn t ht) (henergy t ht)
  have h₀ : (0:ℝ)∈span N := ⟨le_rfl,N.time_pos.le⟩
  have hpS := N.base_mem hv
  have hor : o≠0 := by
    apply nonzero_time m a e hp hpS _ (hT.2 p).le
    intro h
    have hh := hT.2 p
    change (T p : E4)=0 at h
    change F m a e p.val (T p : E4) (T p : E4) < 0 at hh
    simp [h] at hh
  have hdiff (s : ℝ) (hs : s∈span N) : HasDerivAt (fun t => R t 0) (d s 0) s :=
    time_deriv (hR s hs).2
  have hstrict : 0 < o*(R N.time 0-R 0 0) := by
    have h0' : R 0=p.val := hfirst
    have hs := exists_hasDerivAt_eq_slope (fun t => R t 0) (fun t => d t 0) N.time_pos
      (fun t ht => (hdiff t ht).continuousAt.continuousWithinAt) (fun t ht => hdiff t (Ioo_subset_Icc_self ht))
    obtain ⟨t,ht,he⟩ := hs
    have hdne : R N.time 0 - R 0 0 ≠ 0 := fun hh => hdt t (Ioo_subset_Icc_self ht) (by simpa [hh] using he)
    apply lt_of_le_of_ne _ ((mul_ne_zero hor hdne).symm)
    rw [hlast,h0',mul_comm]
    exact ho
  have hsign := clock_positive N.time_pos R d (fun s hs => (hR s hs).2) hdc hdt hstrict
  have horient (s : ℝ) (hs : s∈span N) : 0 < o*(W a T (R s)) 0 := by
    have hc : ContinuousOn (fun t => o*(W a T (R t)) 0) (span N) := by
      intro t ht
      let z : U a := ⟨R t,inU m a e hp (hR t ht).1⟩
      have hz : ContinuousAt (W a T) (R t) := W_cont m a e T hT z
      have hr : ContinuousAt R t := (hR t ht).2.continuousAt
      have ht' : ContinuousAt (fun s => W a T (R s)) t := hz.comp (f:=R) hr
      let proj : E4 →L[ℝ] ℝ := EuclideanSpace.proj 0
      have hh : ContinuousAt (fun s => proj (W a T (R s))) t :=
        proj.continuous.continuousAt.comp (f:=fun s => W a T (R s)) ht'
      exact (continuousAt_const.mul hh).continuousWithinAt
    have hn (t : ℝ) (ht : t∈span N) : o*(W a T (R t)) 0≠0 := by
      let z : U a := ⟨R t,inU m a e hp (hR t ht).1⟩
      have hg := hT.2 z
      change F m a e (R t) (T z : E4) (T z : E4) < 0 at hg
      have he : W a T (R t)=(T z:E4) := W_on a T z
      rw [he]
      exact mul_ne_zero hor (nonzero_time m a e hp (hR t ht).1 (fun hh => by simp [hh] at hg) hg.le)
    apply sign_prop hc hn h₀ _ s hs
    change 0 < o*(W a T (R 0)) 0
    rw [show R 0=p.val from hfirst,W_on]
    exact mul_self_pos.mpr hor
  let A : Set ℝ := {s | (s,(p.val,v))∈N.domain}
  have hA : IsOpen A := N.domain_open.preimage (continuous_id.prodMk continuous_const)
  obtain ⟨f,hf,hfA,hfe⟩ := fit_clock hA N.time_pos (N.source_stays (p.val,v) hv)
  let γ (t : ℝ) : U a := ⟨R (f (N.time*t)),inU m a e hp (N.ode _ (hfA _)).1⟩
  have hc : ContDiff ℝ 1 (Subtype.val ∘ γ) := by
    apply contDiff_iff_contDiffAt.mpr
    intro t
    let param (u : ℝ) : ℝ×(E4×E4) := (f (N.time*u),(p.val,v))
    have hparam : ContDiff ℝ 1 param := (hf.comp (contDiff_const.mul contDiff_id)).prodMk contDiff_const
    have hh : ContDiffAt ℝ 1 N.flow (param t) :=
      ((N.flow_smooth _ (hfA (N.time*t))).contDiffAt (N.domain_open.mem_nhds (hfA (N.time*t)))).of_le
        (show (1:ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    have hh' : ContDiffAt ℝ 1 (N.flow ∘ param) t := hh.comp (f:=param) t hparam.contDiffAt
    exact hh'.fst
  have hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ := fun s =>
    (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff γ univ s).mp (hc.contMDiff s)
  have eqF (s : ℝ) (hs : s∈span N) : f s=s := (hfe s hs).eq_of_nhds
  refine Or.inr ⟨γ,⟨hγ,?_⟩,Subtype.ext ?_,Subtype.ext ?_⟩
  · intro s hs
    have hts : N.time*s∈span N := ⟨mul_nonneg N.time_pos.le hs.1,by simpa using mul_le_mul_of_nonneg_left hs.2 N.time_pos.le⟩
    let t := N.time*s
    have hz : (γ s).val=R t := by change R (f t)=R t; rw [eqF t hts]
    have hb : HasDerivAt (fun u => f (N.time*u)) N.time s := by
      have hclock : HasDerivAt (fun u : ℝ => N.time*u) N.time s := by
        simpa only [id_eq,mul_one] using (hasDerivAt_id s).const_mul N.time
      have hequal : (fun u : ℝ => f (N.time*u)) =ᶠ[𝓝 s] (fun u : ℝ => N.time*u) :=
        (hfe t hts).comp_tendsto hclock.continuousAt.tendsto
      exact hclock.congr_of_eventuallyEq hequal
    have hr : HasDerivAt R (d t) (f t) := by rw [eqF t hts]; exact (hR t hts).2
    have hder : HasDerivAt (fun u => (γ u).val) (N.time • d t) s := by
      change HasDerivAt (R ∘ fun u => f (N.time*u)) (N.time • d t) s
      exact hr.scomp s hb
    have hv' := ambient_velocity a γ hγ s _ hder
    have htim := hT.2 (γ s)
    have heW : W a T (R t)=(T (γ s):E4) := hz ▸ W_on a T (γ s)
    have hpair := cone_pair_negative m a e hp (hR t hts).1 (henergy t hts)
      (w:=W a T (R t)) (by
        change F m a e (R t) (W a T (R t)) (W a T (R t)) < 0
        rw [heW,←hz]
        exact htim) (common_sign (hsign t hts) (horient t hts))
    refine ⟨show (γ s).val∈S m a e by rw [hz]; exact (hR t hts).1,?_,?_,?_⟩
    · change (velocity γ s:E4)≠0
      rw [hv']
      exact smul_ne_zero N.time_pos.ne' (hdn t hts)
    · change F m a e (γ s).val (velocity γ s:E4) (velocity γ s:E4) ≤ 0
      rw [hv',hz]
      simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos N.time_pos.le (mul_nonpos_of_nonneg_of_nonpos N.time_pos.le (henergy t hts))
    · change F m a e (γ s).val (velocity γ s:E4) (T (γ s):E4) < 0
      rw [hv',hz,←heW]
      simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
      exact mul_neg_of_pos_of_neg N.time_pos hpair
  · simpa only [γ,mul_zero,eqF 0 h₀] using hfirst
  · simpa only [γ,mul_one,eqF _ (right_mem_Icc.mpr N.time_pos.le)] using hlast

theorem energy_cont {m a e : ℝ} (hp : IsKerrNewmanBlackHoleParams m a e) {x₀ : E4}
    (N : NF m a e x₀) {p q : E4} (hpS : p∈S m a e) (ht : (p,q)∈N.normal.target) :
    ContinuousAt (fun k : E4×E4 => initialEnergy N k.1 k.2) (p,q) := by
  have hF := ((field_smooth m a e hp p hpS).continuousWithinAt.continuousAt ((openS m a e).mem_nhds hpS)).comp
    (continuous_fst.continuousAt (x:=(p,q)))
  exact (hF.clm_apply (logVec_continuousAt N ht)).clm_apply (logVec_continuousAt N ht)


end
end NoHair.ExteriorGeodesics


