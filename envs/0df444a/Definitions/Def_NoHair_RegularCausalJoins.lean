-- Prove2me | Definitions.Def_NoHair_RegularCausalJoins
-- name    : NoHair_RegularCausalJoins
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-22T21:42:09.910568+00:00
-- url     : https://prove2.me/theorems/0dbe2e6d-4009-42b7-8b43-da45481ca670
-- title:
--   Regular parametrized arcs and causal corner rounding in the Kerr–Newman exterior
-- statement:
--   A differentiable parametrized arc with a continuous velocity, its matching-jet join, and a quadratic rounding of two future causal arcs near a strict corner. The estimates ensure that the rounded middle arc is causal and that its velocity is nonzero, including at null endpoints.
-- source:
--   Regular causal joins in Lorentzian causality theory, E. Minguzzi, https://doi.org/10.1007/s41114-019-0019-x. The quadratic interpolation and its error estimate are provided in the proof.

import Definitions.Def_NoHair_KerrNewmanEinstein_Base

open NoHair NoHair.KNE Set Filter
open scoped ContDiff Manifold BigOperators Topology

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 350000

/-! Regular parametrized arcs and rounding of causal corners. Matching first derivatives
give a regular join. For a strict corner the quadratic middle arc matches both endpoint jets. -/
namespace NoHair.CausalJoining
noncomputable section

abbrev U (a : ℝ) := kerrNewmanSpacetime a
abbrev D (m a e : ℝ) := (Subtype.val : U a → E4) ⁻¹' kerrNewmanDOC m a e
private abbrev I4 := 𝓘(ℝ, E4)
abbrev G (m a e : ℝ) := kerrNewmanMetricField m a e
private def timeComponent (v : E4) : ℝ := v 0
def kEval (a : ℝ) (z u : E4) := ∑ i, ksNull a z i * u i

private theorem metric_formula (m a e : ℝ) (x : U a) (v w : E4) :
    G m a e x v w = -(v 0*w 0) + v 1*w 1 + v 2*w 2 + v 3*w 3
      + ksProfile m a e x.val * kEval a x.val v * kEval a x.val w := by
  change Matrix.toLinearMap₂' ℝ (kerrNewmanMetric m a e x.val) (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul, kerrNewmanMetric, kEval, Fin.sum_univ_four]
  simp [minkowski] <;> ring

private theorem exterior_profile (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
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

private theorem cone_estimates (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
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

private theorem ambient_velocity (a : ℝ) (γ : ℝ → U a) (hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ)
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

theorem eval_smooth (m a e : ℝ) (z v w : E4) (hz : 0 < ksRadius a z) :
    ContDiffAt ℝ 1 (fun k : E4 × E4 × E4 => F m a e k.1 k.2.1 k.2.2) (z,v,w) := by
  have hc (i j : Fin 4) : ContDiffAt ℝ ∞ (fun y => kerrNewmanMetric m a e y i j) z := by
    have hr := radius_smooth a z hz
    have hi := null_smooth a z hz i
    have hj := null_smooth a z hz j
    have hd := (ks_den_pos a z hz).ne'
    unfold kerrNewmanMetric ksProfile
    fun_prop (disch := assumption)
  simp_rw [F, matrix_eval]
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  have hk : ContDiffAt ℝ 1 (fun y : E4 => kerrNewmanMetric m a e y i j) z :=
    (hc i j).of_le (show (1:ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hk' := hk.comp (f:=fun k : E4×E4×E4 => k.1) (z,v,w) contDiffAt_fst
  exact (((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt.comp _ (contDiffAt_fst.comp _ contDiffAt_snd))).mul
    ((((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffAt.comp _ (contDiffAt_snd.comp _ contDiffAt_snd))).mul hk')

def Good (m a e : ℝ) (T : VecField (U a)) (z v : E4) : Prop :=
  z ∈ kerrNewmanDOC m a e ∧ F m a e z v v ≤ 0 ∧ F m a e z v (W a T z) < 0

private theorem good_scale (m a e : ℝ) (T : VecField (U a)) {z v : E4} (h : Good m a e T z v)
    {c : ℝ} (hc : 0<c) : Good m a e T z (c • v) := by
  obtain ⟨hz,hv,hw⟩ := h
  refine ⟨hz, ?_, ?_⟩
  · simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos hc.le (mul_nonpos_of_nonneg_of_nonpos hc.le hv)
  · simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hc hw

theorem directions (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) (T : VecField (U a))
    (hT : IsTimeOrientation (G m a e) T) (x : U a) (v w : E4)
    (hv : Good m a e T x.val v) (hw : Good m a e T x.val w) :
    (∃ c : ℝ, 0<c ∧ v=c • w) ∨ F m a e x.val v w < 0 := by
  have hf := exterior_profile m a e hp x hv.1
  have vn (h : E4) (hh : Good m a e T x.val h) : h ≠ 0 := by
    intro he
    have hh' := hh.2.2
    simp [he] at hh'
  have ht (h : E4) (hh : Good m a e T x.val h) : 0 < h 0 * timeComponent (T x) := by
    apply (cone_estimates m a e x hf h (T x) (vn h hh) hh.2.1 _ (hT.2 x)).2
    exact (show F m a e x.val h (T x : E4)<0 by simpa only [W_on] using hh.2.2)
  have hprod : 0 < v 0*w 0 := by
    rcases mul_pos_iff.mp (ht v hv) with h₁|h₁ <;> rcases mul_pos_iff.mp (ht w hw) with h₂|h₂
    · exact mul_pos h₁.1 h₂.1
    · linarith [h₁.2,h₂.2]
    · linarith [h₁.2,h₂.2]
    · exact mul_pos_of_neg_of_neg h₁.1 h₂.1
  let u : E4 := (w 0) • v - (v 0) • w
  by_cases h : u=0
  · left
    have hw0 := (mul_ne_zero_iff.mp hprod.ne').2
    refine ⟨v 0/w 0, (div_pos_iff.mpr (mul_pos_iff.mp hprod)), ?_⟩
    have hh : (w 0) • v = (v 0) • w := sub_eq_zero.mp h
    ext i
    have ee := congrArg (fun k : E4 => k i) hh
    change w 0*v i = v 0*w i at ee
    change v i = v 0/w 0*w i
    field_simp [hw0]
    linarith
  · right
    have hu0 : u 0 = 0 := by simp [u, smul_eq_mul, mul_comm]
    have hpos : 0 < F m a e x.val u u := by
      by_contra! hle
      have hsq := spatial_squares m a e x hf u hle
      rw [hu0] at hsq
      apply h
      ext i
      fin_cases i
      · exact hu0
      · change u 1=0
        apply sq_eq_zero_iff.mp
        nlinarith only [hsq, sq_nonneg (u 1), sq_nonneg (u 2), sq_nonneg (u 3)]
      · change u 2=0
        apply sq_eq_zero_iff.mp
        nlinarith only [hsq, sq_nonneg (u 1), sq_nonneg (u 2), sq_nonneg (u 3)]
      · change u 3=0
        apply sq_eq_zero_iff.mp
        nlinarith only [hsq, sq_nonneg (u 1), sq_nonneg (u 2), sq_nonneg (u 3)]
    let A := F m a e x.val
    have hsym : A w v = A v w := by
      change G m a e x w v = G m a e x v w
      rw [metric_formula, metric_formula]; ring
    change 0 < A ((w 0) • v - (v 0) • w) ((w 0) • v - (v 0) • w) at hpos
    simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, hsym] at hpos
    by_contra! hn
    change 0 ≤ A v w at hn
    nlinarith only [hpos, mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (w 0)) hv.2.1,
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (v 0)) hw.2.1, mul_nonneg hprod.le hn]

structure Arc where
  pos : ℝ → E4
  vel : ℝ → E4
  hasDeriv : ∀ s, HasDerivAt pos (vel s) s
  continuous_vel : Continuous vel

theorem Arc.smooth (P : Arc) : ContDiff ℝ 1 P.pos := by
  have he : deriv P.pos = P.vel := funext fun s => (P.hasDeriv s).deriv
  exact contDiff_one_iff_deriv.mpr ⟨fun s => (P.hasDeriv s).differentiableAt,he ▸ P.continuous_vel⟩

private def Arc.reparam (P : Arc) (f d : ℝ → ℝ) (hd : ∀ s, HasDerivAt f (d s) s)
    (hc : Continuous d) : Arc where
  pos := fun t => P.pos (f t)
  vel := fun t => d t • P.vel (f t)
  hasDeriv s := (P.hasDeriv (f s)).scomp s (hd s)
  continuous_vel := hc.smul (P.continuous_vel.comp (continuous_iff_continuousAt.mpr fun s => (hd s).continuousAt))

private def Arc.affine (P : Arc) (c b : ℝ) : Arc :=
  P.reparam (fun s => c*(s-b)) (fun _ => c) (fun s => by
    simpa using (((hasDerivAt_id s).sub_const b).const_mul c)) continuous_const

def join (c : ℝ) (P Q : Arc) (hp : P.pos c=Q.pos c) (hv : P.vel c=Q.vel c) : Arc where
  pos := fun s => if s ≤ c then P.pos s else Q.pos s
  vel := fun s => if s ≤ c then P.vel s else Q.vel s
  continuous_vel := continuous_if_le continuous_id continuous_const P.continuous_vel.continuousOn
    Q.continuous_vel.continuousOn (fun _ he => he ▸ hv)
  hasDeriv s := by
    rcases lt_trichotomy s c with h|rfl|h
    · rw [if_pos h.le]
      apply (P.hasDeriv s).congr_of_eventuallyEq
      filter_upwards [eventually_lt_nhds h] with t ht using if_pos ht.le
    · rw [if_pos le_rfl]
      apply hasDerivWithinAt_univ.mp
      rw [← Iic_union_Ici (a := s)]
      apply HasDerivWithinAt.union
      · exact (P.hasDeriv s).hasDerivWithinAt.congr_of_mem (fun t ht => if_pos ht) (Set.mem_Iic.mpr (le_refl s))
      · rw [hv]
        apply (Q.hasDeriv s).hasDerivWithinAt.congr_of_mem _ (Set.mem_Ici.mpr (le_refl s))
        intro t ht
        by_cases hs : t ≤ s
        · have he : t=s := le_antisymm hs ht
          simpa [he] using hp
        · exact if_neg hs
    · rw [if_neg h.not_ge]
      apply (Q.hasDeriv s).congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds h] with t ht using if_neg ht.not_ge

def fromCurve {a : ℝ} (γ : ℝ → U a) (hc : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ) : Arc :=
  let hval : ContMDiff I4 I4 1 (Subtype.val : U a → E4) := contMDiff_subtype_val
  let h : ContDiff ℝ 1 (Subtype.val ∘ γ) := (hval.comp hc).contDiff
  ⟨Subtype.val ∘ γ,deriv (Subtype.val ∘ γ),fun s => (h.differentiable (by simp) s).hasDerivAt,
    h.continuous_deriv le_rfl⟩

theorem fromCurve_good (m a e : ℝ) (T : VecField (U a)) (γ : ℝ → U a)
    (hγ : IsFutureCausalCurveIn (G m a e) T (D m a e) γ) (s : ℝ) (hs : s∈J) :
    Good m a e T ((fromCurve γ hγ.1).pos s) ((fromCurve γ hγ.1).vel s) := by
  let P := fromCurve γ hγ.1
  have he := ambient_velocity a γ hγ.1 s (P.vel s) (P.hasDeriv s)
  change Good m a e T (γ s).val (P.vel s)
  rw [← he]
  obtain ⟨hx,_,hv,ht⟩ := hγ.2 s hs
  change F m a e (γ s).val (velocity γ s:E4) (T (γ s):E4)<0 at ht
  exact ⟨hx,hv,by rw [W_on]; exact ht⟩

private theorem realize (m a e : ℝ) (T : VecField (U a)) (P : Arc) (L : ℝ) (hL : 0<L)
    (p q : U a) (h0 : P.pos 0=p.val) (h1 : P.pos L=q.val) (hU : ∀ s, P.pos s∈U a)
    (hg : ∀ s ∈ Icc (0:ℝ) L, Good m a e T (P.pos s) (P.vel s)) :
    q∈causalFuture (G m a e) T (D m a e) p := by
  let γ (s : ℝ) : U a := ⟨P.pos (L*s),hU _⟩
  have hc : ContDiff ℝ 1 (Subtype.val ∘ γ) := P.smooth.comp (contDiff_const.mul contDiff_id)
  have hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ := by
    intro s
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff γ univ s).mp (hc.contMDiff s)
  refine Or.inr ⟨γ,⟨hγ,?_⟩,Subtype.ext (by simpa [γ] using h0),Subtype.ext (by simpa [γ] using h1)⟩
  intro s hs
  have hls : L*s∈Icc (0:ℝ) L := ⟨mul_nonneg hL.le hs.1,by simpa using mul_le_mul_of_nonneg_left hs.2 hL.le⟩
  have h := good_scale m a e T (hg _ hls) hL
  have hd : HasDerivAt (fun t => (γ t).val) (L • P.vel (L*s)) s :=
    (P.hasDeriv (L*s)).scomp s (by simpa using (hasDerivAt_id s).const_mul L)
  have he := ambient_velocity a γ hγ s _ hd
  have htg : G m a e (γ s) (velocity γ s) (T (γ s)) < 0 := by
    change F m a e (γ s).val (velocity γ s : E4) (T (γ s) : E4) < 0
    rw [he, ← W_on a T (γ s)]
    exact h.2.2
  refine ⟨h.1,?_,?_,htg⟩
  · intro hh
    simp [hh] at htg
  · change F m a e (γ s).val (velocity γ s : E4) (velocity γ s : E4) ≤ 0
    rw [he]
    exact h.2.1

def middleTime (d s : ℝ) := (s-(1-d))/(2*d)
def middle (d : ℝ) (hd : 0<d) (P Q : Arc) (y : E4) : Arc where
  pos s := let u := middleTime d s; P.pos (1-d*(1-u)^2)+Q.pos (d*u^2)-y
  vel s := let u := middleTime d s; (1-u) • P.vel (1-d*(1-u)^2) + u • Q.vel (d*u^2)
  continuous_vel := by
    have h := P.continuous_vel
    have h' := Q.continuous_vel
    unfold middleTime
    fun_prop
  hasDeriv s := by
    let u := middleTime d
    have hu : HasDerivAt u (1/(2*d)) s := by
      change HasDerivAt (fun t : ℝ => (t-(1-d))/(2*d)) (1/(2*d)) s
      exact ((hasDerivAt_id s).sub_const (1-d)).div_const (2*d)
    have hα : HasDerivAt (fun t => 1-d*(1-u t)^2) (1-u s) s := by
      have h := (((hu.const_sub 1).pow 2).const_mul d).const_sub 1
      apply h.congr_deriv
      field_simp [hd.ne'] <;> ring
    have hβ : HasDerivAt (fun t => d*(u t)^2) (u s) s := by
      have h := (hu.pow 2).const_mul d
      apply h.congr_deriv
      field_simp [hd.ne'] <;> ring
    exact (((P.hasDeriv _).scomp s hα).add ((Q.hasDeriv _).scomp s hβ)).sub_const y

private theorem use_join (c : ℝ) (P Q : Arc) (h : P.pos c=Q.pos c) (h' : P.vel c=Q.vel c)
    (s : ℝ) (R : E4→E4→Prop) (hL : s ≤ c → R (P.pos s) (P.vel s))
    (hR : c ≤ s → R (Q.pos s) (Q.vel s)) :
    R ((join c P Q h h').pos s) ((join c P Q h h').vel s) := by
  by_cases hs : s ≤ c
  · simpa [join,hs] using hL hs
  · simpa [join,hs] using hR (le_of_not_ge hs)

theorem combine_parallel (m a e : ℝ) (T : VecField (U a)) (P Q : Arc) (p x q : U a)
    (h0 : P.pos 0=p.val) (h1 : P.pos 1=x.val) (g0 : Q.pos 0=x.val) (g1 : Q.pos 1=q.val)
    (pU : ∀ s, P.pos s∈U a) (qU : ∀ s, Q.pos s∈U a)
    (pG : ∀ s∈J, Good m a e T (P.pos s) (P.vel s)) (qG : ∀ s∈J, Good m a e T (Q.pos s) (Q.vel s))
    (c : ℝ) (hc : 0<c) (he : P.vel 1=c • Q.vel 0) : q∈causalFuture (G m a e) T (D m a e) p := by
  let B := Q.affine c 1
  have hj : P.pos 1=B.pos 1 := by simpa [B,Arc.affine,Arc.reparam,g0] using h1
  have hv : P.vel 1=B.vel 1 := by simpa [B,Arc.affine,Arc.reparam] using he
  let A := join 1 P B hj hv
  let L := 1+1/c
  have hL : 1<L := by dsimp [L]; linarith [one_div_pos.mpr hc]
  have hlast : c*(L-1)=1 := by dsimp [L]; field_simp [hc.ne'] <;> ring
  apply realize m a e T A L (by linarith) p q
  · simpa [A,join] using h0
  · simpa [A,join,hL.not_ge,B,Arc.affine,Arc.reparam,hlast] using g1
  · intro s
    apply use_join 1 P B hj hv s (fun z _ => z∈U a) (fun _ => pU s) (fun _ => qU _)
  · intro s hs
    apply use_join 1 P B hj hv s (Good m a e T) (fun ht => pG s ⟨hs.1,ht⟩)
    intro ht
    apply good_scale m a e T _ hc
    apply qG _ ⟨mul_nonneg hc.le (sub_nonneg.mpr ht),?_⟩
    exact (mul_le_mul_of_nonneg_left (sub_le_sub_right hs.2 1) hc.le).trans_eq hlast

theorem combine_round (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (U a)) (P Q : Arc) (p x q : U a)
    (h0 : P.pos 0=p.val) (h1 : P.pos 1=x.val) (g0 : Q.pos 0=x.val) (g1 : Q.pos 1=q.val)
    (pU : ∀ s, P.pos s∈U a) (qU : ∀ s, Q.pos s∈U a)
    (pG : ∀ s∈J, Good m a e T (P.pos s) (P.vel s)) (qG : ∀ s∈J, Good m a e T (Q.pos s) (Q.vel s))
    (d : ℝ) (hd : 0<d) (hd1 : d<1)
    (hmid : ∀ u∈J,
      let s := 1-d*(1-u)^2
      let t := d*u^2
      Good m a e T (P.pos s+Q.pos t-x.val) ((1-u) • P.vel s + u • Q.vel t)) :
    q∈causalFuture (G m a e) T (D m a e) p := by
  let M := middle d hd P Q x.val
  let B := Q.affine 1 1
  have hleft : middleTime d (1-d)=0 := by simp [middleTime]
  have hright : middleTime d (1+d)=1 := by unfold middleTime; field_simp [hd.ne']; ring
  have hj : P.pos (1-d)=M.pos (1-d) := by
    change P.pos (1-d) = P.pos (1-d*(1-middleTime d (1-d))^2)+Q.pos (d*middleTime d (1-d)^2)-x.val
    rw [hleft]
    simp [g0]
  have hv : P.vel (1-d)=M.vel (1-d) := by simp [M,middle,hleft]
  let A := join (1-d) P M hj hv
  have hlt : 1-d < 1+d := by linarith
  have hj' : A.pos (1+d)=B.pos (1+d) := by simp [A,join,hlt.not_ge,M,middle,hright,h1,B,Arc.affine,Arc.reparam]
  have hv' : A.vel (1+d)=B.vel (1+d) := by simp [A,join,hlt.not_ge,M,middle,hright,B,Arc.affine,Arc.reparam]
  let path := join (1+d) A B hj' hv'
  have hmg (s : ℝ) (hl : 1-d ≤ s) (hr : s ≤ 1+d) : Good m a e T (M.pos s) (M.vel s) := by
    apply hmid (middleTime d s)
    constructor
    · exact div_nonneg (sub_nonneg.mpr hl) (by positivity)
    · apply (div_le_iff₀ (by positivity : 0<2*d)).mpr
      linarith
  have hdu {z : E4} (h : z∈kerrNewmanDOC m a e) : z∈U a := by
    change m+Real.sqrt (m^2-a^2-e^2) < ksRadius a z at h
    change 0<ksRadius a z
    linarith only [h,hp.1,Real.sqrt_nonneg (m^2-a^2-e^2)]
  apply realize m a e T path 2 (by norm_num) p q
  · simpa [path,A,join,show (0:ℝ) ≤ 1+d by linarith,show (0:ℝ) ≤ 1-d by linarith] using h0
  · simpa [path,join,show ¬ (2:ℝ) ≤ 1+d by linarith,B,Arc.affine,Arc.reparam,show (2:ℝ)-1=1 by norm_num] using g1
  · intro s
    apply use_join _ A B hj' hv' s (fun z _ => z∈U a) _ (fun _ => qU _)
    intro hr
    exact use_join _ P M hj hv s (fun z _ => z∈U a) (fun _ => pU _) (fun hl => hdu (hmg s hl hr).1)
  · intro s hs
    apply use_join _ A B hj' hv' s (Good m a e T)
    · intro hr
      apply use_join _ P M hj hv s (Good m a e T) _ (fun hl => hmg s hl hr)
      intro hl
      exact pG s ⟨hs.1,by linarith⟩
    · intro hl
      have hJ : s-1∈J := ⟨by linarith,by linarith [hs.2]⟩
      simpa [B,Arc.affine,Arc.reparam] using qG (s-1) hJ


end
end NoHair.CausalJoining


