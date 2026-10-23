-- Prove2me | solution 1 for ApproxOLO.FullInfo.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:51:32.921065+00:00
-- url     : https://prove2.me/submissions/82371090-3251-4a2a-9462-86899b50c80e

import Mathlib
import Definitions.Def_ApproxOLO_FullInfo_Model
import Theorems.Thm_ApproxOLO_FullInfo_lemma_5

set_option autoImplicit false

namespace ApproxOLO.FullInfo.EuclideanProof

open Matrix
open scoped RealInnerProductSpace

lemma euclNorm_nonneg {d : ℕ} (x : Vec d) : 0 ≤ euclNorm x := Real.sqrt_nonneg _

lemma euclNorm_eq_norm {d : ℕ} (x : Vec d) :
    euclNorm x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [euclNorm, dotProduct, Real.norm_eq_abs, pow_two]

lemma dot_eq_inner {d : ℕ} (x y : Vec d) :
    x ⬝ᵥ y = inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 y) := by
  simp [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]

lemma euclNorm_sq {d : ℕ} (x : Vec d) : euclNorm x ^ 2 = x ⬝ᵥ x := by
  apply Real.sq_sqrt
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

lemma euclNorm_zero {d : ℕ} : euclNorm (0 : Vec d) = 0 := by simp [euclNorm]

lemma euclNorm_eq_zero {d : ℕ} (x : Vec d) : euclNorm x = 0 ↔ x = 0 := by
  rw [euclNorm_eq_norm, norm_eq_zero]
  exact WithLp.toLp_eq_zero 2

lemma euclNorm_sub_comm {d : ℕ} (x y : Vec d) : euclNorm (x - y) = euclNorm (y - x) := by
  simp only [euclNorm_eq_norm, WithLp.toLp_sub]
  exact norm_sub_rev _ _

lemma euclNorm_smul {d : ℕ} (a : ℝ) (x : Vec d) : euclNorm (a • x) = |a| * euclNorm x := by
  simp only [euclNorm_eq_norm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

lemma euclNorm_neg {d : ℕ} (x : Vec d) : euclNorm (-x) = euclNorm x := by
  simp only [euclNorm_eq_norm, WithLp.toLp_neg, norm_neg]

lemma euclNorm_add_le {d : ℕ} (x y : Vec d) : euclNorm (x + y) ≤ euclNorm x + euclNorm y := by
  simpa only [euclNorm_eq_norm, WithLp.toLp_add] using
    norm_add_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 y)

lemma euclNorm_sub_le {d : ℕ} (x y : Vec d) : euclNorm (x - y) ≤ euclNorm x + euclNorm y := by
  simpa only [euclNorm_eq_norm, WithLp.toLp_sub] using
    norm_sub_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 y)

lemma abs_dot_le_norm_mul {d : ℕ} (x y : Vec d) : |x ⬝ᵥ y| ≤ euclNorm x * euclNorm y := by
  simpa only [euclNorm_eq_norm, dot_eq_inner] using
    abs_real_inner_le_norm (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 y)

lemma dot_le_norm_mul {d : ℕ} (x y : Vec d) : x ⬝ᵥ y ≤ euclNorm x * euclNorm y :=
  (le_abs_self _).trans (abs_dot_le_norm_mul x y)

lemma neg_norm_mul_le_dot {d : ℕ} (x y : Vec d) : -(euclNorm x * euclNorm y) ≤ x ⬝ᵥ y :=
  (abs_le.mp (abs_dot_le_norm_mul x y)).1

lemma euclNorm_sub_sq {d : ℕ} (x y : Vec d) :
    euclNorm (x - y) ^ 2 = euclNorm x ^ 2 + euclNorm y ^ 2 - 2 * (x ⬝ᵥ y) := by
  simp only [euclNorm_sq, sub_dotProduct, dotProduct_sub, dotProduct_comm y x]
  ring

lemma euclNorm_step_sq {d : ℕ} (x z w : Vec d) (eps : ℝ) :
    euclNorm (x - eps • w - z) ^ 2 = euclNorm (x - z) ^ 2 +
      eps ^ 2 * euclNorm w ^ 2 - 2 * eps * ((x - z) ⬝ᵥ w) := by
  have heq : x - eps • w - z = (x - z) - eps • w := by abel
  rw [heq, euclNorm_sub_sq]
  simp only [euclNorm_sq, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

end ApproxOLO.FullInfo.EuclideanProof

set_option autoImplicit false

namespace ApproxOLO.FullInfo.EuclideanProof

open Matrix

lemma continuous_euclNorm {d : ℕ} : Continuous (euclNorm : Vec d → ℝ) := by
  unfold euclNorm
  fun_prop

lemma convex_euclBall {d : ℕ} (B : ℝ) : Convex ℝ {x : Vec d | euclNorm x ≤ B} := by
  intro x hx y hy a b ha hb hab
  calc
    euclNorm (a • x + b • y) ≤ euclNorm (a • x) + euclNorm (b • y) := euclNorm_add_le _ _
    _ = a * euclNorm x + b * euclNorm y := by rw [euclNorm_smul, euclNorm_smul,
      abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * B + b * B := add_le_add
      (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = B := by rw [← add_mul, hab, one_mul]

lemma norm_le_of_mem_scaledHull {d : ℕ} (K : Set (Vec d)) (R alpha : ℝ)
    (hR : ∀ x ∈ K, euclNorm x ≤ R) (halpha : 0 ≤ alpha)
    {z : Vec d} (hz : z ∈ scaledHull K alpha) : euclNorm z ≤ alpha * R := by
  apply convexHull_min (t := {x : Vec d | euclNorm x ≤ alpha * R}) ?_ (convex_euclBall _) hz
  rintro _ ⟨x, hx, rfl⟩
  change euclNorm (alpha • x) ≤ alpha * R
  rw [euclNorm_smul, abs_of_nonneg halpha]
  exact mul_le_mul_of_nonneg_left (hR x hx) halpha

lemma radial_scaled_distance {d : ℕ} (y z : Vec d) (B t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hta : t * euclNorm y = B)
    (hz : euclNorm z ≤ B) : euclNorm (t • y - z) ^ 2 ≤ euclNorm (y - z) ^ 2 := by
  have hdot : y ⬝ᵥ z ≤ euclNorm y * B :=
    (dot_le_norm_mul y z).trans (mul_le_mul_of_nonneg_left hz (euclNorm_nonneg y))
  have hcross : (1 - t) * (y ⬝ᵥ z) ≤ (euclNorm y - B) * B := by
    calc
      _ ≤ (1 - t) * (euclNorm y * B) := mul_le_mul_of_nonneg_left hdot (sub_nonneg.mpr ht1)
      _ = (euclNorm y - B) * B := by
        rw [show (1 - t) * (euclNorm y * B) = (euclNorm y - t * euclNorm y) * B by ring, hta]
  rw [euclNorm_sub_sq, euclNorm_sub_sq, euclNorm_smul, abs_of_nonneg ht0,
    smul_dotProduct, smul_eq_mul, hta]
  nlinarith [sq_nonneg (euclNorm y - B)]

lemma radial_clip_norm {d : ℕ} (y : Vec d) (B : ℝ) (hB : 0 < B) :
    euclNorm ((max 1 (euclNorm y / B))⁻¹ • y) ≤ B := by
  by_cases hy : euclNorm y ≤ B
  · have hratio : euclNorm y / B ≤ 1 := (div_le_one hB).mpr hy
    simpa only [max_eq_left hratio, inv_one, one_smul] using hy
  · have hyB : B < euclNorm y := lt_of_not_ge hy
    have hy0 : 0 < euclNorm y := hB.trans hyB
    have hratio : 1 ≤ euclNorm y / B := (one_le_div hB).mpr hyB.le
    rw [max_eq_right hratio, inv_div, euclNorm_smul, abs_of_nonneg (div_nonneg hB.le hy0.le)]
    exact le_of_eq (div_mul_cancel₀ B hy0.ne')

lemma radial_clip_distance {d : ℕ} (y z : Vec d) (B : ℝ) (hB : 0 < B)
    (hz : euclNorm z ≤ B) :
    euclNorm ((max 1 (euclNorm y / B))⁻¹ • y - z) ^ 2 ≤ euclNorm (y - z) ^ 2 := by
  by_cases hy : euclNorm y ≤ B
  · have hratio : euclNorm y / B ≤ 1 := (div_le_one hB).mpr hy
    simp only [max_eq_left hratio, inv_one, one_smul, le_refl]
  · have hyB : B < euclNorm y := lt_of_not_ge hy
    have hy0 : 0 < euclNorm y := hB.trans hyB
    have hratio : 1 ≤ euclNorm y / B := (one_le_div hB).mpr hyB.le
    rw [max_eq_right hratio, inv_div]
    exact radial_scaled_distance y z B (B / euclNorm y)
      (div_nonneg hB.le hy0.le) ((div_le_one hy0).mpr hyB.le)
      (div_mul_cancel₀ B hy0.ne') hz

end ApproxOLO.FullInfo.EuclideanProof

namespace ApproxOLO.FullInfo.ProjectionProof

noncomputable section
open Matrix

lemma exists_simplex_opt {d N : ℕ} (hN : 1 ≤ N) (v : Fin N → Vec d) (x : Vec d) :
    ∃ a, IsSimplexOpt v x a := by
  have hnonempty : (stdSimplex ℝ (Fin N)).Nonempty :=
    ⟨Pi.single (⟨0,by omega⟩ : Fin N) 1, single_mem_stdSimplex ℝ _⟩
  have hc : Continuous (fun a : Fin N → ℝ =>
      euclNorm (∑ i, a i • v i - x) ^ 2 / 2) := by
    unfold euclNorm dotProduct
    fun_prop
  obtain ⟨a,ha,hmin⟩ := (isCompact_stdSimplex ℝ (Fin N)).exists_isMinOn hnonempty hc.continuousOn
  exact ⟨a,ha.1,ha.2,fun b hb hsum => hmin ⟨hb,hsum⟩⟩

lemma exists_iteration_budget {X : Type*} (bound : X → ℝ) :
    ∃ N : X → ℕ, ∀ x, 1 ≤ N x ∧ bound x ≤ (N x : ℝ) := by
  classical
  have h (x : X) : ∃ N : ℕ, 1 ≤ N ∧ bound x ≤ (N : ℝ) := by
    obtain ⟨N,hN⟩ := exists_nat_gt (max (bound x) 0)
    refine ⟨N,?_,le_of_lt ((le_max_left _ _).trans_lt hN)⟩
    have hpos : (0:ℝ)<N := (le_max_right _ _).trans_lt hN
    exact_mod_cast hpos
  choose N hN using h
  exact ⟨N,hN⟩

lemma exists_inactive_iterate {X : Type*} (step : X → X) (active : X → Prop)
    (potential : X → ℝ) (delta : ℝ) (hdelta : 0 < delta)
    (hnonneg : ∀ x, 0 ≤ potential x)
    (hdecrease : ∀ x, active x → potential (step x) ≤ potential x-delta) (x₀ : X) :
    ∃ n : ℕ, ¬ active (step^[n] x₀) := by
  by_contra h
  push Not at h
  have hbound (n : ℕ) : potential (step^[n] x₀) ≤ potential x₀-(n:ℝ)*delta := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hs := hdecrease (step^[n] x₀) (h n)
      push_cast
      linarith
  obtain ⟨n,hn⟩ := exists_nat_gt (potential x₀/delta)
  have hn' : potential x₀ < (n:ℝ)*delta := (div_lt_iff₀ hdelta).mp hn
  have hb := hbound n
  have hp := hnonneg (step^[n] x₀)
  linarith

lemma separator_on_hull {d : ℕ} (K : Set (Vec d)) (alpha eps : ℝ) (x w : Vec d)
    (hsep : ∀ z∈K, eps ≤ (x-alpha•z) ⬝ᵥ w) :
    ∀ z∈scaledHull K alpha, eps ≤ (x-z) ⬝ᵥ w := by
  change convexHull ℝ ((fun z => alpha • z) '' K) ⊆ {z : Vec d | eps ≤ (x-z) ⬝ᵥ w}
  apply convexHull_min
  · rintro z ⟨q,hq,rfl⟩
    exact hsep q hq
  · intro u hu v hv a b ha hb hab
    change eps ≤ (x-u) ⬝ᵥ w at hu
    change eps ≤ (x-v) ⬝ᵥ w at hv
    change eps ≤ (x-(a•u+b•v)) ⬝ᵥ w
    have heq : (x-(a•u+b•v)) ⬝ᵥ w = a*((x-u) ⬝ᵥ w)+b*((x-v) ⬝ᵥ w) := by
      simp only [sub_dotProduct,add_dotProduct,smul_dotProduct,smul_eq_mul]
      have hmul := congrArg (fun t : ℝ => t * (x ⬝ᵥ w)) hab
      nlinarith [hmul]
    rw [heq]
    calc
      eps = (a+b)*eps := by rw [hab,one_mul]
      _ = a*eps+b*eps := by ring
      _ ≤ a*((x-u) ⬝ᵥ w)+b*((x-v) ⬝ᵥ w) :=
        add_le_add (mul_le_mul_of_nonneg_left hu ha) (mul_le_mul_of_nonneg_left hv hb)

end
end ApproxOLO.FullInfo.ProjectionProof

namespace ApproxOLO.FullInfo.ProjectionProof

noncomputable section
open Matrix EuclideanProof

structure ProcedureFacts {d : ℕ} (c : ℝ) (K : Set (Vec d)) (O : Vec d → Vec d)
    (alpha R eps : ℝ) : Prop where
  separate : ∀ (x : Vec d) (N : ℕ), 1 ≤ N →
    c*(d:ℝ)^2*Real.log (((alpha+1)*R+euclNorm x)/eps) ≤ (N:ℝ) →
    ∀ j<N, ellFeasibleAt O alpha R x eps j →
      (∀ z∈scaledHull K alpha, eps ≤ (x-z) ⬝ᵥ (ellIter O alpha R x eps j).1) ∧
      euclNorm (ellIter O alpha R x eps j).1 ≤ 1
  decompose : ∀ (x : Vec d) (N : ℕ), 1 ≤ N →
    c*(d:ℝ)^2*Real.log (((alpha+1)*R+euclNorm x)/eps) ≤ (N:ℝ) →
    (∀ j<N, ¬ ellFeasibleAt O alpha R x eps j) →
    ∀ a : Fin N → ℝ, IsSimplexOpt (fun i => (ellOut O alpha R x eps i).1) x a →
      euclNorm (x-∑ i, a i • (ellOut O alpha R x eps i).1) ≤ 3*eps

def HasSeparator {d : ℕ} (O : Vec d → Vec d) (alpha R eps : ℝ)
    (budget : Vec d → ℕ) (x : Vec d) : Prop :=
  ∃ j<budget x, ellFeasibleAt O alpha R x eps j

def separatorStep {d : ℕ} (O : Vec d → Vec d) (alpha R eps : ℝ)
    (budget : Vec d → ℕ) (x : Vec d) : Vec d := by
  classical
  exact if h : HasSeparator O alpha R eps budget x then
    x-eps • (ellIter O alpha R x eps (Nat.find h)).1 else x

lemma separatorStep_spec {d : ℕ} (O : Vec d → Vec d) (alpha R eps : ℝ)
    (budget : Vec d → ℕ) (x : Vec d) (h : HasSeparator O alpha R eps budget x) :
    ∃ j<budget x, ellFeasibleAt O alpha R x eps j ∧
      (∀ j'<j, ¬ ellFeasibleAt O alpha R x eps j') ∧
      separatorStep O alpha R eps budget x = x-eps • (ellIter O alpha R x eps j).1 := by
  classical
  refine ⟨Nat.find h,(Nat.find_spec h).1,(Nat.find_spec h).2,?_,?_⟩
  · intro j' hj' hf
    exact Nat.find_min h hj' ⟨hj'.trans (Nat.find_spec h).1,hf⟩
  · simp only [separatorStep,dif_pos h]

lemma separator_decrease {d : ℕ} (x z w : Vec d) (eps : ℝ) (heps : 0 < eps)
    (hw : euclNorm w ≤ 1) (hsep : eps ≤ (x-z) ⬝ᵥ w) :
    euclNorm (x-eps•w-z)^2 ≤ euclNorm (x-z)^2-eps^2 := by
  rw [euclNorm_step_sq]
  have hw0 := euclNorm_nonneg w
  have hw2 : euclNorm w ^ 2 ≤ 1 := by nlinarith
  have h₁ := mul_le_mul_of_nonneg_left hw2 (sq_nonneg eps)
  have h₂ := mul_le_mul_of_nonneg_left hsep heps.le
  nlinarith

lemma separatorStep_decrease {d : ℕ} {c alpha R eps : ℝ} {K : Set (Vec d)}
    {O : Vec d → Vec d} (facts : ProcedureFacts c K O alpha R eps) (heps : 0 < eps)
    (budget : Vec d → ℕ)
    (hbudget : ∀ x, 1 ≤ budget x ∧
      c*(d:ℝ)^2*Real.log (((alpha+1)*R+euclNorm x)/eps) ≤ (budget x:ℝ))
    (x z : Vec d) (hz : z∈scaledHull K alpha) (h : HasSeparator O alpha R eps budget x) :
    euclNorm (separatorStep O alpha R eps budget x-z)^2 ≤ euclNorm (x-z)^2-eps^2 := by
  obtain ⟨j,hj,hf,_,hstep⟩ := separatorStep_spec O alpha R eps budget x h
  obtain ⟨hsep,hw⟩ := facts.separate x (budget x) (hbudget x).1 (hbudget x).2 j hj hf
  rw [hstep]
  exact separator_decrease x z _ eps heps hw (hsep z hz)

lemma exists_complete_run {d : ℕ} {c alpha R eps : ℝ} {K : Set (Vec d)}
    {O : Vec d → Vec d} (facts : ProcedureFacts c K O alpha R eps) (heps : 0 < eps)
    (hK : (scaledHull K alpha).Nonempty) (y : Vec d) :
    ∃ out : Alg2Out d, IsAlg2Run c O alpha R y eps out := by
  classical
  obtain ⟨budget,hbudget⟩ := exists_iteration_budget
    (fun x : Vec d => c*(d:ℝ)^2*Real.log (((alpha+1)*R+euclNorm x)/eps))
  let start : Vec d := (max 1 (euclNorm y/(alpha*R)))⁻¹ • y
  let step := separatorStep O alpha R eps budget
  let ys : ℕ → Vec d := fun i => step^[i] start
  let Ns : ℕ → ℕ := fun i => budget (ys i)
  obtain ⟨z,hz⟩ := hK
  have hterm : ∃ n : ℕ, ¬ HasSeparator O alpha R eps budget (ys n) :=
    exists_inactive_iterate step (HasSeparator O alpha R eps budget)
      (fun x => euclNorm (x-z)^2) (eps^2) (sq_pos_of_pos heps)
      (fun _ => sq_nonneg _) (fun x hx => separatorStep_decrease facts heps budget hbudget x z hz hx) start
  let n : ℕ := Nat.find hterm
  have hstop : ¬ HasSeparator O alpha R eps budget (ys n) := Nat.find_spec hterm
  have hactive (i : ℕ) (hi : i<n) : HasSeparator O alpha R eps budget (ys i) := by
    by_contra h
    exact Nat.find_min hterm hi h
  obtain ⟨a,ha⟩ := exists_simplex_opt (hbudget (ys n)).1
    (fun i : Fin (Ns n) => (ellOut O alpha R (ys n) eps i).1) (ys n)
  let out : Alg2Out d :=
    {yt:=ys n, N:=Ns n, pts:=fun i => ellOut O alpha R (ys n) eps i, a:=a, loops:=n+1}
  refine ⟨out,ys,Ns,by dsimp [out]; omega,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rfl
  · intro i _
    exact hbudget (ys i)
  · intro i hi
    have hin : i<n := by dsimp [out] at hi; omega
    obtain ⟨j,hj,hf,hfirst,hstep⟩ := separatorStep_spec O alpha R eps budget (ys i) (hactive i hin)
    refine ⟨j,hj,hf,hfirst,?_⟩
    exact (Function.iterate_succ_apply' step i start).trans hstep
  · intro j hj hf
    apply hstop
    exact ⟨j,by simpa only [out,Nat.add_sub_cancel] using hj,by simpa only [out,Nat.add_sub_cancel] using hf⟩
  · simp only [out,Nat.add_sub_cancel]
  · simp only [out,Nat.add_sub_cancel]
  · intro i
    simp only [out,Nat.add_sub_cancel]
  · exact ha

end
end ApproxOLO.FullInfo.ProjectionProof

namespace ApproxOLO.FullInfo.ProjectionProof

noncomputable section
open Matrix EuclideanProof

lemma run_distance {d : ℕ} {c alpha R eps : ℝ} {K : Set (Vec d)}
    {O : Vec d → Vec d} (facts : ProcedureFacts c K O alpha R eps) (heps : 0 < eps)
    (y : Vec d) (out : Alg2Out d) (hrun : IsAlg2Run c O alpha R y eps out)
    (hclip : ∀ z∈scaledHull K alpha,
      euclNorm ((max 1 (euclNorm y/(alpha*R)))⁻¹•y-z)^2 ≤ euclNorm (y-z)^2) :
    ∀ z∈scaledHull K alpha, euclNorm (out.yt-z)^2 ≤ euclNorm (y-z)^2 := by
  obtain ⟨ys,Ns,hloops,hinit,hbudget,hsteps,hstop,hyt,hN,hpts,hopt⟩ := hrun
  intro z hz
  have hbound : ∀ i, i<out.loops → euclNorm (ys i-z)^2 ≤ euclNorm (y-z)^2 := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [hinit]
      exact hclip z hz
    | succ i ih =>
      intro hi
      have hi' : i<out.loops := by omega
      obtain ⟨j,hj,hfeas,_,hstep⟩ := hsteps i hi
      obtain ⟨hsep,hw⟩ := facts.separate (ys i) (Ns i) (hbudget i hi').1
        (hbudget i hi').2 j hj hfeas
      rw [hstep]
      exact (separator_decrease (ys i) z _ eps heps hw (hsep z hz)).trans
        ((sub_le_self _ (sq_nonneg eps)).trans (ih hi'))
  rw [hyt]
  exact hbound _ (by omega)

lemma run_decomposition {d : ℕ} {c alpha R eps : ℝ} {K : Set (Vec d)}
    {O : Vec d → Vec d} (facts : ProcedureFacts c K O alpha R eps)
    (y : Vec d) (out : Alg2Out d) (hrun : IsAlg2Run c O alpha R y eps out) :
    euclNorm (∑ i, out.a i • (out.pts i).1-out.yt) ≤ 3*eps := by
  rcases out with ⟨yt,N,pts,a,loops⟩
  obtain ⟨ys,Ns,hloops,hinit,hbudget,hsteps,hstop,hyt,hN,hpts,hopt⟩ := hrun
  dsimp only at hyt hN hpts hopt ⊢
  subst yt
  subst N
  have hp : pts = fun i : Fin (Ns (loops-1)) => ellOut O alpha R (ys (loops-1)) eps i := funext hpts
  subst pts
  rw [euclNorm_sub_comm]
  exact facts.decompose _ _ (hbudget _ (by omega)).1 (hbudget _ (by omega)).2 hstop a hopt

end
end ApproxOLO.FullInfo.ProjectionProof

open ApproxOLO.FullInfo ApproxOLO.FullInfo.ProjectionProof ApproxOLO.FullInfo.EuclideanProof

/-- Algorithm 2 terminates, preserves distance to the scaled hull, and returns a nearby simplex
combination. Its separation-or-decomposition guarantee is the existing Lemma 5. -/
theorem solution : ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ), 2 ≤ d →
    ∀ (K Fs : Set (Vec d)) (R Fb C alpha : ℝ) (O : Vec d → Vec d) (y : Vec d) (eps : ℝ),
    IsInstance K Fs R Fb C → 0 < alpha → IsApproxOracle K alpha O →
    0 < eps → eps ≤ (alpha + 2) * R →
    (∃ out : Alg2Out d, IsAlg2Run c O alpha R y eps out) ∧
    ∀ out : Alg2Out d, IsAlg2Run c O alpha R y eps out →
      (∀ z ∈ scaledHull K alpha, euclNorm (out.yt - z) ^ 2 ≤ euclNorm (y - z) ^ 2) ∧
      euclNorm (∑ i, out.a i • (out.pts i).1 - out.yt) ≤ 3 * eps := by
  obtain ⟨c,hc,hprocedure⟩ := ApproxOLO.FullInfo.lemma_5
  refine ⟨c,hc,?_⟩
  intro d hd K Fs R Fb C alpha O y eps hinst halpha horacle heps hepsupper
  have facts : ProcedureFacts c K O alpha R eps := by
    constructor
    · intro x N hN hbudget j hj hfeas
      obtain ⟨hsep,hw⟩ := (hprocedure d hd K Fs R Fb C alpha O x eps N
        hinst halpha horacle heps hepsupper hN hbudget).1 j hj hfeas
      exact ⟨separator_on_hull K alpha eps x _ hsep,hw⟩
    · intro x N hN hbudget
      exact (hprocedure d hd K Fs R Fb C alpha O x eps N
        hinst halpha horacle heps hepsupper hN hbudget).2
  obtain ⟨_,hK,_,_,_,hR,_,_,hKR,_,_⟩ := hinst
  have hhull : (scaledHull K alpha).Nonempty := by
    obtain ⟨x,hx⟩ := hK
    exact ⟨alpha • x,subset_convexHull ℝ ((fun x => alpha • x) '' K) ⟨x,hx,rfl⟩⟩
  refine ⟨exists_complete_run facts heps hhull y,?_⟩
  intro out hrun
  refine ⟨run_distance facts heps y out hrun ?_,run_decomposition facts y out hrun⟩
  intro z hz
  exact radial_clip_distance y z (alpha*R) (mul_pos halpha hR)
    (norm_le_of_mem_scaledHull K R alpha hKR halpha.le hz)
