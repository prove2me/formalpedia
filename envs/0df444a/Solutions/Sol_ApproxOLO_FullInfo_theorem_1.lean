-- Prove2me | solution 1 for ApproxOLO.FullInfo.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:53:17.501585+00:00
-- url     : https://prove2.me/submissions/4ffaa56f-1ebb-4e89-a2b8-0f000ef5cea2

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
theorem ApproxOLO.FullInfo.projection_guarantee : ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ), 2 ≤ d →
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


namespace ApproxOLO.FullInfo.OracleProof

open Matrix EuclideanProof

lemma dot_nonneg {d : ℕ} (x y : Vec d) (hx : IsNonneg x) (hy : IsNonneg y) :
    0 ≤ x ⬝ᵥ y := Finset.sum_nonneg (fun i _ => mul_nonneg (hx i) (hy i))

lemma dot_nonpos {d : ℕ} (x y : Vec d) (hx : IsNonneg x) (hy : ∀ i, y i ≤ 0) :
    x ⬝ᵥ y ≤ 0 := Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hx i) (hy i))

lemma pos_nonneg {d : ℕ} (c : Vec d) : IsNonneg (posCoord c) := fun i => le_max_right (c i) 0
lemma neg_nonpos {d : ℕ} (c : Vec d) (i : Fin d) : negCoord c i ≤ 0 := min_le_right (c i) 0
lemma neg_neg_nonneg {d : ℕ} (c : Vec d) : IsNonneg (-negCoord c) :=
  fun i => neg_nonneg.mpr (neg_nonpos c i)

lemma coord_decomp {d : ℕ} (c : Vec d) : posCoord c + negCoord c = c := by
  ext i
  exact (max_add_min (c i) 0).trans (add_zero _)

lemma coord_orthogonal {d : ℕ} (c : Vec d) : posCoord c ⬝ᵥ negCoord c = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  change max (c i) 0 * min (c i) 0 = 0
  by_cases h : 0 ≤ c i
  · simp [max_eq_left h, min_eq_right h]
  · simp [max_eq_right (le_of_not_ge h), min_eq_left (le_of_not_ge h)]

lemma unitDir_norm_le {d : ℕ} (x : Vec d) : euclNorm (unitDir x) ≤ 1 := by
  by_cases hx : 0 < euclNorm x
  · rw [unitDir, if_pos hx, euclNorm_smul, abs_of_nonneg (inv_nonneg.mpr hx.le)]
    simp only [inv_mul_cancel₀ hx.ne', le_refl]
  · simp only [unitDir, if_neg hx, euclNorm_zero, zero_le_one]

lemma unitDir_nonneg {d : ℕ} (x : Vec d) (hx : IsNonneg x) : IsNonneg (unitDir x) := by
  unfold unitDir
  split_ifs with hp
  · intro i
    exact mul_nonneg (inv_nonneg.mpr (euclNorm_nonneg x)) (hx i)
  · intro i
    exact le_rfl

lemma unitDir_nonpos {d : ℕ} (x : Vec d) (hx : ∀ i, x i ≤ 0) :
    ∀ i, unitDir x i ≤ 0 := by
  unfold unitDir
  split_ifs with hp
  · intro i
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (euclNorm_nonneg x)) (hx i)
  · intro i
    exact le_rfl

lemma unitDir_dot_self {d : ℕ} (x : Vec d) : unitDir x ⬝ᵥ x = euclNorm x := by
  by_cases hx : 0 < euclNorm x
  · rw [unitDir, if_pos hx, smul_dotProduct, smul_eq_mul, ← euclNorm_sq]
    field_simp
  · have hz : x = 0 := (euclNorm_eq_zero x).mp (le_antisymm (le_of_not_gt hx) (euclNorm_nonneg x))
    subst x
    simp [euclNorm_zero]

lemma unitDir_dot_orthogonal {d : ℕ} (x y : Vec d) (hxy : x ⬝ᵥ y = 0) :
    unitDir x ⬝ᵥ y = 0 := by
  unfold unitDir
  split_ifs <;> simp [smul_dotProduct, hxy]

lemma unit_neg_dot {d : ℕ} (c : Vec d) : unitDir (negCoord c) ⬝ᵥ c = euclNorm (negCoord c) := by
  calc
    _ = unitDir (negCoord c) ⬝ᵥ (posCoord c + negCoord c) := by rw [coord_decomp]
    _ = _ := by rw [dotProduct_add, unitDir_dot_self,
    unitDir_dot_orthogonal _ _ (by rw [dotProduct_comm]; exact coord_orthogonal c), zero_add]

lemma unit_pos_dot {d : ℕ} (c : Vec d) : unitDir (posCoord c) ⬝ᵥ c = euclNorm (posCoord c) := by
  calc
    _ = unitDir (posCoord c) ⬝ᵥ (posCoord c + negCoord c) := by rw [coord_decomp]
    _ = _ := by rw [dotProduct_add, unitDir_dot_self,
      unitDir_dot_orthogonal _ _ (coord_orthogonal c), add_zero]

lemma dot_coord {d : ℕ} (x c : Vec d) : x ⬝ᵥ c = x ⬝ᵥ posCoord c + x ⬝ᵥ negCoord c := by
  rw [← dotProduct_add, coord_decomp]

lemma shifted_distance {d : ℕ} (s u : Vec d) (a : ℝ) (ha : 0 ≤ a)
    (hu : euclNorm u ≤ 1) : euclNorm (s - a • u - s) ≤ a := by
  have heq : s - a • u - s = -(a • u) := by abel
  rw [heq, euclNorm_neg, euclNorm_smul, abs_of_nonneg ha]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hu ha

lemma shifted_norm {d : ℕ} (s u : Vec d) (R a : ℝ) (hs : euclNorm s ≤ R)
    (ha : 0 ≤ a) (hu : euclNorm u ≤ 1) : euclNorm (s - a • u) ≤ R + a := by
  calc
    _ ≤ euclNorm s + euclNorm (a • u) := euclNorm_sub_le _ _
    _ = euclNorm s + a * euclNorm u := by rw [euclNorm_smul, abs_of_nonneg ha]
    _ ≤ R + a := by nlinarith

end ApproxOLO.FullInfo.OracleProof

open ApproxOLO.FullInfo ApproxOLO.FullInfo.EuclideanProof ApproxOLO.FullInfo.OracleProof Matrix

theorem ApproxOLO.FullInfo.oracle_properties {d : ℕ} (K Fs : Set (Vec d)) (R Fb C alpha : ℝ) (O : Vec d → Vec d)
    (hinst : IsInstance K Fs R Fb C) (halpha : 0 < alpha) (hO : IsApproxOracle K alpha O)
    (c : Vec d) :
    (extOracle O alpha R c).2 ∈ K ∧
    (∃ k ∈ K, euclNorm ((extOracle O alpha R c).1 - k) ≤ (1 + alpha) * R) ∧
    (∀ z ∈ K, (extOracle O alpha R c).1 ⬝ᵥ c ≤ (alpha • z) ⬝ᵥ c) ∧
    (∀ f ∈ Fs, (1 ≤ alpha → (extOracle O alpha R c).2 ⬝ᵥ f ≤ (extOracle O alpha R c).1 ⬝ᵥ f) ∧
      (alpha < 1 → (extOracle O alpha R c).1 ⬝ᵥ f ≤ (extOracle O alpha R c).2 ⬝ᵥ f)) ∧
    euclNorm (extOracle O alpha R c).1 ≤ (alpha + 2) * R := by
  obtain ⟨_, _, _, hKpos, hFpos, hR, _, _, hKnorm, _, _⟩ := hinst
  by_cases ha : 1 ≤ alpha
  · obtain ⟨hs, hmin, _⟩ := hO (posCoord c) (pos_nonneg c)
    simp only [extOracle, if_pos ha]
    refine ⟨hs, ⟨O (posCoord c), hs, ?_⟩, ?_, ?_, ?_⟩
    · have hb := shifted_distance (O (posCoord c)) (unitDir (negCoord c)) (alpha * R)
        (mul_nonneg halpha.le hR.le) (unitDir_norm_le _)
      linarith
    · intro z hz
      have hpos := hmin ha z hz
      have hsneg := dot_nonpos (O (posCoord c)) (negCoord c) (hKpos _ hs) (neg_nonpos c)
      have hlow : -(R * euclNorm (negCoord c)) ≤ z ⬝ᵥ negCoord c := by
        have hcs := neg_norm_mul_le_dot z (negCoord c)
        have hb := mul_le_mul_of_nonneg_right (hKnorm z hz) (euclNorm_nonneg (negCoord c))
        linarith
      have halow := mul_le_mul_of_nonneg_left hlow halpha.le
      simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul, unit_neg_dot]
      rw [dot_coord (O (posCoord c)) c, dot_coord z c]
      nlinarith
    · intro f hf
      constructor
      · intro _
        have huf : unitDir (negCoord c) ⬝ᵥ f ≤ 0 := by
          rw [dotProduct_comm]
          exact dot_nonpos f _ (hFpos f hf) (unitDir_nonpos _ (neg_nonpos c))
        simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul]
        have := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg halpha.le hR.le) huf
        linarith
      · intro hlt
        exact (not_lt_of_ge ha hlt).elim
    · have hb := shifted_norm (O (posCoord c)) (unitDir (negCoord c)) R (alpha * R)
        (hKnorm _ hs) (mul_nonneg halpha.le hR.le) (unitDir_norm_le _)
      linarith
  · have ha' : alpha < 1 := lt_of_not_ge ha
    obtain ⟨hs, _, hmax⟩ := hO (-negCoord c) (neg_neg_nonneg c)
    simp only [extOracle, if_neg ha]
    refine ⟨hs, ⟨O (-negCoord c), hs, ?_⟩, ?_, ?_, ?_⟩
    · have hb := shifted_distance (O (-negCoord c)) (unitDir (posCoord c)) R hR.le (unitDir_norm_le _)
      nlinarith
    · intro z hz
      have hneg : O (-negCoord c) ⬝ᵥ negCoord c ≤ alpha * (z ⬝ᵥ negCoord c) := by
        have ho := hmax ha' z hz
        simp only [dotProduct_neg] at ho
        linarith
      have hspos : O (-negCoord c) ⬝ᵥ posCoord c ≤ R * euclNorm (posCoord c) :=
        (dot_le_norm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (hKnorm _ hs) (euclNorm_nonneg _))
      have hzpos := dot_nonneg z (posCoord c) (hKpos z hz) (pos_nonneg c)
      have hap := mul_nonneg halpha.le hzpos
      simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul, unit_pos_dot]
      rw [dot_coord (O (-negCoord c)) c, dot_coord z c]
      nlinarith
    · intro f hf
      constructor
      · intro hge
        exact (ha hge).elim
      · intro _
        have huf := dot_nonneg (unitDir (posCoord c)) f (unitDir_nonneg _ (pos_nonneg c)) (hFpos f hf)
        simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul]
        have := mul_nonneg hR.le huf
        linarith
    · have hb := shifted_norm (O (-negCoord c)) (unitDir (posCoord c)) R R
        (hKnorm _ hs) hR.le (unitDir_norm_le _)
      nlinarith


namespace ApproxOLO.FullInfo.GradientProof
open Matrix
open EuclideanProof

lemma telescope (D : ℕ → ℝ) (T : ℕ) :
    (∑ t ∈ Finset.Icc 1 T, (D t - D (t + 1))) = D 1 - D (T + 1) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

lemma loss_bound {d : ℕ} (eta : ℝ) (heta : 0 < eta) (T : ℕ) (hT : 1 ≤ T)
    (xs fs : ℕ → Vec d) (x : Vec d)
    (hproj : ∀ t, 1 ≤ t → t < T →
      euclNorm (x - xs (t + 1)) ^ 2 ≤ euclNorm (x - (xs t - eta • fs t)) ^ 2) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, xs t ⬝ᵥ fs t
        - (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, x ⬝ᵥ fs t
      ≤ 1 / (2 * T * eta) * euclNorm (xs 1 - x) ^ 2
        + eta / (2 * T) * ∑ t ∈ Finset.Icc 1 T, euclNorm (fs t) ^ 2 := by
  let D : ℕ → ℝ := fun t => if t ≤ T then euclNorm (xs t - x) ^ 2 else 0
  have hstep (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ T) :
      2 * eta * (xs t ⬝ᵥ fs t - x ⬝ᵥ fs t) ≤
        (D t - D (t + 1)) + eta ^ 2 * euclNorm (fs t) ^ 2 := by
    have hnext : D (t + 1) ≤ euclNorm (x - (xs t - eta • fs t)) ^ 2 := by
      by_cases hlt : t < T
      · simpa only [D, if_pos (show t + 1 ≤ T by omega), euclNorm_sub_comm (xs (t + 1)) x]
          using hproj t ht1 hlt
      · have heq : t = T := by omega
        simp only [D, heq, if_neg (show ¬T + 1 ≤ T by omega)]
        exact sq_nonneg _
    rw [euclNorm_sub_comm, euclNorm_step_sq, sub_dotProduct] at hnext
    simp only [D, if_pos htT]
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.Icc 1 T) fun t ht =>
    hstep t (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp ht).2
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  have htel : (∑ t ∈ Finset.Icc 1 T, D t) - (∑ t ∈ Finset.Icc 1 T, D (t + 1)) =
      D 1 - D (T + 1) := by rw [← Finset.sum_sub_distrib, telescope]
  rw [htel] at hsum
  simp only [D, if_pos hT, if_neg (show ¬T + 1 ≤ T by omega), sub_zero] at hsum
  have hTr : 0 < (T : ℝ) := by exact_mod_cast (show 0 < T by omega)
  have hT0 : (T : ℝ) ≠ 0 := ne_of_gt hTr
  have heta0 : eta ≠ 0 := ne_of_gt heta
  apply (mul_le_mul_iff_right₀ (show 0 < 2 * (T : ℝ) * eta by positivity)).mp
  calc
    (2 * (T : ℝ) * eta) *
        (1 / (T : ℝ) * ∑ t ∈ Finset.Icc 1 T, xs t ⬝ᵥ fs t -
          1 / (T : ℝ) * ∑ t ∈ Finset.Icc 1 T, x ⬝ᵥ fs t) =
        2 * eta * ((∑ t ∈ Finset.Icc 1 T, xs t ⬝ᵥ fs t) -
          ∑ t ∈ Finset.Icc 1 T, x ⬝ᵥ fs t) := by field_simp
    _ ≤ euclNorm (xs 1 - x) ^ 2 + eta ^ 2 *
        ∑ t ∈ Finset.Icc 1 T, euclNorm (fs t) ^ 2 := hsum
    _ = (2 * (T : ℝ) * eta) *
        (1 / (2 * (T : ℝ) * eta) * euclNorm (xs 1 - x) ^ 2 +
          eta / (2 * (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, euclNorm (fs t) ^ 2) := by
      field_simp

lemma payoff_bound {d : ℕ} (eta : ℝ) (heta : 0 < eta) (T : ℕ) (hT : 1 ≤ T)
    (xs fs : ℕ → Vec d) (x : Vec d)
    (hproj : ∀ t, 1 ≤ t → t < T →
      euclNorm (x - xs (t + 1)) ^ 2 ≤ euclNorm (x - (xs t + eta • fs t)) ^ 2) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, x ⬝ᵥ fs t
        - (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, xs t ⬝ᵥ fs t
      ≤ 1 / (2 * T * eta) * euclNorm (xs 1 - x) ^ 2
        + eta / (2 * T) * ∑ t ∈ Finset.Icc 1 T, euclNorm (fs t) ^ 2 := by
  have h := loss_bound eta heta T hT xs (fun t => -fs t) x (by
    simpa only [smul_neg, sub_neg_eq_add] using hproj)
  simpa only [dotProduct_neg, Finset.sum_neg_distrib, euclNorm_neg, mul_neg,
    neg_sub_neg] using h

end ApproxOLO.FullInfo.GradientProof


namespace ApproxOLO.FullInfo.RootProof
open Matrix EuclideanProof

lemma alg2_data {d : ℕ} {c alpha R eps : ℝ} {O : Vec d → Vec d}
    {y : Vec d} {out : Alg2Out d} (hrun : IsAlg2Run c O alpha R y eps out) :
    (∀ i, 0 ≤ out.a i) ∧ (∑ i, out.a i = 1) ∧
      ∀ i, ∃ w, out.pts i = extOracle O alpha R w := by
  rcases hrun with ⟨ys, Ns, hloops, hinit, hNs, hstep, hstop, hyt, hN, hpts, ha⟩
  refine ⟨ha.1, ha.2.1, ?_⟩
  intro i
  exact ⟨-(ellIter O alpha R (ys (out.loops - 1)) eps i).1, hpts i⟩

lemma output_loss_bounds {d : ℕ} (K Fs : Set (Vec d))
    (R Fb C alpha : ℝ) (O : Vec d → Vec d)
    (hinst : IsInstance K Fs R Fb C) (halpha : 0 < alpha) (hO : IsApproxOracle K alpha O)
    {c eps : ℝ} {y : Vec d} {out : Alg2Out d}
    (hrun : IsAlg2Run c O alpha R y eps out) (heps : 0 < eps)
    (hclose : euclNorm (∑ i, out.a i • (out.pts i).1 - out.yt) ≤ 3 * eps)
    (f : Vec d) (hf : f ∈ Fs) :
    (1 ≤ alpha → (∑ i, out.a i * ((out.pts i).2 ⬝ᵥ f)) ≤ out.yt ⬝ᵥ f + 3 * Fb * eps) ∧
    (alpha < 1 → out.yt ⬝ᵥ f ≤ (∑ i, out.a i * ((out.pts i).2 ⬝ᵥ f)) + 3 * Fb * eps) := by
  have hdata := alg2_data hrun
  let p := ∑ i, out.a i • (out.pts i).1
  have hpnorm : euclNorm (p - out.yt) ≤ 3 * eps := hclose
  have hfnorm : euclNorm f ≤ Fb := hinst.2.2.2.2.2.2.2.2.2.1 f hf
  have herr : |(p - out.yt) ⬝ᵥ f| ≤ 3 * Fb * eps := by
    calc
      |(p - out.yt) ⬝ᵥ f| ≤ euclNorm (p - out.yt) * euclNorm f := abs_dot_le_norm_mul _ _
      _ ≤ (3 * eps) * Fb := mul_le_mul hpnorm hfnorm (euclNorm_nonneg f) (by positivity)
      _ = 3 * Fb * eps := by ring
  have hdot : p ⬝ᵥ f = ∑ i, out.a i * ((out.pts i).1 ⬝ᵥ f) := by
    simp only [p, sum_dotProduct, smul_dotProduct, smul_eq_mul]
  rw [sub_dotProduct] at herr
  constructor
  · intro hcase
    have hdom : (∑ i, out.a i * ((out.pts i).2 ⬝ᵥ f)) ≤ p ⬝ᵥ f := by
      rw [hdot]
      apply Finset.sum_le_sum
      intro i _
      obtain ⟨w, hw⟩ := hdata.2.2 i
      have h := ((oracle_properties K Fs R Fb C alpha O hinst halpha hO w).2.2.2.1 f hf).1 hcase
      rw [← hw] at h
      exact mul_le_mul_of_nonneg_left h (hdata.1 i)
    linarith [(abs_le.mp herr).2]
  · intro hcase
    have hdom : p ⬝ᵥ f ≤ ∑ i, out.a i * ((out.pts i).2 ⬝ᵥ f) := by
      rw [hdot]
      apply Finset.sum_le_sum
      intro i _
      obtain ⟨w, hw⟩ := hdata.2.2 i
      have h := ((oracle_properties K Fs R Fb C alpha O hinst halpha hO w).2.2.2.1 f hf).2 hcase
      rw [← hw] at h
      exact mul_le_mul_of_nonneg_left h (hdata.1 i)
    linarith [(abs_le.mp herr).1]

lemma initial_distance {d : ℕ} (K Fs : Set (Vec d)) (R Fb C alpha : ℝ)
    (hinst : IsInstance K Fs R Fb C) (halpha : 0 < alpha)
    (s x : Vec d) (hs : s ∈ K) (hx : x ∈ K) :
    euclNorm (alpha • s - alpha • x) ^ 2 ≤ 2 * alpha ^ 2 * R ^ 2 := by
  rcases hinst with ⟨hK, hKne, hF, hKn, hFn, hR, hFb, hC, hKR, hFF, hcost⟩
  have hssq : euclNorm s ^ 2 ≤ R ^ 2 := sq_le_sq₀ (euclNorm_nonneg s) hR.le |>.2 (hKR s hs)
  have hxsq : euclNorm x ^ 2 ≤ R ^ 2 := sq_le_sq₀ (euclNorm_nonneg x) hR.le |>.2 (hKR x hx)
  have hdot : 0 ≤ s ⬝ᵥ x := dotProduct_nonneg_of_nonneg (hKn s hs) (hKn x hx)
  have hd : euclNorm (s - x) ^ 2 ≤ 2 * R ^ 2 := by
    rw [euclNorm_sub_sq]
    linarith
  calc
    euclNorm (alpha • s - alpha • x) ^ 2 = alpha ^ 2 * euclNorm (s - x) ^ 2 := by
      rw [← smul_sub, euclNorm_smul, abs_of_pos halpha]
      ring
    _ ≤ alpha ^ 2 * (2 * R ^ 2) := mul_le_mul_of_nonneg_left hd (sq_nonneg alpha)
    _ = 2 * alpha ^ 2 * R ^ 2 := by ring

lemma sum_norm_sq_bound {d T : ℕ} (Fs : Set (Vec d)) (Fb : ℝ) (hFb : 0 < Fb)
    (hF : ∀ f ∈ Fs, euclNorm f ≤ Fb) (fs : ℕ → Vec d)
    (hfs : ∀ t ∈ Finset.Icc 1 T, fs t ∈ Fs) :
    ∑ t ∈ Finset.Icc 1 T, euclNorm (fs t) ^ 2 ≤ (T : ℝ) * Fb ^ 2 := by
  calc
    ∑ t ∈ Finset.Icc 1 T, euclNorm (fs t) ^ 2 ≤ ∑ _t ∈ Finset.Icc 1 T, Fb ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      exact (sq_le_sq₀ (euclNorm_nonneg _) hFb.le).2 (hF _ (hfs t ht))
    _ = (T : ℝ) * Fb ^ 2 := by simp

lemma constants_identity (alpha R Fb eta : ℝ) (T : ℕ) (heta : 0 < eta) (hT : 1 ≤ T) :
    1 / (2 * T * eta) * (2 * alpha ^ 2 * R ^ 2) +
      eta / (2 * T) * ((T : ℝ) * Fb ^ 2) =
        alpha ^ 2 * R ^ 2 / (T * eta) + eta * Fb ^ 2 / 2 := by
  have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast (by omega : T ≠ 0)
  field_simp

lemma continuous_average {d : ℕ} (T : ℕ) (fs : ℕ → Vec d) :
    Continuous (fun x : Vec d => (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, x ⬝ᵥ fs t) := by
  unfold dotProduct
  fun_prop

end ApproxOLO.FullInfo.RootProof


namespace ApproxOLO.FullInfo.RootProof
open Matrix EuclideanProof

lemma average_le_of_round_le (T : ℕ) (hT : 1 ≤ T) (u v : ℕ → ℝ) (e : ℝ)
    (h : ∀ t ∈ Finset.Icc 1 T, u t ≤ v t + e) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, u t ≤
      (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, v t + e := by
  have hTr : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hs := Finset.sum_le_sum h
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hs
  have hc : ((Finset.Icc 1 T).card : ℝ) = T := by simp
  rw [hc] at hs
  have hh := mul_le_mul_of_nonneg_left hs (one_div_nonneg.mpr hTr.le)
  simpa only [mul_add, ← mul_assoc, one_div, inv_mul_cancel₀ (ne_of_gt hTr), one_mul] using hh

lemma iterate_bounds {d : ℕ} (K Fs : Set (Vec d)) (R Fb C alpha eta : ℝ)
    (T : ℕ) (fs : ℕ → Vec d) (s1 : Vec d) (outs : ℕ → Alg2Out d)
    (hinst : IsInstance K Fs R Fb C) (halpha : 0 < alpha) (heta : 0 < eta) (hT : 1 ≤ T)
    (hfs : ∀ t ∈ Finset.Icc 1 T, fs t ∈ Fs) (hs1 : s1 ∈ K)
    (hproj : ∀ t, 1 ≤ t → t < T → ∀ z ∈ scaledHull K alpha,
      euclNorm ((outs (t + 1)).yt - z) ^ 2 ≤
      euclNorm ((if 1 ≤ alpha then alg3Iterate alpha s1 outs t - eta • fs t
        else alg3Iterate alpha s1 outs t + eta • fs t) - z) ^ 2)
    (x : Vec d) (hx : x ∈ K) :
    (1 ≤ alpha →
      (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, alg3Iterate alpha s1 outs t ⬝ᵥ fs t
        - alpha * ((1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, x ⬝ᵥ fs t)
      ≤ alpha ^ 2 * R ^ 2 / (T * eta) + eta * Fb ^ 2 / 2) ∧
    (alpha < 1 →
      alpha * ((1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, x ⬝ᵥ fs t)
        - (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, alg3Iterate alpha s1 outs t ⬝ᵥ fs t
      ≤ alpha ^ 2 * R ^ 2 / (T * eta) + eta * Fb ^ 2 / 2) := by
  have hxscaled : alpha • x ∈ scaledHull K alpha :=
    subset_convexHull ℝ _ ⟨x, hx, rfl⟩
  have hi := initial_distance K Fs R Fb C alpha hinst halpha s1 x hs1 hx
  have hn := sum_norm_sq_bound Fs Fb hinst.2.2.2.2.2.2.1 hinst.2.2.2.2.2.2.2.2.2.1 fs hfs
  have hTr : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hb : 1 / (2 * T * eta) * euclNorm (alpha • s1 - alpha • x) ^ 2 +
      eta / (2 * T) * (∑ t ∈ Finset.Icc 1 T, euclNorm (fs t) ^ 2) ≤
      alpha ^ 2 * R ^ 2 / (T * eta) + eta * Fb ^ 2 / 2 := by
    calc
      _ ≤ 1 / (2 * T * eta) * (2 * alpha ^ 2 * R ^ 2) +
          eta / (2 * T) * ((T : ℝ) * Fb ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hi (by positivity))
          (mul_le_mul_of_nonneg_left hn (by positivity))
      _ = _ := constants_identity alpha R Fb eta T heta hT
  have hscale : (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, (alpha • x) ⬝ᵥ fs t =
      alpha * ((1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, x ⬝ᵥ fs t) := by
    simp only [smul_dotProduct, smul_eq_mul, ← Finset.mul_sum]
    ring
  constructor
  · intro hcase
    have hgrad := GradientProof.loss_bound eta heta T hT
      (alg3Iterate alpha s1 outs) fs (alpha • x) (by
        intro t ht hlt
        have hh := hproj t ht hlt (alpha • x) hxscaled
        rw [euclNorm_sub_comm, euclNorm_sub_comm (alpha • x)]
        simpa only [alg3Iterate, if_neg (show ¬t + 1 ≤ 1 by omega), if_pos hcase] using hh)
    rw [hscale] at hgrad
    exact hgrad.trans (by simpa [alg3Iterate] using hb)
  · intro hcase
    have hgrad := GradientProof.payoff_bound eta heta T hT
      (alg3Iterate alpha s1 outs) fs (alpha • x) (by
        intro t ht hlt
        have hh := hproj t ht hlt (alpha • x) hxscaled
        rw [euclNorm_sub_comm, euclNorm_sub_comm (alpha • x)]
        simpa only [alg3Iterate, if_neg (show ¬t + 1 ≤ 1 by omega),
          if_neg (not_le.mpr hcase)] using hh)
    rw [hscale] at hgrad
    exact hgrad.trans (by simpa [alg3Iterate] using hb)

lemma expected_round_bounds {d : ℕ} (c : ℝ) (K Fs : Set (Vec d))
    (R Fb C alpha eta eps : ℝ) (O : Vec d → Vec d)
    (T : ℕ) (fs : ℕ → Vec d) (s1 : Vec d) (outs : ℕ → Alg2Out d)
    (hinst : IsInstance K Fs R Fb C) (halpha : 0 < alpha) (hO : IsApproxOracle K alpha O)
    (heps : 0 < eps) (hfs : ∀ t ∈ Finset.Icc 1 T, fs t ∈ Fs)
    (hrun : IsAlg3Run c K O alpha R eta eps T fs s1 outs)
    (hclose : ∀ t, 1 ≤ t → t < T →
      euclNorm (∑ i, (outs (t + 1)).a i • ((outs (t + 1)).pts i).1 - (outs (t + 1)).yt) ≤ 3 * eps)
    (t : ℕ) (ht : t ∈ Finset.Icc 1 T) :
    (1 ≤ alpha → alg3ExpLoss s1 outs fs t ≤
      alg3Iterate alpha s1 outs t ⬝ᵥ fs t + 3 * Fb * eps) ∧
    (alpha < 1 → alg3Iterate alpha s1 outs t ⬝ᵥ fs t ≤
      alg3ExpLoss s1 outs fs t + 3 * Fb * eps) := by
  have hFb : 0 < Fb := hinst.2.2.2.2.2.2.1
  have herr : 0 ≤ 3 * Fb * eps := by positivity
  by_cases ht1 : t = 1
  · subst t
    have hnn := (hinst.2.2.2.2.2.2.2.2.2.2 s1 hrun.1 (fs 1) (hfs 1 ht)).1
    simp only [alg3ExpLoss, alg3Iterate, if_pos (le_refl 1), smul_dotProduct, smul_eq_mul]
    constructor <;> intro hcase <;> nlinarith
  · have htlo : 1 ≤ t - 1 := by have := (Finset.mem_Icc.mp ht).1; omega
    have hthi : t - 1 < T := by have := (Finset.mem_Icc.mp ht).2; omega
    have hsucc : t - 1 + 1 = t := by have := (Finset.mem_Icc.mp ht).1; omega
    have hr := hrun.2 (t - 1) htlo hthi
    have hc := hclose (t - 1) htlo hthi
    rw [hsucc] at hr hc
    have hb := output_loss_bounds K Fs R Fb C alpha O hinst halpha hO hr heps hc (fs t) (hfs t ht)
    have hnot : ¬t ≤ 1 := by have := (Finset.mem_Icc.mp ht).1; omega
    simpa only [alg3ExpLoss, alg3Iterate, if_neg hnot] using hb

end ApproxOLO.FullInfo.RootProof


open ApproxOLO.FullInfo ApproxOLO.FullInfo.RootProof Matrix

theorem solution : ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ), 2 ≤ d →
    ∀ (K Fs : Set (Vec d)) (R Fb C alpha eta eps : ℝ) (O : Vec d → Vec d) (T : ℕ)
      (fs : ℕ → Vec d) (s1 : Vec d) (outs : ℕ → Alg2Out d),
    IsInstance K Fs R Fb C → 0 < alpha → IsApproxOracle K alpha O →
    0 < eta → 0 < eps → eps ≤ (alpha + 2) * R → 1 ≤ T →
    (∀ t ∈ Finset.Icc 1 T, fs t ∈ Fs) →
    IsAlg3Run c K O alpha R eta eps T fs s1 outs →
    regretOf K alpha T fs (alg3ExpLoss s1 outs fs)
      ≤ alpha ^ 2 * R ^ 2 / (T * eta) + eta * Fb ^ 2 / 2 + 3 * Fb * eps := by
  obtain ⟨c, hc, h7⟩ := projection_guarantee
  refine ⟨c, hc, ?_⟩
  intro d hd K Fs R Fb C alpha eta eps O T fs s1 outs hinst halpha hO heta heps hepsmax hT hfs hrun
  have hcalls : ∀ t, 1 ≤ t → t < T →
      (∀ z ∈ scaledHull K alpha, euclNorm ((outs (t + 1)).yt - z) ^ 2 ≤
        euclNorm ((if 1 ≤ alpha then alg3Iterate alpha s1 outs t - eta • fs t
          else alg3Iterate alpha s1 outs t + eta • fs t) - z) ^ 2) ∧
      euclNorm (∑ i, (outs (t + 1)).a i • ((outs (t + 1)).pts i).1 - (outs (t + 1)).yt) ≤ 3 * eps := by
    intro t ht hlt
    exact (h7 d hd K Fs R Fb C alpha O
      (if 1 ≤ alpha then alg3Iterate alpha s1 outs t - eta • fs t
        else alg3Iterate alpha s1 outs t + eta • fs t)
      eps hinst halpha hO heps hepsmax).2 (outs (t + 1)) (hrun.2 t ht hlt)
  have hproj := fun t ht hlt => (hcalls t ht hlt).1
  have hclose := fun t ht hlt => (hcalls t ht hlt).2
  have hround := expected_round_bounds c K Fs R Fb C alpha eta eps O T fs s1 outs
    hinst halpha hO heps hfs hrun hclose
  by_cases hcase : 1 ≤ alpha
  · obtain ⟨x, hx, hxmin⟩ := hinst.1.exists_isMinOn hinst.2.1 (continuous_average T fs).continuousOn
    have his : IsLeast ((fun x : Vec d => (1 / (T : ℝ)) *
        ∑ t ∈ Finset.Icc 1 T, x ⬝ᵥ fs t) '' K)
        ((1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, x ⬝ᵥ fs t) := by
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      apply hxmin
      exact hz
    have hg := (iterate_bounds K Fs R Fb C alpha eta T fs s1 outs hinst halpha heta hT hfs
      hrun.1 hproj x hx).1 hcase
    have he := average_le_of_round_le T hT (alg3ExpLoss s1 outs fs)
      (fun t => alg3Iterate alpha s1 outs t ⬝ᵥ fs t) (3 * Fb * eps)
      (fun t ht => (hround t ht).1 hcase)
    rw [regretOf, if_pos hcase, his.csInf_eq]
    linarith
  · have hlt : alpha < 1 := lt_of_not_ge hcase
    obtain ⟨x, hx, hxmax⟩ := hinst.1.exists_isMaxOn hinst.2.1 (continuous_average T fs).continuousOn
    have his : IsGreatest ((fun x : Vec d => (1 / (T : ℝ)) *
        ∑ t ∈ Finset.Icc 1 T, x ⬝ᵥ fs t) '' K)
        ((1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, x ⬝ᵥ fs t) := by
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      apply hxmax
      exact hz
    have hg := (iterate_bounds K Fs R Fb C alpha eta T fs s1 outs hinst halpha heta hT hfs
      hrun.1 hproj x hx).2 hlt
    have he := average_le_of_round_le T hT
      (fun t => alg3Iterate alpha s1 outs t ⬝ᵥ fs t) (alg3ExpLoss s1 outs fs) (3 * Fb * eps)
      (fun t ht => (hround t ht).2 hlt)
    rw [regretOf, if_neg hcase, his.csSup_eq]
    linarith
