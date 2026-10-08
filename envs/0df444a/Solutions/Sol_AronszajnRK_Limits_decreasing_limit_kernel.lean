-- Prove2me | solution 1 for AronszajnRK.Limits.decreasing_limit_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T11:47:57.011061+00:00
-- url     : https://prove2.me/submissions/76a5746e-5fb2-4c83-ad38-d38754faee54

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn
import Definitions.Def_AronszajnRK_Limits_IsDecreasingRKSequence
import Definitions.Def_AronszajnRK_Limits_limitClass

set_option autoImplicit false

universe u v w

open Filter Topology

namespace AronszajnLimAux

open scoped ComplexOrder

section transfer
variable {X : Type*} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

lemma inner_lc_right (a : X → E) (y : E) (d : X →₀ ℂ) :
    inner ℂ y (Finsupp.linearCombination ℂ a d) = d.sum fun x t => t * inner ℂ y (a x) := by
  simp only [Finsupp.linearCombination_apply, Finsupp.inner_sum, inner_smul_right]

lemma inner_lc_left (a : X → E) (d : X →₀ ℂ) (y : E) :
    inner ℂ (Finsupp.linearCombination ℂ a d) y =
      d.sum fun x t => starRingEnd ℂ t * inner ℂ (a x) y := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum_inner, inner_smul_left]

lemma inner_lc_self (a : X → E) (c : X →₀ ℂ) :
    inner ℂ (Finsupp.linearCombination ℂ a c) (Finsupp.linearCombination ℂ a c) =
      c.sum fun i s => s * c.sum fun j t => (starRingEnd ℂ) t * inner ℂ (a j) (a i) := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum_inner, Finsupp.inner_sum,
    inner_smul_left, inner_smul_right]

lemma dsum_gram (a : X → E) (v : X →₀ ℂ) :
    (v.sum fun i xi => v.sum fun j xj => star xi * inner ℂ (a i) (a j) * xj) =
      inner ℂ (Finsupp.linearCombination ℂ a v) (Finsupp.linearCombination ℂ a v) := by
  rw [inner_lc_self, Finsupp.sum_comm]
  refine Finsupp.sum_congr fun j _ => ?_
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun i _ => ?_
  simp only [starRingEnd_apply]
  ring

lemma norm_lc_eq (a : X → E) (b : X → F)
    (G : ∀ x y, inner ℂ (a x) (a y) = inner ℂ (b x) (b y)) (c : X →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ a c‖ = ‖Finsupp.linearCombination ℂ b c‖ := by
  have hin : inner ℂ (Finsupp.linearCombination ℂ a c) (Finsupp.linearCombination ℂ a c) =
      inner ℂ (Finsupp.linearCombination ℂ b c) (Finsupp.linearCombination ℂ b c) := by
    rw [inner_lc_self, inner_lc_self]
    simp only [G]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hin
  have h2 : ‖Finsupp.linearCombination ℂ a c‖ ^ 2 = ‖Finsupp.linearCombination ℂ b c‖ ^ 2 := by
    exact_mod_cast hin
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

lemma transfer [CompleteSpace F] (a : X → E) (b : X → F)
    (G : ∀ x y, inner ℂ (a x) (a y) = inner ℂ (b x) (b y)) (e : E)
    (he : e ∈ closure (Set.range (Finsupp.linearCombination ℂ a : (X →₀ ℂ) → E))) :
    ∃ f : F, (∀ y, inner ℂ (b y) f = inner ℂ (a y) e) ∧ ‖f‖ = ‖e‖ := by
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp he
  choose c hc using hu
  have hu' : u = fun n => Finsupp.linearCombination ℂ a (c n) := funext fun n => (hc n).symm
  subst hu'
  have hd : ∀ m n, dist (Finsupp.linearCombination ℂ b (c m))
      (Finsupp.linearCombination ℂ b (c n)) =
      dist (Finsupp.linearCombination ℂ a (c m)) (Finsupp.linearCombination ℂ a (c n)) := by
    intro m n
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, ← map_sub, norm_lc_eq a b G]
  have hC1 := hlim.cauchySeq
  have hC2 : CauchySeq fun n => Finsupp.linearCombination ℂ b (c n) := by
    rw [Metric.cauchySeq_iff] at hC1 ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hC1 ε hε
    exact ⟨N, fun m hm n hn => (hd m n) ▸ hN m hm n hn⟩
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hC2
  refine ⟨g, fun y => ?_, ?_⟩
  · have t1 : Tendsto (fun n => inner ℂ (b y) (Finsupp.linearCombination ℂ b (c n))) atTop
        (𝓝 (inner ℂ (b y) g)) := tendsto_const_nhds.inner hg
    have t2 : Tendsto (fun n => inner ℂ (a y) (Finsupp.linearCombination ℂ a (c n))) atTop
        (𝓝 (inner ℂ (a y) e)) := tendsto_const_nhds.inner hlim
    have heq : ∀ n, inner ℂ (b y) (Finsupp.linearCombination ℂ b (c n)) =
        inner ℂ (a y) (Finsupp.linearCombination ℂ a (c n)) := by
      intro n
      rw [inner_lc_right, inner_lc_right]
      simp only [G]
    simp_rw [heq] at t1
    exact tendsto_nhds_unique t1 t2
  · have t1 := hg.norm
    have t2 := hlim.norm
    simp_rw [← norm_lc_eq a b G] at t1
    exact tendsto_nhds_unique t1 t2

end transfer

section rk
variable {X : Type*} (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [RKHS ℂ H X ℂ]

lemma eval_inner (y : X) (f : H) : inner ℂ (RKHS.kerFun H y (1 : ℂ)) f = f y := by
  rw [RKHS.kerFun_inner]
  simp

lemma gram (x y : X) :
    inner ℂ (RKHS.kerFun H x (1 : ℂ)) (RKHS.kerFun H y (1 : ℂ)) =
      AronszajnRK.Sum.kernelFn H x y := by
  rw [eval_inner, RKHS.kerFun_apply]
  rfl

end rk

section opk
variable {X : Type*} (K : X → X → ℂ)

/-- The operator-valued matrix attached to a scalar kernel. -/
noncomputable def opK : Matrix X X (ℂ →L[ℂ] ℂ) := Matrix.of fun x y => K x y • (1 : ℂ →L[ℂ] ℂ)

lemma opK_posSemidef (hK : (Matrix.of K).PosSemidef) : (opK K).PosSemidef := by
  have hH : (opK K).IsHermitian := by
    ext i j : 1
    simp only [Matrix.conjTranspose_apply, opK, Matrix.of_apply, star_smul, star_one]
    have := hK.1.apply i j
    simp only [Matrix.of_apply] at this
    rw [this]
  have key := (RKHS.posSemidef_tfae (𝕜 := ℂ) (K := opK K)).out 2 0
  refine key.mp ⟨hH, fun vv => ?_⟩
  have h0 := hK.2 vv
  have heq : (vv.sum fun x w => vv.sum fun x' w' => inner ℂ (opK K x' x w) w') =
      vv.sum fun i xi => vv.sum fun j xj => star xi * (Matrix.of K) i j * xj := by
    refine Finsupp.sum_congr fun x _ => Finsupp.sum_congr fun x' _ => ?_
    have hh : star (K x' x) = K x x' := by
      have := hK.1.apply x x'
      simpa using this
    simp only [opK, Matrix.of_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, smul_eq_mul, RCLike.inner_apply, map_mul]
    rw [← hh]
    simp only [RCLike.star_def]
    ring
  rw [heq]
  exact (Complex.le_def.mp h0).1

lemma kernelFn_ofKernel (hK : (Matrix.of K).PosSemidef) :
    haveI : Fact (opK K).PosSemidef := ⟨opK_posSemidef K hK⟩
    ∀ x y, AronszajnRK.Sum.kernelFn (RKHS.OfKernel (opK K)) x y = K x y := by
  haveI : Fact (opK K).PosSemidef := ⟨opK_posSemidef K hK⟩
  intro x y
  show RKHS.kernel (RKHS.OfKernel (opK K)) x y 1 = K x y
  rw [RKHS.OfKernel.kernel_ofKernel]
  simp [opK]

end opk

section dom
variable {Y E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma defect_psd (a : Y → E) (b : Y → F)
    (hab : ∀ c : Y →₀ ℂ, ‖Finsupp.linearCombination ℂ a c‖ ≤ ‖Finsupp.linearCombination ℂ b c‖) :
    (Matrix.of fun x y => inner ℂ (b x) (b y) - inner ℂ (a x) (a y)).PosSemidef := by
  refine ⟨?_, fun v => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_sub]
    rw [← starRingEnd_apply, ← starRingEnd_apply, inner_conj_symm, inner_conj_symm]
  · have h : (v.sum fun i xi => v.sum fun j xj =>
        star xi * (Matrix.of fun x y => inner ℂ (b x) (b y) - inner ℂ (a x) (a y)) i j * xj) =
        (v.sum fun i xi => v.sum fun j xj => star xi * inner ℂ (b i) (b j) * xj) -
        (v.sum fun i xi => v.sum fun j xj => star xi * inner ℂ (a i) (a j) * xj) := by
      simp only [Matrix.of_apply, mul_sub, sub_mul, Finsupp.sum_sub]
    rw [h, dsum_gram, dsum_gram, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
    have h1 := hab v
    have h2 : (0 : ℝ) ≤ ‖Finsupp.linearCombination ℂ b v‖ ^ 2 -
        ‖Finsupp.linearCombination ℂ a v‖ ^ 2 := by
      nlinarith [norm_nonneg (Finsupp.linearCombination ℂ a v)]
    rw [← RCLike.ofReal_pow, ← RCLike.ofReal_pow, ← RCLike.ofReal_sub]
    exact RCLike.ofReal_nonneg.mpr h2

lemma dom_core {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (a : Y → E) (b : Y → F) (d : Y → G)
    (hd : ∀ x y, inner ℂ (a x) (a y) + inner ℂ (d x) (d y) = inner ℂ (b x) (b y)) (e : E) :
    ∃ f : F, (∀ y, inner ℂ (b y) f = inner ℂ (a y) e) ∧ ‖f‖ ≤ ‖e‖ := by
  set w : Y → WithLp 2 (E × G) := fun y => WithLp.toLp 2 (a y, d y) with hw
  have hwin : ∀ y (p : WithLp 2 (E × G)),
      inner ℂ (w y) p = inner ℂ (a y) p.fst + inner ℂ (d y) p.snd := by
    intro y p
    rw [WithLp.prod_inner_apply]
    rfl
  have hG : ∀ x y, inner ℂ (w x) (w y) = inner ℂ (b x) (b y) := by
    intro x y
    rw [hwin, ← hd]
    rfl
  set v : WithLp 2 (E × G) := WithLp.toLp 2 (e, 0) with hvdef
  set S : Submodule ℂ (WithLp 2 (E × G)) :=
    (Submodule.span ℂ (Set.range w)).topologicalClosure with hS
  have : CompleteSpace S := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  set e' := S.starProjection v with he'
  have hmem : e' ∈ closure (Set.range (Finsupp.linearCombination ℂ w :
      (Y →₀ ℂ) → WithLp 2 (E × G))) := by
    have h1 : e' ∈ S := S.starProjection_apply_mem v
    rw [hS, ← SetLike.mem_coe, Submodule.topologicalClosure_coe,
      ← Finsupp.range_linearCombination, LinearMap.coe_range] at h1
    exact h1
  obtain ⟨f, hf, hn⟩ := transfer w b hG e' hmem
  refine ⟨f, fun y => ?_, ?_⟩
  · have hy := hf y
    have hbS : w y ∈ S :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨y, rfl⟩)
    rw [he', ← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hbS, hwin] at hy
    rw [hy]
    simp [hvdef]
  · have h1 : ‖f‖ ≤ ‖v‖ := hn ▸ S.norm_starProjection_apply_le v
    have h2 : ‖v‖ ^ 2 = ‖e‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2]
      simp [hvdef]
    have h3 : ‖v‖ = ‖e‖ := (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
    linarith

/-- Contractive-inclusion criterion in feature-map form. -/
lemma dom (a : Y → E) (b : Y → F)
    (hab : ∀ c : Y →₀ ℂ, ‖Finsupp.linearCombination ℂ a c‖ ≤ ‖Finsupp.linearCombination ℂ b c‖)
    (e : E) : ∃ f : F, (∀ y, inner ℂ (b y) f = inner ℂ (a y) e) ∧ ‖f‖ ≤ ‖e‖ := by
  have hP := defect_psd a b hab
  haveI : Fact (opK fun x y => inner ℂ (b x) (b y) - inner ℂ (a x) (a y)).PosSemidef :=
    ⟨opK_posSemidef _ hP⟩
  refine dom_core a b
    (fun y => RKHS.kerFun (RKHS.OfKernel (opK fun x y => inner ℂ (b x) (b y) -
      inner ℂ (a x) (a y))) y (1 : ℂ)) (fun x y => ?_) e
  rw [gram, kernelFn_ofKernel _ hP]
  ring

end dom

section lim
variable {X : Type*} (E : ℕ → Set X) (H : ℕ → Type*)
  [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]
  [∀ n, RKHS ℂ (H n) (E n) ℂ]

open Classical in
/-- The feature map of `H n`, extended by zero outside `E n`. -/
noncomputable def kk (n : ℕ) (x : X) : H n :=
  if h : x ∈ E n then RKHS.kerFun (H n) (⟨x, h⟩ : E n) (1 : ℂ) else 0

variable {E H}

lemma kk_of_mem {n : ℕ} {x : X} (h : x ∈ E n) :
    kk E H n x = RKHS.kerFun (H n) (⟨x, h⟩ : E n) (1 : ℂ) := by
  simp [kk, h]

lemma kk_inner {n : ℕ} {x : X} (h : x ∈ E n) (f : H n) :
    inner ℂ (kk E H n x) f = f ⟨x, h⟩ := by
  rw [kk_of_mem h, eval_inner]

lemma kernel_eq {n : ℕ} {x y : X} (hx : x ∈ E n) (hy : y ∈ E n) :
    AronszajnRK.Sum.kernelFn (H n) ⟨x, hx⟩ ⟨y, hy⟩ = inner ℂ (kk E H n x) (kk E H n y) := by
  rw [kk_of_mem hx, kk_of_mem hy, gram]

variable (hS : AronszajnRK.Limits.IsDecreasingRKSequence E H)
include hS

lemma exists_index (s : Finset X) : ∃ N, ∀ x ∈ s, x ∈ E N := by
  have h : ∀ x : X, ∃ n, x ∈ E n := fun x => by
    have : x ∈ ⋃ n, E n := by rw [hS.iUnion_eq]; trivial
    exact Set.mem_iUnion.mp this
  choose nx hnx using h
  exact ⟨s.sup nx, fun x hx => hS.mono (Finset.le_sup hx) (hnx x)⟩

lemma norm_U_anti {m n : ℕ} (hmn : m ≤ n) (c : X →₀ ℂ) (hc : ∀ x ∈ c.support, x ∈ E m) :
    ‖Finsupp.linearCombination ℂ (kk E H n) c‖ ≤ ‖Finsupp.linearCombination ℂ (kk E H m) c‖ := by
  obtain ⟨v, hv⟩ := hS.restrict_mem hmn (Finsupp.linearCombination ℂ (kk E H n) c)
  have hvn := hS.norm_restrict_le hmn _ v hv
  have key : inner ℂ (Finsupp.linearCombination ℂ (kk E H n) c)
      (Finsupp.linearCombination ℂ (kk E H n) c) =
      inner ℂ (Finsupp.linearCombination ℂ (kk E H m) c) v := by
    rw [inner_lc_left, inner_lc_left]
    refine Finsupp.sum_congr fun x hx => ?_
    rw [kk_inner (hS.mono hmn (hc x hx)), kk_inner (hc x hx), hv x (hc x hx)]
  set u := Finsupp.linearCombination ℂ (kk E H n) c
  set A := Finsupp.linearCombination ℂ (kk E H m) c
  have h1 : ‖u‖ ^ 2 ≤ ‖A‖ * ‖u‖ := by
    have hn : ‖inner ℂ u u‖ = ‖u‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      simp
    calc ‖u‖ ^ 2 = ‖inner ℂ u u‖ := hn.symm
      _ = ‖inner ℂ A v‖ := by rw [key]
      _ ≤ ‖A‖ * ‖v‖ := norm_inner_le_norm _ _
      _ ≤ ‖A‖ * ‖u‖ := mul_le_mul_of_nonneg_left hvn (norm_nonneg _)
  by_contra hcon
  push Not at hcon
  nlinarith [norm_nonneg u, norm_nonneg A]

lemma tendsto_norm_U (N : ℕ) (c : X →₀ ℂ) (hc : ∀ x ∈ c.support, x ∈ E N) :
    ∃ l, Tendsto (fun n => ‖Finsupp.linearCombination ℂ (kk E H n) c‖) atTop (𝓝 l) := by
  have hanti : Antitone (fun j => ‖Finsupp.linearCombination ℂ (kk E H (j + N)) c‖) := by
    intro i j hij
    exact norm_U_anti hS (by omega) c (fun x hx => hS.mono (by omega : N ≤ i + N) (hc x hx))
  have hb : BddBelow (Set.range fun j => ‖Finsupp.linearCombination ℂ (kk E H (j + N)) c‖) :=
    ⟨0, by rintro _ ⟨j, rfl⟩; exact norm_nonneg _⟩
  exact ⟨_, (tendsto_add_atTop_iff_nat
    (f := fun n => ‖Finsupp.linearCombination ℂ (kk E H n) c‖) N).mp
    (tendsto_atTop_ciInf hanti hb)⟩

lemma tendsto_K (x y : X) :
    ∃ l, Tendsto (fun n => inner ℂ (kk E H n x) (kk E H n y)) atTop (𝓝 l) := by
  classical
  obtain ⟨N, hN⟩ := exists_index hS {x, y}
  have hx : x ∈ E N := hN x (by simp)
  have hy : y ∈ E N := hN y (by simp)
  have hconv : ∀ t : ℂ, ∃ l, Tendsto (fun n => ‖kk E H n x + t • kk E H n y‖) atTop (𝓝 l) := by
    intro t
    have hc : ∀ z ∈ (Finsupp.single x (1 : ℂ) + Finsupp.single y t).support, z ∈ E N := by
      intro z hz
      rcases Finset.mem_union.mp (Finsupp.support_add hz) with h | h
      · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)]; exact hx
      · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)]; exact hy
    obtain ⟨l, hl⟩ := tendsto_norm_U hS N _ hc
    refine ⟨l, hl.congr fun n => ?_⟩
    simp [Finsupp.linearCombination_single]
  obtain ⟨l1, h1⟩ := hconv 1
  obtain ⟨l2, h2⟩ := hconv (-1)
  obtain ⟨l3, h3⟩ := hconv (-RCLike.I)
  obtain ⟨l4, h4⟩ := hconv RCLike.I
  have c1 := (Complex.continuous_ofReal.tendsto _).comp h1
  have c2 := (Complex.continuous_ofReal.tendsto _).comp h2
  have c3 := (Complex.continuous_ofReal.tendsto _).comp h3
  have c4 := (Complex.continuous_ofReal.tendsto _).comp h4
  have T := ((((c1.pow 2).sub (c2.pow 2)).add
    (((c3.pow 2).sub (c4.pow 2)).mul_const (RCLike.I : ℂ))).div_const (4 : ℂ))
  refine ⟨_, T.congr fun n => ?_⟩
  rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (kk E H n x) (kk E H n y)]
  simp only [Function.comp_apply, one_smul, neg_smul, ← sub_eq_add_neg]
  rfl

/-- The limit kernel. -/
noncomputable def K0 (E : ℕ → Set X) (H : ℕ → Type*)
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]
    [∀ n, RKHS ℂ (H n) (E n) ℂ] (x y : X) : ℂ :=
  limUnder atTop (fun n => inner ℂ (kk E H n x) (kk E H n y))

lemma tendsto_K0 (x y : X) :
    Tendsto (fun n => inner ℂ (kk E H n x) (kk E H n y)) atTop (𝓝 (K0 E H x y)) := by
  obtain ⟨l, hl⟩ := tendsto_K hS x y
  exact tendsto_nhds_limUnder ⟨l, hl⟩

lemma K0_psd : (Matrix.of (K0 E H)).PosSemidef := by
  refine ⟨?_, fun v => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    have h2 := (tendsto_K0 hS j i).star
    have h3 : (fun n => star (inner ℂ (kk E H n j) (kk E H n i))) =
        fun n => inner ℂ (kk E H n i) (kk E H n j) := by
      funext n
      rw [← starRingEnd_apply, inner_conj_symm]
    rw [h3] at h2
    exact tendsto_nhds_unique h2 (tendsto_K0 hS i j)
  · have T : Tendsto (fun n => v.sum fun i xi => v.sum fun j xj =>
        star xi * inner ℂ (kk E H n i) (kk E H n j) * xj) atTop
        (𝓝 (v.sum fun i xi => v.sum fun j xj => star xi * K0 E H i j * xj)) := by
      simp only [Finsupp.sum]
      refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
      exact ((tendsto_K0 hS i j).const_mul _).mul_const _
    simp only [Matrix.of_apply]
    refine ge_of_tendsto' T fun n => ?_
    rw [dsum_gram, inner_self_eq_norm_sq_to_K]
    rw [← RCLike.ofReal_pow]
    exact RCLike.ofReal_nonneg.mpr (sq_nonneg _)

section h0
variable {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀] [CompleteSpace H₀]
  [RKHS ℂ H₀ X ℂ]

lemma tendsto_norm_U_k0 (hK : ∀ x y, AronszajnRK.Sum.kernelFn H₀ x y = K0 E H x y)
    (c : X →₀ ℂ) :
    Tendsto (fun n => ‖Finsupp.linearCombination ℂ (kk E H n) c‖) atTop
      (𝓝 ‖Finsupp.linearCombination ℂ (fun x => RKHS.kerFun H₀ x (1 : ℂ)) c‖) := by
  have T : Tendsto (fun n => inner ℂ (Finsupp.linearCombination ℂ (kk E H n) c)
      (Finsupp.linearCombination ℂ (kk E H n) c)) atTop
      (𝓝 (inner ℂ (Finsupp.linearCombination ℂ (fun x => RKHS.kerFun H₀ x (1 : ℂ)) c)
        (Finsupp.linearCombination ℂ (fun x => RKHS.kerFun H₀ x (1 : ℂ)) c))) := by
    simp only [← dsum_gram, Finsupp.sum]
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
    rw [gram, hK]
    exact ((tendsto_K0 hS i j).const_mul _).mul_const _
  have T1 := (RCLike.continuous_re.tendsto _).comp T
  simp only [Function.comp_def, inner_self_eq_norm_sq] at T1
  have T2 := T1.sqrt
  simpa only [Real.sqrt_sq (norm_nonneg _)] using T2

lemma norm_k0_le (hK : ∀ x y, AronszajnRK.Sum.kernelFn H₀ x y = K0 E H x y)
    (n : ℕ) (c : X →₀ ℂ) (hc : ∀ x ∈ c.support, x ∈ E n) :
    ‖Finsupp.linearCombination ℂ (fun x => RKHS.kerFun H₀ x (1 : ℂ)) c‖ ≤
      ‖Finsupp.linearCombination ℂ (kk E H n) c‖ := by
  have hanti : Antitone (fun j => ‖Finsupp.linearCombination ℂ (kk E H (n + j)) c‖) := by
    intro i j hij
    exact norm_U_anti hS (by omega) c (fun x hx => hS.mono (by omega : n ≤ n + i) (hc x hx))
  have T := (tendsto_norm_U_k0 hS hK c).comp (tendsto_atTop_mono (fun j => Nat.le_add_left j n) tendsto_id)
  exact hanti.le_of_tendsto T 0

lemma restrict_H₀ (hK : ∀ x y, AronszajnRK.Sum.kernelFn H₀ x y = K0 E H x y)
    (f₀ : H₀) (n : ℕ) : ∃ g : H n, (∀ x : E n, g x = f₀ x.1) ∧ ‖g‖ ≤ ‖f₀‖ := by
  classical
  have hab : ∀ c : E n →₀ ℂ,
      ‖Finsupp.linearCombination ℂ (fun y : E n => RKHS.kerFun H₀ y.1 (1 : ℂ)) c‖ ≤
      ‖Finsupp.linearCombination ℂ (fun y : E n => RKHS.kerFun (H n) y (1 : ℂ)) c‖ := by
    intro c
    have e1 : (fun y : E n => RKHS.kerFun H₀ y.1 (1 : ℂ)) =
        (fun x => RKHS.kerFun H₀ x (1 : ℂ)) ∘ Subtype.val := rfl
    have e2 : (fun y : E n => RKHS.kerFun (H n) y (1 : ℂ)) = kk E H n ∘ Subtype.val := by
      funext y
      simp only [Function.comp_apply, kk_of_mem y.2]
    rw [e1, e2, ← Finsupp.linearCombination_mapDomain, ← Finsupp.linearCombination_mapDomain]
    refine norm_k0_le hS hK n _ fun x hx => ?_
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hx)
    exact y.2
  obtain ⟨g, hg, hgn⟩ := dom _ _ hab f₀
  refine ⟨g, fun y => ?_, hgn⟩
  have := hg y
  rwa [eval_inner, eval_inner] at this

lemma criterion (φ : X → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (h : ∀ c : X →₀ ℂ, ‖c.sum fun x t => starRingEnd ℂ t * φ x‖ ≤
      L * ‖Finsupp.linearCombination ℂ (fun x => RKHS.kerFun H₀ x (1 : ℂ)) c‖) :
    ∃ f : H₀, ⇑f = φ ∧ ‖f‖ ≤ L := by
  have hab : ∀ c : X →₀ ℂ,
      ‖Finsupp.linearCombination ℂ (fun x => starRingEnd ℂ (φ x)) c‖ ≤
      ‖Finsupp.linearCombination ℂ (fun x => (L : ℂ) • RKHS.kerFun H₀ x (1 : ℂ)) c‖ := by
    intro c
    have e1 : Finsupp.linearCombination ℂ (fun x => starRingEnd ℂ (φ x)) c =
        starRingEnd ℂ (c.sum fun x t => starRingEnd ℂ t * φ x) := by
      rw [Finsupp.linearCombination_apply, map_finsuppSum]
      refine Finsupp.sum_congr fun x _ => ?_
      simp [smul_eq_mul]
    have e2 : Finsupp.linearCombination ℂ (fun x => (L : ℂ) • RKHS.kerFun H₀ x (1 : ℂ)) c =
        (L : ℂ) • Finsupp.linearCombination ℂ (fun x => RKHS.kerFun H₀ x (1 : ℂ)) c := by
      simp only [Finsupp.linearCombination_apply, Finsupp.smul_sum]
      exact Finsupp.sum_congr fun x _ => smul_comm _ _ _
    rw [e1, e2, RCLike.norm_conj, norm_smul, Complex.norm_real, Real.norm_of_nonneg hL]
    exact h c
  obtain ⟨f₁, hf₁, hn₁⟩ := dom _ _ hab (1 : ℂ)
  refine ⟨(L : ℂ) • f₁, ?_, ?_⟩
  · funext y
    have := hf₁ y
    rw [inner_smul_left, eval_inner, Complex.conj_ofReal] at this
    rw [RKHS.coe_smul, Pi.smul_apply, smul_eq_mul, this]
    simp [RCLike.inner_apply]
  · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hL]
    have : ‖f₁‖ ≤ 1 := by simpa using hn₁
    nlinarith [norm_nonneg f₁]

lemma g_mono (f₀ : X → ℂ) (g : ∀ n, H n) (hg : ∀ (n : ℕ) (x : E n), g n x = f₀ x.1) :
    Monotone (fun n => ‖g n‖) := by
  intro m n hmn
  exact hS.norm_restrict_le hmn (g n) (g m) (fun x hm hn => by
    rw [hg m ⟨x, hm⟩, hg n ⟨x, hn⟩])

lemma mem_of_limit (hK : ∀ x y, AronszajnRK.Sum.kernelFn H₀ x y = K0 E H x y)
    (f₀ : X → ℂ) (g : ∀ n, H n) (hg : ∀ (n : ℕ) (x : E n), g n x = f₀ x.1) (L : ℝ)
    (hL : Tendsto (fun n => ‖g n‖) atTop (𝓝 L)) :
    ∃ f : H₀, ⇑f = f₀ ∧ ‖f‖ ≤ L := by
  have hmono := g_mono hS f₀ g hg
  have hle : ∀ n, ‖g n‖ ≤ L := fun n => hmono.ge_of_tendsto hL n
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hle 0)
  refine criterion hS f₀ L hL0 fun c => ?_
  obtain ⟨N, hN⟩ := exists_index hS c.support
  have T := (tendsto_norm_U_k0 hS hK c).mul_const L
  have hev : ∀ᶠ n in atTop, ‖c.sum fun x t => starRingEnd ℂ t * f₀ x‖ ≤
      ‖Finsupp.linearCombination ℂ (kk E H n) c‖ * L := by
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have hcn : ∀ x ∈ c.support, x ∈ E n := fun x hx => hS.mono hn (hN x hx)
    have e : (c.sum fun x t => starRingEnd ℂ t * f₀ x) =
        inner ℂ (Finsupp.linearCombination ℂ (kk E H n) c) (g n) := by
      rw [inner_lc_left]
      refine Finsupp.sum_congr fun x hx => ?_
      rw [kk_inner (hcn x hx), hg n ⟨x, hcn x hx⟩]
    rw [e]
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hle n) (norm_nonneg _))
  have := ge_of_tendsto T hev
  linarith [mul_comm L ‖Finsupp.linearCombination ℂ (fun x => RKHS.kerFun H₀ x (1 : ℂ)) c‖]

end h0

end lim

end AronszajnLimAux

open Filter Topology AronszajnRK.Limits in
theorem solution {X : Type u} (E : ℕ → Set X) (H : ℕ → Type v)
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]
    [∀ n, RKHS ℂ (H n) (E n) ℂ] (hS : IsDecreasingRKSequence E H) :
    ∃ K₀ : X → X → ℂ,
      (∀ (x y : X) (N : ℕ) (hx : x ∈ E N) (hy : y ∈ E N),
        Tendsto (fun j : ℕ => AronszajnRK.Sum.kernelFn (H (N + j)) ⟨x, hS.mono (Nat.le_add_right N j) hx⟩
          ⟨y, hS.mono (Nat.le_add_right N j) hy⟩) atTop (𝓝 (K₀ x y))) ∧
      (∃ (H₀ : Type u) (_ : NormedAddCommGroup H₀) (_ : InnerProductSpace ℂ H₀)
          (_ : CompleteSpace H₀) (_ : RKHS ℂ H₀ X ℂ), ∀ x y : X, AronszajnRK.Sum.kernelFn H₀ x y = K₀ x y) ∧
      ∀ (H₀ : Type w) [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀] [CompleteSpace H₀]
        [RKHS ℂ H₀ X ℂ], (∀ x y : X, AronszajnRK.Sum.kernelFn H₀ x y = K₀ x y) →
        Set.range (fun f : H₀ => (⇑f : X → ℂ)) = limitClass E H ∧
        ∀ (f₀ : H₀) (g : ∀ n, H n), (∀ (n : ℕ) (x : E n), g n x = f₀ x.1) →
          Tendsto (fun n => ‖g n‖) atTop (𝓝 ‖f₀‖) := by
  refine ⟨AronszajnLimAux.K0 E H, ?_, ?_, ?_⟩
  · intro x y N hx hy
    have e : (fun j : ℕ => AronszajnRK.Sum.kernelFn (H (N + j))
        ⟨x, hS.mono (Nat.le_add_right N j) hx⟩ ⟨y, hS.mono (Nat.le_add_right N j) hy⟩) =
        fun j => (fun n => inner ℂ (AronszajnLimAux.kk E H n x) (AronszajnLimAux.kk E H n y))
          (N + j) := by
      funext j
      exact AronszajnLimAux.kernel_eq _ _
    rw [e]
    exact (AronszajnLimAux.tendsto_K0 hS x y).comp
      (tendsto_atTop_mono (fun j => Nat.le_add_left j N) tendsto_id)
  · have hP := AronszajnLimAux.K0_psd hS
    haveI : Fact (AronszajnLimAux.opK (AronszajnLimAux.K0 E H)).PosSemidef :=
      ⟨AronszajnLimAux.opK_posSemidef _ hP⟩
    exact ⟨RKHS.OfKernel (AronszajnLimAux.opK (AronszajnLimAux.K0 E H)), inferInstance,
      inferInstance, inferInstance, inferInstance, AronszajnLimAux.kernelFn_ofKernel _ hP⟩
  · intro H₀ _ _ _ _ hK
    -- every `g` with the restricted functions is bounded by `‖f₀‖`
    have hbound : ∀ (f₀ : H₀) (g : ∀ n, H n), (∀ (n : ℕ) (x : E n), g n x = f₀ x.1) →
        ∀ n, ‖g n‖ ≤ ‖f₀‖ := by
      intro f₀ g hg n
      obtain ⟨g', hg', hn'⟩ := AronszajnLimAux.restrict_H₀ hS hK f₀ n
      have : g n = g' := DFunLike.coe_injective (funext fun x => (hg n x).trans (hg' x).symm)
      rw [this]
      exact hn'
    have hlim : ∀ (f₀ : H₀) (g : ∀ n, H n), (∀ (n : ℕ) (x : E n), g n x = f₀ x.1) →
        Tendsto (fun n => ‖g n‖) atTop (𝓝 (⨆ n, ‖g n‖)) := by
      intro f₀ g hg
      exact tendsto_atTop_ciSup (AronszajnLimAux.g_mono hS (⇑f₀) g hg)
        ⟨‖f₀‖, by rintro _ ⟨n, rfl⟩; exact hbound f₀ g hg n⟩
    refine ⟨?_, ?_⟩
    · ext φ
      constructor
      · rintro ⟨f₀, rfl⟩
        choose g hg _ using fun n => AronszajnLimAux.restrict_H₀ hS hK f₀ n
        exact ⟨g, hg, _, hlim f₀ g hg⟩
      · rintro ⟨g, hg, L, hL⟩
        obtain ⟨f, hf, -⟩ := AronszajnLimAux.mem_of_limit hS hK φ g hg L hL
        exact ⟨f, hf⟩
    · intro f₀ g hg
      have T := hlim f₀ g hg
      have h1 : (⨆ n, ‖g n‖) ≤ ‖f₀‖ := ciSup_le (hbound f₀ g hg)
      obtain ⟨f, hf, hfn⟩ := AronszajnLimAux.mem_of_limit hS hK (⇑f₀) g hg _ T
      have : f = f₀ := DFunLike.coe_injective hf
      rw [this] at hfn
      have h2 : (⨆ n, ‖g n‖) = ‖f₀‖ := le_antisymm h1 hfn
      rwa [h2] at T
