-- Prove2me | solution 1 for AronszajnRK.Limits.limit_kernel_norm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:45:07.894604+00:00
-- url     : https://prove2.me/submissions/ed781f39-3c3f-44c8-9d94-fca8043e57c9

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn
import Definitions.Def_AronszajnRK_Limits_IsDecreasingRKSequence

set_option autoImplicit false

namespace Aux5aca

open scoped InnerProductSpace

lemma kerFun_inner_one {Y : Type*} {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] [RKHS ℂ G Y ℂ] (x : Y) (f : G) :
    ⟪RKHS.kerFun G x 1, f⟫_ℂ = f x := by
  rw [RKHS.kerFun_inner]; simp

lemma kv_apply {Y : Type*} (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] [RKHS ℂ G Y ℂ] (y x : Y) :
    RKHS.kerFun G y (1 : ℂ) x = AronszajnRK.Sum.kernelFn G x y := by
  rw [RKHS.kerFun_apply]; rfl

lemma diag_eq {Y : Type*} (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] [RKHS ℂ G Y ℂ] (x : Y) :
    AronszajnRK.Sum.kernelFn G x x = ((‖RKHS.kerFun G x (1 : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : AronszajnRK.Sum.kernelFn G x x = ⟪RKHS.kerFun G x 1, RKHS.kerFun G x 1⟫_ℂ := by
    rw [kerFun_inner_one, RKHS.kerFun_apply]
    rfl
  rw [h1]
  exact_mod_cast inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (RKHS.kerFun G x (1 : ℂ))

lemma diag_le {X : Type*} (E : ℕ → Set X) (H : ℕ → Type*)
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]
    [∀ n, RKHS ℂ (H n) (E n) ℂ] (hS : AronszajnRK.Limits.IsDecreasingRKSequence E H)
    {m n : ℕ} (hmn : m ≤ n) (y : X) (hm : y ∈ E m) (hn : y ∈ E n) :
    ‖RKHS.kerFun (H n) (⟨y, hn⟩ : E n) (1 : ℂ)‖ ≤ ‖RKHS.kerFun (H m) (⟨y, hm⟩ : E m) (1 : ℂ)‖ := by
  obtain ⟨v, hv⟩ : ∃ w : H n, w = RKHS.kerFun (H n) (⟨y, hn⟩ : E n) (1 : ℂ) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ w : H m, w = RKHS.kerFun (H m) (⟨y, hm⟩ : E m) (1 : ℂ) := ⟨_, rfl⟩
  rw [← hv, ← hu]
  obtain ⟨g, hg⟩ := hS.restrict_mem hmn v
  have hgv : ‖g‖ ≤ ‖v‖ := hS.norm_restrict_le hmn v g hg
  have hvv : ⟪v, v⟫_ℂ = ⟪u, g⟫_ℂ := by
    nth_rewrite 1 [hv]
    rw [hu, kerFun_inner_one, kerFun_inner_one, hg y hm hn]
  have hv2 : ⟪v, v⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast inner_self_eq_norm_sq_to_K (𝕜 := ℂ) v
  have h1 : ‖v‖ ^ 2 ≤ ‖u‖ * ‖v‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) u g
    rw [← hvv, hv2, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h
    nlinarith [norm_nonneg u]
  nlinarith [norm_nonneg u, norm_nonneg v, sq_nonneg (‖v‖ - ‖u‖)]

/-- Aronszajn's Eq. (5), in `ℝ`. -/
lemma eq5 {X : Type*} (E : ℕ → Set X) (H : ℕ → Type*)
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]
    [∀ n, RKHS ℂ (H n) (E n) ℂ] (hS : AronszajnRK.Limits.IsDecreasingRKSequence E H)
    {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) (y : X) (hym : y ∈ E m) (hyn : y ∈ E n)
    (a b : H k)
    (ha : ∀ (x : X) (hk : x ∈ E k) (hm : x ∈ E m),
      a ⟨x, hk⟩ = AronszajnRK.Sum.kernelFn (H m) ⟨x, hm⟩ ⟨y, hym⟩)
    (hb : ∀ (x : X) (hk : x ∈ E k) (hn : x ∈ E n),
      b ⟨x, hk⟩ = AronszajnRK.Sum.kernelFn (H n) ⟨x, hn⟩ ⟨y, hyn⟩) :
    ‖a - b‖ ^ 2 ≤ ‖RKHS.kerFun (H m) (⟨y, hym⟩ : E m) (1 : ℂ)‖ ^ 2
      - ‖RKHS.kerFun (H n) (⟨y, hyn⟩ : E n) (1 : ℂ)‖ ^ 2 := by
  obtain ⟨u, hu⟩ : ∃ w : H m, w = RKHS.kerFun (H m) (⟨y, hym⟩ : E m) (1 : ℂ) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ w : H n, w = RKHS.kerFun (H n) (⟨y, hyn⟩ : E n) (1 : ℂ) := ⟨_, rfl⟩
  rw [← hu, ← hv]
  obtain ⟨g, hg⟩ := hS.restrict_mem hmn v
  have h1 : ‖a - b‖ ≤ ‖u - g‖ := by
    refine hS.norm_restrict_le hkm (u - g) (a - b) (fun x hk hm => ?_)
    have hn : x ∈ E n := hS.mono hmn hm
    rw [RKHS.coe_sub, RKHS.coe_sub, Pi.sub_apply, Pi.sub_apply, ha x hk hm, hb x hk hn,
      hg x hm hn, hu, hv, kv_apply, kv_apply]
  have h2 : ‖g‖ ≤ ‖v‖ := hS.norm_restrict_le hmn v g hg
  have hvv : ⟪v, v⟫_ℂ = v ⟨y, hyn⟩ := by
    nth_rewrite 1 [hv]
    exact kerFun_inner_one _ _
  have h3 : ⟪u, g⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [hu, kerFun_inner_one, hg y hym hyn, ← hvv]
    exact_mod_cast inner_self_eq_norm_sq_to_K (𝕜 := ℂ) v
  have h4 : RCLike.re ⟪u, g⟫_ℂ = ‖v‖ ^ 2 := by
    rw [h3, RCLike.re_to_complex, Complex.ofReal_re]
  have hsq := norm_sub_sq (𝕜 := ℂ) u g
  rw [h4] at hsq
  nlinarith [pow_le_pow_left₀ (norm_nonneg _) h1 2, pow_le_pow_left₀ (norm_nonneg _) h2 2]

end Aux5aca

open AronszajnRK.Limits Filter Topology ComplexOrder in
theorem solution {X : Type*} (E : ℕ → Set X) (H : ℕ → Type*)
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]
    [∀ n, RKHS ℂ (H n) (E n) ℂ] (hS : IsDecreasingRKSequence E H) (K₀ : X → X → ℂ)
    (hK₀ : ∀ (x y : X) (N : ℕ) (hx : x ∈ E N) (hy : y ∈ E N),
      Tendsto (fun j : ℕ => AronszajnRK.Sum.kernelFn (H (N + j)) ⟨x, hS.mono (Nat.le_add_right N j) hx⟩
        ⟨y, hS.mono (Nat.le_add_right N j) hy⟩) atTop (𝓝 (K₀ x y)))
    {k m : ℕ} (hkm : k ≤ m) (y : X) (hy : y ∈ E k) :
    (∃ c : H k, ∀ x : E k, c x = K₀ x.1 y) ∧
      ∀ a c : H k,
        (∀ x : E k, a x = AronszajnRK.Sum.kernelFn (H m) (Set.inclusion (hS.mono hkm) x) ⟨y, hS.mono hkm hy⟩) →
        (∀ x : E k, c x = K₀ x.1 y) →
        ((‖a - c‖ ^ 2 : ℝ) : ℂ) ≤ AronszajnRK.Sum.kernelFn (H m) ⟨y, hS.mono hkm hy⟩ ⟨y, hS.mono hkm hy⟩ - K₀ y y := by
  set d : ℕ → ℝ := fun j => ‖RKHS.kerFun (H (k + j))
    (⟨y, hS.mono (Nat.le_add_right k j) hy⟩ : E (k + j)) (1 : ℂ)‖ ^ 2 with hd_def
  have hanti : Antitone d := by
    apply antitone_nat_of_succ_le
    intro j
    simp only [hd_def]
    exact pow_le_pow_left₀ (norm_nonneg _) (Aux5aca.diag_le E H hS (by omega) y _ _) 2
  have hbdd : BddBelow (Set.range d) := ⟨0, by rintro _ ⟨j, rfl⟩; exact sq_nonneg _⟩
  have hd : Tendsto d atTop (𝓝 (⨅ j, d j)) := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ j, d j with hL_def
  have hdL : ∀ j, L ≤ d j := fun j => ciInf_le hbdd j
  have hL : K₀ y y = (L : ℂ) := by
    refine tendsto_nhds_unique (hK₀ y y k hy hy) ?_
    have := (Complex.continuous_ofReal.tendsto L).comp hd
    refine this.congr (fun j => ?_)
    simp only [Function.comp_apply, hd_def]
    rw [Aux5aca.diag_eq]
  have hex : ∀ j, ∃ g : H k, ∀ (x : X) (hk : x ∈ E k) (hn : x ∈ E (k + j)),
      g ⟨x, hk⟩ = AronszajnRK.Sum.kernelFn (H (k + j)) ⟨x, hn⟩
        ⟨y, hS.mono (Nat.le_add_right k j) hy⟩ := by
    intro j
    obtain ⟨g, hg⟩ := hS.restrict_mem (Nat.le_add_right k j)
      (RKHS.kerFun (H (k + j)) (⟨y, hS.mono (Nat.le_add_right k j) hy⟩ : E (k + j)) (1 : ℂ))
    exact ⟨g, fun x hk hn => by rw [hg x hk hn, Aux5aca.kv_apply]⟩
  choose r hr using hex
  have hrr : ∀ i j, i ≤ j → ‖r i - r j‖ ^ 2 ≤ d i - d j := fun i j hij =>
    Aux5aca.eq5 E H hS (Nat.le_add_right k i) (by omega) y _ _ (r i) (r j) (hr i) (hr j)
  have hcauchy : CauchySeq r := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := ((tendsto_order.1 hd).2 (L + ε ^ 2)
      (by linarith [sq_pos_of_pos hε])).exists_forall_of_atTop
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm, norm_sub_rev]
    have h1 := hrr N n hn
    have h2 := hN N le_rfl
    have h3 := hdL n
    have h4 : ‖r N - r n‖ ^ 2 < ε ^ 2 := by linarith
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith [pow_le_pow_left₀ hε.le hcon 2]
  obtain ⟨c₀, hc₀⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hc₀x : ∀ x : E k, c₀ x = K₀ x.1 y := by
    intro x
    have t1 : Tendsto (fun j => r j x) atTop (𝓝 (c₀ x)) :=
      ((RKHS.continuous_eval (H := H k) x).tendsto c₀).comp hc₀
    have t2 : Tendsto (fun j => r j x) atTop (𝓝 (K₀ x.1 y)) := by
      refine (hK₀ x.1 y k x.2 hy).congr (fun j => ?_)
      exact (hr j x.1 x.2 _).symm
    exact tendsto_nhds_unique t1 t2
  refine ⟨⟨c₀, hc₀x⟩, fun a c ha hc => ?_⟩
  have hcc : c = c₀ := RKHS.ext (fun x => by rw [hc x, hc₀x x])
  rw [hcc]
  have hym : y ∈ E m := hS.mono hkm hy
  have hlim : Tendsto (fun j => ‖a - r j‖ ^ 2) atTop (𝓝 (‖a - c₀‖ ^ 2)) :=
    ((tendsto_const_nhds.sub hc₀).norm).pow 2
  have hev : ∀ᶠ j in atTop,
      ‖a - r j‖ ^ 2 ≤ ‖RKHS.kerFun (H m) (⟨y, hym⟩ : E m) (1 : ℂ)‖ ^ 2 - d j := by
    refine Filter.eventually_atTop.2 ⟨m, fun j hj => ?_⟩
    exact Aux5aca.eq5 E H hS hkm (by omega) y hym _ a (r j) (fun x hk _ => ha ⟨x, hk⟩) (hr j)
  have hle := le_of_tendsto_of_tendsto hlim (tendsto_const_nhds.sub hd) hev
  rw [Aux5aca.diag_eq, hL, ← Complex.ofReal_sub, Complex.real_le_real]
  exact hle
