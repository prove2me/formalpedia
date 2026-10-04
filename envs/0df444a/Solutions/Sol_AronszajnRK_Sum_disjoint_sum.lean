-- Prove2me | solution 1 for AronszajnRK.Sum.disjoint_sum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T10:21:49.467211+00:00
-- url     : https://prove2.me/submissions/01cc4145-3cf9-4be5-bd59-673a40455131

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn

set_option autoImplicit false

universe u w

namespace AronszajnDisjAux

open RKHS Filter Topology

section transfer
variable {X : Type*} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

lemma inner_lc_right (a : X → E) (y : E) (d : X →₀ ℂ) :
    inner ℂ y (Finsupp.linearCombination ℂ a d) = d.sum fun x t => t * inner ℂ y (a x) := by
  simp only [Finsupp.linearCombination_apply, Finsupp.inner_sum, inner_smul_right]

lemma inner_lc_self (a : X → E) (c : X →₀ ℂ) :
    inner ℂ (Finsupp.linearCombination ℂ a c) (Finsupp.linearCombination ℂ a c) =
      c.sum fun i s => s * c.sum fun j t => (starRingEnd ℂ) t * inner ℂ (a j) (a i) := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum_inner, Finsupp.inner_sum,
    inner_smul_left, inner_smul_right]

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

lemma dense_lc (f : H) : f ∈ closure (Set.range
    (Finsupp.linearCombination ℂ (fun x : X => RKHS.kerFun H x (1 : ℂ)) : (X →₀ ℂ) → H)) := by
  have h1 : Submodule.span ℂ {RKHS.kerFun H x v | (x : X) (v : ℂ)} ≤
      LinearMap.range (Finsupp.linearCombination ℂ (fun x : X => RKHS.kerFun H x (1 : ℂ))) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, v, rfl⟩
    refine ⟨Finsupp.single x v, ?_⟩
    simp only [Finsupp.linearCombination_single]
    rw [← map_smul, smul_eq_mul, mul_one]
  have h2 := RKHS.kerFun_dense (𝕜 := ℂ) (X := X) (V := ℂ) H
  have h3 : (LinearMap.range (Finsupp.linearCombination ℂ
      (fun x : X => RKHS.kerFun H x (1 : ℂ)))).topologicalClosure = ⊤ :=
    top_le_iff.mp (h2 ▸ Submodule.topologicalClosure_mono h1)
  have h4 : f ∈ (LinearMap.range (Finsupp.linearCombination ℂ
      (fun x : X => RKHS.kerFun H x (1 : ℂ)))).topologicalClosure := by rw [h3]; trivial
  have h5 : f ∈ closure ((LinearMap.range (Finsupp.linearCombination ℂ
      (fun x : X => RKHS.kerFun H x (1 : ℂ))) : Set H)) := by
    rw [← Submodule.topologicalClosure_coe]; exact h4
  rwa [LinearMap.coe_range] at h5

end rk

section sum
set_option linter.unusedSectionVars false
variable {X : Type*}
  {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [RKHS ℂ H₁ X ℂ]
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  [RKHS ℂ H₂ X ℂ]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [RKHS ℂ H X ℂ]

/-- The feature map into the `L²` product. -/
noncomputable def bfeat (H₁ H₂ : Type*) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [CompleteSpace H₁] [RKHS ℂ H₁ X ℂ] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    [CompleteSpace H₂] [RKHS ℂ H₂ X ℂ] (x : X) : WithLp 2 (H₁ × H₂) :=
  WithLp.toLp 2 (RKHS.kerFun H₁ x (1 : ℂ), RKHS.kerFun H₂ x (1 : ℂ))

lemma bfeat_inner (y : X) (v : WithLp 2 (H₁ × H₂)) :
    inner ℂ (bfeat H₁ H₂ y) v = v.fst y + v.snd y := by
  rw [WithLp.prod_inner_apply]
  exact congrArg₂ (· + ·) (eval_inner H₁ y _) (eval_inner H₂ y _)

lemma gram_sum (hK : AronszajnRK.Sum.kernelFn H =
      AronszajnRK.Sum.kernelFn H₁ + AronszajnRK.Sum.kernelFn H₂) (x y : X) :
    inner ℂ (RKHS.kerFun H x (1 : ℂ)) (RKHS.kerFun H y (1 : ℂ)) =
      inner ℂ (bfeat H₁ H₂ x) (bfeat H₁ H₂ y) := by
  rw [gram, hK, bfeat_inner]
  show _ = (RKHS.kerFun H₁ y (1 : ℂ)) x + (RKHS.kerFun H₂ y (1 : ℂ)) x
  rw [← eval_inner H₁ x, ← eval_inner H₂ x, gram, gram]
  rfl

lemma partA (hK : AronszajnRK.Sum.kernelFn H =
      AronszajnRK.Sum.kernelFn H₁ + AronszajnRK.Sum.kernelFn H₂) (f : H) :
    ∃ (f₁ : H₁) (f₂ : H₂), (f : X → ℂ) = (f₁ : X → ℂ) + (f₂ : X → ℂ) ∧
      ‖f‖ ^ 2 = ‖f₁‖ ^ 2 + ‖f₂‖ ^ 2 := by
  obtain ⟨v, hv, hn⟩ := transfer (fun x : X => RKHS.kerFun H x (1 : ℂ)) (bfeat H₁ H₂)
    (gram_sum hK) f (dense_lc H f)
  refine ⟨v.fst, v.snd, ?_, ?_⟩
  · funext y
    have := hv y
    rw [bfeat_inner, eval_inner] at this
    rw [Pi.add_apply, this]
  · rw [← hn, WithLp.prod_norm_sq_eq_of_L2]

lemma partB (hK : AronszajnRK.Sum.kernelFn H =
      AronszajnRK.Sum.kernelFn H₁ + AronszajnRK.Sum.kernelFn H₂) (f₁ : H₁) (f₂ : H₂) :
    ∃ f : H, (f : X → ℂ) = (f₁ : X → ℂ) + (f₂ : X → ℂ) ∧
      ‖f‖ ^ 2 ≤ ‖f₁‖ ^ 2 + ‖f₂‖ ^ 2 := by
  set v : WithLp 2 (H₁ × H₂) := WithLp.toLp 2 (f₁, f₂) with hvdef
  set S : Submodule ℂ (WithLp 2 (H₁ × H₂)) :=
    (Submodule.span ℂ (Set.range (bfeat H₁ H₂ (X := X)))).topologicalClosure with hS
  have : CompleteSpace S := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  set e := S.starProjection v with he
  have hmem : e ∈ closure (Set.range (Finsupp.linearCombination ℂ (bfeat H₁ H₂ (X := X)) :
      (X →₀ ℂ) → WithLp 2 (H₁ × H₂))) := by
    have h1 : e ∈ S := S.starProjection_apply_mem v
    rw [hS, ← SetLike.mem_coe, Submodule.topologicalClosure_coe,
      ← Finsupp.range_linearCombination, LinearMap.coe_range] at h1
    exact h1
  obtain ⟨f, hf, hn⟩ := transfer (bfeat H₁ H₂) (fun x : X => RKHS.kerFun H x (1 : ℂ))
    (fun x y => (gram_sum hK x y).symm) e hmem
  refine ⟨f, ?_, ?_⟩
  · funext y
    have hy := hf y
    have hbS : bfeat H₁ H₂ y ∈ S :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨y, rfl⟩)
    rw [eval_inner, he, ← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hbS, bfeat_inner] at hy
    rw [Pi.add_apply, hy]
    rfl
  · have h1 : ‖f‖ ≤ ‖v‖ := hn ▸ S.norm_starProjection_apply_le v
    have h2 : ‖v‖ ^ 2 = ‖f₁‖ ^ 2 + ‖f₂‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2]
      rfl
    rw [← h2]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2


lemma common_zero
    (hdisj : Set.range (fun f : H₁ => (f : X → ℂ)) ∩ Set.range (fun f : H₂ => (f : X → ℂ)) = {0})
    (a : H₁) (b : H₂) (h : (a : X → ℂ) = (b : X → ℂ)) : a = 0 ∧ b = 0 := by
  have hm : (a : X → ℂ) ∈ Set.range (fun f : H₁ => (f : X → ℂ)) ∩
      Set.range (fun f : H₂ => (f : X → ℂ)) := ⟨⟨a, rfl⟩, ⟨b, h.symm⟩⟩
  rw [hdisj, Set.mem_singleton_iff] at hm
  refine ⟨DFunLike.coe_injective (hm.trans RKHS.coe_zero.symm), ?_⟩
  exact DFunLike.coe_injective ((h.symm.trans hm).trans RKHS.coe_zero.symm)

lemma part1 (hK : AronszajnRK.Sum.kernelFn H =
      AronszajnRK.Sum.kernelFn H₁ + AronszajnRK.Sum.kernelFn H₂)
    (hdisj : Set.range (fun f : H₁ => (f : X → ℂ)) ∩ Set.range (fun f : H₂ => (f : X → ℂ)) = {0})
    (f : H) (f₁ : H₁) (f₂ : H₂) (h : (f : X → ℂ) = (f₁ : X → ℂ) + (f₂ : X → ℂ)) :
    ‖f‖ ^ 2 = ‖f₁‖ ^ 2 + ‖f₂‖ ^ 2 := by
  obtain ⟨g₁, g₂, hg, hn⟩ := partA hK f
  have he : ((f₁ - g₁ : H₁) : X → ℂ) = ((g₂ - f₂ : H₂) : X → ℂ) := by
    rw [RKHS.coe_sub, RKHS.coe_sub]
    funext x
    have := congrFun (h.symm.trans hg) x
    simp only [Pi.add_apply] at this
    simp only [Pi.sub_apply]
    linear_combination this
  obtain ⟨h1, h2⟩ := common_zero hdisj _ _ he
  rw [sub_eq_zero] at h1 h2
  rw [h1, ← h2]
  exact hn

lemma emb₁ (hK : AronszajnRK.Sum.kernelFn H =
      AronszajnRK.Sum.kernelFn H₁ + AronszajnRK.Sum.kernelFn H₂)
    (hdisj : Set.range (fun f : H₁ => (f : X → ℂ)) ∩ Set.range (fun f : H₂ => (f : X → ℂ)) = {0})
    (f₁ : H₁) : ∃ f : H, (f : X → ℂ) = (f₁ : X → ℂ) ∧ ‖f‖ = ‖f₁‖ := by
  obtain ⟨f, hf, -⟩ := partB hK f₁ (0 : H₂)
  have hf' : (f : X → ℂ) = (f₁ : X → ℂ) := by rw [hf, RKHS.coe_zero, add_zero]
  refine ⟨f, hf', ?_⟩
  have h := part1 hK hdisj f f₁ 0 hf
  rw [norm_zero] at h
  have h' : ‖f‖ ^ 2 = ‖f₁‖ ^ 2 := by rw [h]; ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h'

lemma emb₂ (hK : AronszajnRK.Sum.kernelFn H =
      AronszajnRK.Sum.kernelFn H₁ + AronszajnRK.Sum.kernelFn H₂)
    (hdisj : Set.range (fun f : H₁ => (f : X → ℂ)) ∩ Set.range (fun f : H₂ => (f : X → ℂ)) = {0})
    (f₂ : H₂) : ∃ f : H, (f : X → ℂ) = (f₂ : X → ℂ) ∧ ‖f‖ = ‖f₂‖ := by
  obtain ⟨f, hf, -⟩ := partB hK (0 : H₁) f₂
  have hf' : (f : X → ℂ) = (f₂ : X → ℂ) := by rw [hf, RKHS.coe_zero, zero_add]
  refine ⟨f, hf', ?_⟩
  have h := part1 hK hdisj f 0 f₂ hf
  rw [norm_zero] at h
  have h' : ‖f‖ ^ 2 = ‖f₂‖ ^ 2 := by rw [h]; ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h'

end sum

/-- Functions of `H` that are functions of `G`. -/
def rangeSub {X : Type*} (H G : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H X ℂ] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] [RKHS ℂ G X ℂ] : Submodule ℂ H where
  carrier := {f | ∃ g : G, (f : X → ℂ) = (g : X → ℂ)}
  add_mem' := by
    rintro a b ⟨ga, ha⟩ ⟨gb, hb⟩
    exact ⟨ga + gb, by rw [RKHS.coe_add, RKHS.coe_add, ha, hb]⟩
  zero_mem' := ⟨0, by rw [RKHS.coe_zero, RKHS.coe_zero]⟩
  smul_mem' := by
    rintro c a ⟨ga, ha⟩
    exact ⟨c • ga, by rw [RKHS.coe_smul, RKHS.coe_smul, ha]⟩

lemma mem_rangeSub {X : Type*} {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H X ℂ] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] [RKHS ℂ G X ℂ] (f : H) :
    f ∈ rangeSub (X := X) H G ↔ ∃ g : G, (f : X → ℂ) = (g : X → ℂ) := Iff.rfl

/-- If every function of `G` lies in `H` with the same norm, the functions of `G` form a closed
subset of `H`. -/
lemma rangeSub_closed {X : Type*} {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H X ℂ] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] [RKHS ℂ G X ℂ]
    (emb : ∀ g : G, ∃ f : H, (f : X → ℂ) = (g : X → ℂ) ∧ ‖f‖ = ‖g‖) :
    IsClosed ((rangeSub (X := X) H G : Submodule ℂ H) : Set H) := by
  choose ι hι hιn using emb
  have hiso : Isometry ι := by
    refine Isometry.of_dist_eq fun a b => ?_
    have hsub : ι a - ι b = ι (a - b) := DFunLike.coe_injective (by
      rw [RKHS.coe_sub, hι, hι, hι, RKHS.coe_sub])
    rw [dist_eq_norm, dist_eq_norm, hsub, hιn]
  have hset : ((rangeSub (X := X) H G : Submodule ℂ H) : Set H) = Set.range ι := by
    ext f
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g, DFunLike.coe_injective ((hι g).trans hg.symm)⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, hι g⟩
  rw [hset]
  exact hiso.isUniformInducing.isComplete_range.isClosed

lemma orth {X : Type*}
    {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [RKHS ℂ H₁ X ℂ]
    {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    [RKHS ℂ H₂ X ℂ]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [RKHS ℂ H X ℂ] (hK : AronszajnRK.Sum.kernelFn H =
      AronszajnRK.Sum.kernelFn H₁ + AronszajnRK.Sum.kernelFn H₂)
    (hdisj : Set.range (fun f : H₁ => (f : X → ℂ)) ∩ Set.range (fun f : H₂ => (f : X → ℂ)) = {0})
    (g h : H) (hg : g ∈ rangeSub (X := X) H H₁) (hh : h ∈ rangeSub (X := X) H H₂) :
    inner ℂ g h = 0 := by
  obtain ⟨g₁, hg⟩ := hg
  obtain ⟨h₂, hh⟩ := hh
  have key : ∀ c : ℂ, ‖g + c • h‖ ^ 2 = ‖g‖ ^ 2 + ‖c • h‖ ^ 2 := fun c => by
    have e1 := part1 hK hdisj (g + c • h) g₁ (c • h₂)
      (by rw [RKHS.coe_add, RKHS.coe_smul, RKHS.coe_smul, hg, hh])
    have e2 := part1 hK hdisj g g₁ (0 : H₂) (by rw [RKHS.coe_zero, add_zero, hg])
    have e3 := part1 hK hdisj (c • h) (0 : H₁) (c • h₂)
      (by rw [RKHS.coe_zero, zero_add, RKHS.coe_smul, RKHS.coe_smul, hh])
    simp only [norm_zero] at e2 e3
    rw [e1, e2, e3]
    ring
  have r1 := key 1
  have r2 := key Complex.I
  rw [norm_add_sq (𝕜 := ℂ)] at r1 r2
  rw [inner_smul_right] at r1 r2
  have a1 : (inner ℂ g h).re = 0 := by
    have : RCLike.re ((1 : ℂ) * inner ℂ g h) = 0 := by linarith
    simpa using this
  have a2 : (inner ℂ g h).im = 0 := by
    have : RCLike.re (Complex.I * inner ℂ g h) = 0 := by linarith
    simpa using this
  exact Complex.ext a1 a2

end AronszajnDisjAux

open AronszajnRK.Sum in
theorem solution {X : Type*}
    {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [RKHS ℂ H₁ X ℂ]
    {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    [RKHS ℂ H₂ X ℂ]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [RKHS ℂ H X ℂ] (hK : kernelFn H = kernelFn H₁ + kernelFn H₂) :
    (Set.range (fun f : H₁ => (f : X → ℂ)) ∩ Set.range (fun f : H₂ => (f : X → ℂ)) = {0} →
      ∀ (f : H) (f₁ : H₁) (f₂ : H₂), (f : X → ℂ) = (f₁ : X → ℂ) + (f₂ : X → ℂ) →
        ‖f‖ ^ 2 = ‖f₁‖ ^ 2 + ‖f₂‖ ^ 2) ∧
    (Set.range (fun f : H₁ => (f : X → ℂ)) ∩ Set.range (fun f : H₂ => (f : X → ℂ)) = {0} ↔
      ∃ S₁ S₂ : Submodule ℂ H, IsClosed (S₁ : Set H) ∧ S₂ = S₁ᗮ ∧
        (∀ f₁ : H₁, ∃ f ∈ S₁, (f : X → ℂ) = (f₁ : X → ℂ) ∧ ‖f‖ = ‖f₁‖) ∧
        (∀ f ∈ S₁, ∃ f₁ : H₁, (f : X → ℂ) = (f₁ : X → ℂ)) ∧
        (∀ f₂ : H₂, ∃ f ∈ S₂, (f : X → ℂ) = (f₂ : X → ℂ) ∧ ‖f‖ = ‖f₂‖) ∧
        (∀ f ∈ S₂, ∃ f₂ : H₂, (f : X → ℂ) = (f₂ : X → ℂ))) := by
  refine ⟨fun hdisj => AronszajnDisjAux.part1 hK hdisj, ⟨fun hdisj => ?_, ?_⟩⟩
  · have e1 := AronszajnDisjAux.emb₁ hK hdisj
    have e2 := AronszajnDisjAux.emb₂ hK hdisj
    refine ⟨AronszajnDisjAux.rangeSub (X := X) H H₁, AronszajnDisjAux.rangeSub (X := X) H H₂,
      AronszajnDisjAux.rangeSub_closed e1, ?_, ?_, fun f hf => hf, ?_, fun f hf => hf⟩
    · ext f
      rw [Submodule.mem_orthogonal]
      constructor
      · intro hf u hu
        exact AronszajnDisjAux.orth hK hdisj u f hu hf
      · intro hfo
        obtain ⟨g₁, g₂, hg, -⟩ := AronszajnDisjAux.partA hK f
        obtain ⟨a, ha, -⟩ := e1 g₁
        obtain ⟨b, hb, -⟩ := e2 g₂
        have hf : f = a + b := DFunLike.coe_injective (by rw [RKHS.coe_add, ha, hb, hg])
        have hamem : a ∈ AronszajnDisjAux.rangeSub (X := X) H H₁ := ⟨g₁, ha⟩
        have hbmem : b ∈ AronszajnDisjAux.rangeSub (X := X) H H₂ := ⟨g₂, hb⟩
        have h0 := hfo a hamem
        rw [hf, inner_add_right, AronszajnDisjAux.orth hK hdisj a b hamem hbmem, add_zero,
          inner_self_eq_zero] at h0
        rw [hf, h0, zero_add]
        exact hbmem
    · intro f₁
      obtain ⟨f, hf, hn⟩ := e1 f₁
      exact ⟨f, ⟨f₁, hf⟩, hf, hn⟩
    · intro f₂
      obtain ⟨f, hf, hn⟩ := e2 f₂
      exact ⟨f, ⟨f₂, hf⟩, hf, hn⟩
  · rintro ⟨S₁, S₂, -, hS2, h1, -, h2, -⟩
    ext g
    rw [Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
      obtain ⟨f, hfS, hfa, -⟩ := h1 a
      obtain ⟨f', hf'S, hfb, -⟩ := h2 b
      have hb' : (b : X → ℂ) = (a : X → ℂ) := hb
      have hff : f = f' := DFunLike.coe_injective (hfa.trans (hb'.symm.trans hfb.symm))
      rw [← hff, hS2, Submodule.mem_orthogonal] at hf'S
      have h0 := hf'S f hfS
      rw [inner_self_eq_zero] at h0
      show (a : X → ℂ) = 0
      rw [← hfa, h0, RKHS.coe_zero]
    · rintro rfl
      exact ⟨⟨0, RKHS.coe_zero⟩, ⟨0, RKHS.coe_zero⟩⟩
