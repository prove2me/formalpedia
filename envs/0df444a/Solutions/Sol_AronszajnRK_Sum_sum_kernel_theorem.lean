-- Prove2me | solution 1 for AronszajnRK.Sum.sum_kernel_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T09:28:56.58424+00:00
-- url     : https://prove2.me/submissions/432781de-7428-4a9b-884a-f5b96c66d1fb

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn

set_option autoImplicit false

universe u w

namespace AronszajnSumAux

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

end sum

end AronszajnSumAux

open AronszajnRK.Sum in
theorem solution {X : Type u}
    {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [RKHS ℂ H₁ X ℂ]
    {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    [RKHS ℂ H₂ X ℂ] :
    (∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
        (_ : RKHS ℂ H X ℂ), kernelFn H = kernelFn H₁ + kernelFn H₂) ∧
    ∀ (H : Type w) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      [RKHS ℂ H X ℂ], kernelFn H = kernelFn H₁ + kernelFn H₂ →
        Set.range (fun f : H => (f : X → ℂ)) =
            {g : X → ℂ | ∃ (f₁ : H₁) (f₂ : H₂), g = (f₁ : X → ℂ) + (f₂ : X → ℂ)} ∧
        ∀ f : H, IsLeast
          {r : ℝ | ∃ (f₁ : H₁) (f₂ : H₂),
            (f : X → ℂ) = (f₁ : X → ℂ) + (f₂ : X → ℂ) ∧ r = ‖f₁‖ ^ 2 + ‖f₂‖ ^ 2}
          (‖f‖ ^ 2) := by
  refine ⟨?_, ?_⟩
  · have : Fact (RKHS.kernel H₁ + RKHS.kernel H₂ : Matrix X X (ℂ →L[ℂ] ℂ)).PosSemidef :=
      ⟨(RKHS.posSemidef_kernel H₁).add (RKHS.posSemidef_kernel H₂)⟩
    refine ⟨RKHS.OfKernel (RKHS.kernel H₁ + RKHS.kernel H₂), inferInstance, inferInstance,
      inferInstance, inferInstance, ?_⟩
    funext x y
    show RKHS.kernel (RKHS.OfKernel (RKHS.kernel H₁ + RKHS.kernel H₂)) x y 1 =
      RKHS.kernel H₁ x y 1 + RKHS.kernel H₂ x y 1
    rw [RKHS.OfKernel.kernel_ofKernel]
    rfl
  · intro H _ _ _ _ hK
    refine ⟨?_, fun f => ⟨?_, ?_⟩⟩
    · ext g
      constructor
      · rintro ⟨f, rfl⟩
        obtain ⟨f₁, f₂, h, -⟩ := AronszajnSumAux.partA hK f
        exact ⟨f₁, f₂, h⟩
      · rintro ⟨f₁, f₂, rfl⟩
        obtain ⟨f, h, -⟩ := AronszajnSumAux.partB hK f₁ f₂
        exact ⟨f, h⟩
    · obtain ⟨f₁, f₂, h, hn⟩ := AronszajnSumAux.partA hK f
      exact ⟨f₁, f₂, h, hn⟩
    · rintro r ⟨f₁, f₂, hf, rfl⟩
      obtain ⟨f', h', hn'⟩ := AronszajnSumAux.partB hK f₁ f₂
      have : f' = f := DFunLike.coe_injective (h'.trans hf.symm)
      rw [← this]
      exact hn'
