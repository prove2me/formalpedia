-- Prove2me | solution 1 for AronszajnRK.Product.product_kernel_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T11:57:48.283986+00:00
-- url     : https://prove2.me/submissions/86b51d32-2622-40b3-90c1-f85a47bd7f33

import Mathlib
import Definitions.Def_AronszajnRK_Product_kernelFn
import Definitions.Def_AronszajnRK_Product_IsDirectProduct

set_option autoImplicit false

universe u v w z t

namespace AronszajnProdAux

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
      AronszajnRK.Product.kernelFn H x y := by
  rw [eval_inner, RKHS.kerFun_apply]
  rfl

lemma kerFun_apply' (x y : X) :
    (RKHS.kerFun H y (1 : ℂ)) x = AronszajnRK.Product.kernelFn H x y := by
  rw [RKHS.kerFun_apply]
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

section prod
variable {X : Type*}
  {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [RKHS ℂ H₁ X ℂ]
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  [RKHS ℂ H₂ X ℂ]
  {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  [RKHS ℂ H' (X × X) ℂ]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [RKHS ℂ H X ℂ]

/-- The kernel of the direct product is the product of the kernels. -/
lemma kernelFn_prod (hH' : AronszajnRK.Product.IsDirectProduct H₁ H₂ H') (p q : X × X) :
    AronszajnRK.Product.kernelFn H' p q =
      AronszajnRK.Product.kernelFn H₁ p.1 q.1 * AronszajnRK.Product.kernelFn H₂ p.2 q.2 := by
  obtain ⟨h1, h2, h3⟩ := hH'
  obtain ⟨u, hu⟩ := h1 (RKHS.kerFun H₁ q.1 (1 : ℂ)) (RKHS.kerFun H₂ q.2 (1 : ℂ))
  have hfun : (fun g : H' => inner ℂ u g) = fun g : H' => g q := by
    refine Continuous.ext_on h3 (continuous_const.inner continuous_id)
      (RKHS.continuous_eval (H := H') q) ?_
    intro g hg
    refine Submodule.span_induction (p := fun g _ => inner ℂ u g = g q) ?_ ?_ ?_ ?_ hg
    · rintro v ⟨f₁, f₂, hv⟩
      rw [h2 _ _ _ _ u v hu hv, eval_inner, eval_inner, hv]
    · simp [RKHS.coe_zero]
    · intro a b _ _ ha hb
      rw [inner_add_right, ha, hb, RKHS.coe_add, Pi.add_apply]
    · intro c a _ ha
      rw [inner_smul_right, ha, RKHS.coe_smul, Pi.smul_apply, smul_eq_mul]
  have hu' : u = RKHS.kerFun H' q (1 : ℂ) := by
    refine ext_inner_right ℂ fun g => ?_
    rw [eval_inner]
    exact congrFun hfun g
  rw [← kerFun_apply', ← hu', hu, kerFun_apply', kerFun_apply']

/-- Diagonal feature map. -/
noncomputable def dfeat (H' : Type*) [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] [RKHS ℂ H' (X × X) ℂ] (x : X) : H' :=
  RKHS.kerFun H' (x, x) (1 : ℂ)

lemma gram_prod (hH' : AronszajnRK.Product.IsDirectProduct H₁ H₂ H')
    (hK : ∀ x y : X, AronszajnRK.Product.kernelFn H x y =
      AronszajnRK.Product.kernelFn H₁ x y * AronszajnRK.Product.kernelFn H₂ x y) (x y : X) :
    inner ℂ (RKHS.kerFun H x (1 : ℂ)) (RKHS.kerFun H y (1 : ℂ)) =
      inner ℂ (dfeat H' x) (dfeat H' y) := by
  rw [gram, hK, dfeat, dfeat, gram, kernelFn_prod hH']

lemma partA (hH' : AronszajnRK.Product.IsDirectProduct H₁ H₂ H')
    (hK : ∀ x y : X, AronszajnRK.Product.kernelFn H x y =
      AronszajnRK.Product.kernelFn H₁ x y * AronszajnRK.Product.kernelFn H₂ x y) (f : H) :
    ∃ g : H', (fun x => g (x, x)) = (f : X → ℂ) ∧ ‖g‖ = ‖f‖ := by
  obtain ⟨g, hg, hn⟩ := transfer (fun x : X => RKHS.kerFun H x (1 : ℂ)) (dfeat H')
    (gram_prod hH' hK) f (dense_lc H f)
  refine ⟨g, ?_, hn⟩
  funext y
  have := hg y
  rw [dfeat, eval_inner, eval_inner] at this
  exact this

lemma partB (hH' : AronszajnRK.Product.IsDirectProduct H₁ H₂ H')
    (hK : ∀ x y : X, AronszajnRK.Product.kernelFn H x y =
      AronszajnRK.Product.kernelFn H₁ x y * AronszajnRK.Product.kernelFn H₂ x y) (v : H') :
    ∃ f : H, (f : X → ℂ) = (fun x => v (x, x)) ∧ ‖f‖ ≤ ‖v‖ := by
  set S : Submodule ℂ H' :=
    (Submodule.span ℂ (Set.range (dfeat H' (X := X)))).topologicalClosure with hS
  have : CompleteSpace S := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  set e := S.starProjection v with he
  have hmem : e ∈ closure (Set.range (Finsupp.linearCombination ℂ (dfeat H' (X := X)) :
      (X →₀ ℂ) → H')) := by
    have h1 : e ∈ S := S.starProjection_apply_mem v
    rw [hS, ← SetLike.mem_coe, Submodule.topologicalClosure_coe,
      ← Finsupp.range_linearCombination, LinearMap.coe_range] at h1
    exact h1
  obtain ⟨f, hf, hn⟩ := transfer (dfeat H') (fun x : X => RKHS.kerFun H x (1 : ℂ))
    (fun x y => (gram_prod hH' hK x y).symm) e hmem
  refine ⟨f, ?_, ?_⟩
  · funext y
    have hy := hf y
    have hbS : dfeat H' y ∈ S :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨y, rfl⟩)
    rw [eval_inner, he, ← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hbS, dfeat, eval_inner] at hy
    exact hy
  · exact hn ▸ S.norm_starProjection_apply_le v

end prod

end AronszajnProdAux

open AronszajnRK.Product in
theorem solution {X : Type u} (H₁ : Type v) [NormedAddCommGroup H₁]
    [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [RKHS ℂ H₁ X ℂ] (H₂ : Type w)
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [RKHS ℂ H₂ X ℂ]
    (H' : Type z) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    [RKHS ℂ H' (X × X) ℂ] (hH' : IsDirectProduct H₁ H₂ H') :
    (∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : CompleteSpace H) (_ : RKHS ℂ H X ℂ),
        ∀ x y : X, kernelFn H x y = kernelFn H₁ x y * kernelFn H₂ x y) ∧
    ∀ (H : Type t) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        [RKHS ℂ H X ℂ], (∀ x y : X, kernelFn H x y = kernelFn H₁ x y * kernelFn H₂ x y) →
      Set.range (fun f : H => (⇑f : X → ℂ)) = {φ : X → ℂ | ∃ g : H', φ = fun x => g (x, x)} ∧
      ∀ f : H, IsLeast
        {r : ℝ | ∃ g : H', (fun x => g (x, x)) = (⇑f : X → ℂ) ∧ r = ‖g‖} ‖f‖ := by
  refine ⟨?_, ?_⟩
  · have : Fact ((RKHS.kernel H').submatrix (fun x : X => (x, x)) (fun x : X => (x, x))).PosSemidef :=
      ⟨(RKHS.posSemidef_kernel H').submatrix _⟩
    refine ⟨RKHS.OfKernel ((RKHS.kernel H').submatrix (fun x : X => (x, x)) (fun x : X => (x, x))),
      inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    intro x y
    rw [← AronszajnProdAux.kernelFn_prod hH' (x, x) (y, y)]
    show RKHS.kernel (RKHS.OfKernel ((RKHS.kernel H').submatrix (fun x : X => (x, x))
      (fun x : X => (x, x)))) x y 1 = RKHS.kernel H' (x, x) (y, y) 1
    rw [RKHS.OfKernel.kernel_ofKernel]
    rfl
  · intro H _ _ _ _ hK
    refine ⟨?_, fun f => ⟨?_, ?_⟩⟩
    · ext φ
      constructor
      · rintro ⟨f, rfl⟩
        obtain ⟨g, hg, -⟩ := AronszajnProdAux.partA hH' hK f
        exact ⟨g, hg.symm⟩
      · rintro ⟨g, rfl⟩
        obtain ⟨f, hf, -⟩ := AronszajnProdAux.partB hH' hK g
        exact ⟨f, hf⟩
    · obtain ⟨g, hg, hn⟩ := AronszajnProdAux.partA hH' hK f
      exact ⟨g, hg, hn.symm⟩
    · rintro r ⟨g, hg, rfl⟩
      obtain ⟨f', h', hn'⟩ := AronszajnProdAux.partB hH' hK g
      have : f' = f := DFunLike.coe_injective (h'.trans hg)
      rw [← this]
      exact hn'
