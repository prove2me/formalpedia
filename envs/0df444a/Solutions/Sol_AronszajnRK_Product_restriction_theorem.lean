-- Prove2me | solution 1 for AronszajnRK.Product.restriction_theorem
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T07:29:20.267816+00:00
-- url     : https://prove2.me/submissions/b9d2d01e-ab46-427b-9f1f-0eb4dff84042

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn
import Definitions.Def_AronszajnRK_Product_kernelFn

universe u v w

/-! # Restriction theorem (Aronszajn §5)

If `K` is the reproducing kernel of an RKHS `H` on `X`, then the restriction of `K` to a
subset `E₁ ⊆ X` is the reproducing kernel of the class of restrictions `f|E₁`, `f ∈ H`, and
`‖f₁‖` is the minimum of `‖f‖` over all extensions of `f₁`.

The proof reuses the Moore development: the restricted scalar kernel is a positive matrix
(a submatrix of a positive one), so `RKHS.OfKernel` constructs an RKHS in the universe of
`X`; every RKHS with the restricted kernel is identified with the closed span `M` of the
kernel functions `k y`, `y ∈ E₁`, inside `H`, via the norm-preserving correspondence from
the Moore uniqueness argument; and the orthogonal projection onto `M` produces the
minimal extension. -/

open scoped ComplexOrder

namespace MooreAux

open RKHS ContinuousLinearMap
open scoped InnerProductSpace

/-! ## The scalar-to-operator embedding -/

/-- Embed a scalar `c : ℂ` as the operator `z ↦ c * z` on `ℂ`. -/
noncomputable def toOp (c : ℂ) : ℂ →L[ℂ] ℂ := c • ContinuousLinearMap.id ℂ ℂ

lemma toOp_apply (c v : ℂ) : toOp c v = c * v := by simp [toOp]

lemma toOp_star (c : ℂ) : star (toOp c) = toOp (star c) := by
  simp only [toOp, star_smul]
  congr 1
  exact ContinuousLinearMap.adjoint_id

lemma toOp_mul (c d : ℂ) : toOp c * toOp d = toOp (c * d) := by
  ext v
  simp [toOp]

lemma toOp_add (c d : ℂ) : toOp (c + d) = toOp c + toOp d := by
  ext v
  simp [toOp]

lemma toOp_eq_of_apply (T : ℂ →L[ℂ] ℂ) : toOp (T 1) = T := by
  ext v
  simp [toOp]

lemma toOp_zero : (toOp 0 : ℂ →L[ℂ] ℂ) = 0 := by
  rw [eq_comm]; ext z; simp [toOp]

lemma toOp_pos {s : ℂ} (hs : 0 ≤ s) : 0 ≤ toOp s := by
  have hre : 0 ≤ s.re := (Complex.nonneg_iff.mp hs).1
  have him : 0 = s.im := (Complex.nonneg_iff.mp hs).2
  have hsreal : s = ((s.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hstar : star s = s := by rw [Complex.star_def, hsreal, Complex.conj_ofReal]
  have hvv : ∀ v : ℂ, ⟪v, v⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    intro v; apply Complex.ext <;> simp
  have key : ∀ v : ℂ, ⟪toOp s v, v⟫_ℂ = ((s.re * Complex.normSq v : ℝ) : ℂ) := by
    intro v
    rw [toOp_apply, hsreal]
    have e1 : ⟪((s.re : ℝ) : ℂ) * v, v⟫_ℂ = ((s.re : ℝ) : ℂ) * ⟪v, v⟫_ℂ := by
      rw [show ((s.re : ℝ) : ℂ) * v = ((s.re : ℝ) : ℂ) • v from by simp [mul_comm],
        inner_smul_left]
      simp
    rw [e1, hvv, ← RCLike.normSq_eq_def']
    norm_num
  have hsa : toOp s - 0 = toOp s := by simp
  rw [ContinuousLinearMap.le_def, hsa, ContinuousLinearMap.isPositive_iff']
  refine ⟨?_, fun v => ?_⟩
  · show star (toOp s) = toOp s
    rw [toOp_star, hstar]
  · rw [key, Complex.nonneg_iff]
    simp only [Complex.ofReal_re, Complex.ofReal_im, and_true]
    exact mul_nonneg hre (Complex.normSq_nonneg v)

lemma toOp_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ∑ i ∈ s, toOp (f i) = toOp (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [eq_comm]; ext z; simp [toOp]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ih, toOp_add]

lemma toOp_finsupp_sum {X : Type*} (c : X →₀ ℂ) (φ : X → ℂ → ℂ) :
    c.sum (fun x cx => toOp (φ x cx)) = toOp (c.sum φ) := by
  simp only [Finsupp.sum]
  exact toOp_sum _ _

/-- The operator matrix associated to a scalar positive matrix is positive. -/
lemma posSemidef_toOp {X : Type*} (K : X → X → ℂ) (hK : (Matrix.of K).PosSemidef) :
    (Matrix.of fun x y => toOp (K x y)).PosSemidef := by
  constructor
  · show Matrix.conjTranspose (Matrix.of fun x y => toOp (K x y))
      = (Matrix.of fun x y => toOp (K x y))
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    have hjk : star (K j i) = K i j := by
      have := hK.1.apply i j
      simpa using this
    rw [toOp_star, hjk]
  · intro c
    set t : X →₀ ℂ := c.mapRange (fun T => T 1) (by simp) with ht
    have hct : ∀ i, t i = (c i) 1 := by
      intro i; simp [ht, Finsupp.mapRange_apply]
    have hc : ∀ i, c i = toOp (t i) := by
      intro i
      rw [← toOp_eq_of_apply (c i)]
      congr 1
    have hterm : ∀ i j, star (c i) * toOp (K i j) * c j
        = toOp (star (t i) * K i j * t j) := by
      intro i j
      rw [hc i, hc j, toOp_star, ← toOp_mul, ← toOp_mul]
    -- rewriting an operator-valued sum of `toOp`s as `toOp` of the t-sum
    have hconv : ∀ ψ : X → ℂ → ℂ, (∀ i, ψ i 0 = 0) →
        c.sum (fun i Ti => toOp (ψ i (Ti 1))) = toOp (t.sum ψ) := by
      intro ψ hψ
      have h1 : c.sum (fun i Ti => toOp (ψ i (Ti 1)))
          = t.sum (fun i ti => toOp (ψ i ti)) := by
        rw [ht]
        exact (Finsupp.sum_mapRange_index (f := fun T => T 1) (g := c)
          (h := fun i ti => toOp (ψ i ti)) (fun i => by
            show toOp (ψ i 0) = (0 : ℂ →L[ℂ] ℂ)
            rw [hψ i, toOp_zero])).symm
      rw [h1, toOp_finsupp_sum]
    have key : (c.sum fun i Ti => c.sum fun j Tj => star Ti * toOp (K i j) * Tj)
        = toOp (t.sum fun i ti => t.sum fun j tj => star ti * K i j * tj) := by
      have step1 : ∀ i : X, (c.sum fun j Tj => star (c i) * toOp (K i j) * Tj)
          = toOp (t.sum fun j tj => star (t i) * K i j * tj) := by
        intro i
        have ha : c.sum (fun j Tj => star (c i) * toOp (K i j) * Tj)
            = c.sum (fun j Tj => toOp (star (t i) * K i j * t j)) :=
          Finsupp.sum_congr (fun j _ => hterm i j)
        rw [ha]
        have hb : c.sum (fun j Tj => toOp (star (t i) * K i j * t j))
            = c.sum (fun j Tj => toOp (star (t i) * K i j * (Tj 1))) :=
          Finsupp.sum_congr (fun j _ => by rw [hct j])
        rw [hb]
        exact hconv (fun j tj => star (t i) * K i j * tj) (fun i => by simp)
      have hb : c.sum (fun i Ti => c.sum fun j Tj => star Ti * toOp (K i j) * Tj)
          = c.sum (fun i Ti => toOp (t.sum fun j tj => star (t i) * K i j * tj)) :=
        Finsupp.sum_congr (fun i _ => step1 i)
      rw [hb]
      have hc2 : c.sum (fun i Ti => toOp (t.sum fun j tj => star (t i) * K i j * tj))
          = c.sum (fun i Ti => toOp ((fun i ti => t.sum fun j tj => star ti * K i j * tj) i (Ti 1))) :=
        Finsupp.sum_congr (fun i _ => by rw [hct i])
      rw [hc2]
      exact hconv (fun i ti => t.sum fun j tj => star ti * K i j * tj) (fun i => by simp)
    simp only [Matrix.of_apply]
    rw [key]
    exact toOp_pos (hK.2 t)

/-- **Existence half of Moore's theorem.** -/
theorem exists_rkhs_of_posSemidef {X : Type u} (K : X → X → ℂ) (hK : (Matrix.of K).PosSemidef) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : CompleteSpace H) (_ : RKHS ℂ H X ℂ), AronszajnRK.Sum.kernelFn H = K := by
  classical
  haveI : Fact (Matrix.of fun x y => toOp (K x y)).PosSemidef := ⟨posSemidef_toOp K hK⟩
  refine ⟨RKHS.OfKernel (Matrix.of fun x y => toOp (K x y)),
    inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  funext x y
  simp only [AronszajnRK.Sum.kernelFn, RKHS.OfKernel.kernel_ofKernel, Matrix.of_apply,
    toOp_apply, mul_one]

/-! ## Uniqueness: two RKHSs with the same scalar kernel -/

section Uniqueness

variable {X : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [RKHS ℂ H X ℂ]

/-- The inner product of two kernel functions is the scalar kernel. -/
lemma inner_kerFun (y y' : X) :
    ⟪kerFun H y 1, kerFun H y' 1⟫_ℂ = AronszajnRK.Sum.kernelFn H y y' := by
  rw [AronszajnRK.Sum.kernelFn, kerFun_inner]
  simp
  rw [kerFun_apply]

/-- The combination map: a finitely supported family of scalars gives the corresponding
combination of kernel functions. -/
noncomputable def e {X : Type*} (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H X ℂ] : (X →₀ ℂ) →ₗ[ℂ] H :=
  Finsupp.linearCombination ℂ (fun y : X => kerFun H y 1)

lemma e_apply (c : X →₀ ℂ) :
    e H c = c.sum fun y cy => cy • kerFun H y 1 := rfl

/-- Point evaluation of a combination of kernel functions. -/
lemma eval_e (c : X →₀ ℂ) (x : X) :
    (e H c) x = c.sum fun y cy => cy * AronszajnRK.Sum.kernelFn H x y := by
  have h1 : (e H c) x = ⟪kerFun H x 1, e H c⟫_ℂ := by
    rw [kerFun_inner]; simp
  rw [h1, e_apply, Finsupp.inner_sum]
  refine Finsupp.sum_congr fun y _ => ?_
  rw [inner_smul_right, inner_kerFun]

/-- The inner product of two combinations depends only on the scalar kernel. -/
lemma inner_e (c d : X →₀ ℂ) :
    ⟪e H c, e H d⟫_ℂ = c.sum fun y cy => d.sum fun y' dy' => (star cy) * dy' *
      AronszajnRK.Sum.kernelFn H y y' := by
  rw [e_apply, e_apply, Finsupp.sum_inner]
  refine Finsupp.sum_congr fun y _ => ?_
  rw [Finsupp.inner_sum]
  refine Finsupp.sum_congr fun y' _ => ?_
  rw [inner_smul_left, inner_smul_right, inner_kerFun]
  simp [mul_assoc, mul_comm, mul_left_comm]

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [RKHS ℂ H₁ X ℂ] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  [RKHS ℂ H₂ X ℂ]

lemma inner_e_congr (hk : AronszajnRK.Sum.kernelFn H₁ = AronszajnRK.Sum.kernelFn H₂)
    (c d : X →₀ ℂ) : ⟪e H₁ c, e H₁ d⟫_ℂ = ⟪e H₂ c, e H₂ d⟫_ℂ := by
  rw [inner_e, inner_e, hk]

lemma norm_e_eq (hk : AronszajnRK.Sum.kernelFn H₁ = AronszajnRK.Sum.kernelFn H₂)
    (c : X →₀ ℂ) : ‖e H₁ c‖ = ‖e H₂ c‖ := by
  have h : RCLike.re ⟪e H₁ c, e H₁ c⟫_ℂ = RCLike.re ⟪e H₂ c, e H₂ c⟫_ℂ := by
    rw [inner_e_congr hk]
  have h2 : (‖e H₁ c‖ : ℝ) ^ 2 = (‖e H₂ c‖ : ℝ) ^ 2 := by
    calc (‖e H₁ c‖ : ℝ) ^ 2 = RCLike.re ⟪e H₁ c, e H₁ c⟫_ℂ := (inner_self_eq_norm_sq _).symm
      _ = RCLike.re ⟪e H₂ c, e H₂ c⟫_ℂ := h
      _ = (‖e H₂ c‖ : ℝ) ^ 2 := inner_self_eq_norm_sq _
  nlinarith [norm_nonneg (e H₁ c), norm_nonneg (e H₂ c)]

lemma kerFun_smul_one (x : X) (v : ℂ) : kerFun H x v = v • kerFun H x 1 := by
  have := (kerFun H x).map_smul v (1 : ℂ)
  simpa using this

lemma span_kerFun_eq :
    Submodule.span ℂ {kerFun H x v | (x) (v)}
      = Submodule.span ℂ (Set.range fun y : X => kerFun H y 1) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro z ⟨x, v, rfl⟩
    rw [kerFun_smul_one]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self x))
  · rw [Submodule.span_le]
    rintro z ⟨y, rfl⟩
    exact Submodule.subset_span ⟨y, 1, rfl⟩

/-- The combinations of kernel functions are dense. -/
lemma dense_range_e : Dense (Set.range fun c : X →₀ ℂ => e H c) := by
  have h1 : LinearMap.range (e H)
      = Submodule.span ℂ (Set.range fun y : X => kerFun H y 1) := by
    show LinearMap.range (Finsupp.linearCombination ℂ (fun y : X => kerFun H y 1)) = _
    rw [Finsupp.range_linearCombination]
  have h2 : (Submodule.span ℂ (Set.range fun y : X => kerFun H y 1)).topologicalClosure = ⊤ := by
    have := kerFun_dense H
    rwa [span_kerFun_eq] at this
  rw [show Set.range (fun c : X →₀ ℂ => e H c) = ↑(LinearMap.range (e H)) from
      (LinearMap.coe_range (e H)).symm,
    h1, Submodule.dense_iff_topologicalClosure_eq_top]
  exact h2

/-- Given two RKHSs with the same scalar kernel, there is a continuous norm-preserving map
sending every function to a function with the same values. -/
theorem exists_kernel_preserving_isometry
    (hk : AronszajnRK.Sum.kernelFn H₁ = AronszajnRK.Sum.kernelFn H₂) :
    ∃ T : H₁ → H₂, Continuous T ∧ (∀ f : H₁, ∀ x : X, T f x = f x) ∧ ∀ f : H₁, ‖T f‖ = ‖f‖ := by
  classical
  set E₁ : (X →₀ ℂ) → H₁ := fun c => e H₁ c with hE₁
  have hdense : Dense (Set.range E₁) := dense_range_e (H := H₁)
  set corr : Set.range E₁ → H₂ := fun z => e H₂ (Function.invFun E₁ z.1) with hcorrdef
  -- `invFun` lands in a preimage
  have hpre : ∀ z : Set.range E₁, e H₁ (Function.invFun E₁ z.1) = z.1 := by
    intro z
    exact Function.invFun_eq z.2
  -- the correspondence is well defined on values
  have hwd : ∀ c c' : X →₀ ℂ, E₁ c = E₁ c' → e H₂ c = e H₂ c' := by
    intro c c' h
    have h2 : e H₁ (c - c') = 0 := by
      have h3 : e H₁ (c - c') = E₁ c - E₁ c' := by simp [hE₁, map_sub]
      rw [h3, h, sub_self]
    have h4 : ‖e H₂ (c - c')‖ = 0 := by
      rw [← norm_e_eq hk, h2, norm_zero]
    have h5 : e H₂ c - e H₂ c' = e H₂ (c - c') := by simp [map_sub]
    rw [← sub_eq_zero, h5]
    exact norm_eq_zero.mp h4
  have hcorr_eq : ∀ c : X →₀ ℂ, corr ⟨E₁ c, ⟨c, rfl⟩⟩ = e H₂ c := by
    intro c
    exact hwd _ _ (Function.invFun_eq ⟨c, rfl⟩)
  have hiso : Isometry corr := by
    refine isometry_iff_dist_eq.mpr fun z z' => ?_
    have h5 : corr z - corr z' = e H₂ (Function.invFun E₁ z.1 - Function.invFun E₁ z'.1) := by
      show e H₂ (Function.invFun E₁ z.1) - e H₂ (Function.invFun E₁ z'.1)
        = e H₂ (Function.invFun E₁ z.1 - Function.invFun E₁ z'.1)
      rw [map_sub]
    have h6 : e H₁ (Function.invFun E₁ z.1 - Function.invFun E₁ z'.1) = z.1 - z'.1 := by
      rw [map_sub, hpre, hpre]
    calc dist (corr z) (corr z') = ‖corr z - corr z'‖ := dist_eq_norm (corr z) (corr z')
      _ = ‖e H₂ (Function.invFun E₁ z.1 - Function.invFun E₁ z'.1)‖ := by rw [h5]
      _ = ‖e H₁ (Function.invFun E₁ z.1 - Function.invFun E₁ z'.1)‖ := (norm_e_eq hk _).symm
      _ = ‖z.1 - z'.1‖ := by rw [h6]
      _ = dist z.1 z'.1 := (dist_eq_norm z.1 z'.1).symm
      _ = dist z z' := (Subtype.dist_eq z z').symm
  have hu : UniformContinuous corr := hiso.uniformContinuous
  have hTcont : Continuous (hdense.extend corr) :=
    (Dense.uniformContinuous_extend hdense hu).continuous
  have hTe : ∀ c : X →₀ ℂ, (hdense.extend corr) (E₁ c) = e H₂ c := by
    intro c
    have h := Dense.extend_of_ind hdense hu (⟨E₁ c, ⟨c, rfl⟩⟩ : Set.range E₁)
    simp only [Subtype.coe_mk] at h
    rw [h]
    exact hcorr_eq c
  refine ⟨hdense.extend corr, hTcont, ?_, ?_⟩
  · -- functions are preserved
    intro f x
    have hg : Continuous (fun g : H₁ => (hdense.extend corr) g x) :=
      (RKHS.continuous_eval x).comp hTcont
    have hh : Continuous (fun g : H₁ => g x) := RKHS.continuous_eval x
    have hagree : ∀ c : X →₀ ℂ, (fun g : H₁ => (hdense.extend corr) g x) (E₁ c)
        = (fun g : H₁ => g x) (E₁ c) := by
      intro c
      show (hdense.extend corr (E₁ c)) x = (E₁ c) x
      rw [hTe, eval_e (H := H₂), eval_e (H := H₁), hk]
    exact congrFun (DenseRange.equalizer hdense hg hh (funext hagree)) f
  · -- norms are preserved
    intro f
    have hg : Continuous (fun g : H₁ => ‖(hdense.extend corr) g‖) :=
      continuous_norm.comp hTcont
    have hh : Continuous (fun g : H₁ => ‖g‖) := continuous_norm
    have hagree : ∀ c : X →₀ ℂ, (fun g : H₁ => ‖(hdense.extend corr) g‖) (E₁ c)
        = (fun g : H₁ => ‖g‖) (E₁ c) := by
      intro c
      show ‖hdense.extend corr (E₁ c)‖ = ‖E₁ c‖
      rw [hTe, norm_e_eq hk]
    exact congrFun (DenseRange.equalizer hdense hg hh (funext hagree)) f

/-- **Uniqueness half of Moore's theorem.** -/
theorem moore_uniqueness (hk : AronszajnRK.Sum.kernelFn H₁ = AronszajnRK.Sum.kernelFn H₂) :
    Set.range (fun f : H₁ => (f : X → ℂ)) = Set.range (fun f : H₂ => (f : X → ℂ)) ∧
      ∀ (f₁ : H₁) (f₂ : H₂), (f₁ : X → ℂ) = (f₂ : X → ℂ) → ‖f₁‖ = ‖f₂‖ := by
  obtain ⟨T, hTcont, hTfun, hTiso⟩ := exists_kernel_preserving_isometry hk
  obtain ⟨S, hScont, hSfun, hSiso⟩ := exists_kernel_preserving_isometry hk.symm
  refine ⟨?_, ?_⟩
  · ext g
    constructor
    · rintro ⟨f₁, rfl⟩
      exact ⟨T f₁, funext fun x => hTfun f₁ x⟩
    · rintro ⟨f₂, rfl⟩
      exact ⟨S f₂, funext fun x => hSfun f₂ x⟩
  · intro f₁ f₂ hf
    have hT : T f₁ = f₂ := by
      refine RKHS.ext (fun x => ?_)
      rw [hTfun f₁ x]
      exact congrFun hf x
    rw [← hT, hTiso]

end Uniqueness

end MooreAux

open MooreAux RKHS
open scoped InnerProductSpace

/-! ## The scalar kernel of an RKHS is a positive matrix -/

lemma star_kernelFn {X : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H X ℂ] (x y : X) :
    star (AronszajnRK.Sum.kernelFn H x y) = AronszajnRK.Sum.kernelFn H y x := by
  rw [← MooreAux.inner_kerFun, ← MooreAux.inner_kerFun]
  exact inner_conj_symm (𝕜 := ℂ) (kerFun H y 1) (kerFun H x 1)

/-- The scalar kernel of an RKHS is a positive matrix (Moore). -/
lemma posSemidef_kernelFn {X : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H X ℂ] : (Matrix.of (AronszajnRK.Sum.kernelFn H)).PosSemidef := by
  refine ⟨?_, fun c => ?_⟩
  · rw [Matrix.IsHermitian.ext_iff]
    intro i j
    exact star_kernelFn (H := H) _ _
  · have hQ : (c.sum fun i ci => c.sum fun j cj =>
          star ci * (Matrix.of (AronszajnRK.Sum.kernelFn H)) i j * cj)
          = ⟪e H c, e H c⟫_ℂ := by
      rw [MooreAux.inner_e]
      refine Finsupp.sum_congr fun i _ => ?_
      refine Finsupp.sum_congr fun j _ => ?_
      simp only [Matrix.of_apply]
      ring
    rw [hQ, Complex.nonneg_iff]
    exact ⟨inner_self_nonneg (𝕜 := ℂ), (inner_self_im (𝕜 := ℂ) (e H c)).symm⟩

/-! ## The restricted RKHS inside `H` -/

section Restriction

variable {X : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [RKHS ℂ H X ℂ]

/-- The closure of the span of the kernel functions indexed by `E₁ ⊆ X`. -/
def restrSub (E₁ : Set X) : Submodule ℂ H :=
  (Submodule.span ℂ (Set.range fun y : E₁ => kerFun H (y : X) 1)).topologicalClosure

lemma kerFun_mem_restrSub (E₁ : Set X) (y : E₁) :
    kerFun H (y : X) (1 : ℂ) ∈ restrSub E₁ :=
  Submodule.le_topologicalClosure (Submodule.span ℂ (Set.range fun y' : E₁ => kerFun H (y' : X) 1))
    (Submodule.subset_span (Set.mem_range_self y))

instance (E₁ : Set X) : CompleteSpace ↥(restrSub (H := H) E₁) := by
  unfold restrSub
  exact (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

noncomputable instance instRKHSrestr (E₁ : Set X) :
    RKHS ℂ ↥(restrSub (H := H) E₁) E₁ ℂ where
  coeCLM := by
    have h1 : ↥(restrSub (H := H) E₁) →L[ℂ] (X → ℂ) :=
      (coeCLM (𝕜 := ℂ) (H := H) (X := X)).comp (Submodule.subtypeL (restrSub (H := H) E₁))
    have h2 : (X → ℂ) →L[ℂ] (E₁ → ℂ) :=
      ContinuousLinearMap.pi fun x : E₁ => (ContinuousLinearMap.proj (x : X) : (X → ℂ) →L[ℂ] ℂ)
    exact h2.comp h1
  coeCLM_injective := by
    rw [injective_iff_map_eq_zero]
    intro g hg
    -- the function of `g` vanishes on `E₁`
    have hzero : ∀ y : E₁, (g : H) (y : X) = 0 := by
      intro y
      have h1 := congrFun hg y
      simpa using h1
    -- the reproducing identity in the form used below
    have hrep : ∀ y : E₁, ⟪kerFun H (y : X) 1, (g : H)⟫_ℂ = 0 := by
      intro y
      rw [kerFun_inner]
      simp [hzero y]
    -- so `g` is orthogonal to the span of the `E₁`-kernel functions
    have horth : (g : H) ∈ (Submodule.span ℂ
        (Set.range fun y : E₁ => kerFun H (y : X) 1))ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro w hw
      rw [inner_eq_zero_symm]
      induction hw using Submodule.span_induction with
      | mem w hw2 =>
          rcases hw2 with ⟨y, rfl⟩
          exact hrep y
      | zero => simp
      | add w₁ w₂ _ _ ih₁ ih₂ => rw [inner_add_left]; simp [ih₁, ih₂]
      | smul a w _ ih =>
          rw [inner_smul_left]; simp [ih]
    -- hence orthogonal to the closure, which contains `g` itself
    have horthM : (g : H) ∈ (restrSub (H := H) E₁)ᗮ := by
      show (g : H) ∈ ((Submodule.span ℂ
        (Set.range fun y : E₁ => kerFun H (y : X) 1)).topologicalClosure)ᗮ
      rw [← Submodule.orthogonal_orthogonal_eq_closure,
        Submodule.triorthogonal_eq_orthogonal]
      exact horth
    have hself : ⟪(g : H), (g : H)⟫_ℂ = 0 :=
      ((Submodule.mem_orthogonal (restrSub (H := H) E₁) (g : H)).mp horthM) ((g : H))
        (Submodule.coe_mem g)
    have h0 : (g : H) = 0 := by
      rw [← inner_self_eq_zero (𝕜 := ℂ), hself]
    exact Subtype.ext (by rw [h0, Submodule.coe_zero])

/-- The kernel functions of the restricted RKHS are the original kernel functions. -/
lemma kerFun_restr (E₁ : Set X) (y : E₁) :
    kerFun (H := ↥(restrSub (H := H) E₁)) y (1 : ℂ)
      = ((⟨kerFun H (y : X) (1 : ℂ), kerFun_mem_restrSub E₁ y⟩ :
          ↥(restrSub (H := H) E₁))) := by
  refine (ext_iff_inner_left (𝕜 := ℂ)
    (x := kerFun (H := ↥(restrSub (H := H) E₁)) y (1 : ℂ))
    (y := ((⟨kerFun H (y : X) (1 : ℂ), kerFun_mem_restrSub E₁ y⟩ :
          ↥(restrSub (H := H) E₁))))).mpr ?_
  intro g
  have hev : ∀ y' : E₁, g y' = ((g : H) : X → ℂ) (y' : X) := fun y' => rfl
  have hL : ⟪g, (kerFun (H := ↥(restrSub (H := H) E₁)) y (1 : ℂ))⟫_ℂ
      = star (((g : H) : X → ℂ) (y : X)) := by
    rw [RKHS.inner_kerFun]
    simp [hev]
  have hR : ⟪g, ((⟨kerFun H (y : X) (1 : ℂ), kerFun_mem_restrSub E₁ y⟩ :
      ↥(restrSub (H := H) E₁)))⟫_ℂ
      = star (((g : H) : X → ℂ) (y : X)) := by
    rw [Submodule.coe_inner (restrSub (H := H) E₁), RKHS.inner_kerFun (H := H)]
    simp
  rw [hL, hR]

/-- The scalar kernel of the restricted RKHS is the restriction of the scalar kernel. -/
lemma kernelFn_restr (E₁ : Set X) (x y : E₁) :
    AronszajnRK.Sum.kernelFn (H := ↥(restrSub (H := H) E₁)) x y
      = AronszajnRK.Sum.kernelFn H (x : X) (y : X) := by
  show (RKHS.kernel (H := ↥(restrSub (H := H) E₁)) x y) 1
      = (RKHS.kernel H (x : X) (y : X)) 1
  rw [← RKHS.kerFun_apply, ← RKHS.kerFun_apply, kerFun_restr E₁ y]
  rfl

/-- Evaluation in the restricted RKHS is evaluation in `H`. -/
lemma restr_eval (E₁ : Set X) (g : ↥(restrSub (H := H) E₁)) (x : E₁) :
    (⇑g : E₁ → ℂ) x = (g : H) (x : X) := rfl

/-- The orthogonal projection onto the closed span preserves evaluations on `E₁`. -/
lemma starProjection_eval (E₁ : Set X) (f : H) (y : E₁) :
    ((restrSub (H := H) E₁).starProjection f) (y : X) = f (y : X) := by
  have h1 : f - (restrSub (H := H) E₁).starProjection f ∈ (restrSub (H := H) E₁)ᗮ :=
    Submodule.sub_starProjection_mem_orthogonal f
  have h2 : ⟪kerFun H (y : X) (1 : ℂ),
      f - (restrSub (H := H) E₁).starProjection f⟫_ℂ = 0 :=
    ((Submodule.mem_orthogonal (restrSub (H := H) E₁)
      (f - (restrSub (H := H) E₁).starProjection f)).mp h1)
      (kerFun H (y : X) (1 : ℂ)) (kerFun_mem_restrSub E₁ y)
  have h3 : (f - (restrSub (H := H) E₁).starProjection f) (y : X) = 0 := by
    have e1 : (f - (restrSub (H := H) E₁).starProjection f) (y : X)
        = ⟪kerFun H (y : X) (1 : ℂ),
            f - (restrSub (H := H) E₁).starProjection f⟫_ℂ := by
      rw [RKHS.kerFun_inner]
      simp
    rw [e1]
    exact h2
  have h5 := h3
  simp only [coe_sub, sub_apply] at h5
  exact (eq_of_sub_eq_zero h5).symm

/-- The functions of the restricted RKHS are exactly the restrictions. -/
lemma range_restr (E₁ : Set X) :
    Set.range (fun g : ↥(restrSub (H := H) E₁) => (⇑g : E₁ → ℂ))
      = {φ : E₁ → ℂ | ∃ f : H, φ = fun x : E₁ => f (x : X)} := by
  ext φ
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨(g : H), funext fun x => (restr_eval E₁ g x).symm⟩
  · rintro ⟨f, rfl⟩
    refine ⟨((⟨(restrSub (H := H) E₁).starProjection f,
        (restrSub (H := H) E₁).starProjection_apply_mem f⟩ :
        ↥(restrSub (H := H) E₁))), ?_⟩
    funext y
    exact (restr_eval E₁ _ y).trans (starProjection_eval E₁ f y)

end Restriction

/-! ## Existence of the restricted RKHS in the universe of `X` -/

section Existence

variable {X : Type u} {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [RKHS ℂ H X ℂ]

/-- The restricted kernel is positive, so the Moore construction gives an RKHS in the
universe of `X`. -/
theorem exists_rkhs_restriction (E₁ : Set X) :
    ∃ (H₁ : Type u) (_ : NormedAddCommGroup H₁) (_ : InnerProductSpace ℂ H₁)
        (_ : CompleteSpace H₁) (_ : RKHS ℂ H₁ E₁ ℂ),
      ∀ x y : E₁, AronszajnRK.Sum.kernelFn H₁ x y = AronszajnRK.Sum.kernelFn H (x : X) (y : X) := by
  classical
  set K' : ↥E₁ → ↥E₁ → ℂ := fun x y => AronszajnRK.Sum.kernelFn H (x : X) (y : X) with hK'
  have hsub : (Matrix.of fun x y : ↥E₁ => K' x y).PosSemidef := by
    have h1 := (posSemidef_kernelFn (H := H)).submatrix (fun x : ↥E₁ => (x : X))
    have h2 : (Matrix.of (AronszajnRK.Sum.kernelFn H)).submatrix (fun x : ↥E₁ => (x : X))
        (fun x : ↥E₁ => (x : X)) = Matrix.of fun x y : ↥E₁ => K' x y := by
      refine Matrix.ext fun x y => ?_
      simp [hK', Matrix.submatrix_apply]
    rwa [h2] at h1
  have hKop : Matrix.PosSemidef (Matrix.of fun x y : ↥E₁ =>
      MooreAux.toOp (AronszajnRK.Sum.kernelFn H (x : X) (y : X))) :=
    MooreAux.posSemidef_toOp _ hsub
  haveI : Fact (Matrix.of fun x y : ↥E₁ =>
      MooreAux.toOp (AronszajnRK.Sum.kernelFn H (x : X) (y : X))).PosSemidef := ⟨hKop⟩
  refine ⟨RKHS.OfKernel (Matrix.of fun x y : ↥E₁ =>
      MooreAux.toOp (AronszajnRK.Sum.kernelFn H (x : X) (y : X))),
    inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro x y
  show (RKHS.kernel (RKHS.OfKernel (Matrix.of fun x y : ↥E₁ =>
      MooreAux.toOp (AronszajnRK.Sum.kernelFn H (x : X) (y : X)))) x y) 1
      = AronszajnRK.Sum.kernelFn H (x : X) (y : X)
  rw [RKHS.OfKernel.kernel_ofKernel]
  simp [MooreAux.toOp_apply]

end Existence

/-! # The theorem -/

/-- **Restriction theorem** (Aronszajn, *Theory of Reproducing Kernels*, §5, Theorem). -/
theorem solution {X : Type u} (H : Type v) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ] (E₁ : Set X) :
    (∃ (H₁ : Type u) (_ : NormedAddCommGroup H₁) (_ : InnerProductSpace ℂ H₁)
        (_ : CompleteSpace H₁) (_ : RKHS ℂ H₁ E₁ ℂ),
        ∀ x y : E₁, AronszajnRK.Product.kernelFn H₁ x y = AronszajnRK.Product.kernelFn H (x : X) (y : X)) ∧
    ∀ (H₁ : Type w) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
      [RKHS ℂ H₁ E₁ ℂ], (∀ x y : E₁, AronszajnRK.Product.kernelFn H₁ x y = AronszajnRK.Product.kernelFn H (x : X) (y : X)) →
      Set.range (fun f₁ : H₁ => (⇑f₁ : E₁ → ℂ)) =
          {φ : E₁ → ℂ | ∃ f : H, φ = fun x : E₁ => f (x : X)} ∧
      ∀ f₁ : H₁, IsLeast
        {r : ℝ | ∃ f : H, (fun x : E₁ => f (x : X)) = (⇑f₁ : E₁ → ℂ) ∧ r = ‖f‖} ‖f₁‖ := by
  constructor
  · exact exists_rkhs_restriction E₁
  · intro H₁ _ _ _ _ hker
    -- identify H₁ with the restricted subspace via Moore uniqueness
    have hk : AronszajnRK.Sum.kernelFn H₁
        = AronszajnRK.Sum.kernelFn (H := ↥(restrSub (H := H) E₁)) := by
      funext x y
      have h1 : AronszajnRK.Sum.kernelFn H₁ x y
          = AronszajnRK.Sum.kernelFn H (x : X) (y : X) := hker x y
      rw [h1]
      exact (kernelFn_restr E₁ x y).symm
    obtain ⟨T, hTcont, hTfun, hTiso⟩ :=
      MooreAux.exists_kernel_preserving_isometry hk
    obtain ⟨S, hScont, hSfun, hSiso⟩ :=
      MooreAux.exists_kernel_preserving_isometry hk.symm
    constructor
    · ext φ
      constructor
      · rintro ⟨f₁, rfl⟩
        refine ⟨(T f₁ : H), funext fun x => ?_⟩
        exact ((restr_eval E₁ (T f₁) x).symm.trans (hTfun f₁ x)).symm
      · rintro ⟨f, rfl⟩
        refine ⟨S ((⟨(restrSub (H := H) E₁).starProjection f,
          (restrSub (H := H) E₁).starProjection_apply_mem f⟩ :
          ↥(restrSub (H := H) E₁))), funext fun x => ?_⟩
        exact (hSfun _ x).trans ((restr_eval E₁ _ x).trans (starProjection_eval E₁ f x))
    · intro f₁
      have hfunT : (fun x : E₁ => ((T f₁ : H)) (x : X)) = (⇑f₁ : E₁ → ℂ) := by
        funext x
        exact hTfun f₁ x
      refine ⟨⟨(T f₁ : H), hfunT, ?_⟩, ?_⟩
      · exact (hTiso f₁).symm.trans (Submodule.norm_coe (T f₁)).symm
      · rintro r ⟨f, hfr, rfl⟩
        -- T f₁ is the orthogonal projection of any extension
        have hproj : T f₁
            = ((⟨(restrSub (H := H) E₁).starProjection f,
                (restrSub (H := H) E₁).starProjection_apply_mem f⟩ :
                ↥(restrSub (H := H) E₁))) := by
          refine RKHS.ext (fun x => ?_)
          rw [restr_eval, restr_eval, starProjection_eval]
          exact ((restr_eval E₁ (T f₁) x).symm.trans (hTfun f₁ x)).trans
            (congrFun hfr x).symm
        calc ‖f₁‖ = ‖T f₁‖ := (hTiso f₁).symm
          _ = ‖((restrSub (H := H) E₁).starProjection f)‖ := by
              rw [hproj]
              exact Submodule.norm_coe
                ((⟨(restrSub (H := H) E₁).starProjection f,
                  (restrSub (H := H) E₁).starProjection_apply_mem f⟩ :
                  ↥(restrSub (H := H) E₁)))
          _ ≤ ‖((restrSub (H := H) E₁).starProjection : H →L[ℂ] H)‖ * ‖f‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ 1 * ‖f‖ := by
              refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg f)
              exact (restrSub (H := H) E₁).starProjection_norm_le
          _ = ‖f‖ := by ring
