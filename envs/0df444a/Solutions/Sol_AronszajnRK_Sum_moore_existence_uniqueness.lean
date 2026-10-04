-- Prove2me | solution 1 for AronszajnRK.Sum.moore_existence_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T06:34:37.20311+00:00
-- url     : https://prove2.me/submissions/a9008c05-aa20-4ac4-a34c-d4e63822d051

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn

universe u v w

open scoped ComplexOrder

/-! # Moore's theorem (existence and uniqueness)

We prove Moore's theorem: a positive matrix `K` on a set `X` is the scalar reproducing
kernel of exactly one Hilbert space of functions (same functions, same norms).

* Existence: embed scalars as operators `toOp c : z ↦ c * z` on `ℂ`; the operator matrix
  `toOp ∘ K` is positive semidefinite whenever `K` is, and `RKHS.OfKernel` produces the RKHS.
* Uniqueness: the kernel functions `k y = kerFun H y 1` span a dense subspace, and the
  Gram matrices of two spaces with the same scalar kernel agree, so the linear maps
  `e : (X →₀ ℂ) →ₗ H` sending a finitely supported family to the corresponding combination
  of kernel functions are norm-preserving for both spaces. The induced isometry between the
  dense spans extends (by `Dense.extend`) to a linear isometry preserving all functions. -/

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

/-! # The theorem -/

/-- **Moore's theorem** (Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68
(1950), §2 (4)): to every positive matrix `K(x, y)` there corresponds one and only one class of
functions with a uniquely determined quadratic form in it, forming a Hilbert space and admitting
`K(x, y)` as a reproducing kernel. -/
theorem solution {X : Type u} (K : X → X → ℂ)
    (hK : (Matrix.of K).PosSemidef) :
    (∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
        (_ : RKHS ℂ H X ℂ), AronszajnRK.Sum.kernelFn H = K) ∧
    ∀ (H₁ : Type v) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
      [RKHS ℂ H₁ X ℂ] (H₂ : Type w) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
      [CompleteSpace H₂] [RKHS ℂ H₂ X ℂ],
      AronszajnRK.Sum.kernelFn H₁ = K → AronszajnRK.Sum.kernelFn H₂ = K →
        Set.range (fun f : H₁ => (f : X → ℂ)) = Set.range (fun f : H₂ => (f : X → ℂ)) ∧
        ∀ (f₁ : H₁) (f₂ : H₂), (f₁ : X → ℂ) = (f₂ : X → ℂ) → ‖f₁‖ = ‖f₂‖ := by
  refine ⟨MooreAux.exists_rkhs_of_posSemidef K hK, ?_⟩
  intro H₁ _ _ _ _ H₂ _ _ _ _ h1 h2
  exact MooreAux.moore_uniqueness (by rw [h1, h2])
