-- Prove2me | solution 2 for AronszajnRK.Sum.disjoint_sum
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T10:13:59.389329+00:00
-- url     : https://prove2.me/submissions/6e71220c-f1d9-41b8-b52d-dc58cadbacb6

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn

universe u v w

-- generous heartbeat budget (the default is tight on the verification server)
set_option maxHeartbeats 2000000

/-!
# The disjoint case of the sum of reproducing kernels (Aronszajn 1950, §6)

When the classes `F₁` and `F₂` have no function besides zero in common:

* the norm in the class `F` with kernel `K₁ + K₂` is given by
  `‖f‖² = ‖f₁‖₁² + ‖f₂‖₂²` for *every* decomposition of `f`; and
* `F₁` and `F₂` realize themselves as complementary closed subspaces of `F` (§1 notion:
  each embeds isometrically, and the subspaces are orthogonal complements) — and conversely,
  any such pair of complementary closed subspaces witnesses disjointness.

The infrastructure is that of the companion `sum_kernel_theorem` submission: the model map
`JmodL : H₀ →ₗᵢ WithLp 2 (H₁ × H₂)` (dense extension of `∑ c_y k_y ↦ (e₁ c, e₂ c)`,
equalizer method) with `Nlin (J f) = fn f`, closed range, and
`(range J)ᗮ ⊆ ker Nlin`. Disjointness makes `ker Nlin` trivial (a pair in the kernel has
`fn p.fst = -fn p.snd`, a common function), hence `(range J)ᗮ = ⊥` and, the range being
complete, `range J = ⊤`: **`J` is a surjective linear isometry**. Part 1 is then direct:
the pair `(f₁, f₂)` is `J f` (identify the preimage by its function), and the `L²`-product
norm is `‖f₁‖² + ‖f₂‖²`. Part 2 takes `S₁ = J⁻¹(ker snd)`, `S₂ = J⁻¹(ker fst)`: closed
(kernels of continuous maps), `S₂ = S₁ᗮ` because a surjective isometry preserves inner
products (`LinearIsometry.inner_map_map`) and `(ker snd)ᗮ = ker fst` in the `L²`-product;
the four embedding conditions come from the preimages of `(f₁, 0)` and `(0, f₂)`.
-/

open Module Matrix
open scoped Matrix InnerProductSpace ComplexOrder

namespace SumAux

open RKHS AronszajnRK.Sum ContinuousLinearMap

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
          = ⟪MooreAux.e H c, MooreAux.e H c⟫_ℂ := by
      rw [MooreAux.inner_e]
      refine Finsupp.sum_congr fun i _ => ?_
      refine Finsupp.sum_congr fun j _ => ?_
      simp only [Matrix.of_apply]
      ring
    rw [hQ, Complex.nonneg_iff]
    exact ⟨inner_self_nonneg (𝕜 := ℂ), (inner_self_im (𝕜 := ℂ) (MooreAux.e H c)).symm⟩

/-! ## Positivity of the sum kernel -/

variable {X : Type u} {H₁ : Type v} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [CompleteSpace H₁] [RKHS ℂ H₁ X ℂ] {H₂ : Type w} [NormedAddCommGroup H₂]
  [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [RKHS ℂ H₂ X ℂ]

/-- The sum of two positive semidefinite matrices is positive semidefinite. -/
lemma posSemidef_add {n : Type*} (A B : Matrix n n ℂ) (hA : A.PosSemidef)
    (hB : B.PosSemidef) : (A + B).PosSemidef := by
  refine ⟨?_, fun t => ?_⟩
  · rw [Matrix.IsHermitian.ext_iff]
    intro i j
    simp only [Matrix.add_apply, star_add]
    rw [hA.1.apply i j, hB.1.apply i j]
  · have h1 : (t.sum fun i ti => t.sum fun j tj =>
        star ti * (A + B) i j * tj)
      = (t.sum fun i ti => t.sum fun j tj => star ti * A i j * tj)
        + (t.sum fun i ti => t.sum fun j tj => star ti * B i j * tj) := by
      simp only [Matrix.add_apply, add_mul, mul_add, Finsupp.sum_add]
    rw [h1]
    exact add_nonneg (hA.2 t) (hB.2 t)

/-- The sum of the two scalar kernels is a positive matrix. -/
lemma posSemidef_Ksum : (Matrix.of (kernelFn H₁ + kernelFn H₂)).PosSemidef := by
  have hAB : Matrix.of (kernelFn H₁ + kernelFn H₂)
      = Matrix.of (kernelFn H₁) + Matrix.of (kernelFn H₂) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  rw [hAB]
  exact posSemidef_add _ _ (posSemidef_kernelFn (H := H₁)) (posSemidef_kernelFn (H := H₂))

/-! ## The pair space and the model map -/

/-- The inner product of a combination of kernel functions with any element. -/
lemma inner_e_left {X : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H X ℂ] (c : X →₀ ℂ) (g : H) :
    ⟪MooreAux.e H c, g⟫_ℂ = c.sum fun y cy => (starRingEnd ℂ) cy * ((g : X → ℂ)) y := by
  rw [MooreAux.e_apply, Finsupp.sum_inner]
  refine Finsupp.sum_congr fun y _ => ?_
  rw [inner_smul_left, kerFun_inner]
  simp

variable {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀] [CompleteSpace H₀]
  [RKHS ℂ H₀ X ℂ]

/-- The pair associated to a combination: `(e H₁ c, e H₂ c)` in the `L²`-product. -/
noncomputable def jpair {X : Type*} (H₁ : Type*) [NormedAddCommGroup H₁]
    [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [RKHS ℂ H₁ X ℂ] (H₂ : Type*)
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    [RKHS ℂ H₂ X ℂ] (c : X →₀ ℂ) : WithLp 2 (H₁ × H₂) :=
  WithLp.toLp 2 (MooreAux.e H₁ c, MooreAux.e H₂ c)

/-- The sum functional on the pair space. -/
noncomputable def Sp : WithLp 2 (H₁ × H₂) → (X → ℂ) :=
  fun p => (p.fst : X → ℂ) + (p.snd : X → ℂ)

/-- Combinations are orthogonal to the kernel of the sum functional. -/
lemma jpair_orth (c : X →₀ ℂ) {p : WithLp 2 (H₁ × H₂)} (hp : Sp p = 0) :
    ⟪jpair H₁ H₂ c, p⟫_ℂ = 0 := by
  simp only [jpair, WithLp.prod_inner_apply, WithLp.ofLp_toLp]
  rw [inner_e_left, inner_e_left]
  have hz : ∀ y : X, (p.fst : X → ℂ) y + (p.snd : X → ℂ) y = 0 := by
    intro y
    have := congrFun hp y
    simpa [Sp] using this
  rw [← Finsupp.sum_add]
  classical
  simp only [Finsupp.sum]
  have hz' : ∀ y : X, (p.ofLp : H₁ × H₂).1 y + (p.ofLp : H₁ × H₂).2 y = 0 := hz
  exact Finset.sum_eq_zero fun y _ => by
    rw [← mul_add, hz' y, mul_zero]

/-- The Gram matrices agree, so `jpair` is norm-preserving on combinations. -/
lemma norm_jpair (hKsum : kernelFn H₀ = kernelFn H₁ + kernelFn H₂) (c : X →₀ ℂ) :
    ‖jpair H₁ H₂ c‖ = ‖MooreAux.e H₀ c‖ := by
  have h3 : ⟪jpair H₁ H₂ c, jpair H₁ H₂ c⟫_ℂ
      = ⟪MooreAux.e H₀ c, MooreAux.e H₀ c⟫_ℂ := by
    simp only [jpair, WithLp.prod_inner_apply, WithLp.ofLp_toLp]
    have e1 := MooreAux.inner_e (H := H₁) (c := c) (d := c)
    have e2 := MooreAux.inner_e (H := H₂) (c := c) (d := c)
    have e0 := MooreAux.inner_e (H := H₀) (c := c) (d := c)
    rw [e1, e2, e0, hKsum]
    simp only [Matrix.of_apply, Pi.add_apply, mul_add, Finsupp.sum_add]
  have h1 : ‖jpair H₁ H₂ c‖ ^ 2
      = RCLike.re ⟪jpair H₁ H₂ c, jpair H₁ H₂ c⟫_ℂ :=
    (inner_self_eq_norm_sq _).symm
  have h2 : ‖MooreAux.e H₀ c‖ ^ 2 = RCLike.re ⟪MooreAux.e H₀ c, MooreAux.e H₀ c⟫_ℂ :=
    (inner_self_eq_norm_sq _).symm
  have hsq : ‖jpair H₁ H₂ c‖ ^ 2 = ‖MooreAux.e H₀ c‖ ^ 2 := by
    rw [h1, h2, h3]
  have hn1 : 0 ≤ ‖jpair H₁ H₂ c‖ := norm_nonneg _
  have hn2 : 0 ≤ ‖MooreAux.e H₀ c‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖jpair H₁ H₂ c‖ - ‖MooreAux.e H₀ c‖), hn1, hn2]

/-- The sum functional as a linear map. -/
noncomputable def Nlin : WithLp 2 (H₁ × H₂) →ₗ[ℂ] (X → ℂ) where
  toFun p := (p.fst : X → ℂ) + (p.snd : X → ℂ)
  map_add' p q := by
    funext x
    have h1 : (p + q).fst = p.fst + q.fst := rfl
    have h2 : (p + q).snd = p.snd + q.snd := rfl
    simp only [h1, h2, Pi.add_apply]
    simp
    ring
  map_smul' r p := by
    funext x
    have h1 : (r • p).fst = r • p.fst := rfl
    have h2 : (r • p).snd = r • p.snd := rfl
    simp only [h1, h2, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    simp
    ring

lemma Sp_eq (p : WithLp 2 (H₁ × H₂)) : Sp p = Nlin p := rfl

/-- The correspondence on the dense range of combinations. -/
noncomputable def corr : Set.range (MooreAux.e H₀) → WithLp 2 (H₁ × H₂) :=
  fun z => jpair H₁ H₂ (Function.invFun (MooreAux.e H₀) z.1)

lemma jpair_sub (c d : X →₀ ℂ) :
    jpair H₁ H₂ (c - d)
      = jpair H₁ H₂ c - jpair H₁ H₂ d := by
  simp only [jpair, map_sub]
  rfl

lemma jpair_zero (hKsum : kernelFn H₀ = kernelFn H₁ + kernelFn H₂) (c : X →₀ ℂ)
    (hz : MooreAux.e H₀ c = 0) : jpair H₁ H₂ c = 0 := by
  have h0 : ‖jpair H₁ H₂ c‖ = 0 := by
    rw [norm_jpair hKsum, hz, norm_zero]
  have h2 : ‖jpair H₁ H₂ c‖ ^ 2 = 0 := by rw [sq, h0, zero_mul]
  have h3 := WithLp.prod_norm_sq_eq_of_L2 (jpair H₁ H₂ c)
  rw [h2] at h3
  have hf : (jpair H₁ H₂ c).fst = 0 := by
    apply (norm_eq_zero (a := (jpair H₁ H₂ c).fst)).mp
    have hn := norm_nonneg ((jpair H₁ H₂ c).fst)
    have hn2 := norm_nonneg ((jpair H₁ H₂ c).snd)
    nlinarith [h3, hn, hn2]
  have hsf : (jpair H₁ H₂ c).snd = 0 := by
    apply (norm_eq_zero (a := (jpair H₁ H₂ c).snd)).mp
    have hn := norm_nonneg ((jpair H₁ H₂ c).fst)
    have hn2 := norm_nonneg ((jpair H₁ H₂ c).snd)
    nlinarith [h3, hn, hn2]
  show WithLp.toLp 2 (MooreAux.e H₁ c, MooreAux.e H₂ c) = 0
  rw [show MooreAux.e H₁ c = 0 from hf, show MooreAux.e H₂ c = 0 from hsf]
  simp

lemma jpair_welldef (hKsum : kernelFn H₀ = kernelFn H₁ + kernelFn H₂) :
    ∀ c c' : X →₀ ℂ, MooreAux.e H₀ c = MooreAux.e H₀ c' →
      jpair H₁ H₂ c = jpair H₁ H₂ c' := by
  intro c c' h
  have hz : MooreAux.e H₀ (c - c') = 0 := by
    rw [map_sub, h, sub_self]
  have h1 : jpair H₁ H₂ (c - c') = 0 := jpair_zero hKsum (c - c') hz
  exact eq_of_sub_eq_zero (by rw [← jpair_sub, h1])

lemma corr_apply (hKsum : kernelFn H₀ = kernelFn H₁ + kernelFn H₂) (c : X →₀ ℂ) :
    (corr (X := X) (H₀ := H₀) (H₁ := H₁) (H₂ := H₂)) ⟨MooreAux.e H₀ c, ⟨c, rfl⟩⟩
      = jpair H₁ H₂ c := by
  simp only [corr]
  exact jpair_welldef hKsum _ _ (Function.invFun_eq (f := MooreAux.e H₀) ⟨c, rfl⟩)

lemma isometry_corr (hKsum : kernelFn H₀ = kernelFn H₁ + kernelFn H₂) :
    Isometry (corr (X := X) (H₀ := H₀) (H₁ := H₁) (H₂ := H₂)) := by
  refine isometry_iff_dist_eq.mpr fun z z' => ?_
  have h5 : corr (X := X) (H₀ := H₀) (H₁ := H₁) (H₂ := H₂) z
      - corr (X := X) (H₀ := H₀) (H₁ := H₁) (H₂ := H₂) z'
      = jpair H₁ H₂ (Function.invFun (MooreAux.e H₀) z.1
          - Function.invFun (MooreAux.e H₀) z'.1) := by
    simp only [corr]
    exact (jpair_sub _ _).symm
  have h6 : MooreAux.e H₀ (Function.invFun (MooreAux.e H₀) z.1
      - Function.invFun (MooreAux.e H₀) z'.1) = z.1 - z'.1 := by
    rw [map_sub, Function.invFun_eq z.2, Function.invFun_eq z'.2]
  have hstep1 : dist (corr (X := X) (H₀ := H₀) (H₁ := H₁) (H₂ := H₂) z)
      (corr (X := X) (H₀ := H₀) (H₁ := H₁) (H₂ := H₂) z')
      = ‖corr (X := X) (H₀ := H₀) (H₁ := H₁) (H₂ := H₂) z
          - corr (X := X) (H₀ := H₀) (H₁ := H₁) (H₂ := H₂) z'‖ :=
    dist_eq_norm _ _
  rw [hstep1, h5, norm_jpair hKsum, h6, Subtype.dist_eq, dist_eq_norm]

/-- The extended model map `J : H₀ → WithLp 2 (H₁ × H₂)`. -/
noncomputable def Jmod (hKsum : kernelFn H₀ = kernelFn H₁ + kernelFn H₂) :
    H₀ → WithLp 2 (H₁ × H₂) :=
  (MooreAux.dense_range_e (H := H₀)).extend
    (corr (X := X) (H₀ := H₀) (H₁ := H₁) (H₂ := H₂))

lemma Jmod_cont (hKsum : kernelFn H₀ = kernelFn H₁ + kernelFn H₂) :
    Continuous (Jmod hKsum) :=
  (Dense.uniformContinuous_extend (MooreAux.dense_range_e (H := H₀))
    (isometry_corr hKsum).uniformContinuous).continuous

lemma Jmod_e (hKsum : kernelFn H₀ = kernelFn H₁ + kernelFn H₂) (c : X →₀ ℂ) :
    Jmod hKsum (MooreAux.e H₀ c) = jpair H₁ H₂ c := by
  have h := Dense.extend_of_ind (MooreAux.dense_range_e (H := H₀))
    (isometry_corr hKsum).uniformContinuous
    (⟨MooreAux.e H₀ c, ⟨c, rfl⟩⟩ : Set.range (MooreAux.e H₀))
  simp only [Subtype.coe_mk] at h
  exact h.trans (corr_apply hKsum c)

/-- `Jmod` preserves norms. -/
lemma Jmod_norm (hKsum : kernelFn H₀ = kernelFn H₁ + kernelFn H₂) (x : H₀) :
    ‖Jmod hKsum x‖ = ‖x‖ := by
  have hg : Continuous (fun x : H₀ => ‖Jmod hKsum x‖) :=
    continuous_norm.comp (Jmod_cont hKsum)
  have hh : Continuous (fun x : H₀ => ‖x‖) := continuous_norm
  have hagree : ∀ c : X →₀ ℂ, (fun x : H₀ => ‖Jmod hKsum x‖) (MooreAux.e H₀ c)
      = (fun x : H₀ => ‖x‖) (MooreAux.e H₀ c) := by
    intro c
    show ‖Jmod hKsum (MooreAux.e H₀ c)‖ = ‖MooreAux.e H₀ c‖
    rw [Jmod_e hKsum c, norm_jpair hKsum]
  exact congrFun (DenseRange.equalizer (MooreAux.dense_range_e (H := H₀)) hg hh
    (funext hagree)) x

/-- The sum of two combinations maps to the sum of the pairs. -/
lemma jpair_add (c d : X →₀ ℂ) :
    jpair H₁ H₂ (c + d) = jpair H₁ H₂ c + jpair H₁ H₂ d := by
  simp only [jpair, map_add]
  rfl

/-- `Jmod` is additive. -/
lemma Jmod_add (hKsum : kernelFn H₀ = kernelFn H₁ + kernelFn H₂) (x y : H₀) :
    Jmod hKsum (x + y) = Jmod hKsum x + Jmod hKsum y := by
  -- first: for combinations in the first argument
  have key : ∀ c : X →₀ ℂ, ∀ y : H₀,
      Jmod hKsum (MooreAux.e H₀ c + y) = Jmod hKsum (MooreAux.e H₀ c) + Jmod hKsum y := by
    intro c y
    have hg : Continuous (fun y : H₀ => Jmod hKsum (MooreAux.e H₀ c + y)) :=
      (Jmod_cont hKsum).comp
        ((continuous_const : Continuous (fun _ : H₀ => (MooreAux.e H₀ c : H₀))).add
          continuous_id)
    have hh : Continuous (fun y : H₀ => Jmod hKsum (MooreAux.e H₀ c) + Jmod hKsum y) :=
      continuous_const.add (Jmod_cont hKsum)
    have hagree : ∀ c' : X →₀ ℂ,
        (fun y : H₀ => Jmod hKsum (MooreAux.e H₀ c + y)) (MooreAux.e H₀ c')
          = (fun y : H₀ => Jmod hKsum (MooreAux.e H₀ c) + Jmod hKsum y)
              (MooreAux.e H₀ c') := by
      intro c'
      show Jmod hKsum (MooreAux.e H₀ c + MooreAux.e H₀ c')
          = Jmod hKsum (MooreAux.e H₀ c) + Jmod hKsum (MooreAux.e H₀ c')
      rw [show MooreAux.e H₀ c + MooreAux.e H₀ c' = MooreAux.e H₀ (c + c') from
        (map_add _ _ _).symm, Jmod_e hKsum (c + c'), Jmod_e hKsum c, Jmod_e hKsum c']
      rw [jpair_add]
    exact congrFun (DenseRange.equalizer (MooreAux.dense_range_e (H := H₀)) hg hh
      (funext hagree)) y
  -- then: equalize over `x` in the dense range
  have hg : Continuous (fun x : H₀ => Jmod hKsum (x + y)) :=
    (Jmod_cont hKsum).comp (continuous_id.add continuous_const)
  have hh : Continuous (fun x : H₀ => Jmod hKsum x + Jmod hKsum y) :=
    (Jmod_cont hKsum).add continuous_const
  have hagree : ∀ c : X →₀ ℂ,
      (fun x : H₀ => Jmod hKsum (x + y)) (MooreAux.e H₀ c)
        = (fun x : H₀ => Jmod hKsum x + Jmod hKsum y) (MooreAux.e H₀ c) :=
    fun c => key c y
  exact congrFun (DenseRange.equalizer (MooreAux.dense_range_e (H := H₀)) hg hh
    (funext hagree)) x

/-- `Jmod` is homogeneous. -/
lemma Jmod_smul (hKsum : kernelFn H₀ = kernelFn H₁ + kernelFn H₂) (r : ℂ) (x : H₀) :
    Jmod hKsum (r • x) = r • Jmod hKsum x := by
  have hg : Continuous (fun x : H₀ => Jmod hKsum (r • x)) :=
    (Jmod_cont hKsum).comp (continuous_const_smul r)
  have hh : Continuous (fun x : H₀ => r • Jmod hKsum x) :=
    (continuous_const_smul r).comp (Jmod_cont hKsum)
  have hagree : ∀ c : X →₀ ℂ,
      (fun x : H₀ => Jmod hKsum (r • x)) (MooreAux.e H₀ c)
        = (fun x : H₀ => r • Jmod hKsum x) (MooreAux.e H₀ c) := by
    intro c
    show Jmod hKsum (r • MooreAux.e H₀ c) = r • Jmod hKsum (MooreAux.e H₀ c)
    rw [show r • MooreAux.e H₀ c = MooreAux.e H₀ (r • c) from (map_smul _ _ _).symm,
      Jmod_e hKsum (r • c), Jmod_e hKsum c, jpair, jpair, map_smul, map_smul]
    rfl
  exact congrFun (DenseRange.equalizer (MooreAux.dense_range_e (H := H₀)) hg hh
    (funext hagree)) x

/-- The model map as a linear isometry. -/
noncomputable def JmodL (hKsum : kernelFn H₀ = kernelFn H₁ + kernelFn H₂) :
    H₀ →ₗᵢ[ℂ] WithLp 2 (H₁ × H₂) where
  toFun := Jmod hKsum
  map_add' := Jmod_add hKsum
  map_smul' := Jmod_smul hKsum
  norm_map' := Jmod_norm hKsum

/-- `Jmod` preserves the function: `f₁ + f₂` of the pair equals the function of the element. -/
lemma Jmod_Nlin (hKsum : kernelFn H₀ = kernelFn H₁ + kernelFn H₂) (x : H₀) :
    Nlin (Jmod hKsum x) = ((x : X → ℂ)) := by
  funext y
  have hg : Continuous (fun x : H₀ => (Nlin (Jmod hKsum x)) y) := by
    have h1 : Continuous (fun x : H₀ => (Jmod hKsum x).fst) :=
      (WithLp.continuous_fst 2 H₁ H₂).comp (Jmod_cont hKsum)
    have h2 : Continuous (fun x : H₀ => (Jmod hKsum x).snd) :=
      (WithLp.continuous_snd 2 H₁ H₂).comp (Jmod_cont hKsum)
    exact ((RKHS.continuous_eval y).comp h1).add ((RKHS.continuous_eval y).comp h2)
  have hh : Continuous (fun x : H₀ => ((x : X → ℂ)) y) := RKHS.continuous_eval y
  have hagree : ∀ c : X →₀ ℂ,
      (fun x : H₀ => (Nlin (Jmod hKsum x)) y) (MooreAux.e H₀ c)
        = (fun x : H₀ => ((x : X → ℂ)) y) (MooreAux.e H₀ c) := by
    intro c
    show (Nlin (Jmod hKsum (MooreAux.e H₀ c))) y = ((MooreAux.e H₀ c : X → ℂ)) y
    rw [Jmod_e hKsum c]
    show (Nlin (jpair H₁ H₂ c)) y = ((MooreAux.e H₀ c : X → ℂ)) y
    have nexp : Nlin (jpair H₁ H₂ c)
        = (MooreAux.e H₁ c : X → ℂ) + (MooreAux.e H₂ c : X → ℂ) := rfl
    rw [nexp, MooreAux.eval_e, hKsum]
    simp only [Pi.add_apply, Finsupp.sum_add, MooreAux.eval_e, mul_add]
  exact congrFun (DenseRange.equalizer (MooreAux.dense_range_e (H := H₀)) hg hh
    (funext hagree)) x

/-- The image of `Jmod` is orthogonal to the kernel of the sum functional. -/
lemma Jmod_orth (hKsum : kernelFn H₀ = kernelFn H₁ + kernelFn H₂) (x : H₀)
    {p : WithLp 2 (H₁ × H₂)} (hp : p ∈ LinearMap.ker Nlin) :
    ⟪Jmod hKsum x, p⟫_ℂ = 0 := by
  have hg : Continuous (fun x : H₀ => ⟪Jmod hKsum x, p⟫_ℂ) := by
    have h1 : Continuous (fun x : H₀ => ⟪p, Jmod hKsum x⟫_ℂ) :=
      ((innerSL ℂ p).continuous).comp (Jmod_cont hKsum)
    have hc : Continuous (fun x : H₀ => star (⟪p, Jmod hKsum x⟫_ℂ)) :=
      Continuous.star h1
    have heq : (fun x : H₀ => ⟪Jmod hKsum x, p⟫_ℂ)
        = fun x : H₀ => star (⟪p, Jmod hKsum x⟫_ℂ) :=
      funext fun x => (inner_conj_symm (Jmod hKsum x) p).symm
    rw [heq]
    exact hc
  have hagree : ∀ c : X →₀ ℂ,
      (fun x : H₀ => ⟪Jmod hKsum x, p⟫_ℂ) (MooreAux.e H₀ c) = (0 : ℂ) := by
    intro c
    show ⟪Jmod hKsum (MooreAux.e H₀ c), p⟫_ℂ = 0
    rw [Jmod_e hKsum c]
    exact jpair_orth c (by rw [Sp_eq]; exact LinearMap.mem_ker.mp hp)
  exact congrFun (DenseRange.equalizer (MooreAux.dense_range_e (H := H₀)) hg
    continuous_const (funext hagree)) x

/-- If `u` pairs to zero with every pair of combinations, its components sum to zero. -/
lemma u_orth_Nlin {u : WithLp 2 (H₁ × H₂)}
    (hu : ∀ c : X →₀ ℂ, ⟪jpair H₁ H₂ c, u⟫_ℂ = 0) : Nlin u = 0 := by
  funext y
  have h1 : ⟪jpair H₁ H₂ (Finsupp.single y (1 : ℂ)), u⟫_ℂ = 0 := hu _
  have h2 : ⟪jpair H₁ H₂ (Finsupp.single y (1 : ℂ)), u⟫_ℂ
      = (Nlin u) y := by
    simp only [jpair, WithLp.prod_inner_apply]
    have g1 := inner_e_left (H := H₁) (c := Finsupp.single y (1 : ℂ)) (g := (u.ofLp : H₁ × H₂).1)
    have g2 := inner_e_left (H := H₂) (c := Finsupp.single y (1 : ℂ)) (g := (u.ofLp : H₁ × H₂).2)
    rw [g1, g2]
    show (Finsupp.single y (1 : ℂ)).sum (fun y' cy' =>
        (starRingEnd ℂ) cy' * ((u.ofLp : H₁ × H₂).1 : X → ℂ) y')
        + (Finsupp.single y (1 : ℂ)).sum (fun y' cy' =>
          (starRingEnd ℂ) cy' * ((u.ofLp : H₁ × H₂).2 : X → ℂ) y')
        = Nlin u y
    simp
    rfl
  rw [h2] at h1
  exact h1

/-- The orthogonal complement of the range is contained in the kernel. -/
lemma range_orth_Nlin (hKsum : kernelFn H₀ = kernelFn H₁ + kernelFn H₂)
    {u : WithLp 2 (H₁ × H₂)}
    (hu : u ∈ (LinearMap.range (JmodL hKsum).toLinearMap)ᗮ) : Nlin u = 0 := by
  refine u_orth_Nlin fun c => ?_
  have h1 : JmodL hKsum (MooreAux.e H₀ c) ∈ LinearMap.range (JmodL hKsum).toLinearMap :=
    LinearMap.mem_range.mpr ⟨_, rfl⟩
  have h2 := Submodule.inner_right_of_mem_orthogonal h1 hu
  rw [← Jmod_e hKsum c]
  exact h2

/-- The first-component projection of the pair space, as a linear map. -/
def WfstL : WithLp 2 (H₁ × H₂) →ₗ[ℂ] H₁ where
  toFun p := p.fst
  map_add' p q := rfl
  map_smul' r p := rfl

/-- The second-component projection of the pair space, as a linear map. -/
def WsndL : WithLp 2 (H₁ × H₂) →ₗ[ℂ] H₂ where
  toFun p := p.snd
  map_add' p q := rfl
  map_smul' r p := rfl

lemma WfstL_apply (p : WithLp 2 (H₁ × H₂)) : WfstL p = p.fst := rfl
lemma WsndL_apply (p : WithLp 2 (H₁ × H₂)) : WsndL p = p.snd := rfl

end SumAux



open SumAux RKHS AronszajnRK.Sum in
/-- **Aronszajn §6, p. 354 — the disjoint case of the sum** (see the docstring of
`disjoint_sum` for the statement). -/
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
  classical
  -- elements with equal functions are equal
  have hfneq : ∀ (g g' : H), ((g : X → ℂ)) = ((g' : X → ℂ)) → g = g' :=
    fun g g' h => RKHS.ext fun x => by rw [h]
  -- the value of the sum functional on a pair
  have hval : ∀ (f₁ : H₁) (f₂ : H₂), Nlin (WithLp.toLp 2 (f₁, f₂))
      = (f₁ : X → ℂ) + (f₂ : X → ℂ) := by
    intro f₁ f₂
    funext y
    show ((WithLp.toLp 2 (f₁, f₂)).fst : X → ℂ) y
        + ((WithLp.toLp 2 (f₁, f₂)).snd : X → ℂ) y
      = (f₁ : X → ℂ) y + (f₂ : X → ℂ) y
    simp
  -- disjointness makes the kernel of the sum functional trivial
  have hkertriv : (Set.range (fun f : H₁ => (f : X → ℂ)) ∩
      Set.range (fun f : H₂ => (f : X → ℂ)) = {0}) →
      ∀ p ∈ LinearMap.ker Nlin, p = (0 : WithLp 2 (H₁ × H₂)) := by
    intro hdis p hp
    have h0 : Nlin p = 0 := LinearMap.mem_ker.mp hp
    have hfst : ((p.fst : X → ℂ)) = 0 := by
      have hmem : (p.fst : X → ℂ) ∈
          Set.range (fun f : H₁ => (f : X → ℂ)) ∩ Set.range (fun f : H₂ => (f : X → ℂ)) := by
        refine ⟨⟨p.fst, rfl⟩, ?_⟩
        refine ⟨-(p.snd), ?_⟩
        have hfn : ((p.fst : X → ℂ)) = -((p.snd : X → ℂ)) := by
          funext y
          have h2 : ((p.fst : X → ℂ)) y + ((p.snd : X → ℂ)) y = 0 := congrFun h0 y
          exact eq_neg_iff_add_eq_zero.mpr h2
        simp [hfn]
      rw [hdis] at hmem
      simpa using hmem
    have hsnd : ((p.snd : X → ℂ)) = 0 := by
      have h1 : ∀ y : X, ((p.snd : X → ℂ)) y = 0 := by
        intro y
        have h2 : ((p.fst : X → ℂ)) y + ((p.snd : X → ℂ)) y = 0 := congrFun h0 y
        rw [congrFun hfst y] at h2
        simpa using h2
      exact funext h1
    have hpfst : p.fst = 0 := RKHS.ext (fun x => by rw [hfst]; simp)
    have hpsnd : p.snd = 0 := RKHS.ext (fun x => by rw [hsnd]; simp)
    have he : p.ofLp = (0, 0) := Prod.ext hpfst hpsnd
    rw [← WithLp.toLp_ofLp 2 p, he]
    simp
  -- the range of the model map is complete
  haveI : CompleteSpace ↥(LinearMap.range (JmodL hK).toLinearMap) := by
    have hiso : Isometry (Jmod hK) := (JmodL hK).isometry
    have hcl : IsClosed (Set.range (Jmod hK)) := hiso.isClosedEmbedding.isClosed_range
    have hc : IsComplete ((LinearMap.range (JmodL hK).toLinearMap :
        Set (WithLp 2 (H₁ × H₂)))) := by
      have heq : ((LinearMap.range (JmodL hK).toLinearMap :
          Set (WithLp 2 (H₁ × H₂)))) = Set.range (Jmod hK) := rfl
      rw [heq]
      exact hcl.isComplete
    exact hc.completeSpace_coe
  -- under disjointness the model map is surjective
  have hsurj : (Set.range (fun f : H₁ => (f : X → ℂ)) ∩
      Set.range (fun f : H₂ => (f : X → ℂ)) = {0}) →
      ∀ p : WithLp 2 (H₁ × H₂), ∃ f : H, (JmodL hK) f = p := by
    intro hdis p
    have hbot : (LinearMap.range (JmodL hK).toLinearMap)ᗮ = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun u hu => ?_
      exact hkertriv hdis u (LinearMap.mem_ker.mpr (range_orth_Nlin hK hu))
    have hsup : (LinearMap.range (JmodL hK).toLinearMap)
        ⊔ (LinearMap.range (JmodL hK).toLinearMap)ᗮ = ⊤ :=
      Submodule.sup_orthogonal_of_hasOrthogonalProjection
    rw [hbot] at hsup
    have htop : (LinearMap.range (JmodL hK).toLinearMap) = ⊤ := by simpa using hsup
    have hmem : p ∈ LinearMap.range (JmodL hK).toLinearMap := by
      rw [htop]; trivial
    exact LinearMap.mem_range.mp hmem
  constructor
  · -- **Part 1**: the norm is the sum for every decomposition
    intro hdis f f₁ f₂ hdecomp
    obtain ⟨f', hf'⟩ := hsurj hdis (WithLp.toLp 2 (f₁, f₂))
    have hfnf : ((f' : X → ℂ)) = ((f : X → ℂ)) := by
      rw [show ((f' : X → ℂ)) = Nlin ((JmodL hK) f') from (Jmod_Nlin hK f').symm, hf',
        hval f₁ f₂, hdecomp]
    have heq : f' = f := hfneq _ _ hfnf
    calc ‖f‖ ^ 2 = ‖f'‖ ^ 2 := by rw [heq]
      _ = ‖(JmodL hK) f'‖ ^ 2 := by rw [(JmodL hK).norm_map]
      _ = ‖WithLp.toLp 2 (f₁, f₂)‖ ^ 2 := by rw [hf']
      _ = ‖f₁‖ ^ 2 + ‖f₂‖ ^ 2 := WithLp.prod_norm_sq_eq_of_L2 _
  · -- **Part 2**: the complementary-subspace characterization
    constructor
    · intro hdis
      -- the two subspaces
      refine ⟨LinearMap.ker (WsndL.comp (JmodL hK).toLinearMap),
        LinearMap.ker (WfstL.comp (JmodL hK).toLinearMap), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- closedness
        have hcont : Continuous (fun f : H => ((JmodL hK) f).snd) :=
          (WithLp.continuous_snd 2 H₁ H₂).comp (Jmod_cont hK)
        have h0 : (LinearMap.ker (WsndL.comp (JmodL hK).toLinearMap) : Set H)
            = (fun f : H => ((JmodL hK) f).snd) ⁻¹' ({0} : Set H₂) := by
          ext f
          simp only [SetLike.mem_coe, Set.mem_preimage, LinearMap.mem_ker, LinearMap.coe_comp,
            Function.comp_apply, WsndL_apply, Set.mem_ofPred_eq]
          rfl
        rw [h0]
        exact IsClosed.preimage hcont isClosed_singleton
      · -- S₂ = S₁ᗮ
        apply Submodule.ext
        intro f
        constructor
        · intro hf g hg
          rw [← (JmodL hK).inner_map_map]
          have h2 : ((JmodL hK) f).ofLp.1 = (0 : H₁) := hf
          have h1 : ((JmodL hK) g).ofLp.2 = (0 : H₂) := hg
          rw [WithLp.prod_inner_apply, h2, h1]
          simp
        · intro hf
          -- pair `f` against the preimages of `(a, 0)`
          have hkey : ∀ a : H₁, ⟪a, ((JmodL hK) f).fst⟫_ℂ = 0 := by
            intro a
            obtain ⟨g, hg⟩ := hsurj hdis (WithLp.toLp 2 (a, 0))
            have hgmem : g ∈ (WsndL.comp (JmodL hK).toLinearMap).ker := by
              refine LinearMap.mem_ker.mpr ?_
              show ((JmodL hK) g).snd = (0 : H₂)
              rw [hg]
              rfl
            have hzero : ⟪g, f⟫_ℂ = 0 := hf g hgmem
            rw [← (JmodL hK).inner_map_map, hg, WithLp.prod_inner_apply,
              WithLp.ofLp_toLp] at hzero
            simpa using hzero
          have hself := hkey ((JmodL hK) f).fst
          have hfst0 : ((JmodL hK) f).fst = 0 :=
            (inner_self_eq_zero (𝕜 := ℂ) (x := ((JmodL hK) f).fst)).mp hself
          -- hence `f ∈ S₂`
          refine LinearMap.mem_ker.mpr ?_
          show ((JmodL hK) f).fst = (0 : H₁)
          exact hfst0
      · -- condition 1
        intro f₁
        obtain ⟨f, hf⟩ := hsurj hdis (WithLp.toLp 2 (f₁, (0 : H₂)))
        have hfc : Jmod hK f = WithLp.toLp 2 (f₁, (0 : H₂)) := hf
        refine ⟨f, ?_, ?_, ?_⟩
        · refine LinearMap.mem_ker.mpr ?_
          show ((JmodL hK) f).snd = (0 : H₂)
          rw [hf]
          rfl
        · rw [← Jmod_Nlin hK f, hfc, hval f₁ (0 : H₂)]
          simp
        · rw [← Jmod_norm hK f, hfc]
          have hsq : ‖WithLp.toLp 2 (f₁, (0 : H₂))‖ ^ 2 = ‖f₁‖ ^ 2 := by
            rw [WithLp.prod_norm_sq_eq_of_L2]
            simp
          have hn1 : 0 ≤ ‖WithLp.toLp 2 (f₁, (0 : H₂))‖ := norm_nonneg _
          have hn2 : 0 ≤ ‖f₁‖ := norm_nonneg _
          nlinarith [sq_nonneg (‖WithLp.toLp 2 (f₁, (0 : H₂))‖ - ‖f₁‖), hn1, hn2]
      · -- condition 2
        intro g hg
        have h1 : ((JmodL hK) g).snd = (0 : H₂) := hg
        refine ⟨((JmodL hK) g).fst, ?_⟩
        rw [← Jmod_Nlin hK g]
        show (((JmodL hK) g).fst : X → ℂ) + (((JmodL hK) g).snd : X → ℂ)
            = ((JmodL hK) g).fst
        rw [h1]
        simp
      · -- condition 3
        intro f₂
        obtain ⟨f, hf⟩ := hsurj hdis (WithLp.toLp 2 ((0 : H₁), f₂))
        have hfc : Jmod hK f = WithLp.toLp 2 ((0 : H₁), f₂) := hf
        refine ⟨f, ?_, ?_, ?_⟩
        · refine LinearMap.mem_ker.mpr ?_
          show ((JmodL hK) f).fst = (0 : H₁)
          rw [hf]
          rfl
        · rw [← Jmod_Nlin hK f, hfc, hval (0 : H₁) f₂]
          simp
        · rw [← Jmod_norm hK f, hfc]
          have hsq : ‖WithLp.toLp 2 ((0 : H₁), f₂)‖ ^ 2 = ‖f₂‖ ^ 2 := by
            rw [WithLp.prod_norm_sq_eq_of_L2]
            simp
          have hn1 : 0 ≤ ‖WithLp.toLp 2 ((0 : H₁), f₂)‖ := norm_nonneg _
          have hn2 : 0 ≤ ‖f₂‖ := norm_nonneg _
          nlinarith [sq_nonneg (‖WithLp.toLp 2 ((0 : H₁), f₂)‖ - ‖f₂‖), hn1, hn2]
      · -- condition 4
        intro g hg
        have h1 : ((JmodL hK) g).fst = (0 : H₁) := hg
        refine ⟨((JmodL hK) g).snd, ?_⟩
        rw [← Jmod_Nlin hK g]
        show (((JmodL hK) g).fst : X → ℂ) + (((JmodL hK) g).snd : X → ℂ)
            = ((JmodL hK) g).snd
        rw [h1]
        simp
    · intro ⟨S₁, S₂, hcl, hS₂, c1, c2, c3, c4⟩
      ext g
      constructor
      · intro hmem
        obtain ⟨hg₁, hg₂⟩ := hmem.1, hmem.2
        obtain ⟨f₁, hf₁⟩ := Set.mem_range.mp hg₁
        obtain ⟨f₂, hf₂⟩ := Set.mem_range.mp hg₂
        beta_reduce at hf₁ hf₂
        obtain ⟨f, hfmem, hffn, _⟩ := c1 f₁
        obtain ⟨f', hf'mem, hf'fn, _⟩ := c3 f₂
        have hff : f = f' := by
          refine hfneq f f' ?_
          rw [hffn, hf'fn, hf₁, ← hf₂]
        have hortho : ⟪f, f'⟫_ℂ = 0 :=
          Submodule.inner_right_of_mem_orthogonal hfmem (by rw [← hS₂]; exact hf'mem)
        rw [hff] at hortho
        have hf0 : f = 0 := by
          have h2 : f' = 0 :=
            (inner_self_eq_zero (𝕜 := ℂ) (x := f')).mp hortho
          rw [h2] at hff
          exact hff
        show g = (0 : X → ℂ)
        rw [← hf₁, ← hffn, hf0]
        simp
      · intro hmem
        rw [Set.mem_singleton_iff] at hmem
        subst hmem
        refine ⟨⟨0, by simp⟩, 0, by simp⟩
