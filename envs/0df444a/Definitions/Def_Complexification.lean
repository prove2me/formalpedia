-- Prove2me | Definitions.Def_Complexification
-- name    : Complexification
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-03T18:40:55.561329+00:00
-- url     : https://prove2.me/theorems/99bf40a2-4b13-48e9-b937-297e8a9671a9
-- title:
--   The Lean 4 theorem `norm_sq` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/Complexification.lean`): generated def bundle for Complexification. See BookProof/Complexification.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/Complexification.lean

import Definitions.Def_ChapterA1
import Mathlib


/-!
# Complexification of a real inner-product space (Chapter A, §A.1 infrastructure)

`FORMALIZATION_ROADMAP.md` records a genuine obstruction for the §A.1 real↔complex
trichotomy (work-package **N1**, Props 11/12): the arguments require a *complex
inner-product* structure on the complexification `Wᶜ = ℂ ⊗_ℝ W` of a real Hilbert
space `W`, which is **not** available in Mathlib (only the *real* inner product on
a complex space, via `InnerProductSpace.complexToReal`, exists).

This file builds that missing infrastructure from scratch.  The complexification
is modelled as pairs `⟨u, v⟩` of vectors of `W`, thought of as `u + i v`, with

* complex scalar multiplication `z • ⟨u, v⟩ = ⟨z.re • u - z.im • v, z.re • v + z.im • u⟩`;
* the Hermitian inner product (conjugate-linear in the **first** argument, matching
  Mathlib's convention)
  `⟪⟨u₁,v₁⟩, ⟨u₂,v₂⟩⟫ = (⟪u₁,u₂⟫ + ⟪v₁,v₂⟫) + i (⟪u₁,v₂⟫ − ⟪v₁,u₂⟫)`.

We equip `Cx W` with the full `NormedAddCommGroup` + `InnerProductSpace ℂ`
instances (via `InnerProductSpace.Core`), and provide the canonical **conjugation**
`conj : Cx W → Cx W`, `conj ⟨u,v⟩ = ⟨u,-v⟩`, an anti-unitary involution whose fixed
set is the real form `W ↪ Cx W`.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped RealInnerProductSpace
open RCLike

namespace BookProof.Complexification

set_option linter.unusedSectionVars false

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The complexification of a real inner-product space `W`, modelled as pairs
`⟨re, im⟩` thought of as `re + i · im`. -/
structure Cx (W : Type*) where
  /-- Real part of a vector of the complexification. -/
  re : W
  /-- Imaginary part of a vector of the complexification. -/
  im : W

namespace Cx

@[ext] lemma ext {x y : Cx W} (h1 : x.re = y.re) (h2 : x.im = y.im) : x = y := by
  cases x; cases y; simp_all

/-! ### Additive group structure -/

instance : Add (Cx W) := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Zero (Cx W) := ⟨⟨0, 0⟩⟩
instance : Neg (Cx W) := ⟨fun x => ⟨-x.re, -x.im⟩⟩
instance : Sub (Cx W) := ⟨fun x y => ⟨x.re - y.re, x.im - y.im⟩⟩

@[simp] lemma add_re (x y : Cx W) : (x + y).re = x.re + y.re := rfl
@[simp] lemma add_im (x y : Cx W) : (x + y).im = x.im + y.im := rfl
@[simp] lemma zero_re : (0 : Cx W).re = 0 := rfl
@[simp] lemma zero_im : (0 : Cx W).im = 0 := rfl
@[simp] lemma neg_re (x : Cx W) : (-x).re = -x.re := rfl
@[simp] lemma neg_im (x : Cx W) : (-x).im = -x.im := rfl
@[simp] lemma sub_re (x y : Cx W) : (x - y).re = x.re - y.re := rfl
@[simp] lemma sub_im (x y : Cx W) : (x - y).im = x.im - y.im := rfl

instance : AddCommGroup (Cx W) where
  add_assoc a b c := by ext <;> simp [add_assoc]
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp [add_comm]
  neg_add_cancel a := by ext <;> simp
  sub_eq_add_neg a b := by ext <;> simp [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

/-! ### Complex module structure -/

noncomputable instance : SMul ℂ (Cx W) :=
  ⟨fun z x => ⟨z.re • x.re - z.im • x.im, z.re • x.im + z.im • x.re⟩⟩

@[simp] lemma csmul_re (z : ℂ) (x : Cx W) : (z • x).re = z.re • x.re - z.im • x.im := rfl
@[simp] lemma csmul_im (z : ℂ) (x : Cx W) : (z • x).im = z.re • x.im + z.im • x.re := rfl

noncomputable instance : Module ℂ (Cx W) where
  one_smul x := by ext <;> simp
  mul_smul z w x := by
    ext <;> simp [Complex.mul_re, Complex.mul_im, sub_smul, add_smul, smul_sub, smul_add,
      smul_smul] <;> abel
  smul_zero z := by ext <;> simp
  smul_add z x y := by ext <;> simp [smul_add] <;> abel
  add_smul z w x := by ext <;> simp [Complex.add_re, Complex.add_im, add_smul] <;> abel
  zero_smul x := by ext <;> simp

/-! ### Hermitian inner product and the normed/inner-product-space instances -/

/-- The Hermitian inner product on the complexification, conjugate-linear in the
first argument (Mathlib's convention). -/
noncomputable def cxInner (x y : Cx W) : ℂ :=
  ⟨inner ℝ x.re y.re + inner ℝ x.im y.im, inner ℝ x.re y.im - inner ℝ x.im y.re⟩

noncomputable instance : Inner ℂ (Cx W) := ⟨cxInner⟩

@[simp] lemma inner_def (x y : Cx W) : inner ℂ x y = cxInner x y := rfl

noncomputable instance : NormedAddCommGroup (Cx W) :=
  letI core : InnerProductSpace.Core ℂ (Cx W) :=
  { conj_inner_symm x y := by
      simp only [inner_def]
      apply Complex.ext <;> simp only [cxInner, Complex.conj_re, Complex.conj_im]
      · rw [real_inner_comm y.re x.re, real_inner_comm y.im x.im]
      · rw [real_inner_comm y.re x.im, real_inner_comm y.im x.re]; ring
    re_inner_nonneg x := by
      simp only [inner_def]
      have h1 := real_inner_self_nonneg (x := x.re)
      have h2 := real_inner_self_nonneg (x := x.im)
      have : (0 : ℝ) ≤ inner ℝ x.re x.re + inner ℝ x.im x.im := by linarith
      simpa [cxInner] using this
    add_left x y z := by
      simp only [inner_def]
      apply Complex.ext <;>
        simp only [cxInner, add_re, add_im, inner_add_left, Complex.add_re, Complex.add_im] <;> ring
    smul_left x y r := by
      simp only [inner_def]
      apply Complex.ext <;>
        simp only [cxInner, csmul_re, csmul_im, inner_sub_left, inner_add_left,
          real_inner_smul_left, Complex.mul_re, Complex.mul_im, Complex.conj_re,
          Complex.conj_im] <;> ring
    definite x hx := by
      simp only [inner_def] at hx
      have hre : inner ℝ x.re x.re + inner ℝ x.im x.im = 0 := by
        have := congrArg Complex.re hx; simpa [cxInner] using this
      have h1 := real_inner_self_nonneg (x := x.re)
      have h2 := real_inner_self_nonneg (x := x.im)
      have e1 : inner ℝ x.re x.re = 0 := by linarith
      have e2 : inner ℝ x.im x.im = 0 := by linarith
      ext
      · exact inner_self_eq_zero.mp e1
      · exact inner_self_eq_zero.mp e2 }
  core.toNormedAddCommGroup

noncomputable instance : InnerProductSpace ℂ (Cx W) := .ofCore _

/-- Real part of the inner product. -/
lemma inner_re (x y : Cx W) :
    RCLike.re (inner ℂ x y) = inner ℝ x.re y.re + inner ℝ x.im y.im := rfl



/-! ### Real embedding and the action of `i` -/

/-- The canonical embedding of the real form `W ↪ Cx W`, `w ↦ w + i·0`. -/
def ofReal (w : W) : Cx W := ⟨w, 0⟩

@[simp] lemma ofReal_re (w : W) : (ofReal w).re = w := rfl
@[simp] lemma ofReal_im (w : W) : (ofReal w).im = 0 := rfl





/-! ### The canonical conjugation `⟨u,v⟩ ↦ ⟨u,-v⟩` -/

/-- The canonical conjugation as a conjugate-linear equivalence. -/
noncomputable def cxConjLE : Cx W ≃ₗ⋆[ℂ] Cx W where
  toFun x := ⟨x.re, -x.im⟩
  map_add' x y := by ext <;> simp [add_comm]
  map_smul' z x := by
    ext <;> simp [Complex.conj_re, Complex.conj_im, neg_smul, smul_neg, add_comm]
  invFun x := ⟨x.re, -x.im⟩
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp

/-- **Canonical conjugation** of the complexification: the anti-unitary involution
`θ ⟨u,v⟩ = ⟨u,-v⟩` whose fixed set is the real form `ofReal '' W`.  It witnesses
that `Cx W` is C-real over its real form. -/
noncomputable def cxConj : Cx W ≃ₗᵢ⋆[ℂ] Cx W :=
  { cxConjLE with
    norm_map' := by
      intro x
      rw [← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_sq (norm_nonneg (cxConjLE x))]
      congr 1
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
      change RCLike.re (cxInner (cxConjLE x) (cxConjLE x)) = RCLike.re (cxInner x x)
      simp [cxConjLE, cxInner, inner_neg_left, inner_neg_right] }

@[simp] lemma cxConj_apply (x : Cx W) : cxConj x = ⟨x.re, -x.im⟩ := rfl









/-! ### The norm and the complexification of a real operator -/

/-- The squared norm on `Cx W` splits over the real and imaginary parts. -/
lemma norm_sq (x : Cx W) : ‖x‖ ^ 2 = ‖x.re‖ ^ 2 + ‖x.im‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp only [inner_re]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- The real-part projection is `1`-Lipschitz. -/
lemma norm_re_le (x : Cx W) : ‖x.re‖ ≤ ‖x‖ := by
  have h := norm_sq x
  nlinarith [norm_nonneg x, norm_nonneg x.re, norm_nonneg x.im, sq_nonneg ‖x.im‖]

/-- The imaginary-part projection is `1`-Lipschitz. -/
lemma norm_im_le (x : Cx W) : ‖x.im‖ ≤ ‖x‖ := by
  have h := norm_sq x
  nlinarith [norm_nonneg x, norm_nonneg x.re, norm_nonneg x.im, sq_nonneg ‖x.re‖]

/-- The complexification of a real linear map `m`, acting coordinatewise
`⟨u,v⟩ ↦ ⟨m u, m v⟩`, as a `ℂ`-linear map. -/
noncomputable def cxMapₗ (m : W →ₗ[ℝ] W) : Cx W →ₗ[ℂ] Cx W where
  toFun x := ⟨m x.re, m x.im⟩
  map_add' x y := by ext <;> simp
  map_smul' z x := by ext <;> simp [map_sub, map_add]

@[simp] lemma cxMapₗ_re (m : W →ₗ[ℝ] W) (x : Cx W) : (cxMapₗ m x).re = m x.re := rfl
@[simp] lemma cxMapₗ_im (m : W →ₗ[ℝ] W) (x : Cx W) : (cxMapₗ m x).im = m x.im := rfl

/-- The complexification of a real *bounded* operator, as a bounded `ℂ`-linear
operator on `Cx W` (with the same operator-norm bound). -/
noncomputable def cxMap (m : W →L[ℝ] W) : Cx W →L[ℂ] Cx W :=
  LinearMap.mkContinuous (cxMapₗ (m : W →ₗ[ℝ] W)) ‖m‖ (fun x => by
    rw [← Real.sqrt_sq (norm_nonneg (cxMapₗ (m : W →ₗ[ℝ] W) x)),
        show ‖m‖ * ‖x‖ = Real.sqrt ((‖m‖ * ‖x‖) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    rw [norm_sq, mul_pow, norm_sq, cxMapₗ_re, cxMapₗ_im]
    simp only [ContinuousLinearMap.coe_coe]
    have h1 : ‖m x.re‖ ^ 2 ≤ ‖m‖ ^ 2 * ‖x.re‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (m.le_opNorm x.re) 2
    have h2 : ‖m x.im‖ ^ 2 ≤ ‖m‖ ^ 2 * ‖x.im‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (m.le_opNorm x.im) 2
    nlinarith [h1, h2])

@[simp] lemma cxMap_apply (m : W →L[ℝ] W) (x : Cx W) : cxMap m x = ⟨m x.re, m x.im⟩ := rfl

/-- Complexification preserves the identity. -/
@[simp] lemma cxMap_one : cxMap (1 : W →L[ℝ] W) = 1 := by
  ext x <;> simp







/-! ### Completeness -/

/-
`Cx W` is a complete space (hence a complex Hilbert space) whenever `W` is:
the coordinate projections are `1`-Lipschitz, so a Cauchy sequence has Cauchy
coordinates, which converge in `W` and recombine to a limit in `Cx W`.
-/
instance [CompleteSpace W] : CompleteSpace (Cx W) := by
  refine Metric.complete_of_cauchySeq_tendsto ?_
  intro u hu
  obtain ⟨a, ha⟩ : ∃ a : W, Filter.Tendsto (fun n => (u n).re) Filter.atTop (nhds a) := by
    refine cauchySeq_tendsto_of_complete ?_
    rw [Metric.cauchySeq_iff] at hu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have h_dist : dist (u m).re (u n).re ≤ dist (u m) (u n) := by
      convert norm_re_le (u m - u n) using 1 <;> simp [dist_eq_norm]
    exact lt_of_le_of_lt h_dist (hN m hm n hn)
  obtain ⟨b, hb⟩ : ∃ b : W, Filter.Tendsto (fun n => (u n).im) Filter.atTop (nhds b) := by
    refine cauchySeq_tendsto_of_complete ?_
    rw [Metric.cauchySeq_iff] at hu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have h_dist : dist (u m).im (u n).im ≤ dist (u m) (u n) := by
      convert norm_im_le (u m - u n) using 1 <;> simp [dist_eq_norm]
    exact lt_of_le_of_lt h_dist (hN m hm n hn)
  refine ⟨⟨a, b⟩, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero] at *
  convert (ha.pow 2).add (hb.pow 2) |>.sqrt using 2 with n
  · rw [← Real.sqrt_sq (norm_nonneg _), norm_sq]; aesop
  · norm_num

end Cx

/-! ## Connection to the `System` framework: complexification is C-real -/

open BookProof.ChapterA in
/-- The complexification of a real system `(M, W)`, as a complex system on
`Cx W` obtained by complexifying every operator. -/
noncomputable def cxSystem [CompleteSpace W] (M : System ℝ W) : System ℂ (Cx W) :=
  ⟨(fun m => Cx.cxMap m) '' M.ops⟩



end BookProof.Complexification


