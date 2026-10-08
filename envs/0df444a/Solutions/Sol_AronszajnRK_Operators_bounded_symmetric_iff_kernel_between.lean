-- Prove2me | solution 1 for AronszajnRK.Operators.bounded_symmetric_iff_kernel_between
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T08:55:52.175148+00:00
-- url     : https://prove2.me/submissions/d0225dac-245e-460f-ba2d-d5532e1c6d5e

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn
import Definitions.Def_AronszajnRK_Operators_opKernel
import Definitions.Def_AronszajnRK_Limits_KernelLE

set_option autoImplicit false

open scoped InnerProductSpace ComplexOrder
open ComplexConjugate

namespace AronszajnOpAux

section form
variable {X : Type*}

/-- The finite sesquilinear form of a kernel. -/
def Fm (A : X → X → ℂ) (ξ η : X →₀ ℂ) : ℂ :=
  ξ.sum fun i a => η.sum fun j b => star a * A i j * b

lemma Fm_add_right (A : X → X → ℂ) (ξ η η' : X →₀ ℂ) :
    Fm A ξ (η + η') = Fm A ξ η + Fm A ξ η' := by
  unfold Fm
  rw [← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro i _
  rw [Finsupp.sum_add_index'] <;> intros <;> ring

lemma Fm_smul_right (A : X → X → ℂ) (ξ η : X →₀ ℂ) (c : ℂ) :
    Fm A ξ (c • η) = c * Fm A ξ η := by
  unfold Fm
  rw [Finsupp.mul_sum]
  apply Finsupp.sum_congr
  intro i _
  rw [Finsupp.sum_smul_index (by intro; ring), Finsupp.mul_sum]
  apply Finsupp.sum_congr
  intro j _
  ring

lemma Fm_add_left (A : X → X → ℂ) (ξ ξ' η : X →₀ ℂ) :
    Fm A (ξ + ξ') η = Fm A ξ η + Fm A ξ' η := by
  unfold Fm
  rw [Finsupp.sum_add_index']
  · intro i
    simp
  · intro i a b
    rw [← Finsupp.sum_add]
    apply Finsupp.sum_congr
    intro j _
    simp only [star_add]
    ring

lemma Fm_smul_left (A : X → X → ℂ) (ξ η : X →₀ ℂ) (c : ℂ) :
    Fm A (c • ξ) η = conj c * Fm A ξ η := by
  unfold Fm
  rw [Finsupp.sum_smul_index (by intro; simp), Finsupp.mul_sum]
  apply Finsupp.sum_congr
  intro i _
  rw [Finsupp.mul_sum]
  apply Finsupp.sum_congr
  intro j _
  simp only [star_mul']
  rw [Complex.star_def]
  ring

lemma Fm_add_kernel (A B : X → X → ℂ) (ξ η : X →₀ ℂ) :
    Fm (fun i j => A i j + B i j) ξ η = Fm A ξ η + Fm B ξ η := by
  unfold Fm
  rw [← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro i _
  rw [← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro j _
  ring

lemma Fm_smul_kernel (A : X → X → ℂ) (c : ℂ) (ξ η : X →₀ ℂ) :
    Fm (fun i j => c * A i j) ξ η = c * Fm A ξ η := by
  unfold Fm
  rw [Finsupp.mul_sum]
  apply Finsupp.sum_congr
  intro i _
  rw [Finsupp.mul_sum]
  apply Finsupp.sum_congr
  intro j _
  ring

lemma Fm_congr {A B : X → X → ℂ} (h : ∀ i j, A i j = B i j) (ξ η : X →₀ ℂ) :
    Fm A ξ η = Fm B ξ η := by
  have : A = B := funext fun i => funext fun j => h i j
  rw [this]

lemma Fm_conj (A : X → X → ℂ) (hA : ∀ i j, star (A j i) = A i j) (ξ η : X →₀ ℂ) :
    conj (Fm A η ξ) = Fm A ξ η := by
  unfold Fm
  rw [Finsupp.sum_comm]
  simp only [map_finsuppSum]
  apply Finsupp.sum_congr
  intro i _
  apply Finsupp.sum_congr
  intro j _
  rw [← hA i j]
  simp only [map_mul, Complex.star_def, Complex.conj_conj]
  ring

lemma Fm_single (A : X → X → ℂ) (x y : X) :
    Fm A (Finsupp.single x 1) (Finsupp.single y 1) = A x y := by
  simp [Fm]

lemma Fm_cs (P : X → X → ℂ) (hP : ∀ i j, star (P j i) = P i j)
    (hpos : ∀ ξ, 0 ≤ (Fm P ξ ξ).re) (ξ η : X →₀ ℂ) :
    ‖Fm P ξ η‖ * ‖Fm P η ξ‖ ≤ (Fm P ξ ξ).re * (Fm P η η).re := by
  letI c : PreInnerProductSpace.Core ℂ (X →₀ ℂ) :=
    { inner := Fm P
      conj_inner_symm := fun x y => Fm_conj P hP x y
      re_inner_nonneg := hpos
      add_left := fun x y z => Fm_add_left P x y z
      smul_left := fun x y r => Fm_smul_left P x y r }
  exact InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) ξ η

end form

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

/-- The synthesis map. -/
noncomputable abbrev T : (X →₀ ℂ) →ₗ[ℂ] H :=
  Finsupp.linearCombination ℂ (fun x : X => RKHS.kerFun H x (1 : ℂ))

lemma T_dense : DenseRange (T (X := X) H) := fun f => dense_lc H f

lemma T_single (x : X) : T H (Finsupp.single x 1) = RKHS.kerFun H x (1 : ℂ) := by
  simp [T]

lemma Fm_inner (L : H →L[ℂ] H) (ξ η : X →₀ ℂ) :
    Fm (fun i j => inner ℂ (L (RKHS.kerFun H i (1 : ℂ))) (RKHS.kerFun H j (1 : ℂ))) ξ η =
      inner ℂ (L (T H ξ)) (T H η) := by
  simp only [T, Finsupp.linearCombination_apply, map_finsuppSum, map_smul, Finsupp.sum_inner,
    Finsupp.inner_sum, inner_smul_left, inner_smul_right, Fm]
  rw [Finsupp.sum_comm]
  apply Finsupp.sum_congr
  intro i _
  rw [Finsupp.mul_sum]
  apply Finsupp.sum_congr
  intro j _
  rw [Complex.star_def]
  ring

lemma Fm_K (ξ η : X →₀ ℂ) :
    Fm (AronszajnRK.Sum.kernelFn H) ξ η = inner ℂ (T H ξ) (T H η) := by
  have := Fm_inner H (ContinuousLinearMap.id ℂ H) ξ η
  simp only [ContinuousLinearMap.id_apply, gram] at this
  exact this

lemma Fm_K_self (ξ : X →₀ ℂ) :
    Fm (AronszajnRK.Sum.kernelFn H) ξ ξ = ((‖T H ξ‖ ^ 2 : ℝ) : ℂ) := by
  rw [Fm_K, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

lemma opKernel_eq (L : H →L[ℂ] H) (x y : X) :
    AronszajnRK.Operators.opKernel L x y =
      inner ℂ (L (RKHS.kerFun H x (1 : ℂ))) (RKHS.kerFun H y (1 : ℂ)) := by
  unfold AronszajnRK.Operators.opKernel
  rw [← eval_inner, ContinuousLinearMap.adjoint_inner_right]

lemma K_herm (i j : X) :
    star (AronszajnRK.Sum.kernelFn H j i) = AronszajnRK.Sum.kernelFn H i j := by
  rw [← gram, ← gram]
  exact inner_conj_symm _ _

end rk

lemma kernelLE_iff {X : Type*} (A B : X → X → ℂ) :
    AronszajnRK.Limits.KernelLE A B ↔
      (∀ i j, star (B j i - A j i) = B i j - A i j) ∧
        ∀ ξ, 0 ≤ Fm (fun i j => B i j - A i j) ξ ξ := by
  unfold AronszajnRK.Limits.KernelLE Matrix.PosSemidef
  rw [Matrix.IsHermitian.ext_iff]
  simp only [Matrix.sub_apply, Matrix.of_apply]
  rfl


section construct
variable {X : Type*} (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [RKHS ℂ H X ℂ]

/-- Row functional of the form. -/
noncomputable def phi (Λ : X → X → ℂ) (η : X →₀ ℂ) : (X →₀ ℂ) →ₗ[ℂ] ℂ where
  toFun := Fm Λ η
  map_add' := Fm_add_right Λ η
  map_smul' c ξ := by rw [Fm_smul_right]; rfl

/-- Its bounded extension. -/
noncomputable def Phi (Λ : X → X → ℂ) (η : X →₀ ℂ) : H →L[ℂ] ℂ :=
  (phi Λ η).extendOfNorm (T H)

/-- The Riesz vector. -/
noncomputable def vec (Λ : X → X → ℂ) (η : X →₀ ℂ) : H :=
  (InnerProductSpace.toDual ℂ H).symm (Phi H Λ η)

variable {H}

lemma vec_inner {Λ : X → X → ℂ} {C : ℝ}
    (hb : ∀ η ξ, ‖Fm Λ η ξ‖ ≤ C * ‖T H η‖ * ‖T H ξ‖)
    (η ξ : X →₀ ℂ) : ⟪vec H Λ η, T H ξ⟫_ℂ = Fm Λ η ξ := by
  rw [vec, InnerProductSpace.toDual_symm_apply, Phi,
    LinearMap.extendOfNorm_eq (T_dense H) ⟨C * ‖T H η‖, fun ξ => hb η ξ⟩ ξ]
  rfl

lemma vec_norm {Λ : X → X → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ η ξ, ‖Fm Λ η ξ‖ ≤ C * ‖T H η‖ * ‖T H ξ‖)
    (η : X →₀ ℂ) : ‖vec H Λ η‖ ≤ C * ‖T H η‖ := by
  rw [vec, LinearIsometryEquiv.norm_map, Phi]
  exact LinearMap.opNorm_extendOfNorm_le (T_dense H) (mul_nonneg hC (norm_nonneg _))
    (fun ξ => hb η ξ)

lemma ext_T {a b : H} (h : ∀ ξ : X →₀ ℂ, ⟪a, T H ξ⟫_ℂ = ⟪b, T H ξ⟫_ℂ) : a = b := by
  refine ext_inner_right ℂ fun w => ?_
  exact (T_dense H).induction_on (p := fun w => ⟪a, w⟫_ℂ = ⟪b, w⟫_ℂ) w
    (isClosed_eq (by fun_prop) (by fun_prop)) h

lemma construct (Λ P Q : X → X → ℂ) (m M : ℝ) (hΛh : ∀ i j, star (Λ j i) = Λ i j)
    (hPh : ∀ i j, star (P j i) = P i j)
    (hP : ∀ ξ, 0 ≤ (Fm P ξ ξ).re) (hQ : ∀ ξ, 0 ≤ (Fm Q ξ ξ).re)
    (hdP : ∀ ξ η, Fm Λ ξ η = (m : ℂ) * Fm (AronszajnRK.Sum.kernelFn H) ξ η + Fm P ξ η)
    (hdQ : ∀ ξ, Fm Λ ξ ξ = (M : ℂ) * Fm (AronszajnRK.Sum.kernelFn H) ξ ξ - Fm Q ξ ξ) :
    ∃ L : H →L[ℂ] H, IsSelfAdjoint L ∧ AronszajnRK.Operators.opKernel L = Λ ∧
        ∀ f : H, m * ‖f‖ ^ 2 ≤ RCLike.re ⟪f, L f⟫_ℂ ∧ RCLike.re ⟪f, L f⟫_ℂ ≤ M * ‖f‖ ^ 2 := by
  have reP : ∀ ξ, (Fm Λ ξ ξ).re = m * ‖T H ξ‖ ^ 2 + (Fm P ξ ξ).re := by
    intro ξ
    have := congrArg Complex.re (hdP ξ ξ)
    rwa [Fm_K_self, Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re] at this
  have reQ : ∀ ξ, (Fm Λ ξ ξ).re = M * ‖T H ξ‖ ^ 2 - (Fm Q ξ ξ).re := by
    intro ξ
    have := congrArg Complex.re (hdQ ξ)
    rwa [Fm_K_self, Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re] at this
  have hPle : ∀ ξ, (Fm P ξ ξ).re ≤ (M - m) * ‖T H ξ‖ ^ 2 := by
    intro ξ
    have a1 := reP ξ
    have a2 := reQ ξ
    have a3 := hQ ξ
    nlinarith
  have hPb : ∀ η ξ, ‖Fm P η ξ‖ ≤ |M - m| * ‖T H η‖ * ‖T H ξ‖ := by
    intro η ξ
    have cs := Fm_cs P hPh hP η ξ
    have hsw : ‖Fm P ξ η‖ = ‖Fm P η ξ‖ := by
      rw [← Fm_conj P hPh ξ η, Complex.norm_conj]
    rw [hsw] at cs
    have h1 := hPle η
    have h2 := hPle ξ
    have h3 := hP η
    have h4 := hP ξ
    have hprod : (Fm P η η).re * (Fm P ξ ξ).re ≤
        ((M - m) * ‖T H η‖ ^ 2) * ((M - m) * ‖T H ξ‖ ^ 2) :=
      mul_le_mul h1 h2 h4 (le_trans h3 h1)
    have hsq : ‖Fm P η ξ‖ ^ 2 ≤ (|M - m| * ‖T H η‖ * ‖T H ξ‖) ^ 2 := by
      have e : (|M - m| * ‖T H η‖ * ‖T H ξ‖) ^ 2 =
          ((M - m) * ‖T H η‖ ^ 2) * ((M - m) * ‖T H ξ‖ ^ 2) := by
        rw [mul_pow, mul_pow, sq_abs]; ring
      rw [e, sq]
      linarith
    have hnn : 0 ≤ |M - m| * ‖T H η‖ * ‖T H ξ‖ := by positivity
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hnn two_ne_zero).mp hsq
  obtain ⟨C, hC, hb⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ η ξ, ‖Fm Λ η ξ‖ ≤ C * ‖T H η‖ * ‖T H ξ‖ := by
    refine ⟨|m| + |M - m|, by positivity, fun η ξ => ?_⟩
    rw [hdP, Fm_K]
    calc ‖(m : ℂ) * ⟪T H η, T H ξ⟫_ℂ + Fm P η ξ‖
        ≤ ‖(m : ℂ) * ⟪T H η, T H ξ⟫_ℂ‖ + ‖Fm P η ξ‖ := norm_add_le _ _
      _ ≤ |m| * (‖T H η‖ * ‖T H ξ‖) + |M - m| * ‖T H η‖ * ‖T H ξ‖ := by
          refine add_le_add ?_ (hPb η ξ)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (abs_nonneg _)
      _ = (|m| + |M - m|) * ‖T H η‖ * ‖T H ξ‖ := by ring
  have hadd : ∀ η η' : X →₀ ℂ, vec H Λ (η + η') = vec H Λ η + vec H Λ η' := by
    intro η η'
    refine ext_T fun ξ => ?_
    rw [inner_add_left, vec_inner hb, vec_inner hb, vec_inner hb, Fm_add_left]
  have hsmul : ∀ (c : ℂ) (η : X →₀ ℂ), vec H Λ (c • η) = c • vec H Λ η := by
    intro c η
    refine ext_T fun ξ => ?_
    rw [inner_smul_left, vec_inner hb, vec_inner hb, Fm_smul_left]
  let V : (X →₀ ℂ) →ₗ[ℂ] H := IsLinearMap.mk' (vec H Λ) ⟨hadd, hsmul⟩
  have hVb : ∀ η, ‖V η‖ ≤ C * ‖T H η‖ := fun η => vec_norm hC hb η
  let L : H →L[ℂ] H := V.extendOfNorm (T H)
  have hLT : ∀ η, L (T H η) = vec H Λ η := fun η =>
    LinearMap.extendOfNorm_eq (T_dense H) ⟨C, hVb⟩ η
  have hkey : ∀ η ξ, ⟪L (T H η), T H ξ⟫_ℂ = Fm Λ η ξ := by
    intro η ξ
    rw [hLT, vec_inner hb]
  refine ⟨L, ?_, ?_, ?_⟩
  · rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro a b
    simp only [ContinuousLinearMap.coe_coe]
    refine (T_dense H).induction_on₂ (p := fun a b => ⟪L a, b⟫_ℂ = ⟪a, L b⟫_ℂ)
      (isClosed_eq (by fun_prop) (by fun_prop)) (fun η ξ => ?_) a b
    show ⟪L (T H η), T H ξ⟫_ℂ = ⟪T H η, L (T H ξ)⟫_ℂ
    rw [hkey, ← inner_conj_symm (T H η), hkey, Fm_conj Λ hΛh η ξ]
  · funext x y
    rw [opKernel_eq, ← T_single H x, ← T_single H y, hkey, Fm_single]
  · intro f
    have hre : ∀ ξ, RCLike.re ⟪T H ξ, L (T H ξ)⟫_ℂ = (Fm Λ ξ ξ).re := by
      intro ξ
      rw [← inner_conj_symm, hkey]
      simp
    constructor
    · refine (T_dense H).induction_on (p := fun f => m * ‖f‖ ^ 2 ≤ RCLike.re ⟪f, L f⟫_ℂ) f
        (isClosed_le (by fun_prop) (by fun_prop)) (fun ξ => ?_)
      show m * ‖T H ξ‖ ^ 2 ≤ RCLike.re ⟪T H ξ, L (T H ξ)⟫_ℂ
      rw [hre, reP]
      linarith [hP ξ]
    · refine (T_dense H).induction_on (p := fun f => RCLike.re ⟪f, L f⟫_ℂ ≤ M * ‖f‖ ^ 2) f
        (isClosed_le (by fun_prop) (by fun_prop)) (fun ξ => ?_)
      show RCLike.re ⟪T H ξ, L (T H ξ)⟫_ℂ ≤ M * ‖T H ξ‖ ^ 2
      rw [hre, reQ]
      linarith [hQ ξ]

end construct

open AronszajnRK.Operators in
theorem main_thm {H : Type*} {X : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    (Λ : X → X → ℂ) (hΛ : ∀ x y : X, Λ x y = conj (Λ y x)) (m M : ℝ) :
    (∃ L : H →L[ℂ] H, IsSelfAdjoint L ∧ opKernel L = Λ ∧
        ∀ f : H, m * ‖f‖ ^ 2 ≤ RCLike.re ⟪f, L f⟫_ℂ ∧ RCLike.re ⟪f, L f⟫_ℂ ≤ M * ‖f‖ ^ 2) ↔
      (AronszajnRK.Limits.KernelLE (fun x y => (m : ℂ) * AronszajnRK.Sum.kernelFn H x y) Λ ∧
        AronszajnRK.Limits.KernelLE Λ (fun x y => (M : ℂ) * AronszajnRK.Sum.kernelFn H x y)) := by
  have hΛh : ∀ i j, star (Λ j i) = Λ i j := fun i j => by rw [hΛ i j]; rfl
  have herm1 : ∀ i j, star (Λ j i - (m : ℂ) * AronszajnRK.Sum.kernelFn H j i) =
      Λ i j - (m : ℂ) * AronszajnRK.Sum.kernelFn H i j := by
    intro i j
    rw [star_sub, star_mul', hΛh, K_herm H, Complex.star_def, Complex.conj_ofReal]
  have herm2 : ∀ i j, star ((M : ℂ) * AronszajnRK.Sum.kernelFn H j i - Λ j i) =
      (M : ℂ) * AronszajnRK.Sum.kernelFn H i j - Λ i j := by
    intro i j
    rw [star_sub, star_mul', hΛh, K_herm H, Complex.star_def, Complex.conj_ofReal]
  have decomp1 : ∀ ξ η, Fm Λ ξ η = (m : ℂ) * Fm (AronszajnRK.Sum.kernelFn H) ξ η +
      Fm (fun i j => Λ i j - (m : ℂ) * AronszajnRK.Sum.kernelFn H i j) ξ η := by
    intro ξ η
    rw [← Fm_smul_kernel, ← Fm_add_kernel]
    exact Fm_congr (fun i j => by ring) ξ η
  have decomp2 : ∀ ξ η, Fm Λ ξ η = (M : ℂ) * Fm (AronszajnRK.Sum.kernelFn H) ξ η -
      Fm (fun i j => (M : ℂ) * AronszajnRK.Sum.kernelFn H i j - Λ i j) ξ η := by
    intro ξ η
    rw [← Fm_smul_kernel, eq_sub_iff_add_eq, ← Fm_add_kernel]
    exact Fm_congr (fun i j => by ring) ξ η
  rw [kernelLE_iff, kernelLE_iff]
  constructor
  · rintro ⟨L, hsa, hL, hb⟩
    have hsym := hsa.isSymmetric
    have hFL : ∀ ξ, Fm Λ ξ ξ = ((RCLike.re ⟪T H ξ, L (T H ξ)⟫_ℂ : ℝ) : ℂ) := by
      intro ξ
      have e1 : Fm Λ ξ ξ = ⟪L (T H ξ), T H ξ⟫_ℂ := by
        rw [← Fm_inner H L]
        exact Fm_congr (fun i j => by rw [← hL, opKernel_eq]) ξ ξ
      have e2 : ⟪L (T H ξ), T H ξ⟫_ℂ = ⟪T H ξ, L (T H ξ)⟫_ℂ := hsym _ _
      have e3 : conj ⟪T H ξ, L (T H ξ)⟫_ℂ = ⟪T H ξ, L (T H ξ)⟫_ℂ := by
        rw [inner_conj_symm, e2]
      rw [e1, e2, RCLike.re_to_complex]
      exact (Complex.conj_eq_iff_re.mp e3).symm
    refine ⟨⟨herm1, fun ξ => ?_⟩, ⟨herm2, fun ξ => ?_⟩⟩
    · have h := decomp1 ξ ξ
      rw [hFL, Fm_K_self] at h
      have e : Fm (fun i j => Λ i j - (m : ℂ) * AronszajnRK.Sum.kernelFn H i j) ξ ξ =
          ((RCLike.re ⟪T H ξ, L (T H ξ)⟫_ℂ - m * ‖T H ξ‖ ^ 2 : ℝ) : ℂ) := by
        push_cast at h ⊢
        linear_combination -h
      rw [e]
      exact_mod_cast sub_nonneg.mpr (hb _).1
    · have h := decomp2 ξ ξ
      rw [hFL, Fm_K_self] at h
      have e : Fm (fun i j => (M : ℂ) * AronszajnRK.Sum.kernelFn H i j - Λ i j) ξ ξ =
          ((M * ‖T H ξ‖ ^ 2 - RCLike.re ⟪T H ξ, L (T H ξ)⟫_ℂ : ℝ) : ℂ) := by
        push_cast at h ⊢
        linear_combination h
      rw [e]
      exact_mod_cast sub_nonneg.mpr (hb _).2
  · rintro ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
    exact construct (H := H) Λ _ _ m M hΛh herm1
      (fun ξ => (Complex.nonneg_iff.mp (h1 ξ)).1) (fun ξ => (Complex.nonneg_iff.mp (h2 ξ)).1)
      decomp1 (fun ξ => decomp2 ξ ξ)

end AronszajnOpAux

open AronszajnRK.Operators InnerProductSpace ComplexConjugate in
theorem solution {H : Type*} {X : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    (Λ : X → X → ℂ) (hΛ : ∀ x y : X, Λ x y = conj (Λ y x)) (m M : ℝ) :
    (∃ L : H →L[ℂ] H, IsSelfAdjoint L ∧ opKernel L = Λ ∧
        ∀ f : H, m * ‖f‖ ^ 2 ≤ RCLike.re ⟪f, L f⟫_ℂ ∧ RCLike.re ⟪f, L f⟫_ℂ ≤ M * ‖f‖ ^ 2) ↔
      (AronszajnRK.Limits.KernelLE (fun x y => (m : ℂ) * AronszajnRK.Sum.kernelFn H x y) Λ ∧
        AronszajnRK.Limits.KernelLE Λ (fun x y => (M : ℂ) * AronszajnRK.Sum.kernelFn H x y)) := by
  exact AronszajnOpAux.main_thm Λ hΛ m M
