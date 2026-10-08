-- Prove2me | solution 1 for AronszajnRK.Inclusion.kernel_rescale_norm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T02:46:46.385059+00:00
-- url     : https://prove2.me/submissions/b7917086-5c83-441e-895f-e39f3c1183e5

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn

universe uX uH uH₁

set_option autoImplicit false

namespace KRN44B

/-- Type synonym of `H` carrying the rescaled reproducing structure. -/
def Scaled (H : Type uH) (_c : ℝ) : Type uH := H

section
variable {X : Type uX} (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [RKHS ℂ H X ℂ] (c : ℝ)

noncomputable instance instNACG : NormedAddCommGroup (Scaled H c) :=
  inferInstanceAs (NormedAddCommGroup H)
noncomputable instance instIPS : InnerProductSpace ℂ (Scaled H c) :=
  inferInstanceAs (InnerProductSpace ℂ H)
instance instComplete : CompleteSpace (Scaled H c) :=
  inferInstanceAs (CompleteSpace H)

/-- Identity maps between the synonym and the original type. -/
def toH : Scaled H c → H := id
def ofH : H → Scaled H c := id

omit [CompleteSpace H] [RKHS ℂ H X ℂ] in
@[simp] lemma toH_ofH (f : H) : toH H c (ofH H c f) = f := rfl

omit [CompleteSpace H] [RKHS ℂ H X ℂ] in
lemma norm_toH (f : Scaled H c) : ‖toH H c f‖ = ‖f‖ := rfl

omit [CompleteSpace H] [RKHS ℂ H X ℂ] in
lemma toH_smul (a : ℂ) (f : Scaled H c) : toH H c (a • f) = a • toH H c f := rfl

noncomputable instance instRKHS [Fact (c ≠ 0)] : RKHS ℂ (Scaled H c) X ℂ where
  coeCLM := ((c : ℂ)⁻¹) • (RKHS.coeCLM ℂ : H →L[ℂ] X → ℂ)
  coeCLM_injective := by
    intro f g h
    have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Fact.out)
    have h1 : (c : ℂ)⁻¹ • (RKHS.coeCLM ℂ : H →L[ℂ] X → ℂ) f =
        (c : ℂ)⁻¹ • (RKHS.coeCLM ℂ : H →L[ℂ] X → ℂ) g := h
    have h2 : (RKHS.coeCLM ℂ : H →L[ℂ] X → ℂ) f = (RKHS.coeCLM ℂ : H →L[ℂ] X → ℂ) g :=
      smul_right_injective (X → ℂ) (inv_ne_zero hc') h1
    exact (RKHS.coeCLM_injective (𝕜 := ℂ) (H := H) (X := X) (V := ℂ) h2 :)

lemma coe_scaled [Fact (c ≠ 0)] (f : Scaled H c) :
    (⇑f : X → ℂ) = (c : ℂ)⁻¹ • ⇑(toH H c f) := rfl

end

end KRN44B

theorem solution {X : Type uX} (H : Type uH)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    (c : ℝ) (hc : 0 < c) :
    (∃ (H₁ : Type uH) (_ : NormedAddCommGroup H₁) (_ : InnerProductSpace ℂ H₁)
        (_ : CompleteSpace H₁) (_ : RKHS ℂ H₁ X ℂ),
        Set.range (fun f₁ : H₁ => ⇑f₁) = Set.range (fun f : H => ⇑f) ∧
          ∀ (f₁ : H₁) (f : H), ⇑f = ⇑f₁ → ‖f₁‖ = c * ‖f‖) ∧
      ∀ (H₁ : Type uH₁) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
        [RKHS ℂ H₁ X ℂ],
        Set.range (fun f₁ : H₁ => ⇑f₁) = Set.range (fun f : H => ⇑f) →
        (∀ (f₁ : H₁) (f : H), ⇑f = ⇑f₁ → ‖f₁‖ = c * ‖f‖) →
        AronszajnRK.Sum.kernelFn H₁ = fun x y => (1 / (c : ℂ) ^ 2) * AronszajnRK.Sum.kernelFn H x y := by
  have hc0 : c ≠ 0 := hc.ne'
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc0
  have : Fact (c ≠ 0) := ⟨hc0⟩
  refine ⟨⟨KRN44B.Scaled H c, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩, ?_⟩
  · ext g
    constructor
    · rintro ⟨f₁, rfl⟩
      refine ⟨(c : ℂ)⁻¹ • KRN44B.toH H c f₁, ?_⟩
      show ⇑((c : ℂ)⁻¹ • KRN44B.toH H c f₁) = ⇑f₁
      rw [RKHS.coe_smul, KRN44B.coe_scaled]
    · rintro ⟨f, rfl⟩
      refine ⟨KRN44B.ofH H c ((c : ℂ) • f), ?_⟩
      show ⇑(KRN44B.ofH H c ((c : ℂ) • f)) = ⇑f
      rw [KRN44B.coe_scaled, KRN44B.toH_ofH, RKHS.coe_smul, smul_smul, inv_mul_cancel₀ hc', one_smul]
  · intro f₁ f h
    rw [KRN44B.coe_scaled, ← RKHS.coe_smul] at h
    have hf : f = (c : ℂ)⁻¹ • KRN44B.toH H c f₁ := DFunLike.coe_injective h
    rw [← KRN44B.norm_toH, hf, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hc.le]
    field_simp
  · intro H₁ _ _ _ _ hrange hnorm
    have hT : ∀ f : H, ∃ f₁ : H₁, (⇑f₁ : X → ℂ) = ⇑f := by
      intro f
      have : (⇑f : X → ℂ) ∈ Set.range (fun f₁ : H₁ => ⇑f₁) := by
        rw [hrange]; exact ⟨f, rfl⟩
      obtain ⟨f₁, hf₁⟩ := this
      exact ⟨f₁, hf₁⟩
    choose T hT using hT
    have Tadd : ∀ a b : H, T (a + b) = T a + T b := by
      intro a b
      apply DFunLike.coe_injective
      rw [hT, RKHS.coe_add, RKHS.coe_add, hT, hT]
    have Tsmul : ∀ (r : ℂ) (a : H), T (r • a) = r • T a := by
      intro r a
      apply DFunLike.coe_injective
      rw [hT, RKHS.coe_smul, RKHS.coe_smul, hT]
    let L : H →ₗ[ℂ] H₁ :=
      { toFun := fun f => (c : ℂ)⁻¹ • T f
        map_add' := by intro a b; simp only [Tadd, smul_add]
        map_smul' := by
          intro r a
          simp only [Tsmul, RingHom.id_apply, smul_smul, mul_comm] }
    have hiso : ∀ f : H, ‖L f‖ = ‖f‖ := by
      intro f
      show ‖(c : ℂ)⁻¹ • T f‖ = ‖f‖
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hc.le,
        hnorm (T f) f (hT f).symm]
      field_simp
    have hinner := (LinearMap.norm_map_iff_inner_map_map L).mp hiso
    funext x y
    show RKHS.kernel H₁ x y 1 = 1 / (c : ℂ) ^ 2 * RKHS.kernel H x y 1
    rw [← RKHS.kerFun_apply, ← RKHS.kerFun_apply]
    have hk : (⇑(RKHS.kerFun H₁ y (1 : ℂ)) : X → ℂ) ∈ Set.range (fun f : H => ⇑f) := by
      rw [← hrange]; exact ⟨_, rfl⟩
    obtain ⟨f, hf⟩ := hk
    have hTf : T f = RKHS.kerFun H₁ y (1 : ℂ) := by
      apply DFunLike.coe_injective
      rw [hT]; exact hf
    have hclaim : f = (1 / (c : ℂ) ^ 2) • RKHS.kerFun H y (1 : ℂ) := by
      apply ext_inner_right ℂ
      intro v
      have e1 := hinner f v
      have e2 : inner ℂ (L f) (L v) = (c : ℂ)⁻¹ * ((c : ℂ)⁻¹ * v y) := by
        show inner ℂ ((c : ℂ)⁻¹ • T f) ((c : ℂ)⁻¹ • T v) = _
        rw [inner_smul_left, inner_smul_right, hTf, RKHS.kerFun_inner, hT]
        simp
      rw [← e1, e2, inner_smul_left, RKHS.kerFun_inner]
      simp
      ring
    have hf' : (⇑f : X → ℂ) = ⇑(RKHS.kerFun H₁ y (1 : ℂ)) := hf
    rw [← hf', hclaim, RKHS.coe_smul, Pi.smul_apply, smul_eq_mul]
