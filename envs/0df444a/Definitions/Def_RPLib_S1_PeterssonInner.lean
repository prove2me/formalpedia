-- Prove2me | Definitions.Def_RPLib_S1_PeterssonInner
-- name    : RPLib_S1_PeterssonInner
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T05:18:39.825639+00:00
-- url     : https://prove2.me/theorems/0924f6e6-700f-4cc6-ad75-4e22ad08ce0d
-- title:
--   The Petersson inner product on cusp forms for a finite-index subgroup of $\mathrm{SL}_2(\mathbb{Z})$
-- statement:
--   For $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ of finite index and cusp forms $f, g \in S_k(\Gamma)$, the (unnormalised) Petersson product is $$\langle f, g\rangle_\Gamma = \int_{\Gamma\backslash\mathbb{H}} \overline{f(\tau)}\, g(\tau)\, (\operatorname{Im}\tau)^k\, d\mu(\tau).$$ The file proves that the integrand is integrable over a fundamental domain, that the product is sesquilinear, Hermitian and positive definite, so that $S_k(\Gamma)$ becomes a complex inner product space, and that it behaves as expected under unfolding, change of group and the trace map.
--
--   **Formalization note.** This file is a library module of a formalization of the Ramanujan-Petersson conjecture for holomorphic cusp forms on $\Gamma_1(M)$. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, doi:10.1007/978-0-387-27226-9, Section 5.4

import Mathlib
import Definitions.Def_RPLib_S1_FundDomain

/-!
# The Petersson inner product on `S_k(Γ)` (RP project, unit S1-PETERSSON)

For `Γ ≤ SL(2, ℤ)` we integrate Mathlib's Petersson integrand `petersson k f g` over the
fundamental domain `fdom Γ = ⋃ c : SL(2, ℤ) ⧸ ±Γ, c.out⁻¹ • 𝒟` of S1-FUNDDOM (UNNORMALISED).

Main results (namespace `RP.Petersson`):
* `isOpenPosMeasure_volume` : the hyperbolic measure charges nonempty open sets;
* `peterssonInner`, `integrableOn_petersson`, sesquilinearity, `peterssonInner_conj_symm`,
  `peterssonInner_self`, `eq_zero_of_peterssonInner_self_eq_zero`;
* `peterssonInner_eq_of_isFundamentalDomain`, `peterssonInner_eq_sum_fd` (sum over cosets on `𝒟`);
* `PeterssonSpace Γ k` (type synonym of `CuspForm Γ k`) with `InnerProductSpace ℂ` for finite index;
* `setIntegral_fdom_eq_sum` (unfolding), `peterssonInner_of_le` (change of group) and
  `peterssonInner_trace` (trace adjointness), under `-1 ∈ Γ → -1 ∈ Γ'`.
-/

set_option autoImplicit false

open MeasureTheory Set Matrix Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup ModularForm
open scoped MatrixGroups Modular Pointwise ENNReal NNReal ComplexConjugate

noncomputable section

namespace RP.Petersson

open RP.FundDomain

attribute [local instance] measurableConstSMul_pgl smulInvariantMeasure_pgl
  smulInvariantMeasure_subgroup

/-! ### The hyperbolic measure charges open sets -/

theorem isOpenPosMeasure_volume : (volume : Measure ℍ).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  rw [volume_eq_lintegral]
  have hU' : IsOpen (((↑) : ℍ → ℂ) '' U) := UpperHalfPlane.isOpenEmbedding_coe.isOpenMap U hU
  have hpos : volume (((↑) : ℍ → ℂ) '' U) ≠ 0 := hU'.measure_ne_zero volume (hne.image _)
  refine ((setLIntegral_pos_iff (by fun_prop)).2 ?_).ne'
  have hsub : ((↑) : ℍ → ℂ) '' U ⊆
      Function.support (fun z : ℂ => (((1 / ‖z.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) := by
    rintro _ ⟨z, -, rfl⟩
    rw [Function.mem_support]
    simpa using z.im_pos.ne'
  rw [inter_eq_right.2 hsub]
  exact pos_iff_ne_zero.2 hpos

attribute [local instance] isOpenPosMeasure_volume

/-! ### The fundamental domain of `Γ` -/

/-- The fundamental domain of `Γ ≤ SL(2, ℤ)` built in S1-FUNDDOM. -/
def fdom (Γ : Subgroup SL(2, ℤ)) : Set ℍ := ⋃ c : SL(2, ℤ) ⧸ pmSL Γ, c.out⁻¹ • 𝒟

theorem isFundamentalDomain_fdom (Γ : Subgroup SL(2, ℤ)) :
    IsFundamentalDomain (pglImage (Γ : Subgroup (GL (Fin 2) ℝ))) (fdom Γ) volume :=
  isFundamentalDomain_iUnion_out_inv_smul_fd Γ

theorem measurableSet_fdom (Γ : Subgroup SL(2, ℤ)) : MeasurableSet (fdom Γ) := by
  have := countable_quotient_pmSL Γ
  refine MeasurableSet.iUnion fun c => ?_
  rw [← toPGLR_smul_set]
  exact isClosed_fd.measurableSet.const_smul _

theorem volume_fdom_lt_top (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] : volume (fdom Γ) < ∞ :=
  volume_iUnion_inv_smul_fd_lt_top Γ _

/-- Bounded measurable functions are integrable on sets of finite volume. -/
theorem integrableOn_of_bounded {E : Type*} [NormedAddCommGroup E] {f : ℍ → E}
    (hf : AEStronglyMeasurable f volume) {C : ℝ} (hC : ∀ z, ‖f z‖ ≤ C) {s : Set ℍ}
    (hs : volume s < ∞) : IntegrableOn f s volume :=
  ⟨hf.restrict, .restrict_of_bounded (C := C) hs (Filter.Eventually.of_forall hC)⟩

/-! ### The integrand -/

variable {k : ℤ}

/-- `petersson k f g` is bounded on `ℍ` for cusp forms `f`, `g` (possibly for different groups). -/
theorem exists_bound_petersson {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} [Γ₁.IsArithmetic]
    [Γ₂.IsArithmetic] {F₁ F₂ : Type*} [FunLike F₁ ℍ ℂ] [FunLike F₂ ℍ ℂ] [CuspFormClass F₁ Γ₁ k]
    [CuspFormClass F₂ Γ₂ k] (f : F₁) (g : F₂) : ∃ C, ∀ τ, ‖petersson k f g τ‖ ≤ C := by
  obtain ⟨C₁, h₁⟩ := CuspFormClass.exists_bound f
  obtain ⟨C₂, h₂⟩ := CuspFormClass.exists_bound g
  refine ⟨C₁ * C₂, fun τ => ?_⟩
  have hy := τ.im_pos
  have e : ‖petersson k f g τ‖ = ‖f τ‖ * ‖g τ‖ * τ.im ^ k := by
    simp only [petersson, norm_mul, Complex.norm_conj, norm_zpow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hy]
  have hr : τ.im ^ k = τ.im ^ ((k : ℝ) / 2) * τ.im ^ ((k : ℝ) / 2) := by
    rw [← Real.rpow_add hy, add_halves, Real.rpow_intCast]
  have hp : 0 < τ.im ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos hy _
  have a1 : ‖f τ‖ * τ.im ^ ((k : ℝ) / 2) ≤ C₁ := by
    have := h₁ τ; rwa [le_div_iff₀ hp] at this
  have a2 : ‖g τ‖ * τ.im ^ ((k : ℝ) / 2) ≤ C₂ := by
    have := h₂ τ; rwa [le_div_iff₀ hp] at this
  rw [e, hr]
  calc ‖f τ‖ * ‖g τ‖ * (τ.im ^ ((k : ℝ) / 2) * τ.im ^ ((k : ℝ) / 2))
      = (‖f τ‖ * τ.im ^ ((k : ℝ) / 2)) * (‖g τ‖ * τ.im ^ ((k : ℝ) / 2)) := by ring
    _ ≤ C₁ * C₂ := mul_le_mul a1 a2 (by positivity) (le_trans (by positivity) a1)

theorem continuous_petersson {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} {F₁ F₂ : Type*} [FunLike F₁ ℍ ℂ]
    [FunLike F₂ ℍ ℂ] [ModularFormClass F₁ Γ₁ k] [ModularFormClass F₂ Γ₂ k] (f : F₁) (g : F₂) :
    Continuous (petersson k f g) :=
  petersson_continuous k (ModularFormClass.continuous f) (ModularFormClass.continuous g)

/-- Slash invariance of a form for `Γ ≤ SL(2, ℤ)` under an element of `Γ`. -/
theorem slash_SL_eq {Γ : Subgroup SL(2, ℤ)} {F : Type*} [FunLike F ℍ ℂ]
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Γ) : (⇑f : ℍ → ℂ) ∣[k] γ = ⇑f := by
  rw [ModularForm.SL_slash]
  exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ)

theorem petersson_smul_eq {Γ : Subgroup SL(2, ℤ)} {f g : ℍ → ℂ} (hf : ∀ γ ∈ Γ, f ∣[k] γ = f)
    (hg : ∀ γ ∈ Γ, g ∣[k] γ = g) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (z : ℍ) :
    petersson k f g (γ • z) = petersson k f g z := by
  rw [← petersson_slash_SL, hf γ hγ, hg γ hγ]

theorem petersson_self (f : ℍ → ℂ) (z : ℍ) :
    petersson k f f z = ((‖f z‖ ^ 2 * z.im ^ k : ℝ) : ℂ) := by
  rw [petersson, Complex.conj_mul']
  push_cast
  ring

/-! ### The Petersson inner product -/

/-- The (unnormalised) Petersson inner product of `f, g : ℍ → ℂ` for `Γ ≤ SL(2, ℤ)`:
`∫_{fdom Γ} conj (f z) g z (im z)^k dμ(z)` with the hyperbolic measure. -/
def peterssonInner (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : ℍ → ℂ) : ℂ :=
  ∫ z in fdom Γ, petersson k f g z

section Basic

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]

theorem integrableOn_petersson {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} [Γ₁.IsArithmetic]
    [Γ₂.IsArithmetic] (f : CuspForm Γ₁ k) (g : CuspForm Γ₂ k) :
    IntegrableOn (petersson k f g) (fdom Γ) volume := by
  obtain ⟨C, hC⟩ := exists_bound_petersson f g
  exact integrableOn_of_bounded (continuous_petersson f g).aestronglyMeasurable hC
    (volume_fdom_lt_top Γ)

theorem peterssonInner_add_left (f f' g : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    peterssonInner Γ k ⇑(f + f') g = peterssonInner Γ k f g + peterssonInner Γ k f' g := by
  unfold peterssonInner
  rw [← integral_add (integrableOn_petersson f g) (integrableOn_petersson f' g)]
  congr 1
  funext z
  simp only [petersson, FunLike.coe_add, Pi.add_apply, map_add]
  ring

theorem peterssonInner_add_right (f g g' : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    peterssonInner Γ k f ⇑(g + g') = peterssonInner Γ k f g + peterssonInner Γ k f g' := by
  unfold peterssonInner
  rw [← integral_add (integrableOn_petersson f g) (integrableOn_petersson f g')]
  congr 1
  funext z
  simp only [petersson, FunLike.coe_add, Pi.add_apply]
  ring

theorem peterssonInner_smul_left (c : ℂ) (f g : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    peterssonInner Γ k ⇑(c • f) g = conj c * peterssonInner Γ k f g := by
  unfold peterssonInner
  rw [← integral_const_mul]
  congr 1
  funext z
  simp only [petersson, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem peterssonInner_smul_right (c : ℂ) (f g : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    peterssonInner Γ k f ⇑(c • g) = c * peterssonInner Γ k f g := by
  unfold peterssonInner
  rw [← integral_const_mul]
  congr 1
  funext z
  simp only [petersson, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

end Basic

theorem peterssonInner_conj_symm (Γ : Subgroup SL(2, ℤ)) (f g : ℍ → ℂ) :
    conj (peterssonInner Γ k f g) = peterssonInner Γ k g f := by
  unfold peterssonInner
  rw [← integral_conj]
  congr 1
  funext z
  exact (petersson_symm k f g z).symm

theorem peterssonInner_self (Γ : Subgroup SL(2, ℤ)) (f : ℍ → ℂ) :
    peterssonInner Γ k f f = ((∫ z in fdom Γ, ‖f z‖ ^ 2 * z.im ^ k : ℝ) : ℂ) := by
  unfold peterssonInner
  simp_rw [petersson_self]
  exact integral_ofReal

theorem re_peterssonInner_self_nonneg (Γ : Subgroup SL(2, ℤ)) (f : ℍ → ℂ) :
    0 ≤ (peterssonInner Γ k f f).re := by
  rw [peterssonInner_self, Complex.ofReal_re]
  exact setIntegral_nonneg (measurableSet_fdom Γ) fun z _ =>
    mul_nonneg (sq_nonneg _) (zpow_nonneg z.im_pos.le _)

/-- **Positive definiteness.** -/
theorem eq_zero_of_peterssonInner_self_eq_zero {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (h : peterssonInner Γ k f f = 0) : f = 0 := by
  set ψ : ℍ → ℝ := fun z => ‖f z‖ ^ 2 * z.im ^ k with hψ
  have hψc : Continuous ψ :=
    ((continuous_norm.comp (ModularFormClass.continuous f)).pow 2).mul
      (UpperHalfPlane.continuous_im.zpow₀ k fun z => Or.inl z.im_pos.ne')
  have hψ0 : ∀ z, 0 ≤ ψ z := fun z => mul_nonneg (sq_nonneg _) (zpow_nonneg z.im_pos.le _)
  have hint : IntegrableOn ψ (fdom Γ) volume := by
    obtain ⟨C, hC⟩ := exists_bound_petersson f f
    refine integrableOn_of_bounded hψc.aestronglyMeasurable (C := C) (fun z => ?_)
      (volume_fdom_lt_top Γ)
    have := hC z
    rwa [petersson_self, Complex.norm_real] at this
  have h0 : ∫ z in fdom Γ, ψ z = 0 := by
    rw [peterssonInner_self] at h
    exact_mod_cast h
  have hae : ψ =ᵐ[volume.restrict (fdom Γ)] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hψ0) hint).1 h0
  have hinv : ∀ γ ∈ Γ, ∀ z, ψ (γ • z) = ψ z := by
    intro γ hγ z
    have := petersson_smul_eq (k := k) (fun δ hδ => slash_SL_eq f hδ)
      (fun δ hδ => slash_SL_eq f hδ) hγ z
    rw [petersson_self, petersson_self] at this
    exact_mod_cast this
  have hnull : volume {z | ψ z ≠ 0} = 0 := by
    have := countable_pglImage_coe Γ
    refine (isFundamentalDomain_fdom Γ).measure_zero_of_invariant _ (fun g => ?_) ?_
    · obtain ⟨γ, hγ, hg⟩ := mem_pglImage_coe.1 g.2
      ext z
      change z ∈ (g : PGL(2, ℝ)) • {z | ψ z ≠ 0} ↔ _
      rw [mem_smul_set_iff_inv_smul_mem, ← hg, ← map_inv, toPGLR_smul]
      simp only [mem_setOf_eq, hinv _ (Γ.inv_mem hγ)]
    · rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_fdom Γ), ae_iff] at hae
      refine measure_mono_null ?_ hae
      rintro z ⟨hz1, hz2⟩ h'
      exact hz1 (h' hz2)
  have hψeq : ψ = 0 := (Continuous.ae_eq_iff_eq volume hψc continuous_zero).1 (by
    rw [Filter.EventuallyEq, ae_iff]
    simpa using hnull)
  ext z
  have h1 := congr_fun hψeq z
  simp only [hψ, Pi.zero_apply] at h1
  have h2 : ‖f z‖ ^ 2 = 0 := (mul_eq_zero.1 h1).resolve_right (zpow_ne_zero _ z.im_pos.ne')
  simpa using h2

/-- The Petersson product does not depend on the fundamental domain. -/
theorem peterssonInner_eq_of_isFundamentalDomain {Γ : Subgroup SL(2, ℤ)} {F : Set ℍ}
    (hF : IsFundamentalDomain (pglImage (Γ : Subgroup (GL (Fin 2) ℝ))) F volume)
    (f g : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    peterssonInner Γ k f g = ∫ z in F, petersson k f g z :=
  setIntegral_eq_of_isFundamentalDomain Γ (isFundamentalDomain_fdom Γ) hF fun _ hγ z =>
    petersson_smul_eq (fun _ hδ => slash_SL_eq f hδ) (fun _ hδ => slash_SL_eq g hδ) hγ z

/-- The Petersson product as a finite sum over `SL(2, ℤ) ⧸ ±Γ` of integrals over `𝒟`, and as
`∫_𝒟 ∑_q petersson k (f ∣ q) (g ∣ q)`. -/
theorem peterssonInner_eq_sum_fd {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    [Fintype (SL(2, ℤ) ⧸ pmSL Γ)] (f g : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    peterssonInner Γ k f g = ∑ c : SL(2, ℤ) ⧸ pmSL Γ, ∫ z in 𝒟, petersson k f g (c.out⁻¹ • z) ∧
    peterssonInner Γ k f g =
      ∫ z in 𝒟, ∑ c : SL(2, ℤ) ⧸ pmSL Γ, petersson k (⇑f ∣[k] c.out⁻¹) (⇑g ∣[k] c.out⁻¹) z := by
  have h1 : peterssonInner Γ k f g = ∑ c : SL(2, ℤ) ⧸ pmSL Γ, ∫ z in 𝒟, petersson k f g (c.out⁻¹ • z) := by
    unfold peterssonInner fdom
    rw [setIntegral_iUnion_inv_smul_fd Γ _ QuotientGroup.out_eq' (integrableOn_petersson f g),
      tsum_fintype]
  refine ⟨h1, ?_⟩
  rw [h1, integral_finsetSum]
  · simp_rw [petersson_slash_SL]
  · intro c _
    obtain ⟨C, hC⟩ := exists_bound_petersson f g
    have hm : Measurable fun z : ℍ => petersson k f g (c.out⁻¹ • z) := by
      have e : (fun z : ℍ => petersson k f g (c.out⁻¹ • z)) =
          fun z => petersson k f g (toPGLR c.out⁻¹ • z) := by
        funext z; rw [toPGLR_smul]
      rw [e]
      exact (continuous_petersson f g).measurable.comp (measurable_const_smul _)
    have e : petersson k (⇑f ∣[k] c.out⁻¹) (⇑g ∣[k] c.out⁻¹) =
        fun z => petersson k f g (c.out⁻¹ • z) :=
      funext fun z => petersson_slash_SL k _ _ _ z
    rw [e]
    exact integrableOn_of_bounded hm.aestronglyMeasurable (fun z => hC _) volume_fd_lt_top

/-! ### The inner product space (type synonym, S1-PROBE rule) -/

/-- `S_k(Γ)` retyped so that it carries the Petersson inner product. -/
def PeterssonSpace (Γ : Subgroup SL(2, ℤ)) (k : ℤ) : Type :=
  CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k

namespace PeterssonSpace

variable (Γ : Subgroup SL(2, ℤ)) (k : ℤ)

instance instAddCommGroup : AddCommGroup (PeterssonSpace Γ k) :=
  inferInstanceAs (AddCommGroup (CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k))

instance instModule : Module ℂ (PeterssonSpace Γ k) :=
  inferInstanceAs (Module ℂ (CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k))

variable {Γ k}

/-- The underlying cusp form. -/
def toCuspForm (f : PeterssonSpace Γ k) : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k := f

/-- A cusp form viewed in the Petersson space. -/
def ofCuspForm (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) : PeterssonSpace Γ k := f

@[simp] theorem toCuspForm_ofCuspForm (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    toCuspForm (ofCuspForm f) = f := rfl

@[simp] theorem toCuspForm_add (f g : PeterssonSpace Γ k) :
    toCuspForm (f + g) = toCuspForm f + toCuspForm g := rfl

@[simp] theorem toCuspForm_smul (c : ℂ) (f : PeterssonSpace Γ k) :
    toCuspForm (c • f) = c • toCuspForm f := rfl

@[simp] theorem toCuspForm_zero : toCuspForm (0 : PeterssonSpace Γ k) = 0 := rfl

theorem toCuspForm_injective : Function.Injective (toCuspForm (Γ := Γ) (k := k)) :=
  fun _ _ h => h

instance instInner : Inner ℂ (PeterssonSpace Γ k) :=
  ⟨fun f g => peterssonInner Γ k (toCuspForm f) (toCuspForm g)⟩

theorem inner_def (f g : PeterssonSpace Γ k) :
    (inner ℂ f g : ℂ) = peterssonInner Γ k (toCuspForm f) (toCuspForm g) := rfl

instance instCore [Γ.FiniteIndex] : InnerProductSpace.Core ℂ (PeterssonSpace Γ k) where
  toInner := instInner
  conj_inner_symm f g := by
    rw [inner_def, inner_def, peterssonInner_conj_symm]
  re_inner_nonneg f := by
    change 0 ≤ (peterssonInner Γ k (toCuspForm f) (toCuspForm f)).re
    exact re_peterssonInner_self_nonneg Γ _
  add_left f g h := by
    rw [inner_def, inner_def, inner_def, toCuspForm_add, peterssonInner_add_left]
  smul_left f g c := by
    rw [inner_def, inner_def, toCuspForm_smul, peterssonInner_smul_left]
  definite f hf := toCuspForm_injective (by
    rw [toCuspForm_zero]
    exact eq_zero_of_peterssonInner_self_eq_zero _ hf)

instance instNormedAddCommGroup [Γ.FiniteIndex] : NormedAddCommGroup (PeterssonSpace Γ k) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance instInnerProductSpace [Γ.FiniteIndex] : InnerProductSpace ℂ (PeterssonSpace Γ k) :=
  InnerProductSpace.ofCore _

theorem inner_ofCuspForm [Γ.FiniteIndex] (f g : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    (inner ℂ (ofCuspForm f) (ofCuspForm g) : ℂ) = peterssonInner Γ k f g := rfl

end PeterssonSpace

example (M : ℕ) [NeZero M] (k : ℤ) :
    InnerProductSpace ℂ (PeterssonSpace (CongruenceSubgroup.Gamma1 M) k) := inferInstance

/-! ### Unfolding, change of group and trace adjointness -/

/-- The right cosets `Γ / Γ'` (of the images in `GL(2, ℝ)`), as used by `CuspForm.trace`. -/
abbrev CosetQ (Γ Γ' : Subgroup SL(2, ℤ)) : Type :=
  (Γ : Subgroup (GL (Fin 2) ℝ)) ⧸ (Γ' : Subgroup (GL (Fin 2) ℝ)).subgroupOf Γ

theorem neg_one_mem_coe_iff {Γ : Subgroup SL(2, ℤ)} :
    (-1 : GL (Fin 2) ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)) ↔ (-1 : SL(2, ℤ)) ∈ Γ := by
  constructor
  · rintro ⟨γ, hγ, h⟩
    have : γ = -1 := mapGL_injective (by rw [h, mapGL_neg, map_one])
    rwa [← this]
  · intro h
    exact ⟨-1, h, by rw [mapGL_neg, map_one]⟩

theorem mk_eq_one_of_mem {Γ : Subgroup SL(2, ℤ)} {y : GL (Fin 2) ℝ}
    (hy : y ∈ (Γ : Subgroup (GL (Fin 2) ℝ))) (h : ProjGenLinGroup.mk y = 1) : y = 1 ∨ y = -1 := by
  obtain ⟨γ, -, rfl⟩ := hy
  rcases (toPGLR_eq_one_iff γ).1 h with rfl | rfl
  · exact Or.inl (map_one _)
  · exact Or.inr (by rw [mapGL_neg, map_one])

theorem isFiniteRelIndex_coe {Γ Γ' : Subgroup SL(2, ℤ)} [Γ'.FiniteIndex] :
    (Γ' : Subgroup (GL (Fin 2) ℝ)).IsFiniteRelIndex Γ := by
  rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero,
    Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective]
  exact (inferInstance : (Γ'.subgroupOf Γ).FiniteIndex).index_ne_zero

variable {Γ Γ' : Subgroup SL(2, ℤ)}

/-- The inverses of the representatives `q.out` of `Γ / Γ'` are right coset representatives of
the image of `Γ'` in the image of `Γ` in `PGL(2, ℝ)`, provided `-1 ∈ Γ → -1 ∈ Γ'`. -/
theorem isRightCosetReps_cosetQ (hle : Γ' ≤ Γ)
    (hneg : (-1 : SL(2, ℤ)) ∈ Γ → (-1 : SL(2, ℤ)) ∈ Γ') :
    IsRightCosetReps (pglImage (Γ : Subgroup (GL (Fin 2) ℝ)))
      (pglImage (Γ' : Subgroup (GL (Fin 2) ℝ)))
      (fun q : CosetQ Γ Γ' => ProjGenLinGroup.mk ((q.out : GL (Fin 2) ℝ)⁻¹)) := by
  have hGH : (Γ' : Subgroup (GL (Fin 2) ℝ)) ≤ Γ := Subgroup.map_mono hle
  have hneg' : (-1 : GL (Fin 2) ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)) →
      (-1 : GL (Fin 2) ℝ) ∈ (Γ' : Subgroup (GL (Fin 2) ℝ)) := fun h =>
    neg_one_mem_coe_iff.2 (hneg (neg_one_mem_coe_iff.1 h))
  refine ⟨fun q => mk_mem_pglImage ((Γ : Subgroup (GL (Fin 2) ℝ)).inv_mem q.out.2),
    fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  have key : ∀ q : CosetQ Γ Γ', (∃ h ∈ pglImage (Γ' : Subgroup (GL (Fin 2) ℝ)),
      ProjGenLinGroup.mk y = h * ProjGenLinGroup.mk ((q.out : GL (Fin 2) ℝ)⁻¹)) ↔
      q = QuotientGroup.mk ⟨y⁻¹, (Γ : Subgroup (GL (Fin 2) ℝ)).inv_mem hy⟩ := by
    intro q
    constructor
    · rintro ⟨h, hh, hq⟩
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hh
      rw [← map_mul] at hq
      have hw : ProjGenLinGroup.mk ((j * (q.out : GL (Fin 2) ℝ)⁻¹)⁻¹ * y) = 1 := by
        rw [map_mul, map_inv, ← hq, inv_mul_cancel]
      have hwH : (j * (q.out : GL (Fin 2) ℝ)⁻¹)⁻¹ * y ∈ (Γ : Subgroup (GL (Fin 2) ℝ)) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ (hGH hj)
          (Subgroup.inv_mem _ q.out.2))) hy
      have hyq : y * (q.out : GL (Fin 2) ℝ) ∈ (Γ' : Subgroup (GL (Fin 2) ℝ)) := by
        rcases mk_eq_one_of_mem hwH hw with h1 | h1
        · have e : y = j * (q.out : GL (Fin 2) ℝ)⁻¹ := (inv_mul_eq_one.1 h1).symm
          rw [e, inv_mul_cancel_right]
          exact hj
        · have hm1 : (-1 : GL (Fin 2) ℝ) ∈ (Γ' : Subgroup (GL (Fin 2) ℝ)) :=
            hneg' (h1 ▸ hwH)
          have e : y = j * (q.out : GL (Fin 2) ℝ)⁻¹ * (-1) := (inv_mul_eq_iff_eq_mul.1 h1)
          rw [e, mul_assoc, mul_assoc, neg_one_mul, mul_neg, inv_mul_cancel]
          exact Subgroup.mul_mem _ hj hm1
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have := Subgroup.inv_mem _ hyq
      rwa [_root_.mul_inv_rev] at this
    · rintro rfl
      obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul ((Γ' : Subgroup (GL (Fin 2) ℝ)).subgroupOf Γ)
        (⟨y⁻¹, (Γ : Subgroup (GL (Fin 2) ℝ)).inv_mem hy⟩ : (Γ : Subgroup (GL (Fin 2) ℝ)))
      refine ⟨ProjGenLinGroup.mk ((j : (Γ : Subgroup (GL (Fin 2) ℝ))) : GL (Fin 2) ℝ),
        mk_mem_pglImage (Subgroup.mem_subgroupOf.1 j.2), ?_⟩
      rw [hj, ← map_mul]
      congr 1
      simp only [Subgroup.coe_mul, _root_.mul_inv_rev, _root_.inv_inv, _root_.mul_inv_cancel_left]
  exact ⟨_, (key _).2 rfl, fun q hq => (key q).1 hq⟩

/-- **Unfolding.** For `Γ' ≤ Γ` of finite index with `-1 ∈ Γ → -1 ∈ Γ'`, the integral of a
bounded measurable `Γ'`-invariant function over `fdom Γ'` is the sum over `q ∈ Γ / Γ'` of the
integrals of its translates by `q.out⁻¹` over `fdom Γ`. -/
theorem setIntegral_fdom_eq_sum (hle : Γ' ≤ Γ) [Γ'.FiniteIndex]
    (hneg : (-1 : SL(2, ℤ)) ∈ Γ → (-1 : SL(2, ℤ)) ∈ Γ') [Fintype (CosetQ Γ Γ')]
    {Φ : ℍ → ℂ} (hΦm : Measurable Φ) {C : ℝ} (hC : ∀ z, ‖Φ z‖ ≤ C)
    (hΦ : ∀ γ ∈ Γ', ∀ z : ℍ, Φ (γ • z) = Φ z) :
    ∫ z in fdom Γ', Φ z =
      ∑ q : CosetQ Γ Γ', ∫ z in fdom Γ, Φ ((q.out : GL (Fin 2) ℝ)⁻¹ • z) := by
  have hr := isRightCosetReps_cosetQ hle hneg
  have hs := isFundamentalDomain_fdom Γ
  have hGH : pglImage (Γ' : Subgroup (GL (Fin 2) ℝ)) ≤ pglImage (Γ : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.map_mono (Subgroup.map_mono hle)
  have hT := isFundamentalDomain_iUnion_smul hGH hs hr
  have := countable_pglImage_coe Γ'
  rw [setIntegral_eq_of_isFundamentalDomain Γ' (isFundamentalDomain_fdom Γ') hT hΦ]
  have hvol : volume (⋃ q : CosetQ Γ Γ', ProjGenLinGroup.mk ((q.out : GL (Fin 2) ℝ)⁻¹) •
      fdom Γ) < ∞ := by
    rw [hT.measure_eq (isFundamentalDomain_fdom Γ')]
    exact volume_fdom_lt_top Γ'
  have hne : ∀ q q' : CosetQ Γ Γ', ProjGenLinGroup.mk ((q.out : GL (Fin 2) ℝ)⁻¹) =
      ProjGenLinGroup.mk ((q'.out : GL (Fin 2) ℝ)⁻¹) → q = q' := by
    intro q q' h
    obtain ⟨i, -, huniq⟩ := hr.2 _ (hr.1 q)
    have h1 := huniq q ⟨1, Subgroup.one_mem _, (one_mul _).symm⟩
    have h2 := huniq q' ⟨1, Subgroup.one_mem _, by simpa only [one_mul] using h⟩
    exact h1.trans h2.symm
  rw [integral_iUnion_ae (s := fun q : CosetQ Γ Γ' => ProjGenLinGroup.mk ((q.out : GL (Fin 2) ℝ)⁻¹) •
      fdom Γ) (fun q => hs.nullMeasurableSet_smul ⟨_, hr.1 q⟩) ?_
    (integrableOn_of_bounded hΦm.aestronglyMeasurable hC hvol), tsum_fintype]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [setIntegral_smul_set]
    simp only [pglMk_smul]
  · intro q q' hqq'
    have hne' : (⟨_, hr.1 q⟩ : pglImage (Γ : Subgroup (GL (Fin 2) ℝ))) ≠ ⟨_, hr.1 q'⟩ :=
      fun h => hqq' (hne q q' (congrArg Subtype.val h))
    have h := hs.aedisjoint hne'
    change AEDisjoint volume (ProjGenLinGroup.mk ((q.out : GL (Fin 2) ℝ)⁻¹) • fdom Γ)
      (ProjGenLinGroup.mk ((q'.out : GL (Fin 2) ℝ)⁻¹) • fdom Γ) at h
    exact h

theorem measurable_petersson_smul {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} (f : CuspForm Γ₁ k)
    (g : CuspForm Γ₂ k) (h : GL (Fin 2) ℝ) :
    Measurable fun z : ℍ => petersson k f g (h • z) :=
  (continuous_petersson f g).measurable.comp (measurable_const_smul h)

/-- **Change of group.** For `Γ' ≤ Γ` of finite index with `-1 ∈ Γ → -1 ∈ Γ'`,
`⟪f, g⟫_{Γ'} = [Γ : Γ'] ⟪f, g⟫_Γ`. (Without the hypothesis the factor is `[±Γ : ±Γ']`.) -/
theorem peterssonInner_of_le (hle : Γ' ≤ Γ) [Γ'.FiniteIndex]
    (hneg : (-1 : SL(2, ℤ)) ∈ Γ → (-1 : SL(2, ℤ)) ∈ Γ')
    (f g : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    peterssonInner Γ' k f g = (Γ'.relIndex Γ : ℂ) * peterssonInner Γ k f g := by
  have : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hle
  have := isFiniteRelIndex_coe (Γ := Γ) (Γ' := Γ')
  let _ : Fintype (CosetQ Γ Γ') := Fintype.ofFinite _
  obtain ⟨C, hC⟩ := exists_bound_petersson f g
  unfold peterssonInner
  rw [setIntegral_fdom_eq_sum hle hneg (continuous_petersson f g).measurable hC
    (fun γ hγ z => petersson_smul_eq (fun δ hδ => slash_SL_eq f hδ)
      (fun δ hδ => slash_SL_eq g hδ) (hle hγ) z)]
  have hq : ∀ q : CosetQ Γ Γ', ∫ z in fdom Γ, petersson k f g ((q.out : GL (Fin 2) ℝ)⁻¹ • z) =
      ∫ z in fdom Γ, petersson k f g z := by
    intro q
    obtain ⟨γ, hγ, hγq⟩ := Subgroup.mem_map.1 ((Γ : Subgroup (GL (Fin 2) ℝ)).inv_mem q.out.2)
    congr 1
    funext z
    rw [← hγq]
    exact petersson_smul_eq (fun δ hδ => slash_SL_eq f hδ) (fun δ hδ => slash_SL_eq g hδ) hγ z
  simp_rw [hq]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  have e : Fintype.card (CosetQ Γ Γ') = (Γ' : Subgroup (GL (Fin 2) ℝ)).relIndex Γ := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [e, Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective]

/-- **Trace adjointness.** For `Γ' ≤ Γ` of finite index with `-1 ∈ Γ → -1 ∈ Γ'`,
`f ∈ S_k(Γ)` and `g ∈ S_k(Γ')`: `⟪f, tr g⟫_Γ = ⟪f, g⟫_{Γ'}` (`f` viewed on `Γ'`). -/
theorem peterssonInner_trace (hle : Γ' ≤ Γ) [Γ'.FiniteIndex]
    (hneg : (-1 : SL(2, ℤ)) ∈ Γ → (-1 : SL(2, ℤ)) ∈ Γ')
    [(Γ' : Subgroup (GL (Fin 2) ℝ)).IsFiniteRelIndex Γ]
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (g : CuspForm (Γ' : Subgroup (GL (Fin 2) ℝ)) k) :
    peterssonInner Γ k f (CuspForm.trace (Γ : Subgroup (GL (Fin 2) ℝ)) g) =
      peterssonInner Γ' k f g := by
  have : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hle
  let _ : Fintype (CosetQ Γ Γ') := Fintype.ofFinite _
  obtain ⟨C, hC⟩ := exists_bound_petersson f g
  have htr : ∀ z, (CuspForm.trace (Γ : Subgroup (GL (Fin 2) ℝ)) g : ℍ → ℂ) z =
      ∑ q : CosetQ Γ Γ', ((⇑g) ∣[k] ((q.out : GL (Fin 2) ℝ)⁻¹)) z := by
    intro z
    show (∑ q : CosetQ Γ Γ', SlashInvariantForm.quotientFunc (k := k) g q) z = _
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  have hterm : ∀ (q : CosetQ Γ Γ') (z : ℍ),
      petersson k f (⇑g ∣[k] ((q.out : GL (Fin 2) ℝ)⁻¹)) z =
        petersson k f g ((q.out : GL (Fin 2) ℝ)⁻¹ • z) := by
    intro q z
    obtain ⟨γ, hγ, hγq⟩ := Subgroup.mem_map.1 ((Γ : Subgroup (GL (Fin 2) ℝ)).inv_mem q.out.2)
    rw [← hγq]
    change petersson k (⇑f) (⇑g ∣[k] γ) z = petersson k (⇑f) (⇑g) (γ • z)
    conv_lhs => rw [← slash_SL_eq f hγ]
    exact petersson_slash_SL k f g γ z
  have hpt : ∀ z, petersson k f (CuspForm.trace (Γ : Subgroup (GL (Fin 2) ℝ)) g) z =
      ∑ q : CosetQ Γ Γ', petersson k f g ((q.out : GL (Fin 2) ℝ)⁻¹ • z) := by
    intro z
    simp_rw [← hterm]
    simp only [petersson, htr z, Finset.mul_sum, Finset.sum_mul]
  unfold peterssonInner
  rw [setIntegral_fdom_eq_sum hle hneg (continuous_petersson f g).measurable hC
    (fun γ hγ z => petersson_smul_eq (fun δ hδ => slash_SL_eq f (hle hδ))
      (fun δ hδ => slash_SL_eq g hδ) hγ z)]
  simp_rw [hpt]
  rw [integral_finsetSum]
  intro q _
  exact integrableOn_of_bounded (measurable_petersson_smul f g _).aestronglyMeasurable
    (fun z => hC _) (volume_fdom_lt_top Γ)

end RP.Petersson


