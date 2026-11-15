-- Prove2me | Definitions.Def_RPLib_S3_EllW2E
-- name    : RPLib_S3_EllW2E
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:10:45.912344+00:00
-- url     : https://prove2.me/theorems/be6cc85e-d161-4fef-ad3f-a1956e299eea
-- title:
--   The Eichler-Selberg trace formula in weight two: dominated convergence on the truncated fundamental domain
-- statement:
--   Dominated convergence on the truncated fundamental domain.
--
--   * `ae_fd_of_ae_fdom`: an a.e. statement on `fdom Γ₁(M)` holds a.e. on `𝒟` after `τ ↦ c.out⁻¹ • τ`.
--   * `integrableOn_fd_comp'`: the same transport for integrability (any normed group).
--   * **`tendsto_trunc_restPartS`**: `∫_{𝒟 ∩ {Im ≤ Y}} restPartS_s(c.out⁻¹ τ) → ∫_{𝒟 ∩ {Im ≤ Y}} restPart0(c.out⁻¹ τ)`
--     as `s → 0+`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2D

/-!
# S3-ES-Wt2 (O6, part E): dominated convergence on the truncated fundamental domain

* `ae_fd_of_ae_fdom`: an a.e. statement on `fdom Γ₁(M)` holds a.e. on `𝒟` after `τ ↦ c.out⁻¹ • τ`.
* `integrableOn_fd_comp'`: the same transport for integrability (any normed group).
* **`tendsto_trunc_restPartS`**: `∫_{𝒟 ∩ {Im ≤ Y}} restPartS_s(c.out⁻¹ τ) → ∫_{𝒟 ∩ {Im ≤ Y}} restPart0(c.out⁻¹ τ)`
  as `s → 0+`.
-/

open MeasureTheory Metric Set Filter Complex UpperHalfPlane CongruenceSubgroup
open scoped Real ComplexConjugate NNReal ENNReal Manifold MatrixGroups Topology Modular Pointwise

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Bergman RamanujanPetersson.Kernel RP.FundDomain RP.Petersson
  RamanujanPetersson.EllTerm RamanujanPetersson.KernelSD

attribute [local instance] measurableConstSMul_pgl smulInvariantMeasure_pgl

variable {M : ℕ}

theorem ae_fd_of_ae_fdom {P : ℍ → Prop} (h : ∀ᵐ z ∂(volume.restrict (fdom (Gamma1 M))), P z)
    (c : SL(2, ℤ) ⧸ pmSL (Gamma1 M)) : ∀ᵐ τ ∂(volume.restrict 𝒟), P (c.out⁻¹ • τ) := by
  rw [ae_restrict_iff' (measurableSet_fdom _)] at h
  have h2 := (measurePreserving_smul (toPGLR c.out⁻¹) (volume : Measure ℍ)).quasiMeasurePreserving.ae h
  rw [ae_restrict_iff' ModularGroup.isClosed_fd.measurableSet]
  filter_upwards [h2] with τ hτ hτD
  rw [toPGLR_smul] at hτ
  refine hτ ?_
  rw [fdom]
  exact mem_iUnion.2 ⟨c, smul_mem_smul_set hτD⟩

lemma integrableOn_fd_comp' {E : Type*} [NormedAddCommGroup E] {F : ℍ → E}
    (hI : IntegrableOn F (fdom (Gamma1 M))) (c : SL(2, ℤ) ⧸ pmSL (Gamma1 M)) :
    IntegrableOn (fun z => F (c.out⁻¹ • z)) 𝒟 := by
  have h1 : IntegrableOn F (c.out⁻¹ • 𝒟) :=
    hI.mono_set (Set.subset_iUnion (fun c : SL(2, ℤ) ⧸ pmSL (Gamma1 M) => c.out⁻¹ • 𝒟) c)
  rw [← toPGLR_smul_set, ← Set.image_smul, (measurePreserving_smul (toPGLR c.out⁻¹)
    volume).integrableOn_image (measurableEmbedding_const_smul _)] at h1
  refine h1.congr_fun (fun z _ => ?_) ModularGroup.isClosed_fd.measurableSet
  show F (toPGLR c.out⁻¹ • z) = F (c.out⁻¹ • z)
  rw [toPGLR_smul]

lemma one_le_two_mul_sqrt_im {τ : ℍ} (h : τ ∈ 𝒟) : 1 ≤ 2 * τ.im ^ (1 / 2 : ℝ) := by
  have h1 : (1 / 4 : ℝ) ≤ τ.im := by linarith [(fd_subset_strip h).2]
  have h2 : (1 / 4 : ℝ) ^ (1 / 2 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h3 := Real.rpow_le_rpow (by norm_num) h1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [h2] at h3
  linarith

/-- **Dominated convergence on `𝒟 ∩ {Im ≤ Y}`** for the regularised rest part. -/
theorem tendsto_trunc_restPartS [NeZero M] (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (δ : (ZMod M)ˣ)
    (c : SL(2, ℤ) ⧸ pmSL (Gamma1 M)) (Y : ℝ) :
    Tendsto (fun s => ∫ τ in 𝒟 ∩ {z : ℍ | z.im ≤ Y},
        restPartS 2 M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) s (c.out⁻¹ • τ)) (𝓝[>] 0)
      (𝓝 (∫ τ in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, restPart0 M n δ (c.out⁻¹ • τ))) := by
  set δ'' : ZMod M := ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) with hδ''
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hmT : MeasurableSet (𝒟 ∩ {z : ℍ | z.im ≤ Y}) :=
    (ModularGroup.isClosed_fd.inter (isClosed_le UpperHalfPlane.continuous_im continuous_const)).measurableSet
  obtain ⟨B, hB⟩ := diag_bound_trunc hM hn hnM (unitOf M n * δ) c.out⁻¹ Y
  have hE := integrableOn_fd_comp' (integrableOn_ellDom hM 0 δ'' n) c
  have hEb := ae_fd_of_ae_fdom (norm_ellPartS_le_ae hM 0 δ'' hn) c
  have hT := ae_fd_of_ae_fdom (tendsto_restPartS_ae hM hn hnM δ) c
  have hsm : Measurable fun τ : ℍ => c.out⁻¹ • τ := by
    have h := measurable_const_smul (toPGLR c.out⁻¹) (α := ℍ)
    simpa only [toPGLR_smul] using h
  set C : ℝ := |B| + ‖scalVal 2 M n δ''‖ with hC
  have hC0 : 0 ≤ C := add_nonneg (abs_nonneg _) (norm_nonneg _)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun τ => C * (2 * τ.im ^ (1 / 2 : ℝ)) + ellDom 0 M n δ'' (c.out⁻¹ • τ)) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact ((measurable_restPartS hn' δ'' hs).comp hsm).aestronglyMeasurable
  · filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with s hs
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hEb, ae_restrict_mem hmT]
      with τ hτE hτm
    have hσ : 1 < ((2 : ℕ) : ℝ) / 2 + s := by norm_num; linarith [hs.1]
    have hsplit := diagS_split (k := 2) hσ hn' δ'' (c.out⁻¹ • τ)
    have e : restPartS 2 M n δ'' s (c.out⁻¹ • τ) =
        conj (KernelS.omegaS M 2 n δ'' s ((c.out⁻¹ • τ : ℍ) : ℂ) (-conj ((c.out⁻¹ • τ : ℍ) : ℂ))) *
          (((c.out⁻¹ • τ : ℍ).im : ℂ) ^ 2) - scalPartS 2 M n δ'' s (c.out⁻¹ • τ) -
            ellPartS 2 M n δ'' s (c.out⁻¹ • τ) := by
      rw [hsplit]; ring
    have hD := hB s hs.1 hs.2 τ hτm.1 hτm.2
    have hS : ‖scalPartS 2 M n δ'' s (c.out⁻¹ • τ)‖ ≤ ‖scalVal 2 M n δ''‖ := by
      rw [scalPartS_eq 2 M δ'' hn s, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (by norm_num) s)]
      exact mul_le_of_le_one_right (norm_nonneg _) (Real.rpow_le_one (by norm_num) (by norm_num) hs.1.le)
    have hEl : ‖ellPartS 2 M n δ'' s (c.out⁻¹ • τ)‖ ≤ ellDom 0 M n δ'' (c.out⁻¹ • τ) := hτE s hs.1.le
    have h1 := one_le_two_mul_sqrt_im hτm.1
    rw [e]
    calc _ ≤ ‖conj (KernelS.omegaS M 2 n δ'' s ((c.out⁻¹ • τ : ℍ) : ℂ) (-conj ((c.out⁻¹ • τ : ℍ) : ℂ))) *
          (((c.out⁻¹ • τ : ℍ).im : ℂ) ^ 2)‖ + ‖scalPartS 2 M n δ'' s (c.out⁻¹ • τ)‖ +
            ‖ellPartS 2 M n δ'' s (c.out⁻¹ • τ)‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ |B| + ‖scalVal 2 M n δ''‖ + ellDom 0 M n δ'' (c.out⁻¹ • τ) :=
          add_le_add (add_le_add (hD.trans (le_abs_self B)) hS) hEl
      _ ≤ C * (2 * τ.im ^ (1 / 2 : ℝ)) + ellDom 0 M n δ'' (c.out⁻¹ • τ) := by
          rw [← hC]
          exact add_le_add (le_mul_of_one_le_right hC0 h1) le_rfl
  · have hI : IntegrableOn (fun τ : ℍ => C * (2 * τ.im ^ (1 / 2 : ℝ)) + ellDom 0 M n δ'' (c.out⁻¹ • τ)) 𝒟 :=
      ((integrableOn_fd_im_rpow.const_mul 2).const_mul C).add hE
    exact hI.mono_set inter_subset_left
  · exact ae_restrict_of_ae_restrict_of_subset inter_subset_left hT

end RamanujanPetersson.EllW2


