-- Prove2me | solution 1 for AutomorphicForm.WhittakerModel.forall_mem_span_smooth_and_law_and_central_and_growth_and_shellRecurrence
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/f354891d-4c56-5873-bb5a-a725d9995fab

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_forall_diagZ_mul_eq_zero_and_norm_le_mul_zpow_of_admissible
import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_polynomial_forall_diagZ_mul_eq_zero_and_sum_coeff_mul_eq_zero_of_admissible
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_WhittakerModel_forall_mem_span_smooth_and_law_and_central_and_growth_and_shellRecurrence

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    :
    ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      (∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
        ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) ∧
      (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)), w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g) ∧
      (∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w g) ∧
      (∃ (C A' : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
        ‖w (diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤ C * (Ideal.absNorm p.asIdeal : ℝ) ^ (A' * m)) ∧
      (∃ (N₁ : ℤ) (D : Polynomial ℂ) (M : ℕ), D.eval 0 ≠ 0 ∧
        ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
          (∀ m : ℤ, m < N₁ → w (diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k) = 0) ∧
          (∀ m : ℕ, M ≤ m →
            ∑ i ∈ Finset.range (D.natDegree + 1), D.coeff i * w (diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ (N₁ + (m : ℤ) - (i : ℤ)) * k) = 0)) := by
  classical

  set V : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) :=
    Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) with hV

  have hstab : ∀ W ∈ V, ∀ h : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * h)) ∈ V := by
    intro W hW h
    induction hW using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h', rfl⟩ := hx
      refine Submodule.subset_span ⟨h * h', ?_⟩
      funext g
      simp only [mul_assoc]
    | zero => exact V.zero_mem
    | add x y _ _ hx hy =>
      have : (fun g => (x + y) (g * h)) = (fun g => x (g * h)) + fun g => y (g * h) := rfl
      rw [this]; exact V.add_mem hx hy
    | smul a x _ hx =>
      have : (fun g => (a • x) (g * h)) = a • fun g => x (g * h) := rfl
      rw [this]; exact V.smul_mem a hx

  have hlaw : ∀ W ∈ V, ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      W (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * W g := by
    intro W hW
    induction hW using Submodule.span_induction with
    | mem W' hW' =>
      obtain ⟨h, rfl⟩ := hW'
      intro x g
      show w₂base (unipotent x * g * h) = _ * w₂base (g * h)
      rw [mul_assoc, hw₂law]
    | zero => intro x g; simp
    | add W₁ W₂ _ _ h₁ h₂ => intro x g; simp only [Pi.add_apply, h₁, h₂, mul_add]
    | smul a W' _ h' => intro x g; simp only [Pi.smul_apply, h', smul_eq_mul]; ring

  have hKo : IsOpen (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set (GL (Fin 2) (p.adicCompletion ℚ))) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN).2
  have hsm : ∀ W ∈ V, ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
      IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g := by
    intro W hW
    induction hW using Submodule.span_induction with
    | mem W' hW' =>
      obtain ⟨h, rfl⟩ := hW'
      refine ⟨(AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N).map (MulAut.conj h).toMonoidHom, ?_, ?_⟩
      · rw [Subgroup.coe_map]
        have : ((MulAut.conj h).toMonoidHom : GL (Fin 2) (p.adicCompletion ℚ) → GL (Fin 2) (p.adicCompletion ℚ)) =
            ((Homeomorph.mulLeft h).trans (Homeomorph.mulRight h⁻¹)) := by
          funext k; simp [MulAut.conj_apply, Homeomorph.mulLeft, Homeomorph.mulRight]
        rw [this]
        exact ((Homeomorph.mulLeft h).trans (Homeomorph.mulRight h⁻¹)).isOpenMap _ hKo
      · rintro k ⟨k₀, hk₀, rfl⟩ g
        show w₂base (g * ((MulAut.conj h) k₀) * h) = w₂base (g * h)
        rw [MulAut.conj_apply, show g * (h * k₀ * h⁻¹) * h = g * h * k₀ by group]
        exact hw₂K k₀ hk₀ (g * h)
    | zero => exact ⟨⊤, isOpen_univ, fun k _ g => rfl⟩
    | add W₁ W₂ _ _ h₁ h₂ =>
      obtain ⟨U₁, hU₁, hW₁⟩ := h₁
      obtain ⟨U₂, hU₂, hW₂⟩ := h₂
      refine ⟨U₁ ⊓ U₂, ?_, fun k hk g => ?_⟩
      · rw [Subgroup.coe_inf]; exact hU₁.inter hU₂
      · simp only [Pi.add_apply, hW₁ k (Subgroup.mem_inf.mp hk).1, hW₂ k (Subgroup.mem_inf.mp hk).2]
    | smul a W' _ h' =>
      obtain ⟨U, hU, hW'⟩ := h'
      exact ⟨U, hU, fun k hk g => by simp only [Pi.smul_apply, hW' k hk]⟩

  have hcen : ∀ W ∈ V, ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      W (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * W g := by
    intro W hW
    induction hW using Submodule.span_induction with
    | mem W' hW' =>
      obtain ⟨h, rfl⟩ := hW'
      intro z g
      show w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g * h) = _ * w₂base (g * h)
      rw [mul_assoc, hcentral]
    | zero => intro z g; simp
    | add W₁ W₂ _ _ h₁ h₂ => intro z g; simp only [Pi.add_apply, h₁, h₂, mul_add]
    | smul a W' _ h' => intro z g; simp only [Pi.smul_apply, h', smul_eq_mul]; ring

  have hgrow := AutomorphicForm.WhittakerModel.exists_forall_diagZ_mul_eq_zero_and_norm_le_mul_zpow_of_admissible p V
    hstab hlaw hsm hw₂adm hπ hϖ
  have hrec := AutomorphicForm.WhittakerModel.exists_polynomial_forall_diagZ_mul_eq_zero_and_sum_coeff_mul_eq_zero_of_admissible
    p V hstab hlaw hsm hw₂adm hπ hϖ

  have hq1 : (1 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) := by
    have h0 : Ideal.absNorm p.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact p.ne_bot
    have h1 : Ideal.absNorm p.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact p.isPrime.ne_top
    have : 2 ≤ Ideal.absNorm p.asIdeal := by omega
    exact_mod_cast this
  have hqpos : (0 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) := lt_trans zero_lt_one hq1
  intro w hw
  refine ⟨hsm w hw, hlaw w hw, hcen w hw, ?_, hrec w hw⟩
  obtain ⟨N₁, C, R, hC, hR, hCR⟩ := hgrow w hw
  refine ⟨C, Real.log R / Real.log (Ideal.absNorm p.asIdeal : ℝ), fun m _ k hk => ?_⟩
  calc ‖w (diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤ C * R ^ m :=
        ((hCR k hk m).2)
    _ = C * (Ideal.absNorm p.asIdeal : ℝ) ^ (Real.log R / Real.log (Ideal.absNorm p.asIdeal : ℝ) * (m : ℝ)) := by
        congr 1
        rw [Real.rpow_def_of_pos hqpos, ← Real.exp_log (zpow_pos hR m), Real.log_zpow]
        congr 1
        have hlq : Real.log (Ideal.absNorm p.asIdeal : ℝ) ≠ 0 := (Real.log_pos hq1).ne'
        field_simp

end S_AutomorphicForm_WhittakerModel_forall_mem_span_smooth_and_law_and_central_and_growth_and_shellRecurrence
end P2MW
export P2MW.S_AutomorphicForm_WhittakerModel_forall_mem_span_smooth_and_law_and_central_and_growth_and_shellRecurrence (solution)
