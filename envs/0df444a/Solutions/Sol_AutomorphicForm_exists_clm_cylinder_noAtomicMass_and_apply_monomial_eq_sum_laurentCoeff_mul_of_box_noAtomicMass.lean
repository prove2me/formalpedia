-- Prove2me | solution 1 for AutomorphicForm.exists_clm_cylinder_noAtomicMass_and_apply_monomial_eq_sum_laurentCoeff_mul_of_box_noAtomicMass
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/d7a48b2a-7cb6-5313-b960-8da2895d1563

import Mathlib
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Theorems.Thm_ContinuousLinearMap_exists_comp_torusEmb_eq_and_cylinder_noAtomicMass_of_box_noAtomicMass
import Theorems.Thm_ContinuousLinearMap_apply_comp_comp_torusEmb_eq_sum_laurentCoeff_mul_of_apply_fourier_eq
import Theorems.Thm_AutomorphicForm_isCompact_and_exists_torusEmb_and_exists_tableMap_apply_eq_of_sq_eq
import Theorems.Thm_ContinuousLinearMap_noAtomicMass_comp_of_finite_fibres
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_clm_cylinder_noAtomicMass_and_apply_monomial_eq_sum_laurentCoeff_mul_of_box_noAtomicMass

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped ComplexConjugate

theorem _root_.P2MW.S_AutomorphicForm_exists_clm_cylinder_noAtomicMass_and_apply_monomial_eq_sum_laurentCoeff_mul_of_box_noAtomicMass.solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (X : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (hXc : IsCompact X)
    (hX : {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = AutomorphicForm.HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} ⊆ X)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L))
    (hw'S : ∀ v ∈ T, w' v ∉ SL)
    (hw'i : ∀ v ∈ T, ∀ v' ∈ T, w' v = w' v' → v = v')
    (s : HeightOneSpectrum (𝓞 K) → ℂ)
    (hs : ∀ v ∈ T, s v ^ 2 =
      ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))
    (μ : C((Fin T.card → AddCircle (1 : ℝ)), ℂ) →L[ℂ] ℂ)
    (hμ : ∀ (τ : Fin T.card → AddCircle (1 : ℝ)), ∀ ε > (0 : ℝ),
        ∃ U : Fin T.card → Set (AddCircle (1 : ℝ)), (∀ i, IsOpen (U i) ∧ τ i ∈ U i) ∧
          ∀ g : C((Fin T.card → AddCircle (1 : ℝ)), ℂ),
            (∀ θ, (∃ i, θ i ∉ U i) → g θ = 0) → (∀ θ, ‖g θ‖ ≤ 1) → ‖μ g‖ < ε)
    (c : (Fin T.card → ℤ) → ℂ)
    (hc : ∀ (n : Fin T.card → ℤ) (e : C((Fin T.card → AddCircle (1 : ℝ)), ℂ)),
        (∀ θ, e θ = ∏ i, fourier (n i) (θ i)) → μ e = c n) :
    ∃ Δ : C(X, ℂ) →L[ℂ] ℂ,
      (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
        ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
          ∀ g : C(X, ℂ),
            (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v) ∉ U v) → g y = 0) →
            (∀ y, ‖g y‖ ≤ 1) → ‖Δ g‖ < ε) ∧
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ) (g : C(X, ℂ)),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).1 ^ ks v *
            ((AutomorphicForm.HeckeEigensystem.cNorm (w' v))⁻¹ *
              ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).2) ^ js v) →
        Δ g =
          ∑ n ∈ Fintype.piFinset
              (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
            (∏ i : Fin T.card,
              ((Real.sqrt (Ideal.absNorm (w' (T.equivFin.symm i).1).asIdeal : ℝ) : ℂ) *
                  s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)),
                  Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js (T.equivFin.symm i).1 *
              ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 :
                LaurentPolynomial ℂ).coeff (n i)) *
            c n := by
  classical

  have hwF_S : ∀ i : Fin T.card, w' (T.equivFin.symm i).1 ∉ SL := fun i => hw'S _ (T.equivFin.symm i).2
  have hwF_i : Function.Injective (fun i : Fin T.card => w' (T.equivFin.symm i).1) := by
    intro i j hij
    have h := hw'i _ (T.equivFin.symm i).2 _ (T.equivFin.symm j).2 hij
    exact T.equivFin.symm.injective (Subtype.ext h)
  have hsF : ∀ i : Fin T.card, (fun i : Fin T.card => s (T.equivFin.symm i).1) i ^ 2 =
      ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)),
        Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := fun i => hs _ (T.equivFin.symm i).2

  obtain ⟨hXKc, ⟨emb, hemb⟩, hBc, hBf, ⟨bc, hbc⟩⟩ :=
    AutomorphicForm.isCompact_and_exists_torusEmb_and_exists_tableMap_apply_eq_of_sq_eq L SL ξL X hX T.card
      (fun i : Fin T.card => w' (T.equivFin.symm i).1) hwF_S hwF_i
      (fun i : Fin T.card => s (T.equivFin.symm i).1) hsF

  obtain ⟨Λ, hΛ, hΛcyl⟩ :=
    ContinuousLinearMap.exists_comp_torusEmb_eq_and_cylinder_noAtomicMass_of_box_noAtomicMass T.card _ emb hemb μ hμ

  let compCLM : C(X, ℂ) →L[ℂ] C(↥(Set.range (fun θ : Fin T.card → AddCircle (1 : ℝ) =>
      fun i : Fin T.card => ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ)))), ℂ) :=
    { toFun := fun g => g.comp bc
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := ContinuousMap.continuous_precomp bc }
  refine ⟨Λ.comp compCLM, ?_, ?_⟩
  ·
    have hcyl := ContinuousLinearMap.noAtomicMass_comp_of_finite_fibres _ hXKc X Finset.univ
      (fun i : Fin T.card => w' (T.equivFin.symm i).1) _ (fun v _ => hBc v) (fun v _ q => hBf v q) bc
      (fun x v _ => hbc x v) Λ hΛcyl
    intro τ ε hε
    obtain ⟨U', hU'o, hU'g⟩ := hcyl (fun i => τ (T.equivFin.symm i).1) ε hε
    refine ⟨fun v => if h : v ∈ T then U' (T.equivFin ⟨v, h⟩) else Set.univ, ?_, ?_⟩
    · intro v hv
      have h1 := hU'o (T.equivFin ⟨v, hv⟩) (Finset.mem_univ _)
      simp only [dif_pos hv]
      refine ⟨h1.1, ?_⟩
      simpa using h1.2
    · intro g hg0 hg1
      show ‖Λ (g.comp bc)‖ < ε
      refine hU'g g ?_ hg1
      rintro y ⟨i, -, hi⟩
      refine hg0 y ⟨(T.equivFin.symm i).1, (T.equivFin.symm i).2, ?_⟩
      simpa [dif_pos (T.equivFin.symm i).2] using hi
  ·
    intro ks js g hg
    show Λ (g.comp bc) = _
    rw [hΛ]
    have hg' : ∀ x : X, g x = ∏ i : Fin T.card,
        (((x : X) : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' (T.equivFin.symm i).1)).1 ^ ks (T.equivFin.symm i).1 *
          ((AutomorphicForm.HeckeEigensystem.cNorm (w' (T.equivFin.symm i).1))⁻¹ *
            (((x : X) : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' (T.equivFin.symm i).1)).2) ^ js (T.equivFin.symm i).1 := by
      intro x
      rw [hg x, ← Finset.prod_coe_sort]
      exact (Fintype.prod_equiv T.equivFin.symm _ _ (fun _ => rfl)).symm
    exact ContinuousLinearMap.apply_comp_comp_torusEmb_eq_sum_laurentCoeff_mul_of_apply_fourier_eq T.card _ X emb hemb
      (fun i : Fin T.card => w' (T.equivFin.symm i).1)
      (fun i : Fin T.card => (Real.sqrt (Ideal.absNorm (w' (T.equivFin.symm i).1).asIdeal : ℝ) : ℂ))
      (fun i : Fin T.card => s (T.equivFin.symm i).1)
      (fun i : Fin T.card => ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)),
        Subgroup.mem_top _⟩ : ℂˣ) : ℂ))
      (fun i : Fin T.card => AutomorphicForm.HeckeEigensystem.cNorm (w' (T.equivFin.symm i).1))
      (fun i => AutomorphicForm.HeckeEigensystem.cNorm_ne_zero _) bc
      (fun x i => by rw [hbc x i]) (fun x i => by rw [hbc x i]) μ c hc
      (fun i : Fin T.card => ks (T.equivFin.symm i).1) (fun i : Fin T.card => js (T.equivFin.symm i).1) g hg'

end S_AutomorphicForm_exists_clm_cylinder_noAtomicMass_and_apply_monomial_eq_sum_laurentCoeff_mul_of_box_noAtomicMass
end P2MW
export P2MW.S_AutomorphicForm_exists_clm_cylinder_noAtomicMass_and_apply_monomial_eq_sum_laurentCoeff_mul_of_box_noAtomicMass (solution)
