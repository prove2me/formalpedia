-- Prove2me | solution 1 for AutomorphicForm.isCompact_and_exists_torusEmb_and_exists_tableMap_apply_eq_of_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/559613d9-6241-55c9-9f38-989b0eb8fb00

import Mathlib
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isCompact_and_exists_torusEmb_and_exists_tableMap_apply_eq_of_sq_eq

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped ComplexConjugate

theorem solution
    (L : Type) [Field L] [NumberField L]
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (X : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ))
    (hX : {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = AutomorphicForm.HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} ⊆ X)
    (d : ℕ) (w' : Fin d → HeightOneSpectrum (𝓞 L)) (hw'S : ∀ i : Fin d, w' i ∉ SL)
    (hw'i : Function.Injective w')
    (s : Fin d → ℂ)
    (hs : ∀ i : Fin d, s i ^ 2 =
      ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' i)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) :
    IsCompact (Set.range (fun θ : Fin d → AddCircle (1 : ℝ) =>
      fun i : Fin d => ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ)))) ∧
    (∃ emb : C((Fin d → AddCircle (1 : ℝ)), ↥(Set.range (fun θ : Fin d → AddCircle (1 : ℝ) =>
        fun i : Fin d => ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ))))),
      ∀ (θ : Fin d → AddCircle (1 : ℝ)) (i : Fin d),
        ((emb θ : ↥(Set.range (fun θ : Fin d → AddCircle (1 : ℝ) =>
          fun i : Fin d => ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ))))) : Fin d → ℂ × ℂ) i =
          ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ))) ∧
    (∀ i : Fin d, Continuous (fun p : ℂ × ℂ =>
      (((Real.sqrt (Ideal.absNorm (w' i).asIdeal : ℝ) : ℂ) * s i * (p.1 + p.2),
        AutomorphicForm.HeckeEigensystem.cNorm (w' i) *
            ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' i)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) +
          (p.1 * p.2 - 1)) : ℂ × ℂ))) ∧
    (∀ (i : Fin d) (q : ℂ × ℂ), ((fun p : ℂ × ℂ =>
      (((Real.sqrt (Ideal.absNorm (w' i).asIdeal : ℝ) : ℂ) * s i * (p.1 + p.2),
        AutomorphicForm.HeckeEigensystem.cNorm (w' i) *
            ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' i)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) +
          (p.1 * p.2 - 1)) : ℂ × ℂ)) ⁻¹' {q}).Finite) ∧
    ∃ bc : C(↥(Set.range (fun θ : Fin d → AddCircle (1 : ℝ) =>
        fun i : Fin d => ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ)))), X),
      ∀ (x : ↥(Set.range (fun θ : Fin d → AddCircle (1 : ℝ) =>
          fun i : Fin d => ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ))))) (i : Fin d),
        ((bc x : X) : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' i) =
          ((Real.sqrt (Ideal.absNorm (w' i).asIdeal : ℝ) : ℂ) * s i *
              (((x : Fin d → ℂ × ℂ) i).1 + ((x : Fin d → ℂ × ℂ) i).2),
            AutomorphicForm.HeckeEigensystem.cNorm (w' i) *
                ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' i)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) +
              (((x : Fin d → ℂ × ℂ) i).1 * ((x : Fin d → ℂ × ℂ) i).2 - 1)) := by
  classical

  let F : (Fin d → AddCircle (1 : ℝ)) → (Fin d → ℂ × ℂ) :=
    fun θ i => ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ))
  let ζ : Fin d → ℂ := fun i =>
    ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' i)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)
  let a : Fin d → ℂ := fun i => ((Real.sqrt (Ideal.absNorm (w' i).asIdeal : ℝ) : ℂ) * s i)
  let B : Fin d → ℂ × ℂ → ℂ × ℂ := fun i p =>
    ((Real.sqrt (Ideal.absNorm (w' i).asIdeal : ℝ) : ℂ) * s i * (p.1 + p.2),
      AutomorphicForm.HeckeEigensystem.cNorm (w' i) * ζ i + (p.1 * p.2 - 1))

  have hF : Continuous F :=
    continuous_pi fun i => ((fourier 1).continuous.comp (continuous_apply i)).prodMk
      ((fourier (-1)).continuous.comp (continuous_apply i))
  have hζ0 : ∀ i, ζ i ≠ 0 := fun i => Units.ne_zero _
  have hs2 : ∀ i, s i ^ 2 = ζ i := hs
  have hs0 : ∀ i, s i ≠ 0 := fun i h => hζ0 i (by rw [← hs2 i, h]; simp)
  have hN0 : ∀ i, (0 : ℝ) < (Ideal.absNorm (w' i).asIdeal : ℝ) := by
    intro i
    have : Ideal.absNorm (w' i).asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact (w' i).ne_bot
    positivity
  have hsqrt0 : ∀ i, ((Real.sqrt (Ideal.absNorm (w' i).asIdeal : ℝ) : ℂ)) ≠ 0 := fun i =>
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hN0 i)).ne'
  have ha0 : ∀ i, a i ≠ 0 := fun i => mul_ne_zero (hsqrt0 i) (hs0 i)
  have hBc : ∀ i, Continuous (B i) := by intro i; unfold B; fun_prop

  have hsnorm : ∀ i, ‖s i‖ = Real.sqrt ‖ζ i‖ := by
    intro i
    rw [← hs2 i, norm_pow, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨isCompact_range hF, ⟨⟨fun θ => ⟨F θ, ⟨θ, rfl⟩⟩, hF.subtype_mk _⟩, fun θ i => rfl⟩,
    hBc, ?_, ?_⟩
  ·
    intro i q
    show (B i ⁻¹' {q}).Finite
    let σ : ℂ := q.1 / a i
    let π : ℂ := q.2 - AutomorphicForm.HeckeEigensystem.cNorm (w' i) * ζ i + 1
    let P : Polynomial ℂ := Polynomial.X ^ 2 - Polynomial.C σ * Polynomial.X + Polynomial.C π
    have hP : P ≠ 0 := by
      intro h
      have h2 := congrArg (fun R : Polynomial ℂ => R.coeff 2) h
      simp [P] at h2
    refine ((Polynomial.finite_setOf_isRoot hP).image (fun z => (z, σ - z))).subset ?_
    rintro ⟨u, t⟩ hut
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.ext_iff, B] at hut
    obtain ⟨e1, e2⟩ := hut
    have hσ : u + t = σ := by
      simp only [σ]
      rw [eq_div_iff (ha0 i)]
      simp only [a]
      linear_combination e1
    have hπ : u * t = π := by
      simp only [π]
      linear_combination e2
    refine ⟨u, ?_, ?_⟩
    · show P.IsRoot u
      simp only [P, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      rw [← hσ, ← hπ]; ring
    · exact Prod.ext rfl (show σ - u = t by rw [← hσ]; ring)
  ·
    let G : (Fin d → ℂ × ℂ) → (HeightOneSpectrum (𝓞 L) → ℂ × ℂ) := fun x w =>
      if h : ∃ i, w' i = w then B h.choose (x h.choose)
      else if w ∈ SL then 0 else (0, AutomorphicForm.HeckeEigensystem.cNorm w *
        ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))
    have hGc : Continuous G := by
      refine continuous_pi fun w => ?_
      by_cases h : ∃ i, w' i = w
      · simp only [G, dif_pos h]
        exact (hBc _).comp (continuous_apply _)
      · simp only [G, dif_neg h]
        exact continuous_const
    have hGw : ∀ (x : Fin d → ℂ × ℂ) (i : Fin d), G x (w' i) = B i (x i) := by
      intro x i
      have hex : ∃ j, w' j = w' i := ⟨i, rfl⟩
      simp only [G, dif_pos hex]
      rw [hw'i hex.choose_spec]

    have hGX : ∀ θ : Fin d → AddCircle (1 : ℝ), G (F θ) ∈ X := by
      intro θ
      apply hX
      refine ⟨fun w hw => ?_, fun w hw => ?_⟩
      · have h : ¬ ∃ i, w' i = w := fun ⟨i, hi⟩ => hw'S i (hi ▸ hw)
        simp only [G, dif_neg h, if_pos hw]
      · by_cases h : ∃ i, w' i = w
        · obtain ⟨i, rfl⟩ := h
          rw [hGw]

          have hut : (fourier 1 (θ i) : ℂ) * fourier (-1) (θ i) = 1 := by
            rw [← fourier_add]; simp
          have ht : (fourier (-1) (θ i) : ℂ) = conj (fourier 1 (θ i)) := by
            rw [← fourier_neg]
          have hu1 : ‖(fourier 1 (θ i) : ℂ)‖ = 1 := by
            rw [fourier_one]; exact Circle.norm_coe _
          have hr : conj ((fourier 1 (θ i) : ℂ) + fourier (-1) (θ i)) =
              (fourier 1 (θ i) : ℂ) + fourier (-1) (θ i) := by
            rw [map_add, ht, Complex.conj_conj, add_comm]
          have hcN : AutomorphicForm.HeckeEigensystem.cNorm (w' i) =
              ((Ideal.absNorm (w' i).asIdeal : ℝ) : ℂ) := by
            simp [AutomorphicForm.HeckeEigensystem.cNorm]
          refine ⟨?_, ?_, ?_⟩
          ·
            show (B i (F θ i)).2 = _
            simp only [B, F, ζ, hut, sub_self, add_zero]
          ·
            show ‖(B i (F θ i)).1‖ ≤ _
            simp only [B, F]
            calc ‖(Real.sqrt (Ideal.absNorm (w' i).asIdeal : ℝ) : ℂ) * s i *
                    ((fourier 1 (θ i) : ℂ) + fourier (-1) (θ i))‖
                ≤ Real.sqrt (Ideal.absNorm (w' i).asIdeal : ℝ) * ‖s i‖ * (1 + 1) := by
                  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
                  gcongr
                  calc ‖(fourier 1 (θ i) : ℂ) + fourier (-1) (θ i)‖
                      ≤ ‖(fourier 1 (θ i) : ℂ)‖ + ‖(fourier (-1) (θ i) : ℂ)‖ := norm_add_le _ _
                    _ = 1 + 1 := by rw [ht, Complex.norm_conj, hu1]
              _ ≤ ((Ideal.absNorm (w' i).asIdeal : ℝ) + 1) * Real.sqrt ‖ζ i‖ := by
                  rw [← hsnorm i]
                  have hsq : Real.sqrt (Ideal.absNorm (w' i).asIdeal : ℝ) ^ 2 =
                      (Ideal.absNorm (w' i).asIdeal : ℝ) := Real.sq_sqrt (hN0 i).le
                  nlinarith [sq_nonneg (Real.sqrt (Ideal.absNorm (w' i).asIdeal : ℝ) - 1),
                    norm_nonneg (s i), Real.sqrt_nonneg (Ideal.absNorm (w' i).asIdeal : ℝ)]
          ·
            show conj (B i (F θ i)).1 = conj (B i (F θ i)).2 / (((‖(B i (F θ i)).2‖ : ℝ)) : ℂ) * (B i (F θ i)).1
            simp only [B, F, hut, sub_self, add_zero]
            have hx2 : AutomorphicForm.HeckeEigensystem.cNorm (w' i) * ζ i ≠ 0 :=
              mul_ne_zero (AutomorphicForm.HeckeEigensystem.cNorm_ne_zero _) (hζ0 i)
            have hx2n : (((‖AutomorphicForm.HeckeEigensystem.cNorm (w' i) * ζ i‖ : ℝ)) : ℂ) ≠ 0 :=
              Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hx2)
            rw [div_mul_eq_mul_div, eq_div_iff hx2n]
            rw [← hs2 i, hcN, hr.symm]
            simp only [map_mul, map_pow, Complex.conj_ofReal, hr, norm_mul, norm_pow, Complex.norm_real,
              Complex.ofReal_mul, Complex.ofReal_pow]
            rw [Real.norm_of_nonneg (hN0 i).le]
            have key : conj (s i) * s i = ((‖s i‖ : ℝ) : ℂ) ^ 2 := Complex.conj_mul' (s i)
            linear_combination (-1 : ℂ) * (((Ideal.absNorm (w' i).asIdeal : ℝ) : ℂ)) *
              ((Real.sqrt (Ideal.absNorm (w' i).asIdeal : ℝ) : ℂ)) *
              ((fourier 1 (θ i) : ℂ) + fourier (-1) (θ i)) * conj (s i) * key
        · simp only [G, dif_neg h, if_neg hw]
          refine ⟨by trivial, ?_, by simp⟩
          simp only [norm_zero]
          positivity
    refine ⟨⟨fun x => ⟨G x.1, ?_⟩, ?_⟩, ?_⟩
    · obtain ⟨θ, hθ⟩ := x.2
      rw [← hθ]; exact hGX θ
    · exact (hGc.comp continuous_subtype_val).subtype_mk _
    · intro x i
      show G x.1 (w' i) = _
      rw [hGw]

end S_AutomorphicForm_isCompact_and_exists_torusEmb_and_exists_tableMap_apply_eq_of_sq_eq
end P2MW
export P2MW.S_AutomorphicForm_isCompact_and_exists_torusEmb_and_exists_tableMap_apply_eq_of_sq_eq (solution)
