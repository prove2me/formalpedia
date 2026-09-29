-- Prove2me | solution 1 for AutomorphicForm.WhittakerModel.exists_mem_span_forall_diagOne_eq_of_shell_window_of_localLevelOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/11e4e3cf-bf5f-503d-bbd7-0aaaebb2553c

import Mathlib
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_mem_span_forall_diagOne_eq_of_shell_window_of_irreducible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_WhittakerModel_exists_mem_span_forall_diagOne_eq_of_shell_window_of_localLevelOne

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker NumberField.AdelicLevel

namespace C2cjf

open IsDedekindDomain NumberField NumberField.AdelicLevel AdelicDock

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem localLevelOne_pow_le (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (b : ℕ) (hNb : ¬ p.asIdeal ^ (b + 1) ∣ N) :
    AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) ≤ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N := by
  classical
  have hpb : (p.asIdeal ^ b : Ideal (𝓞 ℚ)) ≠ ⊥ := pow_ne_zero _ p.ne_bot
  have hle : idealBound (𝓞 ℚ) (p.asIdeal ^ b) p ≤ idealBound (𝓞 ℚ) N p := by
    rw [idealBound_of_ne_bot hpb, idealBound_of_ne_bot hN, WithZero.exp_le_exp, neg_le_neg_iff, Int.ofNat_le]
    have hirr : Irreducible (Associates.mk p.asIdeal) := Associates.irreducible_mk.mpr p.irreducible

    have h1 : (Associates.mk p.asIdeal).count (Associates.mk N).factors ≤ b := by
      by_contra hlt
      push_neg at hlt
      have key := (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hN) hirr).mpr hlt
      rw [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd] at key
      exact hNb key

    have h2 : b ≤ (Associates.mk p.asIdeal).count (Associates.mk (p.asIdeal ^ b)).factors := by
      apply (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hpb) hirr).mp
      rw [← Associates.mk_pow]
    exact h1.trans h2
  intro k hk
  rw [AdelicDock.mem_localLevelOne_iff] at hk ⊢
  obtain ⟨h₁, h₂⟩ := hk
  exact ⟨⟨h₁.integral, h₁.lowerLeft.trans hle, h₁.lowerRight.trans hle⟩,
    ⟨h₂.integral, h₂.lowerLeft.trans hle, h₂.lowerRight.trans hle⟩⟩

theorem exists_not_pow_succ_dvd (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) : ∃ b : ℕ, ¬ p.asIdeal ^ (b + 1) ∣ N := by
  classical
  refine ⟨(Associates.mk p.asIdeal).count (Associates.mk N).factors, fun hdvd => ?_⟩
  have hirr : Irreducible (Associates.mk p.asIdeal) := Associates.irreducible_mk.mpr p.irreducible
  have := (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hN) hirr).mp (by
    rw [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd]; exact hdvd)
  omega

end C2cjf

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))

    (f : (p.adicCompletion ℚ)ˣ → ℂ) (n₁ n₀ : ℤ) (m : ℕ)
    (hf₀ : ∀ y : (p.adicCompletion ℚ)ˣ,
      WithZero.exp (-n₁) < Valued.v (y : p.adicCompletion ℚ) ∨ Valued.v (y : p.adicCompletion ℚ) < WithZero.exp (-n₀) →
        f y = 0)
    (hf₁ : ∀ y u : (p.adicCompletion ℚ)ˣ, Valued.v (u : p.adicCompletion ℚ) = 1 →
      Valued.v ((u : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(m : ℤ)) → f (y * u) = f y) :
    ∃ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ y : (p.adicCompletion ℚ)ˣ, w (diagOne y) = f y := by
  obtain ⟨b, hNb⟩ := C2cjf.exists_not_pow_succ_dvd p N hN
  exact AutomorphicForm.WhittakerModel.exists_mem_span_forall_diagOne_eq_of_shell_window_of_irreducible p w₂base hw₂law b
    (fun k hk g => hw₂K k (C2cjf.localLevelOne_pow_le p N hN b hNb hk) g) hw₂ne hw₂irr f n₁ n₀ m hf₀ hf₁

end S_AutomorphicForm_WhittakerModel_exists_mem_span_forall_diagOne_eq_of_shell_window_of_localLevelOne
end P2MW
export P2MW.S_AutomorphicForm_WhittakerModel_exists_mem_span_forall_diagOne_eq_of_shell_window_of_localLevelOne (solution)
