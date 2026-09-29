-- Prove2me | solution 1 for AutomorphicForm.WhittakerModel.eq_zero_of_forall_apply_diagOne_eq_zero_of_mem_span_of_localLevelOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/fc155b40-e6c8-5571-8c86-cf9995826a63

import Mathlib
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_AutomorphicForm_LocalFunctionSpace_eq_zero_of_forall_apply_diagOne_eq_zero_of_irreducible_of_admissible
import Theorems.Thm_NumberField_StandardAddChar_psiLocal_rat_eq_psiV
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_WhittakerModel_eq_zero_of_forall_apply_diagOne_eq_zero_of_mem_span_of_localLevelOne

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker NumberField.AdelicLevel

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
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) :
    ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      (∀ y : (p.adicCompletion ℚ)ˣ, w (diagOne y) = 0) → w = 0 := by
  classical
  set S : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) :=
    Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) with hS
  have hK1open : IsOpen (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Set (GL (Fin 2) (p.adicCompletion ℚ))) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN).2
  have hgen : ∀ h : GL (Fin 2) (p.adicCompletion ℚ), (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) ∈ S :=
    fun h => Submodule.subset_span ⟨h, rfl⟩

  have hstab : ∀ W ∈ S, ∀ k : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * k)) ∈ S := by
    intro W hW k
    induction hW using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      have : (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (fun g' : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g' * h)) (g * k)) =
          fun g => w₂base (g * (k * h)) := by
        funext g; simp only [mul_assoc]
      rw [this]; exact hgen (k * h)
    | zero => exact S.zero_mem
    | add x y _ _ hx hy => exact S.add_mem hx hy
    | smul a x _ hx => exact S.smul_mem a hx

  have hsm : ∀ W ∈ S, ∃ K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
      IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ K, (fun g => W (g * k)) = W := by
    intro W hW
    induction hW using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      let K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)) :=
        { carrier := {k | h⁻¹ * k * h ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N}
          mul_mem' := fun {a b} ha hb => by
            simp only [Set.mem_setOf_eq] at ha hb ⊢
            have := Subgroup.mul_mem _ ha hb
            simpa [mul_assoc] using this
          one_mem' := by simp
          inv_mem' := fun {a} ha => by
            simp only [Set.mem_setOf_eq] at ha ⊢
            have := Subgroup.inv_mem _ ha
            simpa [mul_assoc] using this }
      refine ⟨K, ?_, fun k hk => ?_⟩
      · have hc : Continuous fun k : GL (Fin 2) (p.adicCompletion ℚ) => h⁻¹ * k * h := by fun_prop
        exact hK1open.preimage hc
      · funext g
        show w₂base (g * k * h) = w₂base (g * h)
        rw [show g * k * h = g * h * (h⁻¹ * k * h) by group]
        exact hw₂K _ hk _
    | zero => exact ⟨⊤, isOpen_univ, fun k _ => rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨K₁, o₁, h₁⟩ := hx
      obtain ⟨K₂, o₂, h₂⟩ := hy
      refine ⟨K₁ ⊓ K₂, o₁.inter o₂, fun k hk => ?_⟩
      funext g
      have e1 := congrFun (h₁ k hk.1) g
      have e2 := congrFun (h₂ k hk.2) g
      simp only [Pi.add_apply] at e1 e2 ⊢
      rw [e1, e2]
    | smul a x _ hx =>
      obtain ⟨K, o, h⟩ := hx
      refine ⟨K, o, fun k hk => ?_⟩
      funext g
      have e1 := congrFun (h k hk) g
      simp only [Pi.smul_apply] at e1 ⊢
      rw [e1]

  have hpsi : ∀ W ∈ S, ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      W (AutomorphicForm.unipotentGL2 x * g) = NumberField.StandardAddChar.psiV p x * W g := by
    intro W hW
    induction hW using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨h, rfl⟩ := hw
      intro x g
      show w₂base (AutomorphicForm.unipotentGL2 x * g * h) = NumberField.StandardAddChar.psiV p x * w₂base (g * h)
      have hu : (AutomorphicForm.unipotentGL2 x : GL (Fin 2) (p.adicCompletion ℚ)) = unipotent x := Units.ext rfl
      rw [mul_assoc, hu, hw₂law, NumberField.StandardAddChar.psiLocal_rat_eq_psiV]
    | zero => intro x g; simp
    | add w w' _ _ hw hw' => intro x g; simp only [Pi.add_apply, hw, hw']; ring
    | smul a w _ hw => intro x g; simp only [Pi.smul_apply, hw, smul_eq_mul]; ring

  have hirr : ∀ T : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), T ≤ S →
      (∀ W ∈ T, ∀ k : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * k)) ∈ T) → T = ⊥ ∨ T = S := by
    intro T hT hTst
    by_cases hbot : T = ⊥
    · exact Or.inl hbot
    right
    refine le_antisymm hT ?_
    obtain ⟨w, hwT, hw0⟩ := (Submodule.ne_bot_iff T).mp hbot
    have hbaseT : w₂base ∈ T := by
      have hmem := hw₂irr w (hT hwT) hw0
      refine (Submodule.span_le.mpr ?_) hmem
      rintro _ ⟨h, rfl⟩
      exact hTst w hwT h
    rw [hS]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h, rfl⟩
    exact hTst _ hbaseT h

  have hadm : ∀ K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∀ T : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), T ≤ S →
        (∀ W ∈ T, ∀ k ∈ K, (fun g => W (g * k)) = W) → FiniteDimensional ℂ T := by
    intro K hK T hT hfix
    obtain ⟨B, hB⟩ := hw₂adm K hK
    have hle : T ≤ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)) :=
      fun W hW => hB W (hT hW) (fun k hk g => congrFun (hfix W hW k hk) g)
    haveI : FiniteDimensional ℂ (Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) :=
      FiniteDimensional.span_of_finite ℂ B.finite_toSet
    exact Submodule.finiteDimensional_of_le hle
  exact AutomorphicForm.LocalFunctionSpace.eq_zero_of_forall_apply_diagOne_eq_zero_of_irreducible_of_admissible p S
    hstab hsm hpsi hirr hadm

end S_AutomorphicForm_WhittakerModel_eq_zero_of_forall_apply_diagOne_eq_zero_of_mem_span_of_localLevelOne
end P2MW
export P2MW.S_AutomorphicForm_WhittakerModel_eq_zero_of_forall_apply_diagOne_eq_zero_of_mem_span_of_localLevelOne (solution)
