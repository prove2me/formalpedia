-- Prove2me | solution 1 for AAInvW.grouping
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:29:50.280909+00:00
-- url     : https://prove2.me/submissions/0877e178-055b-4e28-8ffd-d08ff9d81b68

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CauchyBinet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open AAInvW
namespace AAInvW
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {t N : ℕ} (κ : Fin N → ℕ) (hκ : Function.Injective κ)
    (F : (Fin t → Fin N) → A)
    (hF : ∀ (d : Fin t → Fin N) (τ : Equiv.Perm (Fin t)),
      F (d ∘ τ) = ((Equiv.Perm.sign τ : ℤ) : A) * F d)
    (hF0 : ∀ d : Fin t → Fin N, ¬ Function.Injective d → F d = 0) (W : (Fin t → Fin N) → ℂ) :
    ∑ d, W d • F d = ∑ C : Fin t → Fin N,
      if StrictMono (fun l => κ (C l)) then
        (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * W (C ∘ σ)) • F C else 0 := by
  classical
  have hR : ∀ C : Fin t → Fin N,
      (if StrictMono (fun l => κ (C l)) then
        (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * W (C ∘ σ)) • F C else 0) =
      ∑ σ : Equiv.Perm (Fin t),
        if StrictMono (fun l => κ (C l)) then W (C ∘ σ) • F (C ∘ σ) else 0 := by
    intro C
    split_ifs with h
    · rw [Finset.sum_smul]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [hF C σ, mul_smul]
      first
      | rw [Int.cast_smul_eq_zsmul ℂ, zsmul_eq_mul, mul_smul_comm]
      | simp only [Algebra.smul_def, map_intCast, ← mul_assoc, (Int.cast_commute _ _).eq]
    · simp
  simp only [hR]
  rw [← Fintype.sum_prod_type']
  symm
  refine Finset.sum_bij_ne_zero (fun p _ _ => p.1 ∘ p.2) (fun _ _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · rintro ⟨C, σ⟩ _ h1 ⟨C', σ'⟩ _ h2 heq
    have hC : StrictMono (fun l => κ (C l)) := by
      by_contra hc
      exact h1 (by simp [hc])
    have hC' : StrictMono (fun l => κ (C' l)) := by
      by_contra hc
      exact h2 (by simp [hc])
    have heq' : C ∘ σ = C' ∘ σ' := heq
    have e1 : Set.range (fun l => κ (C l)) = Set.range (fun l => κ (C' l)) := by
      rw [← σ.surjective.range_comp (fun l => κ (C l)), ← σ'.surjective.range_comp (fun l => κ (C' l))]
      congr 1
      funext x
      exact congrArg κ (congrFun heq' x)
    have e2 : (fun l => κ (C l)) = (fun l => κ (C' l)) := by
      first
      | exact (StrictMono.range_inj hC hC').1 e1
      | exact (WellFounded.eq_strictMono_iff_eq_range wellFounded_lt hC hC').1 e1
    have e3 : C = C' := funext fun l => hκ (congrFun e2 l)
    subst e3
    have e4 : σ = σ' := Equiv.ext fun x => hC.injective (congrArg κ (congrFun heq' x))
    rw [e4]
  · intro d _ hd
    have hinj : Function.Injective d := by
      by_contra hni
      apply hd
      simp [hF0 d hni]
    have hmono : Monotone ((fun l => κ (d l)) ∘ Tuple.sort (fun l => κ (d l))) :=
      Tuple.monotone_sort _
    have hsm : StrictMono (fun l => κ ((d ∘ Tuple.sort (fun l => κ (d l))) l)) :=
      hmono.strictMono_of_injective ((hκ.comp hinj).comp (Tuple.sort (fun l => κ (d l))).injective)
    have hcomp : (d ∘ Tuple.sort (fun l => κ (d l))) ∘ (Tuple.sort (fun l => κ (d l))).symm = d := by
      funext x
      simp
    refine ⟨(d ∘ Tuple.sort (fun l => κ (d l)), (Tuple.sort (fun l => κ (d l))).symm),
      Finset.mem_univ _, ?_, ?_⟩
    · dsimp only
      rw [if_pos hsm, hcomp]
      exact hd
    · exact hcomp
  · rintro ⟨C, σ⟩ _ h1
    have hC : StrictMono (fun l => κ (C l)) := by
      by_contra hc
      exact h1 (by simp [hc])
    dsimp only
    rw [if_pos hC]
end AAInvW
