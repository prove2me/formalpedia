-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PiExteriorTensorFlattenedIndexEquivNested
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PiExteriorTensorFlattenedIndexEquivNested
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:07.962611+00:00
-- url     : https://prove2.me/theorems/86b1ba14-1472-4799-bef7-26be38b93cbe
-- title:
--   Pi Exterior Tensor Flattened Index Equiv Nested
-- statement:
--   Definitions and structural lemmas for Pi Exterior Tensor Flattened Index Equiv Nested, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PiExteriorTensorFlattenedIndexEquivNested.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientOfEquiv
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages
noncomputable section
open PiTensorProduct Module
open scoped TensorProduct
namespace GlobalTheory.JacStages
section SigmaCurry
variable {α : Type} [DecidableEq α] {β : α → Type} [∀ a, DecidableEq (β a)]
  (M : (Σ a, β a) → Type) [∀ p, AddCommGroup (M p)] [∀ p, Module ℂ (M p)]
theorem tprod_tprod_update_sigma [DecidableEq (Σ a, β a)] (x : ∀ p, M p) (a₀ : α) (b₀ : β a₀)
    (v : M ⟨a₀, b₀⟩) :
    (fun a => tprod ℂ fun b => Function.update x ⟨a₀, b₀⟩ v ⟨a, b⟩) =
      Function.update (fun a => tprod ℂ fun b => x ⟨a, b⟩) a₀
        (tprod ℂ (Function.update (fun b => x ⟨a₀, b⟩) b₀ v)) := by
  funext a
  by_cases h : a = a₀
  · subst h
    rw [Function.update_self]
    congr 1
    funext b
    by_cases hb : b = b₀
    · subst hb
      simp
    · rw [Function.update_of_ne hb, Function.update_of_ne]
      intro h'
      exact hb (eq_of_heq (Sigma.mk.inj h').2)
  · rw [Function.update_of_ne h]
    congr 1
    funext b
    rw [Function.update_of_ne]
    intro h'
    exact h (congrArg Sigma.fst h')
def curryML : MultilinearMap ℂ M (⨂[ℂ] a, ⨂[ℂ] b, M ⟨a, b⟩) where
  toFun x := tprod ℂ fun a => tprod ℂ fun b => x ⟨a, b⟩
  map_update_add' x p v w := by
    obtain ⟨a₀, b₀⟩ := p
    simp only [tprod_tprod_update_sigma]
    rw [MultilinearMap.map_update_add, MultilinearMap.map_update_add]
  map_update_smul' x p c v := by
    obtain ⟨a₀, b₀⟩ := p
    simp only [tprod_tprod_update_sigma]
    rw [MultilinearMap.map_update_smul, MultilinearMap.map_update_smul]
variable [Finite α] [∀ a, Finite (β a)]
def sigBasis : Basis (∀ p, Free.ChooseBasisIndex ℂ (M p)) ℂ (⨂[ℂ] p, M p) :=
  Basis.piTensorProduct fun p => Free.chooseBasis ℂ (M p)
def nestBasis : Basis (∀ a b, Free.ChooseBasisIndex ℂ (M ⟨a, b⟩)) ℂ (⨂[ℂ] a, ⨂[ℂ] b, M ⟨a, b⟩) :=
  Basis.piTensorProduct fun a => Basis.piTensorProduct fun b => Free.chooseBasis ℂ (M ⟨a, b⟩)
def sigmaCurry : (⨂[ℂ] p, M p) ≃ₗ[ℂ] ⨂[ℂ] a, ⨂[ℂ] b, M ⟨a, b⟩ :=
  (sigBasis M).equiv (nestBasis M) (Equiv.piCurry fun a b => Free.ChooseBasisIndex ℂ (M ⟨a, b⟩))
end SigmaCurry
section Flat
variable {s : ℕ} {t : Fin s → ℕ}
def flatTensorEquiv (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)] [∀ a b, Module ℂ (Y a b)] :
    (⨂[ℂ] c : Fin (∑ a, t a), Y (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) ≃ₗ[ℂ]
      ⨂[ℂ] a, ⨂[ℂ] b, Y a b :=
  (reindex ℂ (fun p : Σ a, Fin (t a) => Y p.1 p.2) finSigmaFinEquiv).symm.trans
    (sigmaCurry fun p : Σ a, Fin (t a) => Y p.1 p.2)
end Flat
end GlobalTheory.JacStages


