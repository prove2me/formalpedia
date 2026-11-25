-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
-- name    : Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T03:47:38.898873+00:00
-- url     : https://prove2.me/theorems/eafe834d-6f1a-4e5f-8df5-ba7b6a964723
-- title:
--   Lemma MLin
-- statement:
--   Definitions and structural lemmas for Lemma MLin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
namespace Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
section General
variable {C : Type*} [Field C] {σ τ : Type*}
def killV (P : σ → Prop) (F : MvPowerSeries σ C) : MvPowerSeries σ C :=
  fun μ => if ∀ w ∈ μ.support, P w then coeff μ F else 0
end General
section Lin
variable {C : Type*} [Field C] {σ τ : Type*} [Fintype τ]
def linS (M : τ → σ → C) : σ → MvPowerSeries τ C := fun w => ∑ c, M c w • (X c : MvPowerSeries τ C)
end Lin
section Rows
variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {ι ι' : Type} [Fintype ι]
  [Fintype ι']
theorem finset_fin_two_eq_cases (g g' : Fin 2) : g' = g ∨ g' = 1 - g := by revert g g'; decide
def rowM (g : Fin 2) (e : ι → I g → C) (v' : ι' → I (1 - g) → C) : ι ⊕ ι' → WV I → C :=
  Sum.elim (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b))
end Rows
section Bridge
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
  {Xc : Cart V d I J} (S : Sys Xc)
variable {τ : Type} [Fintype τ]
end Bridge
section Pull
variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {ι ι' : Type} [Fintype ι]
  [Fintype ι']
theorem fin_two_eq_one_sub_of_ne {g g' : Fin 2} (h : g' ≠ g) : g' = 1 - g := (finset_fin_two_eq_cases g g').resolve_left h
def rowIdx (g : Fin 2) : WV I → I g ⊕ I (1 - g) := fun w =>
  if h : w.1 = g then Sum.inl (h ▸ w.2) else Sum.inr (fin_two_eq_one_sub_of_ne h ▸ w.2)
def ttPull (t : ∀ g, I g → MvPowerSeries (I g) C) (g : Fin 2) (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) : I g ⊕ I (1 - g) → MvPowerSeries (ι ⊕ ι') C :=
  Sum.elim (fun c => rename (Function.Embedding.inl : ι ↪ ι ⊕ ι') (subst (linS e) (t g c)))
    (fun c => rename (Function.Embedding.inr : ι' ↪ ι ⊕ ι') (subst (linS v') (t (1 - g) c)))
end Pull
section RowDataPull
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (Xr : RowData C V d I J) {ι ι' : Type} [Fintype ι]
  [Fintype ι']
end RowDataPull
end Formalism.L2.FormalSeriesBounds


