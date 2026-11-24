-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:19:04.080941+00:00
-- url     : https://prove2.me/theorems/9b8dde25-2dd2-4b58-bfbd-140c21f4695f
-- title:
--   PPAssemble
-- statement:
--   Definitions and structural lemmas for PPAssemble, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/PPAssemble.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GlobWIff
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
namespace PI.ScRefExists.Sk
def Ap (I : Formalism.MainNotions.S.AutInst) (p : ℕ) : Subalgebra (𝓞 I.E) I.E where
  carrier := {x | ∃ s : ℕ, Nat.Coprime s p ∧ ∃ a : 𝓞 I.E, (s : I.E) * x = (a : I.E)}
  mul_mem' := by
    rintro x y ⟨s, hs, a, ha⟩ ⟨t, ht, b, hb⟩
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, a * b, ?_⟩
    push_cast at ha hb ⊢
    linear_combination (↑t * y) * ha + (a : I.E) * hb
  add_mem' := by
    rintro x y ⟨s, hs, a, ha⟩ ⟨t, ht, b, hb⟩
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, (t : 𝓞 I.E) * a + (s : 𝓞 I.E) * b, ?_⟩
    push_cast at ha hb ⊢
    linear_combination (↑t : I.E) * ha + (↑s : I.E) * hb
  algebraMap_mem' := by
    intro a
    exact ⟨1, Nat.coprime_one_left p, a, by simp⟩
def LA (I : Formalism.MainNotions.S.AutInst) (p : ℕ) : Submodule (Ap I p) (Fin I.n → I.E) :=
  Submodule.span (Ap I p) (I.L : Set (Fin I.n → I.E))
def ApPID : Prop := ∀ (I : Formalism.MainNotions.S.AutInst) (p : ℕ), p.Prime → IsPrincipalIdealRing (Ap I p)
def WFrame : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (p r k : ℕ) (e f : Fin r → Fin I.n → I.E) (M : ℕ),
    p.Prime → I.n = 2 * r + k + 1 →
    (∀ a b, hG I (e a) (e b) = 0) → (∀ a b, hG I (f a) (f b) = 0) →
    (∀ a b, hG I (e a) (f b) = if a = b then 1 else 0) →
    Nat.Coprime M p → (∀ a, M • e a ∈ I.L ∧ M • f a ∈ I.L) →
    ∃ w wd : Fin (k + 1) → Fin I.n → I.E,
      (∀ i, w i ∈ LA I p ∧ wd i ∈ LA I p) ∧
      (∀ a i, hG I (e a) (w i) = 0 ∧ hG I (f a) (w i) = 0 ∧
        hG I (e a) (wd i) = 0 ∧ hG I (f a) (wd i) = 0) ∧
      (∀ i j, hG I (wd i) (w j) = if i = j then 1 else 0) ∧
      ∀ y ∈ I.L, y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w) ∧
        y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range wd)
def PPAssemble : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (p m r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M : ℕ)
    (w wd : Fin (k + 1) → Fin I.n → I.E),
    p.Prime → 1 ≤ m → Hyp I (p ^ m) r k θ e f M →
    (∀ i, w i ∈ LA I p ∧ wd i ∈ LA I p) →
    (∀ a i, hG I (e a) (w i) = 0 ∧ hG I (f a) (w i) = 0 ∧
        hG I (e a) (wd i) = 0 ∧ hG I (f a) (wd i) = 0) →
    (∀ i j, hG I (wd i) (w j) = if i = j then 1 else 0) →
    (∀ y ∈ I.L, y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w) ∧
        y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range wd)) →
    Concl I (p ^ m) r k θ e f M
end PI.ScRefExists.Sk


