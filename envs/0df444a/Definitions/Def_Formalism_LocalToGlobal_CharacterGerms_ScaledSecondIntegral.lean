-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
-- name    : Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:16.194819+00:00
-- url     : https://prove2.me/theorems/c53c468e-a39f-469d-b568-5ff39eb994b6
-- title:
--   Scaled Second Integral
-- statement:
--   Definitions and structural lemmas for Scaled Second Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ScaledSecondIntegral.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeNatCast
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.FormalSeriesBounds
open Finset
noncomputable section
variable {C : Type*} [Field C] {V : VF C} {d : ℕ} {I J : Type*}
section Ops
variable {N : Type*}
end Ops
namespace Cart
variable (X : Cart V d I J)
def IsCurve (a : ZMod d) (u : I → C) (x : ℕ → I ⊕ J → C) : Prop :=
  x ∈ X.Ty ∧ x 0 = Sum.elim u 0 ∧ ∀ (i : ℕ) n, X.ty n ≠ a + i → x i n = 0
section Std
variable [DecidableEq I]
theorem exists_std (b : I) : ∃ x, X.IsCurve (X.ty (Sum.inl b)) (Pi.single b 1) x := by
  have hu : ∀ c, V.Ge 0 ((Pi.single b (1 : C) : I → C) c) := by
    intro c
    by_cases hc : c = b
    · subst hc
      simpa using (VF.Ge.one (V := V))
    · simpa [Pi.single_apply, hc] using (VF.Ge.zero (V := V) 0)
  have hty : ∀ c, X.ty (Sum.inl c) ≠ X.ty (Sum.inl b) → (Pi.single b (1 : C) : I → C) c = 0 := by
    intro c hc
    have : c ≠ b := fun h => hc (h ▸ rfl)
    simp [Pi.single_apply, this]
  obtain ⟨x, hx, h0, h1⟩ := X.t4 _ _ hu hty
  exact ⟨x, hx, h0, h1⟩
def std (b : I) : ℕ → I ⊕ J → C := Classical.choose (X.exists_std b)
variable [Fintype I]
def lift (h : I ⊕ J → C) : ℕ → I ⊕ J → C :=
  (∑ b, teich V.l (h (Sum.inl b)) (X.std b)) + const0 (Sum.elim 0 (fun j => h (Sum.inr j)))
def rem (x : ℕ → I ⊕ J → C) : ℕ → (ℕ → I ⊕ J → C)
  | 0 => x
  | s + 1 => rem x s - Vpow s (X.lift (rem x s s))
end Std
def Good (a : ZMod d) (u : I → C) (x : ℕ → I ⊕ J → C) : Prop :=
  X.IsCurve a u x ∧ ∀ c, x 1 (Sum.inl c) = 0
def V2 (_X : Cart V d I J) (x : ℕ → I ⊕ J → C) : I → C := fun b => (V.l : C) * x 2 (Sum.inl b)
def c0' (_X : Cart V d I J) (x : ℕ → I ⊕ J → C) : J → C := fun j => (V.l : C) * x 1 (Sum.inr j)
variable {X}
end Cart
end
end Formalism.L2.FormalSeriesBounds


