-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSignatureFstUniqueSylvester
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSignatureFstUniqueSylvester
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:29.46087+00:00
-- url     : https://prove2.me/theorems/9be4d1aa-c55a-4dd6-af24-90343aa49278
-- title:
--   Has Signature Fst Unique Sylvester
-- statement:
--   Definitions and structural lemmas for Has Signature Fst Unique Sylvester, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSignatureFstUniqueSylvester.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.SylvesterInertia
open Matrix Module
open scoped ComplexOrder
variable {n : Type} [Fintype n] [DecidableEq n]
def qf (J : Matrix n n ℂ) (x : n → ℂ) : ℂ := star x ⬝ᵥ J *ᵥ x
def inlMap (a b : ℕ) : (Fin a → ℂ) →ₗ[ℂ] (Fin a ⊕ Fin b → ℂ) where
  toFun z := Sum.elim z 0
  map_add' x y := by ext k; cases k <;> simp
  map_smul' c x := by ext k; cases k <;> simp
def inrMap (a b : ℕ) : (Fin b → ℂ) →ₗ[ℂ] (Fin a ⊕ Fin b → ℂ) where
  toFun z := Sum.elim 0 z
  map_add' x y := by ext k; cases k <;> simp
  map_smul' c x := by ext k; cases k <;> simp
def chg {a b : ℕ} (e : n ≃ Fin a ⊕ Fin b) (P : GL (Fin a ⊕ Fin b) ℂ) :
    (Fin a ⊕ Fin b → ℂ) →ₗ[ℂ] (n → ℂ) :=
  LinearMap.funLeft ℂ ℂ e ∘ₗ (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ).mulVecLin
end GlobalTheory.SylvesterInertia


