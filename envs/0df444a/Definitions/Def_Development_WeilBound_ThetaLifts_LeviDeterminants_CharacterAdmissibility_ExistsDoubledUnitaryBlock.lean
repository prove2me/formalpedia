-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ExistsDoubledUnitaryBlock
-- name    : Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ExistsDoubledUnitaryBlock
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:23.229991+00:00
-- url     : https://prove2.me/theorems/e8da2dfd-f1a6-4220-994f-9f53c00be82c
-- title:
--   Exists Doubled Unitary Block
-- statement:
--   Definitions and structural lemmas for Exists Doubled Unitary Block, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/ExistsDoubledUnitaryBlock.lean

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_BoxCancel
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_DoublingGramFromBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.ThKF0.Chr
open Matrix GlobalTheory.WeilM PositivityTheory.ThK.SiegelT
variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β β₁ ν κ κ₁ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype β₁] [DecidableEq β₁]
  [Fintype ν] [DecidableEq ν] [Fintype κ] [Fintype κ₁] {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E}
  {JA : Matrix α α E} {J : Matrix β β E} {J₁ : Matrix β₁ β₁ E} {ι : Matrix β β₁ E} {X : Matrix β ν E}
  {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} {e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)}
def fac (C : TestClass R) (χ : Eˣ →* Circle) (n : ℕ) (z : Eˣ) : ℂ :=
  (χ z : ℂ) * (((C.modu (Units.map (Algebra.norm R : E →* R) z) : ℝ) ^ ((n : ℝ) / 2) : ℝ) : ℂ)
def blk {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (s : GL a E) (t : GL b E) : GL (a ⊕ b) E :=
  ⟨fromBlocks s.1 0 0 t.1, fromBlocks (s⁻¹).1 0 0 (t⁻¹).1, by rw [fromBlocks_multiply]; simp, by rw [fromBlocks_multiply]; simp⟩
end PositivityTheory.ThKF0.Chr


