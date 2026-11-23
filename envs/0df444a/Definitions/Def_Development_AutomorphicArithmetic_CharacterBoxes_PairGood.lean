-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_PairGood
-- name    : Development_AutomorphicArithmetic_CharacterBoxes_PairGood
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:45:25.052323+00:00
-- url     : https://prove2.me/theorems/038831e3-b21f-4b55-99bc-0c2b558a51f8
-- title:
--   Pair Good
-- statement:
--   Definitions and structural lemmas for Pair Good, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean

import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_ExistsPageN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace UpperTheory.Top
open Formalism.HC
def tw (ξ : ℕ → ℂ) (q d : ℕ) (i j : Fin 2) (a : ℕ) : ℂ :=
  ξ a * ((jacobiSym (a : ℤ) q : ℤ) : ℂ) ^ (i : ℕ) * ((jacobiSym (a : ℤ) d : ℤ) : ℂ) ^ (j : ℕ)
def ZeroBox (Q : ℝ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, 1 - 1 / 400 < s.re → |s.im| ≤ Q → DirichletCharacter.LFunction χ s ≠ 0
def height (M : ℕ) (eps Y : ℝ) (j : Fin 2) : ℝ :=
  8 * M * Real.exp (Y ^ (eps / 5)) * Real.exp (Y ^ (eps / 5) * Real.log Y ^ 2) ^ (j : ℕ)
structure PairGood (M : ℕ) (eps Y X : ℝ) (q d : ℕ) : Prop where
  pair : WinPair eps Y q d
  coprime : Nat.Coprime M (q * d)
  bounds : ∀ (ξ : DirichletCharacter ℂ M) (i j : Fin 2), (i ≠ 0 ∨ j ≠ 0) →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), An.Induces χ (tw (fun a => ξ (a : ZMod M)) q d i j) (2 * M * q * d) →
      ∀ y : ℝ, Y ≤ y → y ≤ X → ‖An.gChi χ y‖ ≤ y ^ ((1 : ℝ) / 2 + eps / 2) ∧ ‖An.logDerivativeAtOne χ‖ ≤ 4 * Real.log y
  boxes : ∀ ρ : PChar, ρ.IsReal → ρ.N ∣ 8 * M → ∀ i j : Fin 2, (i ≠ 0 ∨ j ≠ 0) →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), An.Induces χ (tw ρ.val q d i j) (2 * M * q * d) →
      ZeroBox (height M eps Y j) χ
def PairEx : Prop :=
  ∀ (M : ℕ), 0 < M → ∀ eps A : ℝ, 0 < eps → eps < 1 / 52 → 1 ≤ A →
    ∃ Y1 : ℝ, ∀ Y ≥ Y1, ∃ q d : ℕ, PairGood M eps Y (Y ^ A) q d
def RealBox {φ : Frame} (H : HostRaw φ) : Prop :=
  ∀ ψ : PChar, H.IsCharE ψ.χ → ψ.IsReal → (H.q ∣ ψ.N ∨ H.d ∣ ψ.N) →
    ∀ β : ℝ, 1 - 1 / 400 < β → DirichletCharacter.LFunction ψ.χ β ≠ 0
def ThinH : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ B eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (φ : Frame) (H : HostRaw φ),
    ((ordCompl[2] H.QS : ℕ) : ℝ) ≤ B → Real.log (H.condN : ℝ) ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2 → RealBox H →
      H.ChebyshevCharacterBound x eps c
end UpperTheory.Top
end


