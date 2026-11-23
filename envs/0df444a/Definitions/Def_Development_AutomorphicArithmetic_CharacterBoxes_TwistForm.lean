-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_TwistForm
-- name    : Development_AutomorphicArithmetic_CharacterBoxes_TwistForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:12.442801+00:00
-- url     : https://prove2.me/theorems/1cd524ee-1a92-4d20-bd0f-ba5c9c1623df
-- title:
--   Twist Form
-- statement:
--   Definitions and structural lemmas for Twist Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CharacterBoxes/TwistForm.lean

import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_PairGood
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
def KerChi (ψ : PChar) {φ : Frame} (H : HostRaw φ) : Prop :=
  ψ.N ∣ H.QS ∧ ∀ (a : ℕ) (h : a.Coprime H.condN), H.art (ZMod.unitOfCoprime a h) = 1 ↔
    (a ≡ 1 [MOD 2 ^ (φ.e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (φ.e + 2)]) ∧ ψ.val a = 1 ∧
      jacobiSym (a : ℤ) H.q = 1 ∧ jacobiSym (a : ℤ) H.d = 1
def TwistForm (ψ : PChar) {φ : Frame} (H : HostRaw φ) : Prop :=
  ∀ θ : φ.Char, Frame.TrivialOnFirstFactor θ → ∃ ξ ∈ Subgroup.zpowers ψ.χ, ∃ i j : Fin 2,
    θ φ.iod = (-1) ^ (j : ℕ) ∧
      ∀ a : ℕ, a.Coprime H.condN → H.dirAt θ a = tw (fun b => ξ (b : ZMod ψ.N)) H.q H.d i j a
structure WinDatum (ψ : PChar) (eps J c x Y : ℝ) (q d e : ℕ) : Prop where
  lo : x ^ (1 / J) ≤ Y
  up : Y ≤ x
  good : PairGood ψ.N eps Y x q d
  n_lo : x ^ (2 + 8 * eps) ≤ c * 2 ^ e
  n_up : c * 2 ^ e ≤ 2 * x ^ (2 + 8 * eps)
  bound : ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ e q d E →
    VVle E ⌊x ^ (400 : ℝ)⌋₊ (Real.sqrt (Real.exp (x ^ eps)))
end UpperTheory.Top
end


