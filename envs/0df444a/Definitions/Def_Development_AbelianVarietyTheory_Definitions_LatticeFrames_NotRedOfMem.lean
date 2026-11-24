-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
-- name    : Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T21:21:33.66355+00:00
-- url     : https://prove2.me/theorems/bb4cc52f-c84d-42a4-a9e9-db04c3d27c90
-- title:
--   Not Red Of Mem
-- statement:
--   Definitions and structural lemmas for Not Red Of Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/LatticeFrames/NotRedOfMem.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Klein
open Formalism.L2.Th1.F
open scoped ComplexConjugate
variable {p : ℕ} [Fact p.Prime]
def Good (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ) : Prop :=
  p ≠ 2 ∧ ‖ι (12 * r)‖ ≤ 1 ∧ ‖ι (12 * r ^ 2 - L.g₂)‖ ≤ 1 ∧ ‖ι (4 * r ^ 3 - L.g₂ * r - L.g₃)‖ ≤ 1 ∧
    ‖ι (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)‖ = 1
def Red (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r z : ℂ) : Prop :=
  z ∉ L.lattice ∧ ‖ι (L.weierstrassP z - r)‖ ≤ 1
def Zs (L : PeriodPair) (z : ℂ) : ℂ := wZeta L z - s2 L * z - (Real.pi : ℂ) * conj z / (area L : ℂ)
def kl (L : PeriodPair) (z : ℂ) : ℂ := opU L z (sgStar L) 0
def JetLe (ι : ℂ ≃+* ℂ_[p]) (B : ℝ) (F : ℂ → ℂ) : Prop := ∀ n : ℕ, ‖ι (iteratedDeriv n F 0)‖ ≤ B ^ n
end GlobalTheory.Klein


