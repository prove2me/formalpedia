-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_CommOfBounded
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_CommOfBounded
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T22:04:32.069353+00:00
-- url     : https://prove2.me/theorems/977d7174-4450-4bc5-a470-f7c9335f0d0e
-- title:
--   Comm Of Bounded
-- statement:
--   Definitions and structural lemmas for Comm Of Bounded, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/CommOfBounded.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
variable {m : Type*} [Fintype m] [DecidableEq m]
def IsKv (b : ℤ) (d : ℕ) (lam : ℂ) (v : m → ℂ) : Prop := ∀ i, IsK b d (v i / lam)
def kappa (L : PeriodPair) (lam : ℂ) : ℂ := lam * conj lam * ((area L : ℝ) : ℂ)⁻¹
end PI.UnitaryGroupMassFormula.UnimodLocStd


