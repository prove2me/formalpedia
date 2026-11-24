-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepRamDef
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepRamDef
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T21:43:38.677558+00:00
-- url     : https://prove2.me/theorems/f86eff38-7140-4961-aca5-589e77758de1
-- title:
--   Rep Ram Def
-- statement:
--   Definitions and structural lemmas for Rep Ram Def, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RepRamDef.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
def KeyStartRam : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) (l : ℕ) (x y : ℤ) (T : Finset m) (i₀ : m), KeyHyps a b c d ha hd lam hlam m Λ l x y T i₀ → l = d → ∃ w, ApproxAt a b c d ha hd lam hlam m Λ l x y T i₀ 1 w
end PI.UnitaryGroupMassFormula.UnimodLocStd


