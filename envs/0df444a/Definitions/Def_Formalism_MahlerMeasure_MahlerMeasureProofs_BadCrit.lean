-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_BadCrit
-- name    : Formalism_MahlerMeasure_MahlerMeasureProofs_BadCrit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:10:08.252306+00:00
-- url     : https://prove2.me/theorems/07bf6581-ada2-4e1b-988c-d1c29f9bca9b
-- title:
--   Bad Crit
-- statement:
--   Definitions and structural lemmas for Bad Crit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/BadCrit.lean

import Definitions.Def_Formalism_MahlerMeasure_StatementT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM
open Module
section
variable {p : ℕ} [Fact p.Prime] {Vs : Type} [AddCommGroup Vs] [Module ℚ_[p] Vs] [Module ℤ_[p] Vs]
    [IsScalarTower ℤ_[p] ℚ_[p] Vs]
end
section
variable {p : ℕ} [Fact p.Prime] {Vs : Type} [AddCommGroup Vs] [Module ℚ_[p] Vs] [Module ℤ_[p] Vs]
    [IsScalarTower ℤ_[p] ℚ_[p] Vs]
end
end Formalism.GM


