-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_ExistsNeZeroMem
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_ExistsNeZeroMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:45:16.874725+00:00
-- url     : https://prove2.me/theorems/43f76614-e892-40a4-979d-8757ea6ae038
-- title:
--   Exists Ne Zero Mem
-- statement:
--   Definitions and structural lemmas for Exists Ne Zero Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleClassFiniteness/ExistsNeZeroMem.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_OhatCompact
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_AdeleIntA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PIW.ClassFinD.Icf
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type} [Field F] [NumberField F]
def latI (b : (FiniteAdeleRing (𝓞 F) F)ˣ) : Ideal (𝓞 F) where
  carrier := {x | ∀ w : HeightOneSpectrum (𝓞 F), w.intValuation x ≤ Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w)}
  add_mem' := fun {x y} hx hy w => (Valuation.map_add _ x y).trans (max_le (hx w) (hy w))
  zero_mem' := fun w => by rw [map_zero]; exact zero_le
  smul_mem' := fun c x hx w => by
    rw [smul_eq_mul, map_mul]
    exact (mul_le_of_le_one_left' (w.intValuation_le_one c)).trans (hx w)
end PIW.ClassFinD.Icf
end


