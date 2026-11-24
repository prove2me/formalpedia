-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_TorsUnitsOfNbhd
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_TorsUnitsOfNbhd
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T22:04:45.184809+00:00
-- url     : https://prove2.me/theorems/855d619d-1526-4b3b-9308-dc2c8133f931
-- title:
--   Tors Units Of Nbhd
-- statement:
--   Definitions and structural lemmas for Tors Units Of Nbhd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/TorsUnitsOfNbhd.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_EvFLocalIdeleSelf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_NormEqOneOfForallZpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_PowCardSubOneMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
namespace PI.AlgValsFin.W
def ufinSub (L : Type) [Field L] [NumberField L] : Subgroup (Ideles L) where
  carrier := UFin L
  one_mem' := ⟨rfl, fun v => by
    show Valued.v (1 : v.adicCompletion L) = 1
    exact map_one _⟩
  mul_mem' := fun {a b} ha hb => ⟨by
    change (a : AdeleRing (𝓞 L) L).1 * (b : AdeleRing (𝓞 L) L).1 = 1
    rw [ha.1, hb.1, mul_one],
    fun v => by rw [comp_mul, map_mul, ha.2 v, hb.2 v, mul_one]⟩
  inv_mem' := fun {a} ha => by
    refine ⟨?_, fun v => ?_⟩
    · have e : (a : AdeleRing (𝓞 L) L).1 * (a⁻¹ : Ideles L).val.1 = 1 := by
        change ((a * a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).1 = 1
        rw [mul_inv_cancel]; rfl
      rw [ha.1, one_mul] at e
      exact e
    · have e := congrArg Valued.v (comp_mul_inv L a v)
      rw [map_mul, ha.2 v, one_mul, map_one] at e
      exact e
variable {L : Type} [Field L] [NumberField L]
end PI.AlgValsFin.W


