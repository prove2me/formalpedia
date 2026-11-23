-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_ZeroMemLatSet
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_ZeroMemLatSet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:23.540251+00:00
-- url     : https://prove2.me/theorems/9a7ecb58-1192-4f69-a18a-f9661bfd5c48
-- title:
--   Zero Mem Lat Set
-- statement:
--   Definitions and structural lemmas for Zero Mem Lat Set, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelProductIndex/ZeroMemLatSet.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
namespace PI.UnitaryGroupMassFormula.LevelProdIdx
open Formalism.UG
variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ}
def latSet (R : Type) [CommRing R] [Algebra F R] (O : Subring R) {k : ℕ} (G : Fin k → (Fin n → E)) :
    Set (Fin n → E ⊗[F] R) :=
  {y | ∃ c : Fin k → R, (∀ i, c i ∈ O) ∧ y = fun l => ∑ i, G i l ⊗ₜ[F] c i}
section Set
variable {R : Type} [CommRing R] [Algebra F R] {O : Subring R} {k : ℕ} {G : Fin k → (Fin n → E)}
end Set
variable [NumberField E]
end PI.UnitaryGroupMassFormula.LevelProdIdx
namespace PI.LPI
end PI.LPI


