-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatVec
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatVec
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T12:23:57.069502+00:00
-- url     : https://prove2.me/theorems/270bcbb1-8380-4b2f-a1ea-34a7b636817f
-- title:
--   Exists Nat Vec
-- statement:
--   Definitions and structural lemmas for Exists Nat Vec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ExistsNatVec.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatLocal
import Definitions.Def_Lemmata_NatMulIsIntegral_ExistsNatMulIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WAU.B
open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.UG Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
abbrev incA (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (a : Af F) :
    E ⊗[F] Af F :=
  (Algebra.TensorProduct.includeRight : Af F →ₐ[F] E ⊗[F] Af F) a
abbrev ivec (x : Fin n → E) : Fin n → E ⊗[F] Af F := fun i => inclE (F := F) (Af F) (x i)
def Tset {k : ℕ} (m : Fin k → Fin n → E) : Set (Fin n → E ⊗[F] Af F) :=
  {w | ∃ a : Fin k → Af F, (∀ j, a j ∈ intAd F) ∧ w = ∑ j, incA F E (a j) • ivec (F := F) (m j)}
section T
variable {k : ℕ} {m : Fin k → Fin n → E}
end T
end PI.WAU.B


