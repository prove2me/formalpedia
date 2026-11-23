-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Imports
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Imports
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:16:50.105993+00:00
-- url     : https://prove2.me/theorems/cc05daf0-3a6b-4cf5-919e-78dfea864c9c
-- title:
--   Imports
-- statement:
--   Definitions and structural lemmas for Imports, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeEquality/Imports.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocLatEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc
namespace PI.LocLatEq.W
def ιO {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) (d : 𝓞 F) : A.Ep :=
  A.ιE ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E)
def IntP : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Module.finrank F E = 2 → ∀ (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p),
    ∀ a : E, A.ιE a ∈ A.O → ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ ∃ b : 𝓞 E,
      ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) * a = b
end PI.LocLatEq.W


