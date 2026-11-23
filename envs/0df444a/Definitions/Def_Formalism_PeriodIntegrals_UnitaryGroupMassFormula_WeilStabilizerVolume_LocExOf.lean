-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocExOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocExOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:10:34.799883+00:00
-- url     : https://prove2.me/theorems/a8ce8f37-1f12-4845-8f54-ca23acaf7fe0
-- title:
--   Loc Ex Of
-- statement:
--   Definitions and structural lemmas for Loc Ex Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocExOf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SWeqOm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
def LatSB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (d M n : ℕ)
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)),
    IsSB ((latV (M := M) (n := n) b v).indicator (1 : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ))
end PI.VolStabW


