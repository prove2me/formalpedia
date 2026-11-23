-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:31.374137+00:00
-- url     : https://prove2.me/theorems/4292512f-9b8c-4f4e-b179-fc63db240da7
-- title:
--   Loc Unit Apply
-- statement:
--   Definitions and structural lemmas for Loc Unit Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LocUnitApply.lean

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal
namespace GlobalTheory.NormCompat
def locUnit (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : Fˣ →* Ideles F :=
  (localIdele F v).comp (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom)
end GlobalTheory.NormCompat


