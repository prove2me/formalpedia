-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FirstFamilyOperatorEnd
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FirstFamilyOperatorEnd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:27.787363+00:00
-- url     : https://prove2.me/theorems/be554d6c-dc18-4194-8d5e-ae96d2c4f77f
-- title:
--   First Family Operator End
-- statement:
--   Definitions and structural lemmas for First Family Operator End, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FirstFamilyOperatorEnd.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEleventh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix Filter Topology
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd
open HermitianSublattices LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans traceDeterminantCongruences reductionMapsOfForms localValuationFiltration hermitianFormColumns vectorCountBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
end Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd


