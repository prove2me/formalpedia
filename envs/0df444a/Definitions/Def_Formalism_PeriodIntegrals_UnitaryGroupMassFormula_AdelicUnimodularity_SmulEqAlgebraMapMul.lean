-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_SmulEqAlgebraMapMul
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_SmulEqAlgebraMapMul
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T12:24:17.2017+00:00
-- url     : https://prove2.me/theorems/649b98f7-2aad-433d-b42f-c9dfb2ec1d9c
-- title:
--   Smul Eq Algebra Map Mul
-- statement:
--   Definitions and structural lemmas for Smul Eq Algebra Map Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/SmulEqAlgebraMapMul.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CoordTmulOneMul
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WAU
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped TensorProduct
variable {F : Type} [Field F] [NumberField F]
def IntF (f : F) : Prop := algebraMap F (FiniteAdeleRing (𝓞 F) F) f ∈ Ohat F
section Coord
variable {E : Type} [Field E] [NumberField E] [Algebra F E]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
local notation "Af" => FiniteAdeleRing (𝓞 F) F
def IntC (x : E ⊗[F] Af) : Prop := ∀ k, coord b x k ∈ Ohat F
variable {b}
end Coord
end PI.WAU


