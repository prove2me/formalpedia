-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMul
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:25:28.149222+00:00
-- url     : https://prove2.me/theorems/0b14d2b0-28df-43d6-b615-6ebade31af4a
-- title:
--   Box Mul
-- statement:
--   Definitions and structural lemmas for Box Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/BoxMul.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_Transport
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_GoodTransvection
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_DiagonalOneJacobian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.LocJacTyp.BM
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp PI.UnitaryGroupMassFormula.LocJacTyp
open scoped TensorProduct ENNReal NNReal
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
def mulL {ι : Type} (z : ι → Fv F v ⊗[F] E) :
    (ι → Fv F v ⊗[F] E) →ₗ[Fv F v] (ι → Fv F v ⊗[F] E) :=
  LinearMap.pi fun i => (Algebra.lmul (Fv F v) (Fv F v ⊗[F] E) (z i)).comp (LinearMap.proj i)
end PI.UnitaryGroupMassFormula.LocJacTyp.BM


