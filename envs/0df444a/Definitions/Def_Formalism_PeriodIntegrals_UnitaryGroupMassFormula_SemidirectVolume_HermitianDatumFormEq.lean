-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianDatumFormEq
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianDatumFormEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:30:57.213792+00:00
-- url     : https://prove2.me/theorems/e8821c65-2981-4aac-8f7b-02934e768596
-- title:
--   Hermitian Datum Form Eq
-- statement:
--   Definitions and structural lemmas for Hermitian Datum Form Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/HermitianDatumFormEq.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_NnrealEqOneOfMulSelf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjTDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_LocallyCompactAdelicUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolSemiDirect.W.Cj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub MeasureTheory Measure
open scoped TensorProduct
section Alg
variable {F E : Type} [Field F] [Field E] [Algebra F E] {A : Type} [CommRing A] [Algebra F A]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
def dat0 : PG.Dat (A ⊗[F] E) (Fin M) 0 where
  σA := sigR A σ
  JA := JR A J
  e := Fin.elim0
  f := Fin.elim0
  z := 0
  tz := 0
def Bf (u v : Fin M → A ⊗[F] E) : A := Algebra.trace A (A ⊗[F] E) (hR A σ J u v)
end Alg
end PI.VolSemiDirect.W.Cj


