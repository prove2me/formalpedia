-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ContinuousAtPlace
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ContinuousAtPlace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:12:44.094006+00:00
-- url     : https://prove2.me/theorems/cff7eb2e-f0ed-48ff-8eac-e5fb9230af36
-- title:
--   Continuous At Place
-- statement:
--   Definitions and structural lemmas for Continuous At Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/ContinuousAtPlace.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MeasDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LevelKSplit.W.Cont
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct
section
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
def phiV (v : HeightOneSpectrum (𝓞 F)) : Af F ⊗[F] E →ₐ[F] Fv F v ⊗[F] E :=
  Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)
theorem phiV_smul (v : HeightOneSpectrum (𝓞 F)) (a : Af F) (x : Af F ⊗[F] E) :
    phiV (E := E) v (a • x) = evalV F v a • phiV v x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
def phiSL (v : HeightOneSpectrum (𝓞 F)) :
    Af F ⊗[F] E →ₛₗ[(evalV F v).toRingHom] Fv F v ⊗[F] E where
  toFun := phiV v
  map_add' := map_add _
  map_smul' := fun a x => phiV_smul v a x
end
end PI.LevelKSplit.W.Cont


