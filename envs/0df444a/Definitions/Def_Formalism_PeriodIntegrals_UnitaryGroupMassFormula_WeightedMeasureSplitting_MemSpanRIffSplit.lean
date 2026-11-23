-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedMeasureSplitting_MemSpanRIffSplit
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedMeasureSplitting_MemSpanRIffSplit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:39:10.169255+00:00
-- url     : https://prove2.me/theorems/520c0254-f502-4cb5-b697-1e51c3f3f759
-- title:
--   Mem Span RIff Split
-- statement:
--   Definitions and structural lemmas for Mem Span RIff Split, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedMeasureSplitting/MemSpanRIffSplit.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedMeasureSplitting_SplTApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.MeasWCore
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures NumberField
open scoped TensorProduct
namespace Memb
section Gen
variable {F E : Type} [Field F] [Field E] [Algebra F E]
  {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (φ : R →ₐ[F] R') {n : ℕ}
def mapV : (Fin n → R ⊗[F] E) →+ (Fin n → R' ⊗[F] E) :=
  (tensMap (E := E) φ).toAddMonoidHom.compLeft (Fin n)
variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
end Gen
section Split
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
end Split
end Memb
open Memb
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)
end PI.UnitaryGroupMassFormula.MeasWCore


