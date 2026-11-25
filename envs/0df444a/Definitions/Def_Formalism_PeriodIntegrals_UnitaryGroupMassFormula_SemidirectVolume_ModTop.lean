-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModTop
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModTop
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T12:03:07.641607+00:00
-- url     : https://prove2.me/theorems/5a6201c7-dc7c-4c9a-91b0-a40e134864cb
-- title:
--   Mod Top
-- statement:
--   Definitions and structural lemmas for Mod Top, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ModTop.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjCont
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolSemiDirect.W.Md
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct Matrix
section Cont
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)
def sigRLin : R ⊗[F] E →ₗ[R] R ⊗[F] E :=
  TensorProduct.AlgebraTensorModule.map (LinearMap.id : R →ₗ[R] R) σ.toLinearMap
variable [IsTopologicalRing (R ⊗[F] E)]
end Cont
section HAcont
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
variable [TopologicalSpace R] [IsTopologicalRing R] [IsTopologicalRing (R ⊗[F] E)]
end HAcont
section Raw
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsTopologicalRing (R ⊗[F] E)] (σ : E →ₐ[F] E)
  {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)
end Raw
end PI.VolSemiDirect.W.Md


