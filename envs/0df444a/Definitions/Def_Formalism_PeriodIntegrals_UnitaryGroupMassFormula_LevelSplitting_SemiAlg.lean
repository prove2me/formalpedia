-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:17:53.339212+00:00
-- url     : https://prove2.me/theorems/87f6c464-f82d-45bd-bdbf-44ec333fa313
-- title:
--   Semi Alg
-- statement:
--   Definitions and structural lemmas for Semi Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiAlg.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LevelKSplit.W.SemiA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct
section R
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)
def datR : SemiG.Dat (R ⊗[F] E) (Fin M) r where
  σA := sigR R σ
  JA := JR R J
  e a := ratV (F := F) R (P.e a)
  f a := ratV (F := F) R (P.f a)
  z := ratV (F := F) R P.z
  tz := inclR (F := F) R ((algebraMap F E (-T))⁻¹)
variable {R σ J P T}
end R
end PI.LevelKSplit.W.SemiA


