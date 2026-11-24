-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsGamma
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsGamma
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:35.340944+00:00
-- url     : https://prove2.me/theorems/faade871-8f8c-4ae2-a235-4e49c7498974
-- title:
--   Exists Is Gamma
-- statement:
--   Definitions and structural lemmas for Exists Is Gamma, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIsGamma.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DI
namespace FrobTwist
def Tw (K V : Type) [CommRing K] [AddCommGroup V] [Module K V] : Type := ExteriorAlgebra K V
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
instance : Ring (Tw K V) := inferInstanceAs (Ring (ExteriorAlgebra K V))
abbrev twAlg (p : ℕ) [Fact p.Prime] [CharP K p] : Algebra K (Tw K V) :=
  RingHom.toAlgebra' ((algebraMap K (ExteriorAlgebra K V)).comp (frobenius K p))
    (fun c x => Algebra.commutes (R := K) (A := ExteriorAlgebra K V) _ x)
end FrobTwist
end GlobalTheory.DI


