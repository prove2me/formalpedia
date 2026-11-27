-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DetRestrictRangeIdempotentMatrix
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_DetRestrictRangeIdempotentMatrix
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-27T06:27:33.562015+00:00
-- url     : https://prove2.me/theorems/23cb939f-d0ce-5618-a5fd-c867dbcd857f
-- title:
--   Det Restrict Range Idempotent Matrix
-- statement:
--   Definitions and structural lemmas for Det Restrict Range Idempotent Matrix, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DetRestrictRangeIdempotentMatrix.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.RegSS
noncomputable section
open Matrix Formalism.UG
open scoped TensorProduct
namespace GlobalTheory.RegSS.IdemDet
section Rep
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {ι : Type} [Fintype ι] [DecidableEq ι]
def regRep (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R] :
    E ⊗[F] R →ₐ[F] Matrix ι ι R :=
  Algebra.TensorProduct.lift
    ((AlgHom.mapMatrix (Algebra.ofId F R)).comp (Algebra.leftMulMatrix b))
    (IsScalarTower.toAlgHom F R (Matrix ι ι R))
    (fun _ a => (Algebra.commutes a _).symm)
variable {n : Type} [Fintype n] [DecidableEq n]
def blockRep (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R] :
    Matrix n n (E ⊗[F] R) →+* Matrix (n × ι) (n × ι) R :=
  (Matrix.compRingEquiv n ι R).toRingHom.comp (regRep b R).toRingHom.mapMatrix
def blockRat (b : Module.Basis ι F E) : Matrix n n E →+* Matrix (n × ι) (n × ι) F :=
  (Matrix.compRingEquiv n ι F).toRingHom.comp (Algebra.leftMulMatrix b).toRingHom.mapMatrix
end Rep
end GlobalTheory.RegSS.IdemDet
namespace GlobalTheory.RegSS
open IdemDet
end GlobalTheory.RegSS


