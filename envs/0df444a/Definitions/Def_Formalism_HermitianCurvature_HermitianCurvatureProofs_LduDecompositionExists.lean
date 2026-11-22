-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:23:30.202456+00:00
-- url     : https://prove2.me/theorems/7ec694a2-317a-45f4-b31b-124dc40b6ebe
-- title:
--   Ldu Decomposition Exists
-- statement:
--   Definitions and structural lemmas for Ldu Decomposition Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.S3x7
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isLowUni_mul isUpUni_inv isLowUni_inv isUpUni_one isLowUni_one
  isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
section Minors
variable {A : Type} [CommRing A]
end Minors
section Border
variable {A : Type} [CommRing A]
def border {r : ℕ} (B : Matrix (Fin r) (Fin r) A) (v u : Fin r → A) (c : A) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) A :=
  Matrix.of fun i j =>
    Fin.lastCases (motive := fun _ => A) (Fin.lastCases (motive := fun _ => A) c u j)
      (fun i' => Fin.lastCases (motive := fun _ => A) (v i') (B i') j) i
end Border
section Blocks
variable {A : Type} [CommRing A] {r k : ℕ}
end Blocks
section Corner
variable {o : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o]
end Corner
end Formalism.FourierDecayAlt.P.S3x7
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.S3x7
end Formalism.FourierDecayAlt.P


