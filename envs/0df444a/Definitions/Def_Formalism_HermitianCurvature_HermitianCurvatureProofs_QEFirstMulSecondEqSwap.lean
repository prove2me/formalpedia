-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:40:00.006337+00:00
-- url     : https://prove2.me/theorems/2c5ae311-d306-4051-a252-d07cf56cf83f
-- title:
--   QEFirst Mul Second Eq Swap
-- statement:
--   Definitions and structural lemmas for QEFirst Mul Second Eq Swap, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QEFirstMulSecondEqSwap.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.Wd4
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.W
section Units
variable {K B : Type} [Field K] [Ring B] [Algebra K B]
def PE (e : Fin 2 → Fin 2 → B) : M2 B := Matrix.of fun i j => e j i
def QE (e : Fin 2 → Fin 2 → B) : M2 B := Matrix.of fun i j => e i j
def RhE (e : Fin 2 → Fin 2 → B) (D : K) : M2 B := (D - 1)⁻¹ • (D • (1 : M2 B) - PE e)
def RhtE (e : Fin 2 → Fin 2 → B) (d : K) : M2 B := (d - 1)⁻¹ • (d • (1 : M2 B) - QE e)
structure MU (e : Fin 2 → Fin 2 → B) : Prop where
  mul : ∀ i j k l, e i j * e k l = if j = k then e i l else 0
  sum : e 0 0 + e 1 1 = 1
variable {e : Fin 2 → Fin 2 → B}
end Units
section Star
variable {K B : Type} [Field K] [StarRing K] [Ring B] [StarRing B] [Algebra K B] [StarModule K B]
  {e : Fin 2 → Fin 2 → B}
end Star
section Slots
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
end Slots
end Formalism.FourierDecayAlt.P.Wd4
namespace Formalism.FourierDecayAlt.P
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
end Formalism.FourierDecayAlt.P


