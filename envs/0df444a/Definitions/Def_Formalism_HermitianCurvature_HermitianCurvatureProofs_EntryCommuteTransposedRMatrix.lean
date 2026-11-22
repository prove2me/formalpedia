-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:16.97172+00:00
-- url     : https://prove2.me/theorems/9c12adac-b95a-4e9b-a24a-9466f8ce3e40
-- title:
--   Entry Commute Transposed RMatrix
-- statement:
--   Definitions and structural lemmas for Entry Commute Transposed RMatrix, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
section Units
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
end Units
def EC {B : Type} [Mul B] (z : B) (M : M2 B) : Prop := ∀ i j, Commute z (M i j)
section General
variable {B : Type} [Ring B]
end General
section Slots
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
end Slots
section Slots
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
def Rel (M N : M2 A) (D : K) : Prop :=
  ∀ i k r s, D • (M i k * N r s) - M r k * N i s = D • (N r s * M i k) - N r k * M i s
end Slots
section General
variable {B : Type} [Ring B]
end General
section Slots
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
end Slots
section Star
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
end Star
section Star
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
end Star
end Formalism.FourierDecayAlt.P.Wd6
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


