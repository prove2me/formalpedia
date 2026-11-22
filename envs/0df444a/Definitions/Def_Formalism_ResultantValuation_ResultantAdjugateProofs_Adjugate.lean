-- Prove2me | Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Adjugate
-- name    : Formalism_ResultantValuation_ResultantAdjugateProofs_Adjugate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:10:02.627653+00:00
-- url     : https://prove2.me/theorems/3db6cb61-7826-4ac4-918e-77d7fe1296c9
-- title:
--   Adjugate
-- statement:
--   Definitions and structural lemmas for Adjugate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Adjugate.lean

import Definitions.Def_Formalism_ResultantValuation_KoszulSecondDifferential
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace Formalism.ResultantValuation
namespace AdjugateJacobi
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
def minorF (M : Matrix n n R) (k i l j : n) : R :=
  M.adjugate k l * M.adjugate i j - M.adjugate i l * M.adjugate k j
def minorQ (M : Matrix n n R) (k i l j : n) : R :=
  ((M.updateCol i (Pi.single j 1)).updateCol k (Pi.single l 1)).det
def twoCol (k i : n) (u v : n → R) : Matrix n n R :=
  ((1 : Matrix n n R).updateCol k u).updateCol i v
end AdjugateJacobi
end Formalism.ResultantValuation


