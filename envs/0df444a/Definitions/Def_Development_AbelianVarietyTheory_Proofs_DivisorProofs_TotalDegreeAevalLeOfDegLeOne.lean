-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TotalDegreeAevalLeOfDegLeOne
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_TotalDegreeAevalLeOfDegLeOne
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:38:09.96635+00:00
-- url     : https://prove2.me/theorems/94e84f31-8cb5-538e-ba27-528fd1e40872
-- title:
--   Total Degree Aeval Le Of Deg Le One
-- statement:
--   Definitions and structural lemmas for Total Degree Aeval Le Of Deg Le One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TotalDegreeAevalLeOfDegLeOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open NumberField MvPolynomial
noncomputable section
namespace GlobalTheory.SZShift
def shiftSubst {F E : Type} [CommRing F] [CommRing E] [Algebra F E] {D N n : ℕ}
    (w : Matrix (Fin N) (Fin n) F) (y : Fin D → Fin n → E) (p : Fin D × Fin N) :
    MvPolynomial (Fin D × Fin n) E :=
  ∑ k, C (algebraMap F E (w p.2 k)) * (X (p.1, k) + C (y p.1 k))
end GlobalTheory.SZShift


