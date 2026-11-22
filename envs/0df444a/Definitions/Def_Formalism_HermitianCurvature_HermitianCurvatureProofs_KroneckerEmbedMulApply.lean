-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:35.691269+00:00
-- url     : https://prove2.me/theorems/fe04d395-e65b-4c26-ac44-f17928b56bc5
-- title:
--   Kronecker Embed Mul Apply
-- statement:
--   Definitions and structural lemmas for Kronecker Embed Mul Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KroneckerEmbedMulApply.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.Wd2
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
section Units
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
end Units
section Entries
variable {K B : Type} [CommRing K] [Ring B] [Algebra K B]
end Entries
section Slots
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
end Slots
section Start
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
end Start
end Formalism.FourierDecayAlt.P.Wd2
namespace Formalism.FourierDecayAlt.P
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
end Formalism.FourierDecayAlt.P


