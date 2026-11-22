-- Prove2me | Definitions.Def_Formalism_FockGram_FockGramProofs_FockPerm
-- name    : Formalism_FockGram_FockGramProofs_FockPerm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:33.081829+00:00
-- url     : https://prove2.me/theorems/1f68bbe3-cd2c-4444-a213-2b958808a8b9
-- title:
--   Fock Perm
-- statement:
--   Definitions and structural lemmas for Fock Perm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FockGram/FockGramProofs/FockPerm.lean

import Definitions.Def_Formalism_FockGram_StatementFock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix MvPolynomial
noncomputable section
namespace Formalism.E
namespace FockPermanent
variable {R τ : Type*} [CommRing R]
def bil (f g : MvPolynomial τ R) : R :=
  ∑ m ∈ f.support, f.coeff m * g.coeff m * (Formalism.A.mfact m : R)
end FockPermanent
end Formalism.E


