-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_ProdBlockEmbMonomial
-- name    : Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_ProdBlockEmbMonomial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:22.928359+00:00
-- url     : https://prove2.me/theorems/94973021-8a54-4078-9c6a-b4dfef703f2f
-- title:
--   Prod Block Emb Monomial
-- statement:
--   Definitions and structural lemmas for Prod Block Emb Monomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/ProdBlockEmbMonomial.lean

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
section general
variable {σ R : Type*} [CommRing R]
end general
section block
variable {K S : Type*} [CommRing K] [Fintype S] {k n : ℕ}
def glue (p : S → (Fin k × Fin n →₀ ℕ)) : S × (Fin k × Fin n) →₀ ℕ :=
  ∑ t, (p t).mapDomain (Prod.mk t)
end block
end Formalism.L2.G.Model.TS


