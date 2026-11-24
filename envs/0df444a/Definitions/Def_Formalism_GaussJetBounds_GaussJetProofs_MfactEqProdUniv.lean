-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
-- name    : Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T21:32:01.749082+00:00
-- url     : https://prove2.me/theorems/334ae383-a021-4bf4-a6bc-bbfa70ec3390
-- title:
--   Mfact Eq Prod Univ
-- statement:
--   Definitions and structural lemmas for Mfact Eq Prod Univ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/MfactEqProdUniv.lean

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
namespace Formalism.DworkPowerSeriesWeights
section PairJetAux
def pairExp {ι : Type} [Fintype ι] (n : ι → ℕ) : (Bool × ι) →₀ ℕ :=
  ∑ i, n i • (Finsupp.single (false, i) 1 + Finsupp.single (true, i) 1)
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]
end PairJetAux
end Formalism.DworkPowerSeriesWeights


