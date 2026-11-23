-- Prove2me | Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateThird
-- name    : Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateThird
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:14:35.988592+00:00
-- url     : https://prove2.me/theorems/5992d792-df2b-4af9-9433-c4b760f4f6f2
-- title:
--   Local Estimate Third
-- statement:
--   Definitions and structural lemmas for Local Estimate Third, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/LocalEstimateThird.lean

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ProdPowFactorizationLe
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FourMulSumLeProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace E4
variable {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L]
open Classical in

noncomputable def Bset (K : Type) [Field K] [Fintype K] (δ : ℕ) (c₀ : Kˣ) : Finset (Fin δ → K) :=
  Finset.univ.filter (fun c => Irreducible (monicOf c) ∧
    ∃ l' ∈ (Fintype.card K ^ δ - 1).primeFactors,
      monicOf c ∣ X ^ (l' ^ padicValNat l' (Fintype.card K ^ δ - 1)) -
        C ((c₀ : K) ^ (l' ^ padicValNat l' (Fintype.card K ^ δ - 1))))
end E4
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility


