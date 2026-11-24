-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_EqOfLeOfAbsNormEq
-- name    : Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_EqOfLeOfAbsNormEq
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T19:15:14.262395+00:00
-- url     : https://prove2.me/theorems/b4027a26-9c2b-4748-a979-ff501396bd2a
-- title:
--   Eq Of Le Of Abs Norm Eq
-- statement:
--   Definitions and structural lemmas for Eq Of Le Of Abs Norm Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/EqOfLeOfAbsNormEq.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.UnusedSlot33.HK
open NumberField Polynomial Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.TwoAdicCyclotomicDecomposition
open scoped Pointwise
variable {R : Ranks} (H : Host R)
def DiffKH (H : Host R) : Prop :=
  ∃ β : 𝓞 H.E, (β : H.E) = H.sqrtMinusD ∧
    (differentIdeal ℤ (𝓞 H.K)).map (algebraMap (𝓞 H.K) (𝓞 H.E)) = Ideal.span {β}
def NormKH (H : Host R) : Prop :=
  ∀ cc : Ideal (𝓞 H.K), cc ≠ ⊥ →
    Ideal.map (algebraMap (𝓞 H.K) (𝓞 H.E)) cc *
      (H.conj • Ideal.map (algebraMap (𝓞 H.K) (𝓞 H.E)) cc) =
    Ideal.span {((Ideal.absNorm cc : ℕ) : 𝓞 H.E)}
end Formalism.MainNotions.UnusedSlot33.HK
end


