-- Prove2me | Definitions.Def_CK_GeneralCK_LanePHMC_Chain
-- name    : CK_GeneralCK_LanePHMC_Chain
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T01:16:54.010102+00:00
-- url     : https://prove2.me/theorems/ff148040-677b-4f0a-b1e1-cdc82c736af7
-- title:
--   Courtade–Kumar proof module `GeneralCK.LanePHMC.Chain` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.LanePHMC.Chain` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.LanePHMC.Chain` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.LanePHMC.Chain (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/LanePHMC/Chain.lean)

import Definitions.Def_CK_GeneralCK_LanePHMC_Reduce
import Definitions.Def_CK_E8GlobalRatioCertificate

-- ===== source module GeneralCK.LanePHMC.Chain =====
section
/-
Lane P-HMC — THE CHAIN.  Does my reduction actually land on FIELD 6's type?

`Reduce.lean` proved `HalfMeanSlopeGapOnCompact → PureGapD0CompactOwner`.  That is one link.
This module composes the remaining links and asks the kernel whether the result has EXACTLY
the type `GeneralCK.HalfMeanCurvatureNegative` — the type of field 6 of `ProductionOwners`
(`FinalProductionAssemblyPositiveCutoff.lean:50`, file sha256
39909ae04385a2ac9312e3a54267a48acf23b91277762d01a8d9f80c3ad1ce67).

A prose claim that two types are "the same" is worth nothing; this makes the elaborator say it.

🔴 STILL NOT CLOSURE.  Everything here is conditional on `HalfMeanSlopeGapOnCompact`, which is
UNPROVED.  What this establishes is that the hypothesis is the ONLY thing missing — i.e. that
there is no further type mismatch, no further hypothesis, and no further unowned leaf hiding
behind the composition.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace GeneralCK.LanePHMC

/-- The whole of field 6, from the single `e8Q`-free hypothesis. -/
theorem halfMeanCurvatureNegative_of_slopeGap
    (h : HalfMeanSlopeGapOnCompact) : HalfMeanCurvatureNegative :=
  halfMeanCurvatureNegative_of_remainingD0
    (pureGapD0RemainingOwners_of_compact_and_largeSStructure
      (pureGapD0CompactOwner_of_slopeGap h)
      GeneralCK.E8RatioMonotonicity.e8LargeSStructureCertified)

/-- GATE BY NAME.  The conclusion is the field-6 type under its own name. -/
example (h : HalfMeanSlopeGapOnCompact) : HalfMeanCurvatureNegative :=
  halfMeanCurvatureNegative_of_slopeGap h

/-- GATE UNFOLDED.  The same term against the field type written out in full, so a
`def` that merely *names* the right thing cannot pass for the thing itself. -/
example (h : HalfMeanSlopeGapOnCompact) :
    ∀ a e f : ℝ, a < 1 / 2 → 0 < e → 0 < f →
      e < H a → f < H (1 / 2) →
      e8Theta ((1 / 2 - a) / e) =
        2 * e8Theta ((1 / 2 - a) / (e + f)) →
      deriv (deriv (halfMeanPureGapCurve a e f)) (1 / 2) < 0 :=
  halfMeanCurvatureNegative_of_slopeGap h

/-- The `largeS` certificate really is unconditional: zero binders. -/
example : E8LargeSStructure := GeneralCK.E8RatioMonotonicity.e8LargeSStructureCertified

#check @halfMeanCurvatureNegative_of_slopeGap
#check @GeneralCK.E8RatioMonotonicity.e8LargeSStructureCertified
#print axioms halfMeanCurvatureNegative_of_slopeGap
#print axioms GeneralCK.E8RatioMonotonicity.e8LargeSStructureCertified

theorem phmc_chain_positive_control : (5 : Nat) + 7 = 12 := by norm_num
#print axioms phmc_chain_positive_control

end GeneralCK.LanePHMC

end


