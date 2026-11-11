-- Prove2me | Definitions.Def_OAIQ098G1651
-- name    : OAIQ098G1651
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T08:56:05.391846+00:00
-- url     : https://prove2.me/theorems/96f32c63-94bf-4b96-be36-1eaf0470073f
-- title:
--   Definitions bundle OAIQ098G1651 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 10 definitions. The definitions and types are `OAI.SharpPlanar.exactData`, `OAI.SharpPlanar.exactData₁`, `OAI.SharpPlanar.exactData₂`, `OAI.SharpPlanar.exactJet`, `OAI.SharpPlanar.exactList`, `OAI.SharpPlanar.exactList₁`, `OAI.SharpPlanar.exactList₂`, `OAI.SharpPlanar.headData`, `OAI.SharpPlanar.tailData`, `OAI.SharpPlanar.tailErrorJet`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_ExactJets`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/ExactJets.lean), [`PlanarPacking_FixedRHS`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/FixedRHS.lean), [`PlanarPacking_InterpolationError`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/InterpolationError.lean), [`PlanarPacking_JetError`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/JetError.lean), [`PlanarPacking_TailEnvelope`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/TailEnvelope.lean), [`PlanarPacking_TailSplit`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/TailSplit.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G1645`, `OAIQ098G1649` and `OAIQ098G1650` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1652`, `OAIQ098G1674` and `OAIQ098G1679`; the statements `OAI.SharpPlanar.error_large_cap_g`, `OAI.SharpPlanar.error_one_cap_g`, `OAI.SharpPlanar.error_two_cap_g`, `OAI.SharpPlanar.error_zero_cap_g`, `OAI.SharpPlanar.exact_head_lower_g`, `OAI.SharpPlanar.exact_sign_tail_g`, `OAI.SharpPlanar.halfSign_0_N1_right_g` and `OAI.SharpPlanar.tail_second_bound_g`; the proof of `OAI.SharpPlanar.halfSign_0_N1_right_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G1645
import Definitions.Def_OAIQ098G1649
import Definitions.Def_OAIQ098G1650

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FixedRHS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The exact contact interpolation solution

The inverse interpolation operator determines the coefficient lists for the prescribed contacts.
-/

namespace SharpPlanar
noncomputable def exactList₁ : X := coupledLeft g₁ g₂
noncomputable def exactList₂ : X := coupledRight g₁ g₂
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_ExactJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Jets of the exact cardinal interpolants

The exact interpolation equations give value and derivative contacts on the triangular shell radii.
-/

namespace SharpPlanar
noncomputable def exactData₁ : CardinalData := fixed₁ exactList₁
noncomputable def exactData₂ : CardinalData := fixed₂ exactList₂
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_InterpolationError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Error bounds for cardinal interpolation

Norm bounds for the inverse interpolation operator control the distance from the finite coefficient families to the exact solution.
-/

namespace SharpPlanar
open Numerical
noncomputable def exactList (a : Bool) : X := if a then exactList₂ else exactList₁
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_JetError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
noncomputable def exactData (a : Bool) : CardinalData := if a then exactData₂ else exactData₁
noncomputable def exactJet (a : Bool) (ell : ℕ) (s : ℝ) : ℝ :=
  cardinalSeries (exactData a) ell s+K (exactData (!a)) ell s
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TailEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
noncomputable def tailData (a : Bool) : CardinalData := positiveData (tailList (exactList a) 40)
noncomputable def tailErrorJet (a : Bool) (ell : ℕ) (s : ℝ) : ℝ :=
  cardinalSeries (tailData a) ell s+K (exactData (!a)) ell s
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TailSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
noncomputable def headData (a : Bool) : CardinalData :=
  let p:=exactData a
  ⟨p.C,p.c₀,p.d₀,p.x-tailList p.x 40⟩
end SharpPlanar

end OAI
end


