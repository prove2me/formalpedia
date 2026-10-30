-- Prove2me | Definitions.Def_OAIQ115N024
-- name    : OAIQ115N024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T02:07:37.826737+00:00
-- url     : https://prove2.me/theorems/1ba0bf14-5766-45ce-b57b-92997d70ef1d
-- title:
--   Definitions bundle OAIQ115N024 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_CAR`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/CAR.lean).
--
--   **Imports.** It imports the published bundle `Def_Naimark`; the bundles `OAIQ115N017`, `OAIQ115N018` and `OAIQ115N020` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ115N026` and `OAIQ115N027`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Naimark
import Definitions.Def_OAIQ115N017
import Definitions.Def_OAIQ115N018
import Definitions.Def_OAIQ115N020

section
-- module Solutions.OAIQ115_Naimark.Naimark_CAR
attribute [-instance] _root_.OAI.NaimarkZFC.constructionIndex_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

theorem carStageTrace_tracial (n : ℕ) (a b : CARStage n) :
    (carStageTrace n).1 (a*b) = (carStageTrace n).1 (b*a) := by
  induction n with
  | zero => exact @mul_comm ℂ inferInstance a b
  | succ n ih => exact matrixTraceState_tracial (carStageTrace n).1 (carStageTrace n).2 ih a b

theorem carTrace_tracial (a b : CAR) : carTrace (a*b) = carTrace (b*a) :=
  cstarDirectLimitState_tracial _ _ _ _ _ carStageTrace_tracial a b

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open Filter Topology
open scoped ComplexOrder CStarAlgebra
section

variable {A B : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem Peaks.mapEquiv {p : ℕ → B} {f g : B →L[ℂ] ℂ} (hp : Peaks p f)
    (γ : B ≃⋆ₐ[ℂ] B) (hg : IsState g) (he : restrictState γ.toStarAlgHom g = f) :
    Peaks (fun n => γ (p n)) g := by
  refine ⟨fun n => (hp.1 n).map γ, fun m n h => OrderHomClass.mono γ (hp.2.1 h),
    hg, ?_, ?_⟩
  · intro n
    change restrictState γ.toStarAlgHom g (p n) = 1
    rw [he]
    exact hp.2.2.2.1 n
  · intro G hG hGp
    have hr := hp.2.2.2.2 _ (isState_restrict γ.toStarAlgHom G hG) hGp
    ext a
    obtain ⟨b,rfl⟩ := γ.surjective a
    exact (congrArg (fun h : B →L[ℂ] ℂ => h b) hr).trans
      (congrArg (fun h : B →L[ℂ] ℂ => h b) he).symm

theorem complexInvTwoPow_re (n : ℕ) :
    ((2:ℂ)⁻¹^n).re = (1/2:ℝ)^n := by
  have hc : (2:ℂ)⁻¹ = ((1/2:ℝ):ℂ) := by norm_num
  rw [hc, ← Complex.ofReal_pow, Complex.ofReal_re]

end

end NaimarkZFC

end

end OAI
end


