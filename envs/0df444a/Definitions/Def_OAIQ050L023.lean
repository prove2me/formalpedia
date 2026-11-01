-- Prove2me | Definitions.Def_OAIQ050L023
-- name    : OAIQ050L023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T09:16:52.07096+00:00
-- url     : https://prove2.me/theorems/3315ed25-7c26-4d33-9fc0-304d8a0c6bbe
-- title:
--   Definitions bundle OAIQ050L023 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.Laughlin.Spin.retainedFourColumnsEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Laughlin_FourBody_RetainedSum`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/RetainedSum.lean).
--
--   **Imports.** It imports the bundle `OAIQ050L021` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI_Laughlin_Spin_physicalFourBodyHaar_retained_sum` and `OAI.Laughlin.Spin.physicalFourBodyHaar_retained_sum_s50`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ050L021

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_RetainedSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def retainedFourColumnsEquiv (Q : ℕ) (hQ : 25 ≤ Q) :
    RetainedFourColumns Q ≃ {s : FourCoupledIndex Q // fourCoupledDeficit s ≤ 23} := by
  let f : RetainedFourColumns Q → {s : FourCoupledIndex Q // fourCoupledDeficit s ≤ 23} :=
    fun x => ⟨retainedFourIndex Q (x.1.val+1) (by have := x.1.isLt; omega) x.2.1 x.2.2,
      by rw [retainedFourIndex_deficit]; have := x.1.isLt; omega⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨d,x⟩ ⟨e,y⟩ h
    have hv := congrArg (fun s => fourCoupledDeficit s.val) h
    change fourCoupledDeficit (retainedFourIndex Q _ (by omega) x.1 x.2) =
      fourCoupledDeficit (retainedFourIndex Q _ (by omega) y.1 y.2) at hv
    simp only [retainedFourIndex_deficit] at hv
    have hd : d=e := Fin.ext (by omega)
    subst e
    have he : (retainedFourIndexEquiv Q (d.val+1) (by omega)) x =
        (retainedFourIndexEquiv Q (d.val+1) (by omega)) y := by
      apply Subtype.ext
      exact congrArg (fun s => s.val) h
    exact congrArg (Sigma.mk d) ((retainedFourIndexEquiv Q (d.val+1) (by omega)).injective he)
  · intro s
    let d : Fin 23 := ⟨fourCoupledDeficit s.val-1,by
      have := fourCoupledDeficit_pos s.val; have := s.property; omega⟩
    let t : {t : FourCoupledIndex Q // fourCoupledDeficit t=d.val+1} :=
      ⟨s.val,by have := fourCoupledDeficit_pos s.val; dsimp [d]; omega⟩
    refine ⟨⟨d,(retainedFourIndexEquiv Q (d.val+1) (by omega)).symm t⟩,?_⟩
    apply Subtype.ext
    exact congrArg (fun x : {t : FourCoupledIndex Q // fourCoupledDeficit t=d.val+1} => x.val)
      ((retainedFourIndexEquiv Q (d.val+1) (by omega)).apply_symm_apply t)

end Laughlin.Spin

end OAI
end


