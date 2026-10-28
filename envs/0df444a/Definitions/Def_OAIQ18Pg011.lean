-- Prove2me | Definitions.Def_OAIQ18Pg011
-- name    : OAIQ18Pg011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T16:00:51.284705+00:00
-- url     : https://prove2.me/theorems/81f86f86-d94d-44fb-9e5d-8bc4f10c403f
-- title:
--   Definitions bundle OAIQ18Pg011 of the split of OpenAI, An infinite finitely presented periodic group
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SourceBurnside.thm_main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented periodic group*, OpenAI Math Release, September 23, 2026, result family 247, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 1 definition and 2 theorems. The definitions and types are `OAI.SourceBurnside.SteinbergQuotient.equiv`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory/PeriodicGroups, in whole or in part: [`PeriodicGroups_Steinberg_CoefficientQuotients`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/PeriodicGroups/PeriodicGroups/Steinberg/CoefficientQuotients.lean).
--
--   **Imports.** It imports the published bundle `Def_PeriodicGroup`; the bundle `OAIQ18Pg006` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.SourceBurnside.thm_main`.
-- source:
--   OpenAI, An infinite finitely presented periodic group, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 247; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-infinite-finitely-presented-periodic-group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/PeriodicGroups at commit adc7f12

import Mathlib
import Definitions.Def_PeriodicGroup
import Definitions.Def_OAIQ18Pg006

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_CoefficientQuotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside

namespace SteinbergQuotient

variable {n : ℕ} {R : Type u} [Ring R]

variable (S : Set R)

 theorem fromCoeff_comp_toCoeff (hn : 5 ≤ n) :
    (fromCoeff S hn).comp (toCoeff S) = MonoidHom.id (Quot (n := n) S) := by
  have h : ((fromCoeff S hn).comp (toCoeff S)).comp (proj S) = proj (n := n) S := by
    apply Steinberg.hom_ext
    intro p a
    change fromCoeff S hn (toCoeff S (proj S (Steinberg.x p a))) = _
    rw [toCoeff_proj, Steinberg.map_x, fromCoeff_x]
  apply MonoidHom.ext
  intro g
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (normal S) g
  exact DFunLike.congr_fun h g

 theorem toCoeff_comp_fromCoeff (hn : 5 ≤ n) :
    (toCoeff S).comp (fromCoeff S hn) = MonoidHom.id (Steinberg n (Coeff S)) := by
  apply Steinberg.hom_ext
  intro p a
  obtain ⟨a, rfl⟩ := (coeffIdeal S).ringCon.mk'_surjective a
  change toCoeff S (fromCoeff S hn (Steinberg.x p ((coeffIdeal S).ringCon.mk' a))) = _
  rw [fromCoeff_x, toCoeff_proj, Steinberg.map_x]
  rfl

noncomputable def equiv (hn : 5 ≤ n) : Quot (n := n) S ≃* Steinberg n (Coeff S) where
  toFun := toCoeff S
  invFun := fromCoeff S hn
  left_inv g := DFunLike.congr_fun (fromCoeff_comp_toCoeff S hn) g
  right_inv g := DFunLike.congr_fun (toCoeff_comp_fromCoeff S hn) g
  map_mul' := (toCoeff S).map_mul

end SteinbergQuotient

end SourceBurnside

end

end OAI
end


