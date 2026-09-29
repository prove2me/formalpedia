-- Prove2me | solution 1 for AutomorphicForm.constantTerm_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/f146b92a-e7e5-5622-a7b1-87ab37f2030d

import Mathlib
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_constantTerm_add
open AutomorphicForm MeasureTheory

theorem solution {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    (μ : Measure Q) (u : Q → G) {f₁ f₂ : G → ℂ} (g : G)
    (h₁ : Integrable (constantTermIntegrand u f₁ g) μ)
    (h₂ : Integrable (constantTermIntegrand u f₂ g) μ) :
    constantTerm μ u (fun x => f₁ x + f₂ x) g
      = constantTerm μ u f₁ g + constantTerm μ u f₂ g := by
  simpa [constantTerm, constantTermIntegrand] using integral_add h₁ h₂

end S_AutomorphicForm_constantTerm_add
end P2MW
export P2MW.S_AutomorphicForm_constantTerm_add (solution)
