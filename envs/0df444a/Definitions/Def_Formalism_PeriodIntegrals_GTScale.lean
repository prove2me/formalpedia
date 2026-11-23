-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_GTScale
-- name    : Formalism_PeriodIntegrals_GTScale
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:55:55.723571+00:00
-- url     : https://prove2.me/theorems/f359f6c1-b64f-458a-8054-6fd66406aa59
-- title:
--   GTScale
-- statement:
--   Definitions and structural lemmas for GTScale, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/GTScale.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI
open Formalism.BasicNotions MvPolynomial
def GTScale : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
    (br : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ),
    IsIota h lam sg io → IsBr h lam sg br → ∀ a : ℂˣ,
    (∀ s ∈ nablaSq ℂ n sg,
      (normFock lam (sqAct ℂ N lam (lastGL ℂ N a⁻¹) (io s)) (sqAct ℂ N lam (lastGL ℂ N a⁻¹) (io s))).re ≤
        ‖(a : ℂ)‖ ^ (-(2 * degZ lam sg)) * brBd h lam sg ^ 2 * (normFock sg s s).re) ∧
    (∀ f ∈ delSq ℂ N lam,
      (normFock sg (br f) (br f)).re ≤ ‖(a : ℂ)‖ ^ (-(2 * degZ lam sg)) * brBd h lam sg ^ 2 *
        (normFock lam (sqAct ℂ N lam (lastGL ℂ N a) f) (sqAct ℂ N lam (lastGL ℂ N a) f)).re)
end PI


