-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_GTCoefTop
-- name    : Formalism_PeriodIntegrals_GTCoefTop
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:47.873132+00:00
-- url     : https://prove2.me/theorems/705945f3-1c9b-4e0a-9fb6-4ad8d5630f51
-- title:
--   GTCoef Top
-- statement:
--   Definitions and structural lemmas for GTCoef Top, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/GTCoefTop.lean

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
def GTCoefTop : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (hn : 0 < n) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    lam.w ⟨1, by omega⟩ + D0 h lam sg ≤ lam.w ⟨0, by omega⟩ →
    |((cBr h lam sg : ℤ) : ℝ)| ≤
      (((2 * (sg.w ⟨0, hn⟩ - lam.w ⟨N - 1, by omega⟩) + (N : ℤ) : ℤ) : ℝ)) ^ ((((n : ℤ) * D1 h lam sg : ℤ) : ℝ)) ∧
    ∀ lam' : DomWeight N, (∀ i : Fin N, i.1 ≠ 0 → lam'.w i = lam.w i) →
      lam'.w ⟨1, by omega⟩ + D0 h lam' sg ≤ lam'.w ⟨0, by omega⟩ →
      cBr h lam' sg = cBr h lam sg ∧ D1 h lam' sg = D1 h lam sg
end PI


