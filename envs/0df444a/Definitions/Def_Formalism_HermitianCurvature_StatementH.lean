-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementH
-- name    : Formalism_HermitianCurvature_StatementH
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:12:02.427271+00:00
-- url     : https://prove2.me/theorems/342ab4eb-be31-49d9-9931-045172d52a3a
-- title:
--   Statement H
-- statement:
--   Definitions and structural lemmas for Statement H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementH.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.H
open Real
def HerglotzZd : Prop :=
  ∀ (d : ℕ) (A : (Fin d → ℤ) → ℂ), Summable (fun σ => ‖A σ‖) →
    (∀ (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ),
        0 ≤ (∑ σ ∈ S, ∑ σ' ∈ S, A (σ - σ') * c σ * starRingEnd ℂ (c σ')).re) →
    ∀ x : Fin d → ℝ,
      0 ≤ (∑' σ, A σ * Complex.exp (2 * π * Complex.I * ∑ j, ((σ j : ℝ) : ℂ) * (x j : ℂ))).re
def HerglotzFejerZd : Prop :=
  ∀ (d : ℕ) (A : (Fin d → ℤ) → ℂ),
    (∀ (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ),
        0 ≤ (∑ σ ∈ S, ∑ σ' ∈ S, A (σ - σ') * c σ * starRingEnd ℂ (c σ')).re) →
    ∀ (N : ℕ) (x : Fin d → ℝ),
      0 ≤ (∑ σ ∈ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(N : ℤ)) N),
        (((∏ j, (1 - |((σ j : ℤ) : ℝ)| / ((N : ℝ) + 1))) : ℝ) : ℂ) * A σ *
          Complex.exp (2 * π * Complex.I * ∑ j, ((σ j : ℝ) : ℂ) * (x j : ℂ))).re
end Formalism.FourierDecayAlt.H


