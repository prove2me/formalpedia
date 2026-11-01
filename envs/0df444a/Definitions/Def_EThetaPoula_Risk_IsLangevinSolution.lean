-- Prove2me | Definitions.Def_EThetaPoula_Risk_IsLangevinSolution
-- name    : EThetaPoula_Risk_IsLangevinSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:22:37.961945+00:00
-- url     : https://prove2.me/theorems/f5ff3aea-0e39-4dd2-8bdd-178dc5b00d68
-- title:
--   $Z$ solves the Langevin SDE (37)
-- statement:
--   $Z$ solves
--   $$
--   dZ_t=-h(Z_t)\,dt+\sqrt{2\beta^{-1}}\,dB_t
--   $$
--   with initial condition $Z_0$: its paths are almost surely continuous and, almost surely, for all $t\ge0$,
--   $$
--   Z_t=Z_0-\int_0^t h(Z_s)\,ds+\sqrt{2\beta^{-1}}\,B_t.
--   $$
--   The time-changed process $Z^\lambda_t:=Z_{\lambda t}$ solves (38).
--
--   **Formalization Note** The noise is additive, so the pathwise integral equation needs no Itô integral. Existence and uniqueness are the paper's citation [44, Theorem 1]; the predicate assumes neither.
-- source:
--   Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, §6.1, (37), p.22; (38), p.23

import Mathlib
import Definitions.Def_EThetaPoula_Risk_Model

open MeasureTheory
open scoped NNReal

namespace EThetaPoula.Risk

/-- `Z` solves the Langevin SDE (37), `dZ_t = −h(Z_t) dt + √(2β⁻¹) dB_t`, `Z₀ := Z0`, Lim, Neufeld,
Sabanis, Zhang, arXiv:2210.13193v3, §6.1, p.22.

**Formalization Note.** The noise is additive, so no Itô integral is needed: `Z` has almost surely
continuous paths and satisfies the integral equation pathwise. Existence and uniqueness are the
paper's citation [44, Theorem 1]; neither is assumed by this predicate. The time-changed process
`Z^λ_t = Z_{λt}` of (38) needs no separate definition. -/
def Model.IsLangevinSolution {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (S : Model d m Ω)
    (B : ℝ≥0 → Ω → Eucl d) (β : ℝ) (Z0 : Ω → Eucl d) (Z : ℝ≥0 → Ω → Eucl d) : Prop :=
  (∀ᵐ ω ∂S.P, Continuous fun t => Z t ω) ∧
  ∀ᵐ ω ∂S.P, ∀ t : ℝ≥0, Z t ω =
    Z0 ω - (∫ s in (0 : ℝ)..t, S.h (Z s.toNNReal ω)) + √(2 * β⁻¹) • B t ω

end EThetaPoula.Risk


