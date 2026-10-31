-- Prove2me | Definitions.Def_RBMSensitivity_IsStrongMarkovAt
-- name    : RBMSensitivity_IsStrongMarkovAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:25.820392+00:00
-- url     : https://prove2.me/theorems/97b6f7d8-6645-412f-83e0-3646966529b6
-- title:
--   The strong Markov property
-- statement:
--   A process $Z^x$, one of a family $\{Z^y\}$ indexed by the starting point, is **strong Markov** if for every stopping time $\tau$, every $t\ge 0$ and every bounded Borel function $g$, on the event $\{\tau<\infty\}$,
--   $$\mathbb E[g(Z^x(\tau+t))\mid\mathcal F_\tau]=(T_tg)(Z^x(\tau))\quad\text{a.s.},\qquad T_tg(y):=\mathbb E[g(Z^y(t))].$$
--
--   The argument that the RBM visits every face infinitely often relies on this property.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Theorem 2.8, p.7

import Mathlib
import Definitions.Def_RBMSensitivity_E
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- The strong Markov property of the process `Zf x`, relative to the family `Zf`:
arXiv:1907.00472v2, Theorem 2.8, p.7. For a stopping time `τ`, `t ≥ 0` and bounded Borel `g`, on
`{τ < ∞}`, `E[g(Z(τ + t)) | F_τ] = (T_t g)(Z(τ))` a.s., where `T_t g(y) := E[g(Zf y t)]`.

**Formalization Note.** Stopping times take values in `WithTop ℝ≥0`. `untopD 0` only affects `{τ = ∞}`,
where the indicator vanishes. -/
def IsStrongMarkovAt {J : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (Zf : E J → ℝ≥0 → Ω → E J) (x : E J) : Prop :=
  ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime 𝓕 τ) (t : ℝ≥0) (g : E J → ℝ),
    Measurable g → (∃ C : ℝ, ∀ y, |g y| ≤ C) →
    P[{ω | τ ω < ⊤}.indicator (fun ω => g (Zf x ((τ ω).untopD 0 + t) ω)) | hτ.measurableSpace]
      =ᵐ[P] {ω | τ ω < ⊤}.indicator
        (fun ω => ∫ ω', g (Zf (Zf x ((τ ω).untopD 0) ω) t ω') ∂P)

end RBMSensitivity


