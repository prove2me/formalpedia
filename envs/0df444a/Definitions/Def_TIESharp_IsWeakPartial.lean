-- Prove2me | Definitions.Def_TIESharp_IsWeakPartial
-- name    : TIESharp_IsWeakPartial
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:59.57693+00:00
-- url     : https://prove2.me/theorems/abde6b13-ad27-4341-a0bc-d314f5e68079
-- title:
--   Weak partial derivative $\partial_{ij}V=q$ on the open orthant
-- statement:
--   A function $q$ is the **weak partial derivative** $\partial_{ij}V$ of $V$ on the open orthant $(0,\infty)^{n\times m}$, where $\partial_{ij}=\partial/\partial t_{ij}$, if both are locally integrable on the orthant and
--   $$\int V(t)\,\partial_{ij}\varphi(t)\,dt=-\int q(t)\,\varphi(t)\,dt$$
--   for every smooth test function $\varphi$ with compact support contained in the open orthant. This is the sense of the identity $\partial_{ij}V^{m,*}_i=q^{m,*}_{ij}$ (4.6) and of the weak derivatives in Lemma 4.4.
--
--   **Formalization Note.** Smooth is $C^\infty$ (`ContDiff ℝ (⊤ : ℕ∞)`); $\partial_{ij}\varphi(t)$ is the Fréchet derivative applied to the unit vector of entry $(i,j)$.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), §4.2.3, p.18, (4.6); Lemma 4.4, p.19

import Mathlib

set_option autoImplicit false

namespace TIESharp

open MeasureTheory

/-- `q` is the **weak partial derivative** `∂_ij V` of `V` on the open positive orthant
`(0, ∞)^{n×m}` (Li, *Sharp Bounds for Truthful-in-Expectation Scheduling*, arXiv:2611.05134,
§4.2.3, p.18, (4.6): "`∂_ij V = q` in the distributional sense", with `∂_ij = ∂/∂t_ij`): both
functions are locally integrable on the orthant and, for every smooth test function `φ` with compact
support contained in the open orthant,
`∫ V(t) ∂_ij φ(t) dt = − ∫ q(t) φ(t) dt`.

**Formalization Note.** Smooth is `ContDiff ℝ (⊤ : ℕ∞)` (`C^∞`); `∂_ij φ(t)` is the Fréchet
derivative of `φ` at `t` applied to the unit vector of entry `(i, j)`,
`Pi.single i (Pi.single j 1)`. Integrals are over `Fin n → Fin m → ℝ` with Lebesgue measure; the
test function vanishes off its support, so they are integrals over the orthant. Local
integrability makes the integrals genuine. -/
def IsWeakPartial {n m : ℕ} (V q : (Fin n → Fin m → ℝ) → ℝ) (i : Fin n) (j : Fin m) : Prop :=
  LocallyIntegrableOn V {t : Fin n → Fin m → ℝ | ∀ i j, 0 < t i j} ∧
  LocallyIntegrableOn q {t : Fin n → Fin m → ℝ | ∀ i j, 0 < t i j} ∧
  ∀ φ : (Fin n → Fin m → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ {t : Fin n → Fin m → ℝ | ∀ i j, 0 < t i j} →
    ∫ t, V t * fderiv ℝ φ t (Pi.single i (Pi.single j 1)) = - ∫ t, q t * φ t

end TIESharp


