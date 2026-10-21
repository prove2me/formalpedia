-- Prove2me | Definitions.Def_NatureSLT_IllPosed_operatorDistance
-- name    : NatureSLT_IllPosed_operatorDistance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:52:12.201486+00:00
-- url     : https://prove2.me/theorems/c21b3d7d-ca0f-4449-9251-048625d9b396
-- title:
--   Distance between operators $\|A_\ell - A\| = \sup_f \rho_{E_2}(A_\ell f, Af)/\Omega^{1/2}(f)$ of (7.48)
-- statement:
--   Let $E_1$ be a set, $(E_2, \rho_{E_2})$ a metric space, $\Omega : E_1 \to [0,\infty]$ a regularization functional, and $B, A : E_1 \to E_2$ two maps. Their **distance relative to $\Omega$** is
--
--   $$\|B - A\| = \sup_{f \,:\, \Omega(f) < \infty} \frac{\rho_{E_2}(B f, A f)}{\Omega^{1/2}(f)} \in [0, \infty].$$
--
--   It measures how close an approximate operator $B = A_\ell$ is to the true operator $A$, with the discrepancy at $f$ scaled by the size $\Omega^{1/2}(f)$ of $f$. Theorem 7.5 bounds the error of Tikhonov's method in terms of this distance.
--
--   **Formalization Note** The supremum is taken over the domain $\{\Omega < \infty\}$ of $\Omega$, in $[0, \infty]$, so it always exists. At a point with $\Omega(f) = 0$ the quotient is read as $0$ if $Bf = Af$ and as $+\infty$ otherwise, the convention under which $\rho_{E_2}(Bf, Af) \le \|B - A\|\,\Omega^{1/2}(f)$ holds for every $f$ in the domain.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 251, Eq. (7.48)

import Mathlib

namespace NatureSLT.IllPosed

open scoped ENNReal

/-- The distance between two operators of (7.48) (Vapnik, *The Nature of Statistical Learning
Theory*, 2nd ed., §7.9.1, p. 251):
`‖B − A‖ = sup_f ρ_{E₂}(B f, A f) / Ω^{1/2}(f)`, the supremum over the domain `{Ω < ∞}` of the
regularization functional `Ω : E₁ → [0, ∞]`.

The value is in `[0, ∞]`. For a point with `Ω g = 0` the quotient is `0` if `B g = A g` and `∞`
otherwise (`ENNReal` division: `x / 0 = ∞` for `x ≠ 0`, `0 / 0 = 0`), so that
`ρ_{E₂}(B g, A g) ≤ ‖B − A‖ Ω^{1/2}(g)` holds for every `g` in the domain. -/
noncomputable def operatorDistance {E₁ E₂ : Type*} [MetricSpace E₂] (B A : E₁ → E₂)
    (Ω : E₁ → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (g : E₁) (_ : Ω g ≠ ⊤), ENNReal.ofReal (dist (B g) (A g)) / Ω g ^ ((1 : ℝ) / 2)

end NatureSLT.IllPosed


