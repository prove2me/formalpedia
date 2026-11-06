-- Prove2me | Definitions.Def_AnchoredEP_abar
-- name    : AnchoredEP_abar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:44.532309+00:00
-- url     : https://prove2.me/theorems/a7dc4528-d28e-4041-955a-6356a3d7fd20
-- title:
--   Upper trial step size $\bar a_k$
-- statement:
--   With $\rho=1/\sqrt2$ and $M_p=(p+1)L_p$, the line search at the state $(z_k,v_k,A_k)$ starts from
--   $$
--   \bar a_k=\max\left\{\frac{2A_k\|F(z_k)+v_k\|}{\varepsilon},\ \left(\frac{2(1+\rho)}{\varepsilon}\Big(\frac{p!\rho}{M_p}\Big)^{1/(p-1)}\right)^{(p-1)/p}\right\}.
--   $$
--   If the merit function passes at $\bar a_k$, the trial point is already $\varepsilon$-accurate (Lemma G.2).
--
--   **Formalization Note** The exponents $1/(p-1)$ and $(p-1)/p$ are real exponents.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Appendix G.2, Eq. (90), p.38

import Mathlib
import Definitions.Def_AnchoredEP_IterState

namespace AnchoredEP

/-- **The upper trial step size `ā_k`.** Jiang–Yoon, arXiv:2609.30212, Appendix G.2, Eq. (90),
p.38:
`ā_k := max { 2A_k‖F(z_k) + v_k‖/ε , ( (2(1 + ρ)/ε) (p!ρ/M_p)^{1/(p−1)} )^{(p−1)/p} }`,
with `ρ = 1/√2` and `M_p = (p + 1)L_p` (p.37).

**Formalization Note.** The exponents `1/(p−1)` and `(p−1)/p` are real exponents
(`Real.rpow`); the base `(2(1+ρ)/ε)(p!ρ/M_p)^{1/(p−1)}` is positive when `ε, L_p > 0`. -/
noncomputable def abar {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (p : ℕ) (L ε : ℝ) (s : IterState d) : ℝ :=
  max (2 * s.A * ‖F s.z + s.v‖ / ε)
    ((2 * (1 + 1 / Real.sqrt 2) / ε *
        ((p.factorial : ℝ) * (1 / Real.sqrt 2) / (((p : ℝ) + 1) * L)) ^ ((1 : ℝ) / ((p : ℝ) - 1)))
      ^ (((p : ℝ) - 1) / (p : ℝ)))

end AnchoredEP


