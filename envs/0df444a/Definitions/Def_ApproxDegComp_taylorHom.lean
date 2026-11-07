-- Prove2me | Definitions.Def_ApproxDegComp_taylorHom
-- name    : ApproxDegComp_taylorHom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:30:51.686142+00:00
-- url     : https://prove2.me/theorems/866e53d1-dd6e-4e03-9742-c861481f6848
-- title:
--   Homogeneous Taylor parts $H_r$ at $0$
-- statement:
--   For $R:\mathbb R^n\to\mathbb C$ analytic at $0$ write its Taylor expansion at $0$ as $R=\sum_{r\ge0}H_r$ with $H_r$ homogeneous of degree $r$. Then
--
--   $$H_r(y)=\frac1{r!}\,\frac{d^r}{ds^r}R(sy)\Big|_{s=0},$$
--
--   and in particular $H_0=R(0)$.
--
--   **Formalization Note** $H_r(y)$ is defined by the displayed formula, the $r$-th Taylor coefficient of the one-variable function $s\mapsto R(sy)$; for $R$ analytic at $0$ (a trigonometric polynomial is entire) this is the degree-$r$ homogeneous part of the Taylor series.
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Lemma 7, p.16

import Mathlib

namespace ApproxDegComp

/-- **Homogeneous Taylor part** `H_r` at `0` (Lemma 7, p.16).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Lemma 7, p.16: "Taking Taylor expansion at zero as R = Σ_{r≥0} H_r, where H_r is
homogeneous of degree r."

`taylorHom R r y = (1/r!) (d/ds)^r R(s·y) |_{s=0}`, the degree-`r` homogeneous part of the
Taylor expansion of `R` at `0`, evaluated at `y`.

**Formalization Note** For `R` analytic at `0` (a trigonometric polynomial is entire),
`R(s y) = Σ_r s^r H_r(y)` for small `s`, so `H_r(y)` is the `r`-th Taylor coefficient of the
one-variable function `s ↦ R(s y)`; in particular `H₀ = R(0)`. -/
noncomputable def taylorHom {n : ℕ} (R : (Fin n → ℝ) → ℂ) (r : ℕ) (y : Fin n → ℝ) : ℂ :=
  iteratedDeriv r (fun s : ℝ => R (s • y)) 0 / (r.factorial : ℂ)

end ApproxDegComp


