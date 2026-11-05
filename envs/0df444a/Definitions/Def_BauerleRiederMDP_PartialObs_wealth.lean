-- Prove2me | Definitions.Def_BauerleRiederMDP_PartialObs_wealth
-- name    : BauerleRiederMDP_PartialObs_wealth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:00:31.606049+00:00
-- url     : https://prove2.me/theorems/55835d61-8f1c-4e7a-9a4c-1ec89aaa903c
-- title:
--   The wealth process $X_{n+1}=(1+i_{n+1})(X_n+\varphi_n\cdot R_{n+1})$
-- statement:
--   A portfolio strategy invests the amount $\varphi_n\in\mathbb R^d$ in the $d$ stocks during $[n,n+1)$ and the rest in the bond. Under partial observation $\varphi_n$ is $\mathcal F^S_n$-measurable, $\mathcal F^S_n=\sigma(R_1,\dots,R_n)$, so it is a function of the observed relative risks $(R_1,\dots,R_n)$. Starting from initial wealth $X_0=x$ the self-financing wealth evolves as
--   $$
--   X_{n+1}=(1+i_{n+1})\big(X_n+\varphi_n\cdot R_{n+1}\big),
--   $$
--   where $i_{n+1}$ is the interest rate of the period $[n,n+1)$ (constant in Section 6.1).
--
--   **Formalization Note** A strategy is a family $\varphi_n:(\mathbb R^d)^n\to\mathbb R^d$; its measurability is required where strategies are quantified. The observable history $h_n=(x_0,a_0,z_1,x_1,\dots,z_n,x_n)$ is a function of $x_0$, the strategy and $(z_1,\dots,z_n)$. Return paths are 0-indexed.
-- source:
--   Bäuerle & Rieder (2011), wealth equation (3.1), p.63 (PDF 77); §6.1, p.176 (PDF 189); §6.2, p.184 (PDF 197)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BauerleRiederMDP.PartialObs

/-- **The wealth process of a portfolio strategy.**
Bäuerle & Rieder (2011), wealth equation (3.1), p.63 (PDF 77), as used in §6.1, p.176 (PDF 189):
`X_{n+1} = (1 + i_{n+1})(X_n + φ_n · R_{n+1})`, `X_0 = x`, and in §6.2, p.184 (PDF 197), with the
transition `T_{n,X}(x, a, z) = (1 + i_{n+1})(x + a · z)`.

A portfolio strategy is `φ n : (ℝ^d)^n → ℝ^d`: the amounts `φ_n` invested in the `d` stocks
during `[n, n+1)`, as a function of the observed relative risks `(R_1, …, R_n)`. Since
`F_n = F^S_n = σ(R_1, …, R_n)` (p.176), the `(F_n)`-adapted strategies of the book are exactly
these functions when they are measurable (Doob–Dynkin); the observable history
`h_n = (x_0, a_0, z_1, x_1, …, z_n, x_n)` is itself a function of `x_0`, the strategy and
`(z_1, …, z_n)`.

`wealth i x φ n r` is `X_n` along the return path `r = (R_1, …, R_n)`, where `i (n+1)` is the
interest rate `i_{n+1}` of the period `[n, n+1)` (for §6.1, `i` is constant).

**Formalization Note.** Paths are 0-indexed (`r k = R_{k+1}`); `a · z` is `a ⬝ᵥ z`. -/
noncomputable def wealth {d : ℕ} (i : ℕ → ℝ) (x : ℝ)
    (φ : (n : ℕ) → (Fin n → Fin d → ℝ) → Fin d → ℝ) : (n : ℕ) → (Fin n → Fin d → ℝ) → ℝ
  | 0, _ => x
  | n + 1, r =>
      (1 + i (n + 1)) * (wealth i x φ n (Fin.init r) + φ n (Fin.init r) ⬝ᵥ r (Fin.last n))

end BauerleRiederMDP.PartialObs


