-- Prove2me | Definitions.Def_Gelbart_hecke_conditions
-- name    : Gelbart_hecke_conditions
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-14T03:31:52.489436+00:00
-- url     : https://prove2.me/theorems/6e5096a7-494b-4eac-9fbe-41cf343f0224
-- title:
--   Hecke's conditions (A) and (B)
-- statement:
--   Gelbart's two conditions (§II.B.2, p. 188), for data $(a, h, k, C)$ and an abscissa $\sigma$ beyond which $\varphi$ converges.
--
--   **(A)** There is an entire function $F$ which, on the half-plane $\operatorname{Re} s > \sigma$, equals $$\Phi(s) + \frac{a_0}{s} + \frac{C a_0}{k-s},$$ which is bounded on every vertical strip, and which satisfies $F(k-s) = C\,F(s)$ for all $s$. For $C = \pm 1$ the last condition is equivalent to Gelbart's $\Phi(k-s) = C\,\Phi(s)$.
--
--   **(B)** For every $z$ with $\operatorname{Im} z > 0$, $$f(-1/z) = C\left(\frac{z}{i}\right)^{k} f(z).$$
--
--   The printed source writes the correction term as $C/(k-s)$; $C a_0/(k-s)$ is the standard form (Ogg, *Modular forms and Dirichlet series*, Ch. 1) and the two agree when $a_0 = 0$.
-- source:
--   S. Gelbart, An elementary introduction to the Langlands program, Bull. Amer. Math. Soc. (N.S.) 10 (1984), no. 2, 177-219, https://doi.org/10.1090/S0273-0979-1984-15237-6, p. 188, §II.B.2, conditions (A) and (B)

import Definitions.Def_Gelbart_hecke_series

namespace Gelbart

/-- Hecke's condition (A) for the data `(a, h, k, C)`, with `σ` an abscissa beyond which
the Dirichlet series converges. -/
def HeckeNice (a : ℕ → ℂ) (h k : ℝ) (C : ℂ) (σ : ℝ) : Prop :=
  ∃ F : ℂ → ℂ,
    Differentiable ℂ F ∧
    (∀ s : ℂ, σ < s.re →
      F s = heckeCompletedLSeries a h s + a 0 / s + C * a 0 / ((k : ℂ) - s)) ∧
    (∀ σ₁ σ₂ : ℝ, ∃ M : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖F s‖ ≤ M) ∧
    (∀ s : ℂ, F ((k : ℂ) - s) = C * F s)

/-- Hecke's condition (B) for the data `(a, h, k, C)`: the automorphy relation
`f (-1/z) = C (z/i)^k f (z)` on the upper half-plane. -/
def HeckeAutomorphic (a : ℕ → ℂ) (h k : ℝ) (C : ℂ) : Prop :=
  ∀ z : ℂ, 0 < z.im →
    heckeForm a h (-1 / z) = C * (z / Complex.I) ^ (k : ℂ) * heckeForm a h z

end Gelbart


