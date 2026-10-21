-- Prove2me | Definitions.Def_NatureSLT_SRM_ConvergesWithRate
-- name    : NatureSLT_SRM_ConvergesWithRate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:50:57.723977+00:00
-- url     : https://prove2.me/theorems/57754409-7ab7-4007-b194-14ff0b41fd40
-- title:
--   Convergence of random variables $\xi_\ell$ to $\xi_0$ with asymptotic rate $V(\ell)$ (footnote 3, p. 97)
-- statement:
--   Let $F$ be a probability measure on a set $Z$, and for each sample size $\ell$ let $\xi_\ell = \xi_\ell(z_1, \dots, z_\ell)$ be a real random variable computed from an i.i.d. sample $z_1, \dots, z_\ell$ drawn from $F$. Let $\xi_0$ be a real number and $V(\ell)$ a sequence of reals. The random variables $\xi_\ell$, $\ell = 1, 2, \dots$, **converge to the value $\xi_0$ with asymptotic rate $V(\ell)$** if there exists a constant $C$ such that
--   $$V^{-1}(\ell)\, |\xi_\ell - \xi_0| \xrightarrow[\ell \to \infty]{P} C,$$
--   that is, for every $\varepsilon > 0$,
--   $$\lim_{\ell \to \infty} P\big\{ \big| V^{-1}(\ell) |\xi_\ell - \xi_0| - C \big| > \varepsilon \big\} = 0 .$$
--
--   This is the notion of rate in which Theorem 4.1 (the asymptotic rate of the structural risk minimization principle) is stated.
--
--   **Formalization Note** $\xi_\ell$ is a function on $Z^\ell$ (samples indexed by $\{0, \dots, \ell-1\}$) and the probability is the product measure $F^\ell$. The definition is the book's literal one (convergence in probability of the normalized error to a constant), which is stronger than the usual "$|\xi_\ell - \xi_0| = O_P(V(\ell))$". The book leaves $V^{-1}(\ell)$ undefined when $V(\ell) = 0$; in Lean $0^{-1} = 0$, so at such $\ell$ the normalized error is read as $0$.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 97, Section 4.2, footnote 3

import Mathlib

open MeasureTheory Filter Topology

namespace NatureSLT.SRM

/-- **Convergence with asymptotic rate** (Vapnik, *The Nature of Statistical Learning Theory*,
2nd ed., §4.2, p. 97, footnote 3): the random variables `ξ_ℓ`, `ℓ = 1, 2, …`, converge to the
value `ξ₀` with asymptotic rate `V(ℓ)` if there exists a constant `C` such that
`V⁻¹(ℓ) |ξ_ℓ − ξ₀|` converges in probability to `C` as `ℓ → ∞`.
Here `ξ_ℓ` is a function of an i.i.d. sample `z₁, …, z_ℓ` drawn from `F`, i.e. a function on
`Z^ℓ` under the product measure `F^ℓ`. -/
def ConvergesWithRate {Z : Type*} [MeasurableSpace Z] (F : Measure Z)
    (ξ : ∀ ℓ : ℕ, (Fin ℓ → Z) → ℝ) (ξ₀ : ℝ) (V : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ ε : ℝ, 0 < ε →
    Tendsto (fun ℓ : ℕ => (Measure.pi fun _ : Fin ℓ => F)
      {z | ε < |(V ℓ)⁻¹ * |ξ ℓ z - ξ₀| - C|}) atTop (𝓝 0)

end NatureSLT.SRM


