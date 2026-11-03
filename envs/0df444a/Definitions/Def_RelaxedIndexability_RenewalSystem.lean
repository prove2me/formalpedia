-- Prove2me | Definitions.Def_RelaxedIndexability_RenewalSystem
-- name    : RelaxedIndexability_RenewalSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:20:17.995662+00:00
-- url     : https://prove2.me/theorems/9246b18f-9746-4fa0-b51b-9bfb84f301d1
-- title:
--   The linear equation set (35)–(36) in $2K$ unknowns (corrected: $\mathcal T^{L}(p_k)$ for $\mathcal T^{L}(\omega)$ in (36))
-- statement:
--   Fix an arm (transition matrix $\mathbf P$ with rows $p_0,\dots,p_{K-1}$, rewards $B$), a discount factor $\beta$, a subsidy $m$ and a threshold belief $\omega$, and write $L_k = L(p_k, \omega)$ for the first-crossing times (34). The **linear equation set (35)–(36)** in the $2K$ unknowns $x_k$ (standing for $\hat V_{\beta,m}(p_k)$) and $y_k$ (standing for $\hat V_{\beta,m}(\mathcal T^{L_k}(p_k); u=1)$) requires, for every $k \in \{0,\dots,K-1\}$:
--
--   1. if $L_k = n$ is finite,
--   $$
--   x_k = \frac{1-\beta^{n}}{1-\beta}\, m + \beta^{n} y_k, \qquad y_k = p_k\mathbf P^{n} B' + \beta\, p_k \mathbf P^{n}\,(x_0, \dots, x_{K-1})';
--   $$
--   2. if $L_k = +\infty$, $x_k = m/(1-\beta)$ (equation (35) with $\beta^{+\infty} = 0$); then $y_k$ is unconstrained.
--
--   The second equation of item 1 is (36) with the belief $\mathcal T^{L_k}(p_k) = p_k\mathbf P^{n}$ in its last term; the page prints $\mathcal T^{L_k}(\omega)$ there, which is a misprint (see the theorem `renewal_equations`).
-- source:
--   Liu, Relaxed Indexability and Index Policy for Partially Observable Restless Bandits, arXiv:2107.11939v4, (35)–(36), p.20; Lemma 3, p.21; (EC.38), p.ec9

import Mathlib
import Definitions.Def_RelaxedIndexability_crossTime

open Matrix

namespace RelaxedIndexability

variable {K : ℕ}

/-- **The linear equation set (35)–(36)** (Liu, arXiv:2107.11939v4, p.20), with `(36)` in its
corrected form, in the `2K` unknowns `x k` (for `V̂_{β,m}(p_k)`) and `y k` (for
`V̂_{β,m}(T^{L(p_k,ω)}(p_k); u = 1)`), with coefficients taken from `L(·, ω)`, `m`, `β`, `P`, `B`.
For every `k`:

* if `L(p_k, ω) = n` is finite: `x k = (1 − βⁿ)/(1 − β) · m + βⁿ · y k` (35) and
  `y k = p_k Pⁿ B′ + β p_k Pⁿ x` (36, corrected: `T^{L}(p_k)` in the second term, where the page
  prints `T^{L}(ω)`);
* if `L(p_k, ω) = +∞`: `x k = m/(1 − β)` ((35) with `β^{+∞} = 0`); then `(36)` does not constrain
  `y k`.

**Formalization Note.** `p_k = P k` is the `k`-th row of `P`, `T^n(p_k) = p_k Pⁿ` is
`P k ᵥ* P ^ n`. -/
def RenewalSystem (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ) (B ω : Fin K → ℝ) (m : ℝ)
    (x y : Fin K → ℝ) : Prop :=
  ∀ k : Fin K,
    (∀ n : ℕ, crossTime P B ω (P k) = n →
      x k = (1 - β ^ n) / (1 - β) * m + β ^ n * y k ∧
      y k = (P k ᵥ* P ^ n) ⬝ᵥ B + β * ((P k ᵥ* P ^ n) ⬝ᵥ x)) ∧
    (crossTime P B ω (P k) = ⊤ → x k = m / (1 - β))

end RelaxedIndexability


