-- Prove2me | Definitions.Def_OptimalBAI_ChernoffPAC_KrichevskyTrofimov
-- name    : OptimalBAI_ChernoffPAC_KrichevskyTrofimov
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:01:32.330007+00:00
-- url     : https://prove2.me/theorems/581604cd-44ff-4aa9-a728-a421f1474ed3
-- title:
--   Bernoulli sequence likelihood and the Krichevsky–Trofimov distribution
-- statement:
--   Fix a length $n \ge 0$ and identify $\{0,1\}^n$ with the Boolean vectors $x = (x_1,\dots,x_n)$. For a mean $u \in [0,1]$, the **Bernoulli likelihood** of $x$ is
--
--   $$p_u(x) = \prod_{i=1}^n u^{x_i}(1-u)^{1-x_i},$$
--
--   the probability of observing exactly the sequence $x$ when $n$ independent Bernoulli random variables with mean $u$ are drawn in succession.
--
--   The **Krichevsky–Trofimov distribution** on $\{0,1\}^n$ mixes these likelihoods over the arcsine density $u \mapsto \big(\pi\sqrt{u(1-u)}\big)^{-1}$ on $(0,1)$, which is the Beta$(1/2,1/2)$ law:
--
--   $$\mathrm{kt}(x) = \int_0^1 \frac{1}{\pi\sqrt{u(1-u)}}\, p_u(x)\,\mathrm du .$$
--
--   The KT distribution is the classical universal code for binary memoryless sources. In Garivier and Kaufmann's analysis of Chernoff's stopping rule it replaces the (non-normalized) maximum likelihood by a genuine probability law that is uniformly within a factor $2\sqrt n$ of it (Lemma 11).
--
--   **Formalization Note** Sequences are functions `Fin n → Bool` (`true` = 1). The integral is Lean's interval integral; its integrand is integrable on $(0,1)$ because $u^{-1/2}(1-u)^{-1/2}$ is, so no junk value arises. At $u \in \{0,1\}$ the likelihood follows the convention $0^0 = 1$.
-- source:
--   Garivier, Kaufmann, Optimal Best Arm Identification with Fixed Confidence, arXiv:1602.04589v2, pp. 10–11, Lemma 11

import Mathlib

/-!
Garivier, Kaufmann, *Optimal Best Arm Identification with Fixed Confidence*,
arXiv:1602.04589v2, p. 10–11, Lemma 11 (quoted from Willems et al. 1995):
the likelihood of a binary sequence under a Bernoulli law, and the
Krichevsky–Trofimov mixture distribution on `{0,1}^n`.
-/

namespace OptimalBAI.ChernoffPAC

/-- `p_u(x)`: the likelihood of the successive observations `x ∈ {0,1}^n`
(`true` = 1, `false` = 0) of independent Bernoulli random variables with mean
`u`, i.e. `∏ᵢ u^{xᵢ} (1-u)^{1-xᵢ}`. -/
noncomputable def bernSeqLik {n : ℕ} (u : ℝ) (x : Fin n → Bool) : ℝ :=
  ∏ i, if x i then u else 1 - u

/-- The Krichevsky–Trofimov distribution
`kt(x) = ∫₀¹ (π √(u(1-u)))⁻¹ p_u(x) du` on `{0,1}^n` (Lemma 11, p. 10): the
mixture of the Bernoulli likelihoods under the arcsine (Beta(1/2,1/2)) prior. -/
noncomputable def ktProb {n : ℕ} (x : Fin n → Bool) : ℝ :=
  ∫ u in (0 : ℝ)..1, (Real.pi * Real.sqrt (u * (1 - u)))⁻¹ * bernSeqLik u x

end OptimalBAI.ChernoffPAC


