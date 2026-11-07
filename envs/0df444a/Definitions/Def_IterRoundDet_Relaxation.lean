-- Prove2me | Definitions.Def_IterRoundDet_Relaxation
-- name    : IterRoundDet_Relaxation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:22.215201+00:00
-- url     : https://prove2.me/theorems/6372ea1c-5e60-484a-b263-6c13053340fa
-- title:
--   The relaxation $f(a,x)$ and the maximum-entropy function $E_p(a)$
-- statement:
--   The convex relaxation of the paper is built on
--
--   $$f(a,x)=\inf_{\theta\in\mathbb R^n:\ a^\top\theta\ge 0}\log p(x\circ e^\theta),\qquad \mathrm{REL}=\max_{(a,x)\in\mathcal R} f(a,x).$$
--
--   Its dual uses the maximum entropy of a law $\mu$ on the sets $S$ with $c_S>0$ and marginals $\mathbb E_\mu\mathbf 1_S=a$:
--
--   $$E_p(a)=\max_\mu\sum_S\mu(S)\log\frac{c_S}{\mu(S)}.$$
--
--   The file defines $f$, the set of admissible laws, the entropy value, $E_p$, and the predicate that $\mu$ is the maximizer $\mu_a$.
--
--   **Formalization Note** $f$ is a real infimum and $E_p$ a real supremum. They are meaningful on $\mathcal R$ and on $P(\mathcal N)$ respectively (Lemmas 3.3, 3.4), and no statement of the mission reads them elsewhere: on the paper's own example $f=-\infty$ off $P(\mathcal N)$. A term with $\mu(S)=0$ is $0$, as on the page.
-- source:
--   Bansal, Li, Singh, Xu, Iterative Rounding for Determinant Maximization and Real Stable Polynomials, STOC 2027 submission (manuscript sha256 aa18bcee…), (13), p.12; Lemma 3.4, p.14

import Mathlib
import Definitions.Def_IterRoundDet_StablePoly

set_option autoImplicit false

namespace IterRoundDet

/-!
# The relaxation `f` and the maximum-entropy function `E_p`

Bansal, Li, Singh, Xu, STOC 2027 submission (manuscript sha256 aa18bcee…): (13), p.12; Lemma 3.4, p.14.
-/

variable {n : ℕ}

/-- `f(a, x) = inf_{θ ∈ ℝⁿ : a⊤θ ≥ 0} log p(x ∘ e^θ)`, (13), p.12.

**Formalization Note.** This is a real infimum, and it is used only on `R`, where `p(x ∘ e^θ) > 0` and
the family is bounded below (Lemmas 3.3, 3.4). Off `R` the page's value can be `−∞` and this one is
junk, so no statement of the mission reads it off `R`. -/
noncomputable def relaxObj (c : Finset (Fin n) → ℝ) (a x : Fin n → ℝ) : ℝ :=
  ⨅ θ : {θ : Fin n → ℝ // 0 ≤ a ⬝ᵥ θ},
    Real.log (pEval c fun i => x i * Real.exp ((θ : Fin n → ℝ) i))

/-- `μ` is a distribution on the sets `S` with `c_S > 0`, with `E_μ 1_S = a` (Lemma 3.4, p.14). -/
def IsMarginalLaw (c : Finset (Fin n) → ℝ) (a : Fin n → ℝ) (μ : Finset (Fin n) → ℝ) : Prop :=
  (∀ S, 0 ≤ μ S) ∧ ∑ S, μ S = 1 ∧ (∀ S, 0 < μ S → 0 < c S) ∧ ∀ i, ∑ S, μ S * ind S i = a i

/-- `∑_S μ(S) log(c_S / μ(S))`. At `μ(S) = 0` the term is `0`, as the page means. -/
noncomputable def entropyVal (c μ : Finset (Fin n) → ℝ) : ℝ :=
  ∑ S, μ S * Real.log (c S / μ S)

/-- `E_p(a) = max_μ ∑_S μ(S) log(c_S / μ(S))`, Lemma 3.4, p.14. Lemma 3.4 makes this supremum a
greatest element for `a ∈ P(N)`; off `P(N)` the set is empty and the value is junk. -/
noncomputable def Ep (c : Finset (Fin n) → ℝ) (a : Fin n → ℝ) : ℝ :=
  sSup {t | ∃ μ, IsMarginalLaw c a μ ∧ t = entropyVal c μ}

/-- `μ` is the maximizing distribution `μ_a` in the definition of `E_p(a)`, p.14. -/
def IsMaxEnt (c : Finset (Fin n) → ℝ) (a : Fin n → ℝ) (μ : Finset (Fin n) → ℝ) : Prop :=
  IsMarginalLaw c a μ ∧ ∀ ν, IsMarginalLaw c a ν → entropyVal c ν ≤ entropyVal c μ

end IterRoundDet


