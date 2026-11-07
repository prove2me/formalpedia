-- Prove2me | Definitions.Def_PrivBayesTest_lapLaw
-- name    : PrivBayesTest_lapLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:10.726877+00:00
-- url     : https://prove2.me/theorems/742e2013-3f6b-4843-81ee-031d2bbaf076
-- title:
--   Law of the Laplace statistic $M_{\mathrm{Lap}}(X)=\sum_i\bar\ell(X_i)+Z$
-- statement:
--   Let $\bar\ell:\mathcal X\to\mathbb R$, $s>0$, $n\in\mathbb N$ and $P$ a probability measure on $\mathcal X$. With $X\sim P^n$ and, independently, $Z\sim\mathrm{Lap}(s)$ (density $e^{-|z|/s}/(2s)$), the statistic of §2.3 is
--
--   $$
--   M_{\mathrm{Lap}}(X) \;=\; \sigma(X)+Z,\qquad \sigma(X)=\sum_{i=1}^n \bar\ell(X_i).
--   $$
--
--   This definition is the law $M_{\mathrm{Lap}}(P^n)$ of $M_{\mathrm{Lap}}(X)$ on $\mathbb R$. The paper uses the scale $s=1/(1-\tilde\alpha)$.
--
--   **Formalization Note** The law is the image of $P^n\otimes\mathrm{Lap}(s)$ under $(x,z)\mapsto\sum_i\bar\ell(x_i)+z$, with $\mathrm{Lap}(s)$ the published `PrivLearn.Generic.laplace`.
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), §2.3, p.12; proof of Lemma 3.3, p.16

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy

open MeasureTheory

namespace PrivBayesTest

/-- The **output law of the Laplace test statistic** `M_Lap(X) = σ(X) + Z`, `σ(X) = Σᵢ ℓ̄(Xᵢ)`,
`Z ∼ Lap(s)` independent of `X ∼ Pⁿ` (Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), §2.3, p.12 and proof of Lemma 3.3, p.16).

**Formalization Note** The law is the image of `Pⁿ ⊗ Lap(s)` under `(x, z) ↦ Σᵢ ℓ̄(xᵢ) + z`, with
`Lap(s)` the published `PrivLearn.Generic.laplace s` (density `e^{−|x|/s}/(2s)`). The paper uses the
scale `s = 1/(1 − α̃)`; the theorems that use this law fix `s`. -/
noncomputable def lapLaw {X : Type*} [MeasurableSpace X] (ℓbar : X → ℝ) (s : ℝ) (n : ℕ)
    (P : Measure X) : Measure ℝ :=
  ((Measure.pi (fun _ : Fin n => P)).prod (PrivLearn.Generic.laplace s)).map
    (fun p => (∑ i, ℓbar (p.1 i)) + p.2)

end PrivBayesTest


