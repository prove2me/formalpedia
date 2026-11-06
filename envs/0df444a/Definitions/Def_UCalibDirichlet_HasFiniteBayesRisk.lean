-- Prove2me | Definitions.Def_UCalibDirichlet_HasFiniteBayesRisk
-- name    : UCalibDirichlet_HasFiniteBayesRisk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:10.789344+00:00
-- url     : https://prove2.me/theorems/4c5d9098-6d3a-48ef-9c8f-77824e7050cd
-- title:
--   Finite Bayes risk of a proper loss
-- statement:
--   A loss $\ell$ has **finite Bayes risk** if for every $q\in\Delta_K$
--   $$\mathbb E_{i\sim q}[\ell(q,i)]=\sum_{i=1}^K q_i\,\ell(q,i)<+\infty .$$
--   The paper writes every proper loss as $\ell_F$ with a convex potential $F:\Delta_K\to\mathbb R$, $F(q)=-\mathbb E_{i\sim q}[\ell(q,i)]$, and does not allow $F$ to take the value $+\infty$ (footnote 1). This predicate expresses that restriction.
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), §1.1.1, display (3) and footnote 1, p.3; Theorem 1.2, p.2

import Mathlib

namespace UCalibDirichlet

/-- **Finite Bayes risk (footnote 1).** Frongillo, Luo, Mehta & Schneider (manuscript, STOC 2027
submission), §1.1.1, p.3, display (3) and footnote 1: the convex potential `F` of a proper loss,
with `−F(q) = E_{i∼q}[ℓ(q, i)]` the Bayes risk (Theorem 1.2, p.2), is a function
`F : Δ_K → ℝ`; "We do not allow `F` to take the value `+∞`".

`HasFiniteBayesRisk ℓ` says that the Bayes risk `∑_i q_i ℓ(q, i)` is not `+∞` at any `q ∈ Δ_K`.

**Formalization Note.** Together with `IsProperLoss` (values never `−∞`) this makes the Bayes risk
a real number at every point of the simplex, i.e. `F` is finite, as the paper requires of every
proper loss `ℓ_F`. -/
def HasFiniteBayesRisk {K : ℕ} (ℓ : (Fin K → ℝ) → Fin K → EReal) : Prop :=
  ∀ q ∈ stdSimplex ℝ (Fin K), ∑ i, (q i : EReal) * ℓ q i ≠ ⊤

end UCalibDirichlet


