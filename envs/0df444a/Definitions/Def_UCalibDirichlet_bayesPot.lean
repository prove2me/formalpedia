-- Prove2me | Definitions.Def_UCalibDirichlet_bayesPot
-- name    : UCalibDirichlet_bayesPot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:06.752566+00:00
-- url     : https://prove2.me/theorems/34ede3a0-ee7c-4b12-99a7-ab4ed892f323
-- title:
--   Convex potential $F=-$(Bayes risk) of a proper loss
-- statement:
--   For a loss $\ell$, the potential $F:\Delta_K\to\mathbb R$ is minus the Bayes risk,
--   $$F(q)=-\mathbb E_{i\sim q}[\ell(q,i)]=-\sum_{i=1}^K q_i\,\ell(q,i).$$
--   For a proper loss $F$ is convex and $\ell(p,i)=-F(p)-\langle g(p),e_i-p\rangle$ for a subgradient $g(p)\in\partial F(p)$; the paper writes $\ell=\ell_F$, and the regret bounds of the paper are stated in terms of $F$.
--
--   **Formalization Note** The sum is computed in `EReal` and converted to a real number; for a proper loss with finite Bayes risk it is real at every point of the simplex, so nothing is lost.
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Theorem 1.2, p.2; §1.1.1, display (3), p.3

import Mathlib

namespace UCalibDirichlet

/-- **The convex potential `F` of a proper loss (minus its Bayes risk).** Frongillo, Luo, Mehta &
Schneider (manuscript, STOC 2027 submission), Theorem 1.2, p.2: "For any proper loss `ℓ`, let
`F(q) = −E_{i∼q}[ℓ(q, i)]` be the (negative) Bayes risk of `ℓ`"; §1.1.1, p.3, display (3): every
proper loss is `ℓ(p, i) = −F(p) − ⟨g(p), e_i − p⟩` with `g(p) ∈ ∂F(p)` for this convex `F`, and the
paper writes `ℓ = ℓ_F`.

`bayesPot ℓ q = −∑_i q_i ℓ(q, i)`.

**Formalization Note.** The `EReal` sum is converted to `ℝ` with `EReal.toReal`; for a proper loss
with finite Bayes risk (`IsProperLoss`, `HasFiniteBayesRisk`) the sum is a real number at every
`q ∈ Δ_K`, so no value is lost. Off the simplex the value is irrelevant. -/
noncomputable def bayesPot {K : ℕ} (ℓ : (Fin K → ℝ) → Fin K → EReal) (q : Fin K → ℝ) : ℝ :=
  -(∑ i, (q i : EReal) * ℓ q i).toReal

end UCalibDirichlet


