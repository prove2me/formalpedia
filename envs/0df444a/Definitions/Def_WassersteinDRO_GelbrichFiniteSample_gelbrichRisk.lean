-- Prove2me | Definitions.Def_WassersteinDRO_GelbrichFiniteSample_gelbrichRisk
-- name    : WassersteinDRO_GelbrichFiniteSample_gelbrichRisk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:59:04.940758+00:00
-- url     : https://prove2.me/theorems/da80ef19-0e29-4336-9bb8-3a5e165283e3
-- title:
--   Gelbrich risk $\overline{\mathcal R}_\varepsilon(\widehat\mu, \widehat\Sigma, \ell)$
-- statement:
--   Let $\Xi \subseteq \mathbb R^m$, $\varepsilon \in \mathbb R$, $\widehat\mu \in \mathbb R^m$, let $\widehat\Sigma$ be an $m \times m$ matrix and $\ell : \mathbb R^m \to [-\infty, +\infty]$ a loss function. The **Gelbrich risk** is
--
--   $$\overline{\mathcal R}_\varepsilon(\widehat\mu, \widehat\Sigma, \ell) = \sup_{\mathbb Q \in \mathbb G_\varepsilon(\widehat\mu, \widehat\Sigma)} \mathcal R(\mathbb Q, \ell),$$
--
--   the worst-case risk of $\ell$ over the Gelbrich hull, a value in $[-\infty, +\infty]$.
--
--   It is the quantity that Theorem 22 shows to be an upper confidence bound on the true risk.
--
--   **Formalization Note** The supremum is taken in the extended reals; over an empty hull it is $-\infty$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, §2.3, eq. (18), p. 18

import Mathlib
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_risk
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_gelbrichHull

open MeasureTheory

namespace WassersteinDRO.GelbrichFiniteSample

/-- **The Gelbrich risk `R̄_ε(µ̂, Σ̂, ℓ)`.**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, §2.3, eq. (18), p. 18: "we define the Gelbrich risk as
R̄_ε(µ̂, Σ̂, ℓ) = sup_{Q ∈ G_ε(µ̂, Σ̂)} R(Q, ℓ)".

`gelbrichRisk Ξ ε µ̂ Σ̂ ℓ` is the supremum of the risk `R(Q, ℓ) = E^Q[ℓ(ξ)]` over all `Q` in the
Gelbrich hull `G_ε(µ̂, Σ̂)`, a value in `[−∞, +∞]`.

**Formalization Note.** The supremum is taken in the complete lattice `EReal`, so it always exists;
over an empty hull it is `−∞` (`⊥`). The risk uses the paper's expectation convention (`risk`). -/
noncomputable def gelbrichRisk {m : ℕ} (Ξ : Set (EuclideanSpace ℝ (Fin m))) (ε : ℝ)
    (μh : EuclideanSpace ℝ (Fin m)) (Sigh : Matrix (Fin m) (Fin m) ℝ)
    (ℓ : EuclideanSpace ℝ (Fin m) → EReal) : EReal :=
  ⨆ Q ∈ gelbrichHull Ξ ε μh Sigh, risk Q ℓ

end WassersteinDRO.GelbrichFiniteSample


