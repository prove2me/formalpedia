-- Prove2me | Definitions.Def_MSetBandit_phi
-- name    : MSetBandit_phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:40:39.885651+00:00
-- url     : https://prove2.me/theorems/db8b164e-3d54-4e14-8133-95402541561c
-- title:
--   The affine majorant $\phi_p$ of the leverage score
-- statement:
--   For $p\in\Delta(\mathcal X)$ with marginal vector $\mu=\mu(p)$ and an action $x\in\mathcal X$,
--   $$
--   \phi_p(x)=1+\sum_{i=1}^d\frac{(x_i-\mu_i)^2}{\mu_i(1-\mu_i)} .
--   $$
--   For weighted $m$-set distributions in $\mathcal P_\lambda$ it upper-bounds the leverage score $x^\top M(p)^{-1}x$ and is affine on $\mathcal X$ (Lemma 1).
--
--   **Formalization Note** Real division; for weighted $m$-set distributions every $\mu_i$ lies in $(0,1)$, so no denominator vanishes where the paper uses $\phi_p$.
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Lemma 1, p.11 (and Eq. (7), p.5)

import Mathlib
import Definitions.Def_MSetBandit_marg

namespace MSetBandit

/-- **The affine majorant `ϕ_p` of the leverage score.** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Lemma 1, p.11 (and (7), p.5):
`ϕ_p(x) := 1 + Σ_{i=1}^d (x_i − µ_i)² / (µ_i(1 − µ_i))`, `µ = µ(p)`.

**Formalization Note.** For weighted m-set distributions every `µ_i` lies in `(0, 1)`, so no
denominator vanishes where the paper uses `ϕ_p`. -/
noncomputable def phi {d m : ℕ} (p : Action d m → ℝ) (x : Action d m) : ℝ :=
  1 + ∑ i, (ind x i - marg p i) ^ 2 / (marg p i * (1 - marg p i))

end MSetBandit


