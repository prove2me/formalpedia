-- Prove2me | Definitions.Def_MaskingHardness_lossObjective
-- name    : MaskingHardness_lossObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:50:15.478317+00:00
-- url     : https://prove2.me/theorems/d525b781-bd09-485f-9d42-93ed7ac4cf77
-- title:
--   The regularized loss $\mathbb E[g(y,\pi(c_\lambda(x)))]+\varepsilon\|\lambda\|_1$
-- statement:
--   For a distribution $\mathcal D$ on $\mathcal X\times[k]$, a finite class $\mathcal C=\{c_i\}$, a loss $g:[k]\times\mathbb R^k\to\mathbb R$, $\varepsilon\ge0$ and coefficients $\lambda\in\mathbb R^{\mathcal C}$, the **regularized loss** is
--
--   $$
--   L(\lambda)=\mathbb E_{(x,y)\sim\mathcal D}\bigl[g\bigl(y,\pi(c_\lambda(x))\bigr)\bigr]+\varepsilon\|\lambda\|_1,\qquad \|\lambda\|_1=\sum_i|\lambda_i| .
--   $$
--
--   Its infimum over $\lambda$ is the left-hand side of the main theorem: the least loss of a centered predictor in $\mathrm{span}(\mathcal C)$, with an $\ell_1$ penalty weighted by $\varepsilon$.
--
--   **Formalization Note** $g$ is real-valued, as in Theorem 1.9; the expectation is the weighted finite sum; $\|\lambda\|_1$ is written out as $\sum_i|\lambda_i|$ (Mathlib's norm on `ι → ℝ` is the sup norm).
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Theorem 1.9, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_MaskingHardness_centered
import Definitions.Def_MaskingHardness_combo

namespace MaskingHardness

/-- **The `ℓ₁`-regularized loss of `c_λ`** (Gopalan–Prabhakaran–Tankala, *Universal Hardness From
Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Theorem 1.9, printed
p.6 = PDF p.8): the objective of the left-hand side,
`E_D[g(y, π(c_λ(x)))] + ε ‖λ‖₁`.

**Formalization Note** `g` is real-valued, as in Theorem 1.9; the expectation is the weighted
finite sum over `(x, y) ∈ X × [k]`; `‖λ‖₁ = ∑ᵢ |λᵢ|` (not Mathlib's sup norm on `ι → ℝ`). -/
noncomputable def lossObjective {X ι : Type*} [Fintype X] [Fintype ι] {k : ℕ} (D : X → Fin k → ℝ)
    (c : ι → X → Fin k → ℝ) (g : Fin k → (Fin k → ℝ) → ℝ) (ε : ℝ) (lam : ι → ℝ) : ℝ :=
  ∑ x, ∑ y, D x y * g y (centered (combo c lam x)) + ε * ∑ i, |lam i|

end MaskingHardness


