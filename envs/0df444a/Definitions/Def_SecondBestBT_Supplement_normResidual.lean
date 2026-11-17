-- Prove2me | Definitions.Def_SecondBestBT_Supplement_normResidual
-- name    : SecondBestBT_Supplement_normResidual
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:36:16.586461+00:00
-- url     : https://prove2.me/theorems/b95d2ea7-927b-449f-9e19-0f1d7a094cbf
-- title:
--   Normalized residual $\hat H_{\ell,b_0}(b;x)$, Eq. (13)
-- statement:
--   Fix $\alpha,\beta$, ratios $r_i\in[0,\infty]$ indexed by seller value $i$, a reference pair $(\ell,b_0)$ (threshold and buyer value of the most recent clear step) and an allocation $x$. The **normalized residual** is
--   $$
--   \begin{aligned}
--   \hat H_{\ell,b_0}(b;x):={}&\Big[(b-b_0)(1-\beta)-\alpha\sum_{\ell\le t<b}x(t,b)+\alpha x(\ell,b_0)\Big]\frac{r_\ell}{1+r_\ell}\\
--   &+\Big[(1+\alpha)\big((b-\ell)x(\ell,b)-(b_0-\ell)x(\ell,b_0)\big)-(b-b_0)\beta-\alpha\sum_{\ell<s'<b}x(s',b)-\alpha\sum_{b_0\le b'<b}x(\ell,b')\Big]\frac1{1+r_\ell}\\
--   &+\sum_{\ell<s<b_0}\Big[(1+\alpha)(b-s)x(s,b)-(b-b_0)\beta-\alpha\sum_{s<s'<b}x(s',b)-\alpha\sum_{b_0\le b'<b}x(s,b')\Big]\prod_{\ell<i<s}\Big(1+\frac1{r_i}\Big)\frac1{r_s}\\
--   &+\sum_{b_0\le s<b}\Big[(b-s)\big((1+\alpha)x(s,b)-\beta\big)-\alpha\sum_{s<s'<b}x(s',b)-\alpha\sum_{b_0\le b'<b}x(s,b')\Big]\prod_{\ell<i<s}\Big(1+\frac1{r_i}\Big)\frac1{r_s}.
--   \end{aligned}
--   $$
--   An empty product is $1$; at $r_i=\infty$ the factors $r_i/(1+r_i)$, $1/(1+r_i)$ and $1/r_i$ are $1$, $0$ and $0$.
--
--   When the ratios are those of a seller prior, $H(b;x)-H(b_0;x)=F_S(\ell)\,\hat H_{\ell,b_0}(b;x)$, so $\hat H$ replaces the buyer-wise residual $H$ of Eq. (4) after a clear step.
--
--   **Formalization Note** The factor $1/r_i$ is read only at seller indices above $\ell\ge0$, where admissible ratios are positive.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Appendix C, Eq. (13), p.41 (and Section 5.1, p.17)

import Mathlib

open scoped ENNReal

namespace SecondBestBT.Supplement

/-- The **normalized residual** `Ĥ_{ℓ,b0}(b; x)` of Eq. (13) (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256 17184930…, Appendix C, Eq. (13),
p.41; introduced in Section 5.1, p.17), with ratios `r_i` indexed by seller value `i`:

`Ĥ_{ℓ,b0}(b; x) := [(b − b0)(1 − β) − α ∑_{ℓ≤t<b} x(t, b) + α x(ℓ, b0)] · r_ℓ/(1 + r_ℓ)`
`+ [(1 + α)((b − ℓ) x(ℓ, b) − (b0 − ℓ) x(ℓ, b0)) − (b − b0)β − α ∑_{ℓ<s'<b} x(s', b)
   − α ∑_{b0≤b'<b} x(ℓ, b')] · 1/(1 + r_ℓ)`
`+ ∑_{ℓ<s<b0} [(1 + α)(b − s) x(s, b) − (b − b0)β − α ∑_{s<s'<b} x(s', b)
   − α ∑_{b0≤b'<b} x(s, b')] ∏_{ℓ<i<s} (1 + 1/r_i) · 1/r_s`
`+ ∑_{b0≤s<b} [(b − s)((1 + α) x(s, b) − β) − α ∑_{s<s'<b} x(s', b)
   − α ∑_{b0≤b'<b} x(s, b')] ∏_{ℓ<i<s} (1 + 1/r_i) · 1/r_s`.

An empty product is `1`. At `r_i = ∞`, `r_i/(1 + r_i) = 1`, `1/(1 + r_i) = 0` and `1/r_i = 0`
(p.42).

**Formalization Note** Ratios are a function `r : ℕ → ℝ≥0∞` of the seller index; each bound of
each sum is copied from the page (`Finset.Ico` for `≤ · <`, `Finset.Ioo` for `< · <`). The value
`1/r_i` is read at seller indices `i > ℓ ≥ 0` only, where an admissible ratio vector has
`r_i > 0`; at `r_i = 0` the term would be Lean's `0⁻¹ = 0`, a case the paper never reaches. -/
noncomputable def normResidual (α β : ℝ) (r : ℕ → ℝ≥0∞) (ℓ b0 : ℕ) (x : ℕ → ℕ → ℝ) (b : ℕ) :
    ℝ :=
  let inv : ℝ≥0∞ → ℝ := fun v => if v = ⊤ then 0 else (v.toReal)⁻¹
  let frac : ℝ≥0∞ → ℝ := fun v => if v = ⊤ then 1 else v.toReal / (1 + v.toReal)
  let invOne : ℝ≥0∞ → ℝ := fun v => if v = ⊤ then 0 else 1 / (1 + v.toReal)
  let w : ℕ → ℝ := fun s => (∏ i ∈ Finset.Ioo ℓ s, (1 + inv (r i))) * inv (r s)
  (((b : ℝ) - b0) * (1 - β) - α * ∑ t ∈ Finset.Ico ℓ b, x t b + α * x ℓ b0) * frac (r ℓ) +
  ((1 + α) * (((b : ℝ) - ℓ) * x ℓ b - ((b0 : ℝ) - ℓ) * x ℓ b0) - ((b : ℝ) - b0) * β -
      α * ∑ s' ∈ Finset.Ioo ℓ b, x s' b - α * ∑ b' ∈ Finset.Ico b0 b, x ℓ b') * invOne (r ℓ) +
  ∑ s ∈ Finset.Ioo ℓ b0,
    ((1 + α) * ((b : ℝ) - s) * x s b - ((b : ℝ) - b0) * β -
      α * ∑ s' ∈ Finset.Ioo s b, x s' b - α * ∑ b' ∈ Finset.Ico b0 b, x s b') * w s +
  ∑ s ∈ Finset.Ico b0 b,
    (((b : ℝ) - s) * ((1 + α) * x s b - β) -
      α * ∑ s' ∈ Finset.Ioo s b, x s' b - α * ∑ b' ∈ Finset.Ico b0 b, x s b') * w s

end SecondBestBT.Supplement


