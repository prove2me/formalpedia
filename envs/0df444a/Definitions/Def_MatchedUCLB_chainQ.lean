-- Prove2me | Definitions.Def_MatchedUCLB_chainQ
-- name    : MatchedUCLB_chainQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:36.400162+00:00
-- url     : https://prove2.me/theorems/f6a573cf-b444-4b59-846e-39e00f2e9165
-- title:
--   The chain $Q_j$ in ambient form
-- statement:
--   For a center $c$, a starting direction $v$ and chain directions $u_1,\dots,u_m$, write $t(x)=\langle v,x-c\rangle$ and $x_i(x)=\langle u_i,x-c\rangle$. The **chain** of the phase is
--
--   $$
--   Q(x)=\frac{\lambda}{q}\Bigl(\Bigl|\frac{t(x)}{\sqrt m}-x_1(x)\Bigr|^{q}+\sum_{i=1}^{m-1}|x_i(x)-x_{i+1}(x)|^{q}+|x_m(x)|^{q}\Bigr),
--   $$
--
--   the power chain (4.9) evaluated at the local coordinates $P_{E_j}(x-c_j)$. When $m=1$ the middle sum is empty. Because $q>p$, at a point whose last nonzero chain coordinate is $x_b$ the derivatives of $Q$ through order $p$ involve only $v,u_1,\dots,u_{b+1}$.
--
--   **Formalization Note** The chain directions are indexed from $0$, so $x_1,\dots,x_m$ are the $0$-based coordinates $0,\dots,m-1$. All statements take $m\ge1$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Eq. (4.9), p.7; Definition E.8, p.89

import Mathlib

namespace MatchedUCLB

/-- **The chain `Q_j`, ambient form.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Eq. (4.9), p.7:
"`Q_j(w) = (λ/q)(|t/√m − x_1|^q + ∑_{i=1}^{m−1} |x_i − x_{i+1}|^q + |x_m|^q)`", with
`t = ⟨v_j, w⟩`, `x_i = ⟨u_{j,i}, w⟩`; Definition E.8, p.89: the ambient function uses the local
coordinates `t_j(x) = ⟨v_j, x − c_j⟩`, `x_{j,i}(x) = ⟨u_{j,i}, x − c_j⟩`. "When `m = 1`, the sum over
`i` is empty."

**Formalization Note.** `chainQ q lam c v u x` is `Q_j(P_{E_j}(x − c_j))`. The coordinates are
indexed from `0`: `xc i = ⟨u i, x − c⟩` for `i < m` (the paper's `x_{i+1}`), so the residuals are
`t/√m − xc 0`, `xc i − xc (i+1)` for `i < m − 1`, and `xc (m − 1)`. All mission statements take
`m ≥ 1`. Powers of absolute values are `Real.rpow`. -/
noncomputable def chainQ (q lam : ℝ) {d m : ℕ} (c v : EuclideanSpace ℝ (Fin d)) (u : Fin m → EuclideanSpace ℝ (Fin d)) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  let xc : ℕ → ℝ := fun i => if hi : i < m then inner ℝ (u ⟨i, hi⟩) (x - c) else 0
  lam / q * (|inner ℝ v (x - c) / Real.sqrt m - xc 0| ^ q +
    ∑ i ∈ Finset.range (m - 1), |xc i - xc (i + 1)| ^ q + |xc (m - 1)| ^ q)

end MatchedUCLB


