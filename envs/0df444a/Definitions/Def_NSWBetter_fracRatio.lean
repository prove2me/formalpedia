-- Prove2me | Definitions.Def_NSWBetter_fracRatio
-- name    : NSWBetter_fracRatio
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:29.893915+00:00
-- url     : https://prove2.me/theorems/9133f75a-37d6-409b-8098-4e3393bb417d
-- title:
--   Threshold of Definition 4.7
-- statement:
--   For a set of goods $L$, the threshold $\dfrac{v_i(x_i)-\sum_{g\in L}x_{ig}v_i(g)}{1-\sum_{g\in L}x_{ig}}$ of Definition 4.7, where $v_i(x_i)=\sum_gx_{ig}v_i(g)$.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Definition 4.7, p.20

import Mathlib

namespace NSWBetter

/-- **The threshold of Definition 4.7.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Definition 4.7, p.20: `(vi(xi) − Σ_(g∈Li) xig vi(g)) / (1 − Σ_(g∈Li) xig)`, where `vi(xi) = Σ_g xig vi(g)`. -/
noncomputable def fracRatio {n m : ℕ} (v : Fin n → Fin m → ℝ) (x : Fin n → Fin m → ℝ) (i : Fin n)
    (L : Finset (Fin m)) : ℝ :=
  (∑ g, x i g * v i g - ∑ g ∈ L, x i g * v i g) / (1 - ∑ g ∈ L, x i g)

end NSWBetter


