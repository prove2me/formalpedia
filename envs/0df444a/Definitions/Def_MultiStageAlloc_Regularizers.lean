-- Prove2me | Definitions.Def_MultiStageAlloc_Regularizers
-- name    : MultiStageAlloc_Regularizers
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:29:53.121219+00:00
-- url     : https://prove2.me/theorems/aa6f9e3f-9c3a-4bd6-bda1-c5687f05794d
-- title:
--   The polynomials $f_k$, the regularizers $F_k$, the ratio $\Gamma(K)$, and the extension $\tilde F_k$
-- statement:
--   For stages $k<K$, the polynomial regularizer slope is
--   $$
--   f_k(x)=\Bigl(1-\frac{1-x}{K-k}\Bigr)^{K-k},
--   $$
--   and for the last stage $f_K(x)=\mathbb I\{x=1\}$. The regularizer is $F_k(x)=\int_0^x f_k(y)\,dy$, so that $F_K=0$. The competitive ratio is
--   $$
--   \Gamma(K)=1-\Bigl(1-\frac1K\Bigr)^K .
--   $$
--   These are the objects of Proposition 1 and Algorithm 1.
--
--   The extension $\tilde F_k(t)=\int_0^t \mathrm{slope}_k(s)\,ds$ integrates $\mathrm{slope}_k(s)=f_k(\min(1,\max(0,s)))$ for $k<K$ and $\mathrm{slope}_K=0$. It is a $C^1$ convex function on all of $\mathbb R$ that agrees with $F_k$ on $[0,1]$.
--
--   **Formalization Note** The extension is what gives the unconstrained $\max_x$ in the Lagrangian of Proposition 3 a meaning, because the page takes $x$ with no sign constraint while $F_k$ lives on $[0,1]$. The polynomial itself is not convex off $[0,1]$.
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, Proposition 1, pp.14–15; Algorithm 1, p.18; Theorem 1, p.18; Definition 2, p.39

import Mathlib

namespace MultiStageAlloc

/-- **The polynomial `f_k`.** Feng & Niazadeh, arXiv:2211.16581v1, Proposition 1(i), pp.14–15:
`f_k(x) = (1 - (1 - x)/(K - k))^(K - k)` for `k < K`, and `f_K(x) = 𝕀{x = 1}`.

**Formalization Note.** `K - k` is `ℕ` subtraction, used only under `k < K`. At `k ≥ K` the closed
form would read `(…/0)^0 = 1`, which is why the definition branches: the last stage is the printed
indicator. -/
noncomputable def regPoly (K k : ℕ) (x : ℝ) : ℝ :=
  if k < K then (1 - (1 - x) / ((K - k : ℕ) : ℝ)) ^ (K - k) else if x = 1 then 1 else 0

/-- **The regularizer `F_k(x) = ∫₀ˣ f_k(y) dy`.** Feng & Niazadeh, arXiv:2211.16581v1,
Proposition 1(ii), p.14, and Algorithm 1, p.18. At `k = K` the integrand is an indicator of one
point, so `F_K = 0` ("note that `F_K(x) = 0` for all `x ∈ [0, 1]`", p.21). -/
noncomputable def regF (K k : ℕ) (x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..x, regPoly K k y

/-- **The competitive ratio `Γ(K) = 1 - (1 - 1/K)^K`.** Feng & Niazadeh, arXiv:2211.16581v1,
Theorem 1, p.18. `Γ(1) = 1`, `Γ(2) = 3/4`, `Γ(3) = 19/27`. Used only for `K ≥ 1`. -/
noncomputable def gammaK (K : ℕ) : ℝ := 1 - (1 - 1 / (K : ℝ)) ^ K

/-- **The slope of the extended regularizer.** It is `f_k` clamped to `[0, 1]` for `k < K`, and `0`
at `k = K`.

**Formalization Note.** This supports the reading of Proposition 3 (arXiv:2211.16581v1, p.39), whose
Lagrangian takes `x` with no sign constraint while `F_k` lives on `[0, 1]`. Extending `F_k` by its
polynomial off `[0, 1]` would break concavity. -/
noncomputable def slope (K k : ℕ) (s : ℝ) : ℝ :=
  if k < K then regPoly K k (max 0 (min 1 s)) else 0

/-- **The `C¹` convex extension `F̃_k(t) = ∫₀ᵗ slope`** of the regularizer to all of `ℝ`. It equals
`F_k` on `[0, 1]` for every `k ≤ K` (at `k = K` both vanish). -/
noncomputable def regFext (K k : ℕ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, slope K k s

end MultiStageAlloc


