-- Prove2me | Definitions.Def_TalagrandThinning_liftL
-- name    : TalagrandThinning_liftL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:43:39.654195+00:00
-- url     : https://prove2.me/theorems/3854815b-0063-48e9-9e96-20c1711b2060
-- title:
--   The signed kernel $h$, its products $k_j$ and the lifted function $L_jf$
-- statement:
--   Let $t$ be the retention probability and $p$ the target density, $0<t,p<1$, and set
--
--   $$\beta=\sqrt{\frac{t(1-p)}{p(1-t)}}.$$
--
--   The **one-coordinate kernel** is $h(x,w)=1+\beta\,\phi_t(x)\,\phi_p(w)$ for $x,w\in\{0,1\}$. For a deterministic set $j\subseteq[N]$,
--
--   $$k_j(x,w)=\prod_{i\in j}h(x_i,w_i),\qquad (L_jf)(x)=\mathbb E_{W\sim\mu_p}\big[k_j(x,W)f(W)\big].$$
--
--   Coordinates outside $j$ contribute the factor $1$, so $k_\emptyset=1$ and $L_\emptyset f$ is the constant $\mathbb E_{\mu_p}f$.
--
--   The kernel vanishes exactly when a thinned parent is not contained in the target, which drives the whole argument.
--
--   **Formalization Note** $h$, $k_j$ and $L_jf$ are real-valued: $h(0,1)<0$ when $p<t$ (Remark 2.3). The set $j$ is a cube point and "$i\in j$" is `j i = true`.
-- source:
--   Fang & Wang, A Note on a Result of Chen Li: the Thinning Problem via the Kernel Method, arXiv:2609.18458 (held version dated Sep 12, 2026, sha256 68a0f38d…), §2, eq. (2.2), Lemma 2.1 eq. (2.3), eq. (2.6), p.3

import Mathlib
import Definitions.Def_TalagrandThinning_fourierCoeff

set_option autoImplicit false

namespace TalagrandThinning

/-- `β = √(t(1 − p)/(p(1 − t)))`, eq. (2.2)
(arXiv:2609.18458, held version dated Sep 12, 2026, sha256 68a0f38d…, §2, eq. (2.2), p.3). Here `t` is the retention probability and `p` the target density;
the paper's standing range is `0 < t, p < 1`. -/
noncomputable def beta (t p : ℝ) : ℝ :=
  Real.sqrt (t * (1 - p) / (p * (1 - t)))

/-- The one-coordinate kernel `h(x, w) = 1 + β ϕ_t(x) ϕ_p(w)`, eq. (2.3)
(arXiv:2609.18458, held version dated Sep 12, 2026, sha256 68a0f38d…, Lemma 2.1, eq. (2.3), p.3).

**Formalization Note** Real-valued: `h(0,1)` is negative when `p < t` (Remark 2.3, p.4). -/
noncomputable def kernelH (t p : ℝ) (x w : Bool) : ℝ :=
  1 + beta t p * phi t x * phi p w

/-- The product kernel `k_j(x, w) = ∏_{i∈j} h(x_i, w_i)` for a deterministic set `j ⊆ [N]`,
eq. (2.6) (arXiv:2609.18458, held version dated Sep 12, 2026, sha256 68a0f38d…, §2, eq. (2.6), p.3). Coordinates outside `j` contribute the factor `1`;
`k_∅ = 1`. Real-valued and possibly negative. -/
noncomputable def kernelK {N : ℕ} (t p : ℝ) (j x w : Cube N) : ℝ :=
  ∏ i ∈ Finset.univ.filter (fun i => j i = true), kernelH t p (x i) (w i)

/-- The lifted function `(L_j f)(x) = E_{W∼µ_p}[k_j(x, W) f(W)]`, eq. (2.6)
(arXiv:2609.18458, held version dated Sep 12, 2026, sha256 68a0f38d…, §2, eq. (2.6), p.3). `L_∅ f` is the constant `E_{µ_p} f`. -/
noncomputable def liftL {N : ℕ} (t p : ℝ) (j : Cube N) (f : Cube N → ℝ) (x : Cube N) : ℝ :=
  expect p (fun w => kernelK t p j x w * f w)

end TalagrandThinning


