-- Prove2me | Definitions.Def_AutoregLTF_ltf
-- name    : AutoregLTF_ltf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:40.53592+00:00
-- url     : https://prove2.me/theorems/25188ceb-9209-43a6-86d6-0a4d3fff0c15
-- title:
--   Autoregressive linear threshold functions $f^T_w$ and the class $\mathcal F_{d,T}$, recurrence (1)
-- statement:
--   Let $d,T\ge1$ be integers and $w=(w_1,\dots,w_d)\in\mathbb Q^d$. Given a prompt $x=(x_{1-d},\dots,x_0)\in\{0,1\}^d$, set $z_t=x_t$ for $1-d\le t\le 0$ and
--
--   $$z_t=\mathbf 1\Big\{\sum_{\ell=1}^{d}w_\ell\,z_{t-\ell}\ge1\Big\}\qquad(1\le t\le T).$$
--
--   The **autoregressive linear threshold function** of dimension $d$ with $T$ autoregressive steps is $f^T_w(x)=z_T$, and
--
--   $$\mathcal F_{d,T}=\{f^T_w:\ w\in\mathbb Q^d\}$$
--
--   is the class of all autoregressive LTFs with rational weights. The same threshold rule, with threshold $1$ and no bias term, reads the last $d$ bits at every step; $w_1$ multiplies the most recent bit.
--
--   This is the hypothesis class whose VC dimension the mission bounds.
--
--   **Formalization Note** Bits are `Bool`; a prompt is `Fin d → Bool` with index $k$ holding $x_{1-d+k}$ (index $d-1$ is the most recent bit $x_0$), and `w ⟨ℓ, _⟩` is $w_{\ell+1}$. The trajectory `traj w x n` is $z_{n+1-d}$, so $f^T_w(x)$ is `traj w x (T + d - 1)`.
-- source:
--   Doron-Arad, Mehalel, Mossel, On the VC Dimension of Autoregressive Linear Threshold Functions, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), §1, recurrence (1), p.1; the class F_{d,T}, p.2

import Mathlib

namespace AutoregLTF

/-!
# Autoregressive linear threshold functions, recurrence (1), and the class `F_{d,T}`

I. Doron-Arad, I. Mehalel, E. Mossel, *On the VC Dimension of Autoregressive Linear Threshold
Functions*, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), §1, recurrence (1),
p.1, and the class `F_{d,T}`, p.2.

For `w ∈ ℚ^d` and a prompt `x = (x_{1−d}, …, x_0) ∈ {0,1}^d`, set `z_t = x_t` for `1 − d ≤ t ≤ 0` and
`z_t = 1{∑_{ℓ=1}^d w_ℓ z_{t−ℓ} ≥ 1}` for `t ≥ 1`; `f^T_w(x) = z_T` and
`F_{d,T} = {f^T_w : w ∈ ℚ^d}`.

**Formalization Note.**
* Bits are `Bool` (`true` = 1); `{0,1}^d` is `Fin d → Bool`, with `x ⟨k, _⟩ = x_{1−d+k}`, so
  `x ⟨0, _⟩ = x_{1−d}` (the oldest bit) and `x ⟨d − 1, _⟩ = x_0` (the most recent bit).
* Weights are `w : Fin d → ℚ` with `w ⟨ℓ, _⟩ = w_{ℓ+1}`; `w_1` multiplies the most recent bit
  `z_{t−1}`. The threshold is the constant `1` and there is no bias term, as in (1).
* `traj w x n` is `z_{n+1−d}`: the trajectory is indexed from `0` instead of `1 − d`.
-/

/-- The trajectory of recurrence (1), p.1: `traj w x n = z_{n+1−d}`. For `n < d` it is the prompt
bit `x_{n+1−d}`; for `n ≥ d` (that is `t = n + 1 − d ≥ 1`) it is
`1{∑_{ℓ=1}^d w_ℓ z_{t−ℓ} ≥ 1}`, where `z_{t−ℓ}` is `traj w x (n − ℓ)`. -/
def traj {d : ℕ} (w : Fin d → ℚ) (x : Fin d → Bool) (n : ℕ) : Bool :=
  if h : n < d then x ⟨n, h⟩
  else decide (1 ≤ ∑ ℓ : Fin d, w ℓ * ((traj w x (n - 1 - ℓ.val)).toNat : ℚ))
termination_by n
decreasing_by
  have := ℓ.isLt
  omega

/-- The autoregressive LTF `f^T_w : {0,1}^d → {0,1}` of (1), p.2: `f^T_w(x) = z_T`, which is
`traj w x (T + d − 1)`. -/
def ltf (d T : ℕ) (w : Fin d → ℚ) (x : Fin d → Bool) : Bool :=
  traj w x (T + d - 1)

/-- The class `F_{d,T} = {f^T_w : w ∈ ℚ^d}` of autoregressive LTFs with rational weights, p.2. -/
def cls (d T : ℕ) : Set ((Fin d → Bool) → Bool) :=
  {f | ∃ w : Fin d → ℚ, f = ltf d T w}

end AutoregLTF


