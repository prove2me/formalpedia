-- Prove2me | Definitions.Def_AutoregLTF_Supplement_logisticGen
-- name    : AutoregLTF_Supplement_logisticGen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:55:41.73178+00:00
-- url     : https://prove2.me/theorems/7f7dbfc3-5573-4c30-833c-5dff4779112e
-- title:
--   The logistic autoregressive generator (2), its final probability $q^{(T)}_{w,b}$ and the majority class $\mathcal H_{d,T}$ (3)
-- statement:
--   Let $\sigma(u)=\frac{1}{1+e^{-u}}$ be the sigmoid (logistic) function. Fix integers $d\ge1$, $T\ge0$, weights $w=(w_1,\dots,w_d)\in\mathbb R^d$ and a bias $b\in\mathbb R$. Given a prompt $x=(x_{1-d},\dots,x_0)\in\{0,1\}^d$, initialize $Z_t=x_t$ for $1-d\le t\le0$ and draw the next tokens $Z_1,\dots,Z_T\in\{0,1\}$ by
--
--   $$\Pr(Z_t=1\mid Z_{1-d},\dots,Z_{t-1})=\sigma\Big(b+\sum_{\ell=1}^{d}w_\ell Z_{t-\ell}\Big)\qquad(1\le t\le T).$$
--
--   The **final probability** is $q^{(T)}_{w,b}(x)=\Pr(Z_T=1\mid x)$, and the **majority class** is
--
--   $$\mathcal H_{d,T}=\Big\{x\mapsto\mathbf 1\big\{q^{(T)}_{w,b}(x)>1/2\big\}:\ w\in\mathbb R^d,\ b\in\mathbb R\Big\}.$$
--
--   Concretely, a realization $z=(z_1,\dots,z_T)\in\{0,1\}^T$ of the generated tokens has probability $\prod_{t=1}^{T}\big(\sigma(s_t)\text{ if }z_t=1,\ 1-\sigma(s_t)\text{ if }z_t=0\big)$, where $s_t=b+\sum_{\ell}w_\ell z_{t-\ell}$ is computed on the concatenation of the prompt and $z$, and $q^{(T)}_{w,b}(x)$ is the total probability of the realizations with $z_T=1$.
--
--   $\mathcal H_{d,T}$ collects the deterministic majority predictions of the stochastic logistic generators; it is the class whose VC dimension Theorem 2 bounds.
--
--   **Formalization Note** The prompt and weight orientation are those of the published `AutoregLTF.ltf`: a prompt is `Fin d → Bool` with index $k$ holding $x_{1-d+k}$, and `w ⟨ℓ, _⟩` is $w_{\ell+1}$, multiplying the token $\ell+1$ steps back. The final probability is the explicit finite sum over $z\in\{0,1\}^T$ of the chain's joint law (no measure theory); for $T=0$ it is the last prompt bit $x_0$. Weights and bias are real and the class threshold is strict.
-- source:
--   Doron-Arad, Mehalel, Mossel, On the VC Dimension of Autoregressive Linear Threshold Functions, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), §1, "Implication for stochastic autoregressive learning", sigmoid σ, display (2), q^{(T)}_{w,b} and display (3), p.2 (PDF p.2)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_PACSampleComplexity

namespace AutoregLTF.Supplement

/-!
# The logistic autoregressive generator (2), its final probability `q^{(T)}_{w,b}`, and the
# majority class `H_{d,T}` (3)

I. Doron-Arad, I. Mehalel, E. Mossel, *On the VC Dimension of Autoregressive Linear Threshold
Functions*, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), §1, "Implication for
stochastic autoregressive learning", displays (2) and (3), p.2.

For `w ∈ ℝ^d`, `b ∈ ℝ` and a prompt `x = (x_{1−d}, …, x_0) ∈ {0,1}^d`, set `Z_t = x_t` for
`1 − d ≤ t ≤ 0` and draw `Z_t ∈ {0,1}` with
`Pr(Z_t = 1 | Z_{1−d}, …, Z_{t−1}) = σ(b + ∑_{ℓ=1}^d w_ℓ Z_{t−ℓ})` for `1 ≤ t ≤ T`, where
`σ(u) = 1/(1 + e^{−u})`. Then `q^{(T)}_{w,b}(x) = Pr(Z_T = 1 | x)` and
`H_{d,T} = {x ↦ 1{q^{(T)}_{w,b}(x) > 1/2} : w ∈ ℝ^d, b ∈ ℝ}`.

**Formalization Note.**
* The prompt and weight orientation are those of the published `AutoregLTF.ltf`: a prompt is
  `Fin d → Bool` with `x ⟨k, _⟩ = x_{1−d+k}` (index `d − 1` is the most recent bit `x_0`), and
  `w ⟨ℓ, _⟩ = w_{ℓ+1}` multiplies `Z_{t−ℓ−1}` (so `w_1` multiplies the most recent token).
* A realization of the generated tokens `Z_1, …, Z_T` is `z : Fin T → Bool` with `z ⟨k, _⟩ = Z_{k+1}`.
  The whole sequence `Z_{1−d}, …, Z_T` is `tok x z n = Z_{n+1−d}` for `n < d + T`.
* `q^{(T)}_{w,b}(x)` is defined as an explicit finite sum: the probability of a realization `z` under
  the chain (2) is the product over `1 ≤ t ≤ T` of the conditional probabilities
  `σ(s_t)` (if `Z_t = 1`) or `1 − σ(s_t)` (if `Z_t = 0`), `s_t = b + ∑_ℓ w_ℓ Z_{t−ℓ}`; this is the
  joint law of the chain (2) given the prompt, and `q` sums it over the realizations with
  `Z_T = 1`. For `T = 0` the sum reduces to the prompt bit `x_0`, which is `Pr(Z_0 = 1 | x)`.
* Weights and bias are real, there is a bias, and the class threshold is strict (`q > 1/2`).
-/

/-- The sigmoid (logistic) function `σ(u) = 1/(1 + e^{−u})`, p.2. -/
noncomputable def logistic (u : ℝ) : ℝ := 1 / (1 + Real.exp (-u))

/-- The token sequence `Z_{1−d}, …, Z_T` formed by the prompt `x` followed by the generated tokens
`z`: `tok x z n = Z_{n+1−d}` for `n < d + T` (`false` beyond, never used). -/
def tok {d T : ℕ} (x : Fin d → Bool) (z : Fin T → Bool) (n : ℕ) : Bool :=
  if h : n < d then x ⟨n, h⟩
  else if h' : n - d < T then z ⟨n - d, h'⟩ else false

/-- The affine score `s_t = b + ∑_{ℓ=1}^d w_ℓ Z_{t−ℓ}` of step `t = k + 1` of (2), for
`k : Fin T`. `Z_{t−ℓ}` with `ℓ = j + 1` (`j : Fin d`) is `tok x z (k + d − 1 − j)`. -/
noncomputable def score {d T : ℕ} (w : Fin d → ℝ) (b : ℝ) (x : Fin d → Bool) (z : Fin T → Bool)
    (k : Fin T) : ℝ :=
  b + ∑ j : Fin d, w j * ((tok x z (k.val + d - 1 - j.val)).toNat : ℝ)

/-- The probability, under the chain (2) started at the prompt `x`, that the generated tokens are
`Z_1, …, Z_T = z`: `∏_{t=1}^T Pr(Z_t = z_t | Z_{1−d}, …, Z_{t−1})`. -/
noncomputable def pathProb {d T : ℕ} (w : Fin d → ℝ) (b : ℝ) (x : Fin d → Bool)
    (z : Fin T → Bool) : ℝ :=
  ∏ k : Fin T, (if z k then logistic (score w b x z k) else 1 - logistic (score w b x z k))

/-- The final probability `q^{(T)}_{w,b}(x) = Pr(Z_T = 1 | x)` of (2), p.2: the total probability of
the realizations whose last token `Z_T = tok x z (T + d − 1)` is `1`. -/
noncomputable def qFinal (d T : ℕ) (w : Fin d → ℝ) (b : ℝ) (x : Fin d → Bool) : ℝ :=
  ∑ z : Fin T → Bool, pathProb w b x z * ((tok x z (T + d - 1)).toNat : ℝ)

/-- The majority class `H_{d,T} = {x ↦ 1{q^{(T)}_{w,b}(x) > 1/2} : w ∈ ℝ^d, b ∈ ℝ}` of (3), p.2. -/
def majCls (d T : ℕ) : Set ((Fin d → Bool) → Bool) :=
  {f | ∃ (w : Fin d → ℝ) (b : ℝ), f = fun x => decide (1 / 2 < qFinal d T w b x)}

end AutoregLTF.Supplement


