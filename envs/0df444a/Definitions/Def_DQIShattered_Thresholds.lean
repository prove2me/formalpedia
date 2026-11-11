-- Prove2me | Definitions.Def_DQIShattered_Thresholds
-- name    : DQIShattered_Thresholds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:27:44.08072+00:00
-- url     : https://prove2.me/theorems/df6a3fda-2d85-472b-aca2-49712364fced
-- title:
--   $\Phi_{d,k}$, $K_*(k)$, $\gamma_{\mathrm{USD}}(k,D)$, $\gamma(\beta)$ and the erasure rate $\hat e$
-- statement:
--   This file defines the threshold quantities of Theorem 2.7.
--
--   1. The variational function (2.10): $\Phi_{d,k}(x)=e^{-dx^{k-1}}+dx^{k-1}-\frac{d(k-1)}{k}x^k-\frac dk$.
--   2. The threshold $K_*(k)=\sup\{d>0:\max_{x\in[0,1]}\Phi_{d,k}(x)=1-\frac dk\}$ (2.10).
--   3. The USD threshold (2.9): $\gamma_{\mathrm{USD}}(k,D)=\frac12-\frac12\sqrt{1-(K_*(k)/D)^2}$.
--   4. The error rate matched to an inverse temperature, (3.10): $\gamma(\beta)=\frac12-\frac12\operatorname{sech}\beta$. Equivalently $\beta=\operatorname{sech}^{-1}(1-2\gamma)$, as in (2.6).
--   5. The USD erasure probability (3.21): $\hat e(\gamma)=2\sqrt{\gamma(1-\gamma)}$.
--
--   $K_*(k)$ is the full-rank threshold of random sparse $\mathbb F_2$ matrices (Theorem 3.2). The other quantities convert it into an error rate and an inverse temperature.
--
--   **Formalization Note** For $k\ge2$, $\Phi_{d,k}(0)=1-d/k$, so "$\max_{[0,1]}\Phi_{d,k}=1-d/k$" is written as "$\Phi_{d,k}\le 1-d/k$ on $[0,1]$". $K_*$ is the real supremum of that set. A verification file proves $2/3\le K_*(k)<k$ for $k\ge3$, so the set is nonempty and bounded and the supremum is a genuine one. Mathlib has no $\operatorname{sech}^{-1}$: the map $\beta\mapsto\gamma(\beta)$ is a bijection from $[0,\infty)$ onto $[0,1/2)$.
-- source:
--   Zhou, Shutty, Sellke, Jordan, Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry, arXiv:2609.40345 (held version sha256 0c7f6fdf…), Theorem 2.7, p.7, eqs. (2.9)–(2.10); (3.10), p.11; (3.21), p.14

import Mathlib

namespace DQIShattered

/-- **The variational function** `Φ_{d,k}(x) = e^{−d x^{k−1}} + d x^{k−1} − (d(k−1)/k) x^k − d/k` of (2.10)
(Zhou, Shutty, Sellke, Jordan, arXiv:2609.40345, held version sha256 0c7f6fdf…, Theorem 2.7, p.7). -/
noncomputable def Phi (d : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-d * x ^ (k - 1)) + d * x ^ (k - 1) - d * ((k : ℝ) - 1) / k * x ^ k - d / k

/-- **The full-rank threshold** `K_*(k) := sup{d > 0 : max_{x∈[0,1]} Φ_{d,k}(x) = 1 − d/k}` of (2.10), p.7.

**Formalization Note** `Φ_{d,k}(0) = 1 − d/k` for `k ≥ 2`, so "`max_{[0,1]} Φ_{d,k} = 1 − d/k`" is
"`Φ_{d,k}(x) ≤ 1 − d/k` for every `x ∈ [0,1]`", which is the condition written here. `sSup` is the real
supremum; the verification file shows that for `k ≥ 3` the set is nonempty and bounded (`0 < K_*(k) < k`), so
`sSup` is the true supremum and not Lean's junk value. -/
noncomputable def Kstar (k : ℕ) : ℝ :=
  sSup {d : ℝ | 0 < d ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1, Phi d k x ≤ 1 - d / k}

/-- **The USD-decodable error rate** `γ_USD(k, D) = 1/2 − (1/2)√(1 − (K_*(k)/D)²)` of (2.9), p.7. -/
noncomputable def gammaUSD (k : ℕ) (D : ℝ) : ℝ :=
  1 / 2 - 1 / 2 * Real.sqrt (1 - (Kstar k / D) ^ 2)

/-- **The error rate matched to an inverse temperature**, `γ = 1/2 − (1/2) sech β` of (3.10), p.11,
equivalently `β = sech⁻¹(1 − 2γ)` of (2.6), p.5, for `β ≥ 0`.

**Formalization Note** `sech β = 1 / cosh β`; Mathlib has no `sech⁻¹`, and the paper's `β = sech⁻¹(1 − 2γ)`
with `γ ∈ [0, 1/2)` is exactly `γ = gammaOf β` with `β ∈ [0, ∞)` (a bijection). -/
noncomputable def gammaOf (β : ℝ) : ℝ := 1 / 2 - 1 / (2 * Real.cosh β)

/-- **The USD erasure probability** `ê = 2√(γ(1−γ))` of (3.21), p.14. -/
noncomputable def erasureRate (γ : ℝ) : ℝ := 2 * Real.sqrt (γ * (1 - γ))

end DQIShattered


