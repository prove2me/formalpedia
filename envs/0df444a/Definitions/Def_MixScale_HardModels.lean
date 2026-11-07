-- Prove2me | Definitions.Def_MixScale_HardModels
-- name    : MixScale_HardModels
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:10:42.06562+00:00
-- url     : https://prove2.me/theorems/169d7afe-5cd1-4a43-bc67-b9a72012b997
-- title:
--   The two-point alternatives (84) and (108) and $\Psi_{q,\alpha}$
-- statement:
--   **The alternatives (84).** For an integer $m$ and $0\le j\le m$, the centers are $b_j=(j-m/2)\gamma$, and with $\pi_j=2^{-m}\binom mj$, $\sigma_j=(-1)^j$, $v_j^\pm=1\pm\sigma_jt$ and $Z_q(t)=\tfrac12\{(1+t)^{q/2}+(1-t)^{q/2}\}$ the weights are $w_j^\pm=\pi_j(v_j^\pm)^{q/2}/Z_q(t)$.
--
--   **The alternatives (108).** For $k_0=2^m$, $\ell_0=k_0-1$ and $\sigma_j=(-1)^{s_2(j)}$, where $s_2(j)$ is the binary digit sum of $j$, take $b_j=(j-\ell_0/2)\gamma$, $w_j^\pm=1/k_0$ and $v_j^\pm=1\pm\sigma_jt$.
--
--   Finally $\Psi_{q,\alpha}(\gamma)=\gamma^{E_{q,\alpha}}/\ell_q(\gamma)$ with $E_{q,\alpha}=2(q+\alpha)-\min(q,1)$. These are the pairs whose chi-square divergence drives the two lower bounds.
--
--   **Formalization Note** Components keep the paper's 0-based $j$ in `Fin (m+1)` and `Fin (2^m)`. A one-dimensional component has a center in $\mathbb R^1$ and a $1\times1$ scale matrix. A Boolean selects the sign.
-- source:
--   Wang–Zhang, Learning Mixtures with Unknown Scales: Sharp Dependence on Separation, STOC 2027 submission (sha256 5277f95e…), (84), p.40 (PDF p.42); (107)–(108), p.53 (PDF p.55); (72), p.35

import Mathlib
import Definitions.Def_MixScale_Profile
import Definitions.Def_MixScale_Model

namespace MixScale

/-!
# The two-point alternatives of the lower bounds: (84) and (108)

S. Wang and X. Zhang, *Learning Mixtures with Unknown Scales: Sharp Dependence on Separation*,
STOC 2027 submission manuscript (sha256 5277f95e…7c6c). (84), p.40 (PDF p.42); (107)–(108),
p.53 (PDF p.55); `Ψ_{q,α}` of (72), p.35 (PDF p.37).

(84): "`b_j = (j − m/2)γ`, `π_j = 2^{−m} binom(m, j)`, `σ_j = (−1)^j`, `0 ≤ j ≤ m`. For `0 < t ≤ 1/4`
define `v^±_j = 1 ± σ_jt`, `Z_q(t) = ½{(1 + t)^{q/2} + (1 − t)^{q/2}}`,
`w^±_j = π_j(v^±_j)^{q/2}/Z_q(t)`."

(108): "put `k₀ = 2^m`, `ℓ₀ = k₀ − 1`, and let `s₂(j)` be the number of ones in the binary expansion
of `j`. Set `σ_j = (−1)^{s₂(j)}`. […] `b_j = (j − ℓ₀/2)γ`, `w^±_j = 1/k₀`, `v^±_j = 1 ± σ_jt`,
`0 < t ≤ 1/4`."

(72): "`Ψ_{q,α}(γ) = γ^{E_{q,α}}/ℓ_q(γ)`".

**Formalization Note.** The components are `Fin (m + 1)` and `Fin (2^m)` with the paper's
0-based `j`. The Boolean `plus` selects `+` (true) or `−` (false). A one-dimensional component has
center `b_j e₀ ∈ ℝ¹` and `1 × 1` scale matrix `(v_j)`. `s₂(j)` is the digit sum of `j` in base `2`.
-/

/-- `Z_q(t) = ½((1 + t)^{q/2} + (1 − t)^{q/2})` (84). -/
noncomputable def Zq (q t : ℝ) : ℝ := ((1 + t) ^ (q / 2) + (1 - t) ^ (q / 2)) / 2

/-- The `±` alternative of (84) with `m + 1` components: centers `(j − m/2)γ`, scales
`1 ± (−1)^j t`, weights `2^{−m} binom(m, j) (v^±_j)^{q/2} / Z_q(t)`. -/
noncomputable def binomModel (q : ℝ) (m : ℕ) (γ t : ℝ) (plus : Bool) : Params 1 (m + 1) :=
  fun j =>
    let v : ℝ := 1 + (if plus then 1 else -1) * (-1 : ℝ) ^ (j : ℕ) * t
    (EuclideanSpace.single 0 ((((j : ℕ) : ℝ) - (m : ℝ) / 2) * γ),
      Matrix.of (fun _ _ => v),
      (2 : ℝ)⁻¹ ^ m * (m.choose j : ℝ) * v ^ (q / 2) / Zq q t)

/-- The Prouhet–Thue–Morse sign `σ_j = (−1)^{s₂(j)}`. -/
def ptmSign (j : ℕ) : ℝ := (-1) ^ (Nat.digits 2 j).sum

/-- The `±` alternative of (108) with `2^m` components: centers `(j − (2^m − 1)/2)γ`, scales
`1 ± σ_j t`, weights `1/2^m`. -/
noncomputable def ptmModel (m : ℕ) (γ t : ℝ) (plus : Bool) : Params 1 (2 ^ m) :=
  fun j =>
    let v : ℝ := 1 + (if plus then 1 else -1) * ptmSign j * t
    (EuclideanSpace.single 0 ((((j : ℕ) : ℝ) - ((2 : ℝ) ^ m - 1) / 2) * γ),
      Matrix.of (fun _ _ => v),
      1 / (2 : ℝ) ^ m)

/-- `Ψ_{q,α}(γ) = γ^{E_{q,α}}/ℓ_q(γ)` (72). -/
noncomputable def PsiQA (q α γ : ℝ) : ℝ := γ ^ Efree q α / ellq q γ

end MixScale


