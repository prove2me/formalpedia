-- Prove2me | Definitions.Def_NesterovRCD_Accelerated_ACDM
-- name    : NesterovRCD_Accelerated_ACDM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T15:13:12.156783+00:00
-- url     : https://prove2.me/theorems/7883c45c-1cb0-4a38-9ee8-e39c7d812de8
-- title:
--   Method ACDM$(x_0)$ (5.1): coefficients $a_k,b_k,\gamma_k,\alpha_k,\beta_k$, iterates $(x_k,v_k)$, $\phi_k$ and $\mathbb E\,r_k^2$
-- statement:
--   This file encodes the accelerated coordinate descent method ACDM$(x_0)$ of §5 (5.1). Fix the number of blocks $n\ge1$ and the convexity parameter $\sigma\ge0$ of $f$ in the norm $\|\cdot\|_1$.
--
--   1. **Coefficients.** $a_0=\frac1n$, $b_0=2$. Given $a_k,b_k$, $\gamma_k$ is the root $\gamma\ge\frac1n$ of
--   $$\gamma^2-\frac{\gamma}{n}=\Big(1-\frac{\gamma\sigma}{n}\Big)\frac{a_k^2}{b_k^2},$$
--   computed as the larger root of the quadratic $\gamma^2-c\gamma-a_k^2/b_k^2=0$ with $c=(1-\sigma a_k^2/b_k^2)/n$. Then
--   $$\alpha_k=\frac{n-\gamma_k\sigma}{\gamma_k(n^2-\sigma)},\qquad \beta_k=1-\frac1n\gamma_k\sigma,\qquad b_{k+1}=\frac{b_k}{\sqrt{\beta_k}},\qquad a_{k+1}=\gamma_kb_{k+1}.$$
--   The coefficients are deterministic: they do not depend on the random draws.
--   2. **Iterates.** $v_0=x_0$. Given $x_k,v_k$ and the draw $i_k\in\{1,\dots,n\}$,
--   $$y_k=\alpha_kv_k+(1-\alpha_k)x_k,\qquad x_{k+1}=T_{i_k}(y_k),\qquad v_{k+1}=\beta_kv_k+(1-\beta_k)y_k-\frac{\gamma_k}{L_{i_k}}U_{i_k}f'_{i_k}(y_k)^\#.$$
--   3. **Averages.** The draws $i_0,i_1,\dots$ are independent and uniform on $\{1,\dots,n\}$ (the random counter $\mathcal R_0$). $\phi_k=\mathbb E_{\xi_{k-1}}f(x_k)$ is the expectation over $\xi_{k-1}=(i_0,\dots,i_{k-1})$, and $\mathbb E_{\xi_{k-1}}r_k^2$ is the expectation of $r_k^2=\|v_k-x_*\|_1^2$ for a given point $x_*$.
--
--   The theorems of the mission are statements about these quantities.
--
--   **Formalization Note** `acdm f L sharp σ x0 k idx` is the pair $(x_k,v_k)$ produced by the draws `idx : Fin k → Fin n` (the draw $i_s$ is `idx s`, indices $0,\dots,n-1$). The coefficient functions are defined for every $n$ and $\sigma$; they carry the paper's meaning when $n\ge1$ and $0\le\sigma<n^2$, which every theorem of the mission assumes (the paper's $\alpha_k$ divides by $n^2-\sigma$). That the formula for $\gamma_k$ yields the root $\ge\frac1n$, that it is unique, and that $0<\alpha_k,\beta_k\le1$, is the separate theorem `acdm_params`. The paper prints $f'_i(y_k)^\#$ in the update of $v_{k+1}$; the index is the drawn $i_k$, and the encoding uses it.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 15, §5, Method ACDM(x_0), (5.1); p. 15, proof of Theorem 6 (r_k² = ‖v_k − x_*‖²_1); p. 6 (φ_k); p. 5, (2.5) with α = 0

import Mathlib
import Definitions.Def_NesterovRCD_HighProb_Basic

namespace NesterovRCD.Accelerated

open scoped BigOperators

/-- The root γ ≥ 1/n of γ² − γ/n = (1 − γσ/n)a²/b² (step 1 of (5.1)): the larger root of
γ² − c γ − a²/b² = 0 with c = (1 − σa²/b²)/n. -/
noncomputable def gammaOf (n : ℕ) (σ a b : ℝ) : ℝ :=
  let c := (1 - σ * a ^ 2 / b ^ 2) / n
  (c + Real.sqrt (c ^ 2 + 4 * (a ^ 2 / b ^ 2))) / 2

/-- (a_k, b_k) of (5.1): a_0 = 1/n, b_0 = 2, b_{k+1} = b_k/√β_k, a_{k+1} = γ_k b_{k+1},
with β_k = 1 − γ_kσ/n. -/
noncomputable def coeffAB (n : ℕ) (σ : ℝ) : ℕ → ℝ × ℝ
  | 0 => ((n : ℝ)⁻¹, 2)
  | k + 1 =>
    let a := (coeffAB n σ k).1
    let b := (coeffAB n σ k).2
    let γ := gammaOf n σ a b
    let b' := b / Real.sqrt (1 - γ * σ / n)
    (γ * b', b')

/-- a_k of (5.1). -/
noncomputable def acdmA (n : ℕ) (σ : ℝ) (k : ℕ) : ℝ := (coeffAB n σ k).1

/-- b_k of (5.1). -/
noncomputable def acdmB (n : ℕ) (σ : ℝ) (k : ℕ) : ℝ := (coeffAB n σ k).2

/-- γ_k of (5.1), step 1. -/
noncomputable def acdmGamma (n : ℕ) (σ : ℝ) (k : ℕ) : ℝ :=
  gammaOf n σ (acdmA n σ k) (acdmB n σ k)

/-- α_k = (n − γ_kσ)/(γ_k(n² − σ)) of (5.1), step 1. -/
noncomputable def acdmAlpha (n : ℕ) (σ : ℝ) (k : ℕ) : ℝ :=
  (n - acdmGamma n σ k * σ) / (acdmGamma n σ k * ((n : ℝ) ^ 2 - σ))

/-- β_k = 1 − γ_kσ/n of (5.1), step 1. -/
noncomputable def acdmBeta (n : ℕ) (σ : ℝ) (k : ℕ) : ℝ := 1 - acdmGamma n σ k * σ / n

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

/-- ACDM(x_0) (5.1) along given draws: `acdm f L sharp σ x0 k idx = (x_k, v_k)` when
i_s = idx s (s = 0, …, k − 1). Steps 2)–3): y_k = α_kv_k + (1 − α_k)x_k,
x_{k+1} = T_{i_k}(y_k), v_{k+1} = β_kv_k + (1 − β_k)y_k − (γ_k/L_{i_k}) U_{i_k} f′_{i_k}(y_k)^#. -/
noncomputable def acdm (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ) (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i)
    (σ : ℝ) (x0 : NesterovRCD.Sublinear.Blocks E) : (k : ℕ) → (Fin k → Fin n) → NesterovRCD.Sublinear.Blocks E × NesterovRCD.Sublinear.Blocks E
  | 0, _ => (x0, x0)
  | k + 1, idx =>
    let xv := acdm f L sharp σ x0 k (Fin.init idx)
    let i := idx (Fin.last k)
    let y := acdmAlpha n σ k • xv.2 + (1 - acdmAlpha n σ k) • xv.1
    (NesterovRCD.Sublinear.coordStep f L sharp i y,
     acdmBeta n σ k • xv.2 + (1 - acdmBeta n σ k) • y
       - (acdmGamma n σ k / L i) • Pi.single i (sharp i (NesterovRCD.Sublinear.partialGrad f y i)))

/-- φ_k = E_{ξ_{k−1}} f(x_k) for ACDM(x_0), the draws i_0, …, i_{k−1} being independent and
uniform on {1, …, n} (the counter R_0). -/
noncomputable def acdmPhi (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ) (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i)
    (σ : ℝ) (x0 : NesterovRCD.Sublinear.Blocks E) (k : ℕ) : ℝ :=
  NesterovRCD.Sublinear.expect (fun _ => (n : ℝ)⁻¹) k (fun idx => f (acdm f L sharp σ x0 k idx).1)

/-- E_{ξ_{k−1}}(r_k²) with r_k² = ‖v_k − x_*‖²_1 (proof of Theorem 6, p. 15), uniform draws. -/
noncomputable def acdmR2 (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ) (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i)
    (σ : ℝ) (x0 xs : NesterovRCD.Sublinear.Blocks E) (k : ℕ) : ℝ :=
  NesterovRCD.Sublinear.expect (fun _ => (n : ℝ)⁻¹) k (fun idx => NesterovRCD.Sublinear.wnorm L 1 ((acdm f L sharp σ x0 k idx).2 - xs) ^ 2)

end NesterovRCD.Accelerated


