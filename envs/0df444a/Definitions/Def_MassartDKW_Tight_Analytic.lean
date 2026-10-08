-- Prove2me | Definitions.Def_MassartDKW_Tight_Analytic
-- name    : MassartDKW_Tight_Analytic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:40:20.222194+00:00
-- url     : https://prove2.me/theorems/78ee5774-c4c7-43dd-b145-d95b4a12c8d5
-- title:
--   §2, pp. 1271–1281 — Smirnov's p_{λ,n}(j) (2.1), Csáki's density f_λ (2.2), v_n, C_{λ,n}, φ, ψ (2.6), T, I_{a,b}, η_n
-- statement:
--   The analytic objects of the proof of Theorem 1. Throughout, $n\ge1$ is an integer, $\lambda>0$, and $\varepsilon=\lambda/\sqrt n$.
--
--   1. **Smirnov's point probabilities** (2.1): for an integer $j\ge0$,
--   $$p_{\lambda,n}(j)=\lambda\sqrt n\,(j+\lambda\sqrt n)^{j-1}(n-j-\lambda\sqrt n)^{n-j}\,n^{-n}\binom nj ,$$
--   and their sum $\sum_{0\le j<n-\lambda\sqrt n}p_{\lambda,n}(j)$, the right side of (2.3).
--   2. **Csáki's density** (2.2): $f_\lambda(s)=\dfrac{\lambda}{\sqrt{2\pi}}\,s^{-3/2}(1-s)^{-1/2}\exp\!\Bigl(-\dfrac{\lambda^2}{2s(1-s)}\Bigr)$ for $s\in\,]0,1[$, the density of the first time a Brownian bridge crosses the level $\lambda$.
--   3. $v_n(s)=\bigl(s(s^2-1/(4n^2))\bigr)^{-1}$ (statement of Proposition 1).
--   4. $C_{\lambda,n}=\exp(2\lambda^2)\sum_{0\le j<n-\lambda\sqrt n}p_{\lambda,n}(j)$, which by (2.3) is $\exp(2\lambda^2)P(D_n^->\lambda)$ (p. 1281).
--   5. $\varphi(t)=t-\dfrac{t^2}{2(1+2t/3)}-\log(1+t)$ (Lemma 1) and $\psi(t)=-\log(1+t)+\tfrac32\log(1+2t/3)$ (2.6).
--   6. $T(\nu,t)=\nu^2\varphi(t)-\nu t\psi(t)+\dfrac{\theta t^2}{1+2t/3}$ with $\theta=0.4833$ (Lemma 2).
--   7. $I_{a,b}(\lambda)=\dfrac{\lambda e^{2\lambda^2}}{\sqrt{2\pi}}\displaystyle\int_0^1u^{-1/2-a}(1-u)^{-1/2-b}\exp\!\Bigl(-\frac{\lambda^2}{2u(1-u)}\Bigr)du$ (Lemma 4).
--   8. With $\mu=0.4345$, the right side of (2.11):
--   $$\eta_n(\lambda)=-1+\Bigl(\lambda+\frac1{4\lambda}+\frac{3\mu}\lambda+\frac{3\mu}{2\lambda^3}\Bigr)n^{-1/2}-\frac\mu2\Bigl(4+\frac1{\lambda^2}\Bigr)n^{-1}+\frac\mu2\Bigl(4\lambda+\frac1\lambda\Bigr)n^{-3/2}.$$
--
--   These are the quantities in which the exact law of $D_n^-$ is compared with its Brownian-bridge limit.
--
--   **Formalization Note** $\lambda$ is a reserved word in Lean and is written `l`. The exponent $j-1$ in $p_{\lambda,n}(j)$ is an integer power (`zpow`), so that $p_{\lambda,n}(0)=(1-\varepsilon)^n$; the exponent $n-j$ is a natural power, used only for $j<n$. The sum in (2.3) runs over $j\in\{0,\dots,n-1\}$ with $j<n-\lambda\sqrt n$. $C_{\lambda,n}$ is defined through the exact formula (2.3) rather than through the probability: the two agree for $0<\lambda<\sqrt n$ by milestone (2.3), and for $\lambda\ge\sqrt n$ both are $0$. Fractional powers are `Real.rpow`; $f_\lambda$ and $v_n$ are only used where $s\in\,]0,1[$ and $s>1/(2n)$, where no division by zero occurs. The constants $\theta=0.4833$ and $\mu=0.4345$ are exact decimals.
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), pp. 1271–1281, (2.1), (2.2), (2.3), Proposition 1 (v_n), Lemma 1 (φ), (2.6), Lemma 2, Lemma 4, (2.11), and the definition of C_{λ,n} on p. 1281

import Mathlib

namespace MassartDKW.Tight

/-- Smirnov's point probabilities `p_{λ,n}(j)` of (2.1):
`λ√n (j + λ√n)^{j−1} (n − j − λ√n)^{n−j} n^{−n} C(n, j)`.
The exponent `j − 1` is an integer (`zpow`), so that `p_{λ,n}(0) = (1 − λ/√n)^n`. -/
noncomputable def smirnovP (l : ℝ) (n j : ℕ) : ℝ :=
  l * Real.sqrt n * ((j : ℝ) + l * Real.sqrt n) ^ ((j : ℤ) - 1) *
    ((n : ℝ) - j - l * Real.sqrt n) ^ (n - j) * ((n : ℝ) ^ n)⁻¹ * (n.choose j)

/-- The right side of (2.3): `Σ_{0 ≤ j < n − λ√n} p_{λ,n}(j)`. -/
noncomputable def smirnovTail (n : ℕ) (l : ℝ) : ℝ :=
  ∑ j ∈ (Finset.range n).filter (fun j : ℕ => (j : ℝ) < n - l * Real.sqrt n), smirnovP l n j

/-- Csáki's density (2.2) of the first passage time of a Brownian bridge at level `λ`:
`f_λ(s) = λ/√(2π) s^{−3/2} (1 − s)^{−1/2} exp(−λ²/(2s(1 − s)))`, meaningful for `s ∈ ]0, 1[`. -/
noncomputable def csakiDensity (l s : ℝ) : ℝ :=
  l / Real.sqrt (2 * Real.pi) * s ^ (-(3 / 2 : ℝ)) * (1 - s) ^ (-(1 / 2 : ℝ)) *
    Real.exp (-(l ^ 2) / (2 * s * (1 - s)))

/-- `v_n(s) = (s (s² − 1/(4n²)))^{−1}` (statement of Proposition 1). -/
noncomputable def v (n : ℕ) (s : ℝ) : ℝ :=
  (s * (s ^ 2 - 1 / (4 * (n : ℝ) ^ 2)))⁻¹

/-- `C_{λ,n} = exp(2λ²) Σ_{0 ≤ j < n − λ√n} p_{λ,n}(j)`, i.e. `exp(2λ²) P(D_n⁻ > λ)` through (2.3). -/
noncomputable def C (n : ℕ) (l : ℝ) : ℝ :=
  Real.exp (2 * l ^ 2) * smirnovTail n l

/-- `φ(t) = t − t²/(2(1 + 2t/3)) − log(1 + t)` (Lemma 1). -/
noncomputable def phi (t : ℝ) : ℝ :=
  t - t ^ 2 / (2 * (1 + 2 * t / 3)) - Real.log (1 + t)

/-- `ψ(t) = −log(1 + t) + (3/2) log(1 + 2t/3)` (2.6). -/
noncomputable def psi (t : ℝ) : ℝ :=
  -Real.log (1 + t) + 3 / 2 * Real.log (1 + 2 * t / 3)

/-- `T(ν, t) = ν² φ(t) − ν t ψ(t) + θ t²/(1 + 2t/3)` with `θ = 0.4833` (Lemma 2). -/
noncomputable def T (ν t : ℝ) : ℝ :=
  ν ^ 2 * phi t - ν * t * psi t + 0.4833 * t ^ 2 / (1 + 2 * t / 3)

/-- `I_{a,b}(λ) = λ exp(2λ²)/√(2π) ∫_0^1 u^{−1/2−a} (1 − u)^{−1/2−b} exp(−λ²/(2u(1 − u))) du`
(Lemma 4). -/
noncomputable def I (a b l : ℝ) : ℝ :=
  l * Real.exp (2 * l ^ 2) / Real.sqrt (2 * Real.pi) *
    ∫ u in (0 : ℝ)..1, u ^ (-(1 / 2 : ℝ) - a) * (1 - u) ^ (-(1 / 2 : ℝ) - b) *
      Real.exp (-(l ^ 2) / (2 * u * (1 - u)))

/-- The constant `μ = 0.4345` of the proof of Theorem 1 (p. 1279). -/
noncomputable def mu : ℝ := 0.4345

/-- `η_n(λ)`, the right side of (2.11):
`−1 + (λ + 1/(4λ) + 3μ/λ + 3μ/(2λ³)) n^{−1/2} − (μ/2)(4 + 1/λ²) n^{−1} + (μ/2)(4λ + 1/λ) n^{−3/2}`. -/
noncomputable def eta (n : ℕ) (l : ℝ) : ℝ :=
  -1 + (l + 1 / (4 * l) + 3 * mu / l + 3 * mu / (2 * l ^ 3)) * (n : ℝ) ^ (-(1 / 2 : ℝ))
    - mu / 2 * (4 + 1 / l ^ 2) * (n : ℝ) ^ (-(1 : ℝ))
    + mu / 2 * (4 * l + 1 / l) * (n : ℝ) ^ (-(3 / 2 : ℝ))

end MassartDKW.Tight


