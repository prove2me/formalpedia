-- Prove2me | Definitions.Def_KhintchineTwoRegime_Supplement_IsLTF
-- name    : KhintchineTwoRegime_Supplement_IsLTF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:25:37.243818+00:00
-- url     : https://prove2.me/theorems/f5d37dfd-ddb8-4ff5-93f3-01958004cd8b
-- title:
--   Linear threshold function $h(x)=\operatorname{sgn}(\omega_0+\omega_1x_1+\dots+\omega_nx_n)$
-- statement:
--   A function $h:\{-1,1\}^n\to\mathbb R$ is a **linear threshold function** (LTF) if
--   $$
--   h(x)=\operatorname{sgn}(\omega_0+\omega_1x_1+\omega_2x_2+\dots+\omega_nx_n)\quad\text{for all }x\in\{-1,1\}^n
--   $$
--   for some real constants $\omega_0,\omega_1,\dots,\omega_n$, where $\operatorname{sgn}(x)=1$ for $x\ge0$ and $-1$ for $x<0$. An LTF takes values in $\{-1,1\}$, so it is a Boolean function. The threshold $\omega_0$ and the weights are arbitrary: the linear form may vanish at some points of the cube (ties), where $h=+1$.
--
--   **Formalization Note** The cube is encoded as `x : Fin n → Bool` (true $\mapsto+1$, false $\mapsto-1$), and the paper's $\omega_1,\dots,\omega_n$ are `ω 0, …, ω (n-1)`.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §4, p.10

import Mathlib
import Definitions.Def_KhintchineTwoRegime_Supplement_sgn

namespace KhintchineTwoRegime.Supplement

/-- `h : {−1,1}ⁿ → ℝ` is a (Boolean) **linear threshold function** (LTF):
`h(x) = sgn(ω₀ + ω₁x₁ + ⋯ + ωₙxₙ)` for some real constants `ω₀, ω₁, …, ωₙ`
(Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §4, p.10).

**Formalization Note** The cube is encoded as `x : Fin n → Bool` with `true ↦ +1`,
`false ↦ −1` (the encoding of `KhintchineTwoRegime.K`); indices are 0-based, the paper's
`ω₁` is `ω 0`. The threshold `ω₀` and the weights are arbitrary reals: not homogeneous, not
normalized, and ties are allowed (where the linear form vanishes, `h = sgn 0 = +1`). An LTF
takes only the values `±1`, so it is Boolean. -/
def IsLTF {n : ℕ} (h : (Fin n → Bool) → ℝ) : Prop :=
  ∃ (ω₀ : ℝ) (ω : Fin n → ℝ), ∀ x : Fin n → Bool,
    h x = sgn (ω₀ + ∑ i, ω i * (if x i then (1 : ℝ) else -1))

end KhintchineTwoRegime.Supplement


