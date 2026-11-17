-- Prove2me | Definitions.Def_GraphNNSphere_Supplement_etaGen
-- name    : GraphNNSphere_Supplement_etaGen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:48:32.114149+00:00
-- url     : https://prove2.me/theorems/4ba38b6c-3708-4c8a-8d96-dc001119f434
-- title:
--   Route exponents $\eta_{\mathrm{gen}}$ and $\eta_{\mathrm{entry}}$
-- statement:
--   With $\nu(\psi)=\log(\sin\psi/\sin\theta_1)$ and the transition exponent $g(\varphi\to\psi)=\nu(\psi)+p(\varphi,\psi)$ (with $p=-\infty$ when $w\ge1$), a **chain** consists of a first distance $\varphi_0\ge\theta_{\mathrm{trap}}$ and distances $\varphi_1,\dots,\varphi_\ell\in[\theta_1,\theta_{\mathrm{trap}}]$, $\ell\ge0$, with value
--
--   $$\mathrm{val}(\varphi_0,\dots,\varphi_\ell)=\sum_{i<\ell}g(\varphi_i\to\varphi_{i+1})+p(\varphi_\ell,\theta_1).$$
--
--   In limiting coordinates (limiting angles in the logarithmic regime; normalized distances $x=\varphi/\theta_1$ in the dense regime, with $\nu(x)=\log x$, $w(x,y)=(x^2+y^2-M^2)/(2xy)$, $M=e^\gamma$, and trap distance $L$, $L^2=M^4/(4(M^2-1))$), define
--
--   $$\eta_{\mathrm{gen}}=-\sup_{\text{chains}}\mathrm{val},\qquad \eta_{\mathrm{entry}}=\min\Big\{\lambda,\,-\sup\big[\nu(\varphi_0)-\lambda+\mathrm{val}(\varphi_0,\dots,\varphi_\ell)\big]\Big\},$$
--
--   the latter (logarithmic regime, $\lambda=1/c$) over routes with all distances between the limiting nearest-neighbor and trap angles. They are the exponents in the local-exploration bound of Theorem 5.5.
--
--   **Formalization Note** Values are extended reals. Query distances are below $\pi$, so $\varphi_0\in[\theta_{\mathrm{trap}},\pi)$ in the logarithmic regime and $x_0\in[L,\infty)$ in the dense regime.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Eqs. (56)–(57), pp.60–61

import Mathlib
import Definitions.Def_GraphNNSphere_Supplement_etaStarLog

namespace GraphNNSphere

namespace Supplement

/-- The probability exponent `p = ½ log(1 - w₊²)` of a directional threshold `w`, with `p = -∞` when
`w ≥ 1` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §5.2, p.60). -/
noncomputable def pExp (w : ℝ) : EReal :=
  if 1 ≤ w then ⊥ else ((Real.log (1 - (max w 0) ^ 2) / 2 : ℝ) : EReal)

/-- The limiting chain value in the logarithmic regime, (57):
`val(φ₀, …, φ_ℓ) = Σ_{i<ℓ} g(φ_i → φ_{i+1}) + p(φ_ℓ, θ₁)`, with `g(φ → ψ) = ν(ψ) + p(φ, ψ)` and
`ν(ψ) = log(sin ψ / sin θ₁)`, at the limiting angles `θ₁ = arcsin e^{-1/c}` and
`R = lim ρ_β` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Eqs. (56)–(57), pp.60–61). -/
noncomputable def chainValLog (c β : ℝ) (ℓ : ℕ) (φ : Fin (ℓ + 1) → ℝ) : EReal :=
  (∑ i : Fin ℓ, (((Real.log (Real.sin (φ i.succ) / Real.sin (theta1Lim c)) : ℝ) : EReal) +
      pExp (wRate (Real.cos (rhoLim c β)) (φ i.castSucc) (φ i.succ)))) +
    pExp (wRate (Real.cos (rhoLim c β)) (φ (Fin.last ℓ)) (theta1Lim c))

/-- `η_gen = -sup val` in the logarithmic regime: the supremum is over chains with `ℓ ≥ 0`, a first
distance `φ₀ ≥ θ_trap` and intermediate distances `φ₁, …, φ_ℓ ∈ [θ₁, θ_trap]`, in limiting
angles (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §5.2, p.61).

**Formalization Note** The value is in `EReal`. Query distances are below `π`, so `φ₀ ∈ [θ_trap, π)`
(at `φ₀ = π` the threshold is `+∞` and the paper takes limits). -/
noncomputable def etaGenLog (c β : ℝ) : EReal :=
  -⨆ (ℓ : ℕ) (φ : Fin (ℓ + 1) → ℝ)
      (_ : φ 0 ∈ Set.Ico (thetaTrapLim c β) Real.pi ∧
        ∀ i : Fin ℓ, φ i.succ ∈ Set.Icc (theta1Lim c) (thetaTrapLim c β)),
      chainValLog c β ℓ φ

/-- `η_entry = min{λ, -sup[ν(φ₀) - λ + val(φ₀, …, φ_ℓ)]}` in the logarithmic regime, `λ = 1/c`,
the supremum over routes with all distances `φ₀, …, φ_ℓ` between the limiting nearest-neighbor
and trap angles, `ℓ ≥ 0` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §5.2, p.61). -/
noncomputable def etaEntryLog (c β : ℝ) : EReal :=
  min ((1 / c : ℝ) : EReal)
    (-⨆ (ℓ : ℕ) (φ : Fin (ℓ + 1) → ℝ)
        (_ : ∀ i, φ i ∈ Set.Icc (theta1Lim c) (thetaTrapLim c β)),
        (((Real.log (Real.sin (φ 0) / Real.sin (theta1Lim c)) - 1 / c : ℝ) : EReal) +
          chainValLog c β ℓ φ))

/-- The limiting chain value in the dense regime, in normalized distances `x = φ/θ₁`:
`Σ_{i<ℓ} g(x_i → x_{i+1}) + p(x_ℓ, 1)` with `ν(x) = log x`, `w(x, y) = (x² + y² - M²)/(2xy)`,
`M = e^γ` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §5.2, p.61). -/
noncomputable def chainValDense (γ : ℝ) (ℓ : ℕ) (x : Fin (ℓ + 1) → ℝ) : EReal :=
  (∑ i : Fin ℓ, (((Real.log (x i.succ) : ℝ) : EReal) +
      pExp ((x i.castSucc ^ 2 + x i.succ ^ 2 - Real.exp γ ^ 2) / (2 * x i.castSucc * x i.succ)))) +
    pExp ((x (Fin.last ℓ) ^ 2 + 1 - Real.exp γ ^ 2) / (2 * x (Fin.last ℓ)))

/-- The normalized limiting trap distance `L = lim θ_trap/θ₁`, `L² = M⁴/(4(M² - 1))`, `M = e^γ`
(Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §5.2, p.61). -/
noncomputable def trapLimDense (γ : ℝ) : ℝ :=
  Real.sqrt (Real.exp γ ^ 4 / (4 * (Real.exp γ ^ 2 - 1)))

/-- `η_gen = -sup val` in the dense regime: chains with `x₀ ≥ L` and `x₁, …, x_ℓ ∈ [1, L]`,
`ℓ ≥ 0` (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §5.2, p.61). -/
noncomputable def etaGenDense (γ : ℝ) : EReal :=
  -⨆ (ℓ : ℕ) (x : Fin (ℓ + 1) → ℝ)
      (_ : x 0 ∈ Set.Ici (trapLimDense γ) ∧ ∀ i : Fin ℓ, x i.succ ∈ Set.Icc 1 (trapLimDense γ)),
      chainValDense γ ℓ x

end Supplement

end GraphNNSphere


