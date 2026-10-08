-- Prove2me | Definitions.Def_FracPSG_Enhanced_Algorithm2
-- name    : FracPSG_Enhanced_Algorithm2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T22:07:25.468986+00:00
-- url     : https://prove2.me/theorems/0c65a09c-0271-4e47-8177-3f9a94681b99
-- title:
--   Assumptions 1 and 2′, (BC), and runs of the enhanced extrapolated proximal subgradient algorithm (Algorithm 2)
-- statement:
--   Let $H$ be a finite-dimensional real Hilbert space and $S\subseteq H$ nonempty, closed and convex. Consider
--   $$\min_{x\in S}\ \frac{f(x)}{g(x)},\qquad f=f^{\mathfrak s}+f^{\mathfrak n},\qquad g=\max_{1\le i\le p} g_i .$$
--
--   1. **Assumption 1.** $f^{\mathfrak s}: H\to\mathbb R$ is continuously differentiable and convex with $\ell$-Lipschitz gradient ($\ell\ge0$); $f^{\mathfrak n}: H\to(-\infty,+\infty]$ is proper and lower semicontinuous; $S\cap\operatorname{dom} f\ne\emptyset$; and $f(x)\ge0$ for all $x\in S\cap\operatorname{dom}f$.
--   2. **Assumption 2′.** Each $g_i$ is continuously differentiable on an open set containing $S$ and weakly convex on $S$ with modulus $\beta\ge0$, and the boundedness condition (BC) holds: there are $m,M>0$ with $m\le g(x)\le M$ for all $x\in S\cap\operatorname{dom} f$. As in the standing setting of (P), $g$ is lower semicontinuous and positive on $S$.
--   3. **Step 1 parameters.** $\delta,\varepsilon,\zeta>0$ with $1-\sqrt\beta\,\zeta>0$,
--   $$\bar\mu\in\Big[0,\ \frac{\delta(1-\sqrt\beta\zeta)\sqrt{mM}}{2M}\Big),\qquad \bar\kappa\in\Big[0,\ \sqrt{\frac{m\delta(1-\sqrt\beta\zeta)}{\ell M}-\frac{2m\bar\mu}{\ell\sqrt{mM}}}\Big).$$
--   4. **A run of Algorithm 2.** Start at $x_{-1}=x_0\in S\cap\operatorname{dom}f$. At step $n$ set $\theta_n=f(x_n)/g(x_n)$, choose $0<\tau_n\le 1/\max\{\sqrt\beta\,\theta_n/\zeta,\ \delta\}$, $\kappa_n\in[0,\bar\kappa]$, $\mu_n\in[0,\bar\mu\tau_n]$, and put $u_n=x_n+\kappa_n(x_n-x_{n-1})$, $v_n=x_n+\mu_n(x_n-x_{n-1})$. For each $i\in I_\varepsilon(x_n)$ take
--   $$w_n^{i}\in\operatorname*{argmin}_{x\in S}\Big(f^{\mathfrak n}(x)+f^{\mathfrak s}(u_n)+\langle\nabla f^{\mathfrak s}(u_n),x-u_n\rangle+\frac1{2\tau_n}\|x-v_n-\tau_n\theta_n\nabla g_i(x_n)\|^2+\frac\ell2\|x-u_n\|^2\Big),$$
--   then select
--   $$\hat\imath_n\in\operatorname*{argmin}_{i\in I_\varepsilon(x_n)}\Big(f(w_n^{i})-\theta_n g(w_n^{i})+\frac12\Big(\frac{1-\sqrt\beta\zeta}{\tau_n}-\frac{M\mu_n}{\sqrt{mM}\,\tau_n}\Big)\|w_n^{i}-x_n\|^2\Big)$$
--   and set $x_{n+1}=w_n^{\hat\imath_n}$.
--   5. **Sublevel set and Lyapunov sequence.** $S_0=\{x\in S: f(x)/g(x)\le f(x_0)/g(x_0)\}$, and
--   $$F_n=\frac{f(x_n)}{g(x_n)}+\Big(\frac{\ell\bar\kappa^2}{2m}+\frac{\bar\mu}{2\sqrt{mM}}\Big)\|x_n-x_{n-1}\|^2 .\qquad(27)$$
--
--   Algorithm 2 computes one proximal step per nearly active piece of the denominator and keeps the candidate with the best merit value; this is what lets its cluster points satisfy the stronger stationarity notion.
--
--   **Formalization Note** Two misprints of the source are corrected. (a) Step 1 reads "Let $\delta,\omega\in\mathbb R_{++}$", but $\omega$ is never used and the active-set parameter $\varepsilon$ is never declared; it is read as $\varepsilon>0$. (b) Step 2 prints $0<\tau_n\le1/\max\{\beta\theta_n/(1-\zeta),\delta\}$, but the proof (p. 23) uses $\beta\theta_n\le\sqrt\beta\zeta/\tau_n$, which is the rule $\tau_n\le1/\max\{\sqrt\beta\theta_n/\zeta,\delta\}$ of Algorithm 1; the run uses the latter. The $\bar\kappa$-range is written as $\ell\bar\kappa^2<m\delta(1-\sqrt\beta\zeta)/M-2m\bar\mu/\sqrt{mM}$, which is equivalent for $\ell>0$ and avoids dividing by $\ell$. Candidates $w_n^i$ for $i\notin I_\varepsilon(x_n)$ are unconstrained. The argmin steps are modelled as "some minimizer over $S$", the Step 3 criterion takes values in $(-\infty,+\infty]$, $x_{-1}=x_0$ is encoded by `xPrev`, ratios are real numbers `(f x).toReal / g x` (used only at points of $S\cap\operatorname{dom}f$), indices are `Fin p`, and $\nabla g_i$ is Mathlib's `gradient`.
-- source:
--   Boţ, Dao, Li, Extrapolated Proximal Subgradient Algorithms for Nonconvex and Nonsmooth Fractional Programs, arXiv:2003.04124v2, p. 1 (P), p. 8 (Assumption 1, (BC)), pp. 21–22 (Assumption 2′, Algorithm 2), p. 22 (Theorem 6.1, S₀ and (27))

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_FracPSG_Enhanced_Basic
import Definitions.Def_FracPSG_Subseq_EPSG

open Filter Topology
open scoped InnerProductSpace

namespace FracPSG.Enhanced

open NonconvexSplitting.Shared

/-- Assumption 2′ (p. 21) for `g = max{gᵢ : i ∈ Fin p}`, together with the standing hypotheses
of problem (P) on the denominator (p. 1: `g` lower semicontinuous on `H`, finite and positive on
`S`): each `gᵢ` is continuously differentiable on an open set containing `S` and weakly convex on
`S` with modulus `β`, and (FracPSG.Subseq.BC) holds with constants `m, M`. The paper's indices `1, …, p` are
`0, …, p − 1` here. -/
structure Assumption2' {N p : ℕ} [NeZero p] (S : Set (EuclideanSpace ℝ (Fin N)))
    (f : EuclideanSpace ℝ (Fin N) → EReal) (gi : Fin p → EuclideanSpace ℝ (Fin N) → ℝ)
    (β m M : ℝ) : Prop where
  g_lsc : LowerSemicontinuous (maxFn gi)
  g_pos : ∀ x ∈ S, 0 < maxFn gi x
  contDiff : ∀ i, ∃ O, IsOpen O ∧ S ⊆ O ∧ ContDiffOn ℝ 1 (gi i) O
  weakly_convex : ∀ i, FracPSG.Subseq.IsWeaklyConvexOn S (gi i) β
  bc : FracPSG.Subseq.BC S f (maxFn gi) m M

/-- Step 1 of Algorithm 2 (p. 21), with the active-set parameter `ε` in place of the misprinted
`ω`: `δ, ε, ζ > 0`, `1 − √β ζ > 0`, `μ̄ ∈ [0, δ(1 − √β ζ)√(mM)/(2M))` and
`κ̄ ∈ [0, √(mδ(1 − √β ζ)/(ℓM) − 2mμ̄/(ℓ√(mM))))`, the latter written in the multiplied-out form
`ℓκ̄² < mδ(1 − √β ζ)/M − 2mμ̄/√(mM)` (equivalent for `ℓ > 0`; no division by `ℓ`). -/
def Step1Params (ℓ β δ ε ζ μbar κbar m M : ℝ) : Prop :=
  0 < δ ∧ 0 < ε ∧ 0 < ζ ∧ 0 < 1 - Real.sqrt β * ζ ∧
  0 ≤ μbar ∧ μbar < δ * (1 - Real.sqrt β * ζ) * Real.sqrt (m * M) / (2 * M) ∧
  0 ≤ κbar ∧
  ℓ * κbar ^ 2 < m * δ * (1 - Real.sqrt β * ζ) / M - 2 * m * μbar / Real.sqrt (m * M)

/-- The selection criterion of Step 3 of Algorithm 2 at a candidate `w`:
`f(w) − θ g(w) + ½((1 − √β ζ)/τ − Mμ/(√(mM) τ))‖w − xₙ‖²` (value `+∞` when `f(w) = +∞`). -/
noncomputable def selObj {N : ℕ} (f : EuclideanSpace ℝ (Fin N) → EReal)
    (g : EuclideanSpace ℝ (Fin N) → ℝ) (β ζ m M τ μ θ : ℝ) (xn w : EuclideanSpace ℝ (Fin N)) :
    EReal :=
  f w + ((-(θ * g w) + 1 / 2 * ((1 - Real.sqrt β * ζ) / τ - M * μ / (Real.sqrt (m * M) * τ))
    * ‖w - xn‖ ^ 2 : ℝ) : EReal)

/-- A run of Algorithm 2 (the enhanced e-PSG algorithm, pp. 21–22) with data
`(S, fˢ, fⁿ, (gᵢ), ℓ, β)` and parameters `(δ, ζ, ε, μ̄, κ̄, m, M)`: iterates `x`, candidates
`w n i = wₙ^i`, selected indices `ihat n = îₙ`, step sizes `τ` and extrapolation weights `κ`, `μ`.
Here `x₋₁ = x₀ ∈ S ∩ dom f`, `θₙ = f(xₙ)/g(xₙ)`, `0 < τₙ ≤ 1/max{√β θₙ/ζ, δ}` (the rule used in
the proof, p. 23; the printed rule reads `βθₙ/(1 − ζ)`), `κₙ ∈ [0, κ̄]`, `μₙ ∈ [0, μ̄ τₙ]`,
`uₙ = xₙ + κₙ(xₙ − xₙ₋₁)`, `vₙ = xₙ + μₙ(xₙ − xₙ₋₁)`; for every `i ∈ I_ε(xₙ)` the candidate
`wₙ^i` is some minimizer over `S` of the Step 2 subproblem built with `∇gᵢ(xₙ)`; `îₙ ∈ I_ε(xₙ)`
minimizes the Step 3 criterion over `I_ε(xₙ)`; and `xₙ₊₁ = wₙ^{îₙ}`. -/
structure IsEnhancedRun {N p : ℕ} [NeZero p] (S : Set (EuclideanSpace ℝ (Fin N)))
    (fs : EuclideanSpace ℝ (Fin N) → ℝ) (fn : EuclideanSpace ℝ (Fin N) → EReal)
    (gi : Fin p → EuclideanSpace ℝ (Fin N) → ℝ) (ℓ β δ ζ ε μbar κbar m M : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin N)) (w : ℕ → Fin p → EuclideanSpace ℝ (Fin N))
    (ihat : ℕ → Fin p) (τ κ μ : ℕ → ℝ) : Prop where
  start_mem : x 0 ∈ S
  start_dom : FracPSG.Subseq.objF fs fn (x 0) ≠ ⊤
  step_pos : ∀ n, 0 < τ n
  step_le : ∀ n,
    τ n ≤ 1 / max (Real.sqrt β * FracPSG.Subseq.ratio (FracPSG.Subseq.objF fs fn) (maxFn gi) (x n) / ζ) δ
  kappa_mem : ∀ n, κ n ∈ Set.Icc 0 κbar
  mu_mem : ∀ n, μ n ∈ Set.Icc 0 (μbar * τ n)
  cand_mem : ∀ n, ∀ i ∈ activeSet ε gi (x n), w n i ∈ S
  cand_argmin : ∀ n, ∀ i ∈ activeSet ε gi (x n), ∀ y ∈ S,
    FracPSG.Subseq.subObj fs fn ℓ (τ n) (FracPSG.Subseq.ratio (FracPSG.Subseq.objF fs fn) (maxFn gi) (x n)) (FracPSG.Subseq.extrap x κ n) (FracPSG.Subseq.extrap x μ n)
        (gradient (gi i) (x n)) (w n i) ≤
      FracPSG.Subseq.subObj fs fn ℓ (τ n) (FracPSG.Subseq.ratio (FracPSG.Subseq.objF fs fn) (maxFn gi) (x n)) (FracPSG.Subseq.extrap x κ n) (FracPSG.Subseq.extrap x μ n)
        (gradient (gi i) (x n)) y
  ihat_mem : ∀ n, ihat n ∈ activeSet ε gi (x n)
  ihat_argmin : ∀ n, ∀ i ∈ activeSet ε gi (x n),
    selObj (FracPSG.Subseq.objF fs fn) (maxFn gi) β ζ m M (τ n) (μ n) (FracPSG.Subseq.ratio (FracPSG.Subseq.objF fs fn) (maxFn gi) (x n))
        (x n) (w n (ihat n)) ≤
      selObj (FracPSG.Subseq.objF fs fn) (maxFn gi) β ζ m M (τ n) (μ n) (FracPSG.Subseq.ratio (FracPSG.Subseq.objF fs fn) (maxFn gi) (x n))
        (x n) (w n i)
  next_eq : ∀ n, x (n + 1) = w n (ihat n)

/-- The Lyapunov sequence (27) of Theorem 6.1(i):
`Fₙ = f(xₙ)/g(xₙ) + (ℓκ̄²/(2m) + μ̄/(2√(mM)))‖xₙ − xₙ₋₁‖²`. -/
noncomputable def lyap {N : ℕ} (f : EuclideanSpace ℝ (Fin N) → EReal)
    (g : EuclideanSpace ℝ (Fin N) → ℝ) (ℓ μbar κbar m M : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin N)) (n : ℕ) : ℝ :=
  FracPSG.Subseq.ratio f g (x n) + (ℓ * κbar ^ 2 / (2 * m) + μbar / (2 * Real.sqrt (m * M))) * ‖x n - FracPSG.Subseq.xPrev x n‖ ^ 2

end FracPSG.Enhanced


