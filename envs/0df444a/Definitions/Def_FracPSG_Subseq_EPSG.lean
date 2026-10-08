-- Prove2me | Definitions.Def_FracPSG_Subseq_EPSG
-- name    : FracPSG_Subseq_EPSG
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:17.267631+00:00
-- url     : https://prove2.me/theorems/066e34bd-a4ce-4b37-a36e-bbef48498a8a
-- title:
--   Assumptions 1–2, condition (BC), Algorithm 1 (e-PSG) and the constants (14)
-- statement:
--   Let $H=\mathbb R^N$ with the Euclidean inner product, $S\subseteq H$, and consider the fractional program $\min_{x\in S} f(x)/g(x)$.
--
--   **Assumption 1.** $f=f^{\mathsf s}+f^{\mathsf n}$, where $f^{\mathsf s}: H\to\mathbb R$ is continuously differentiable and convex with an $\ell$-Lipschitz gradient ($\ell\ge0$), $f^{\mathsf n}: H\to(-\infty,+\infty]$ is proper and lower semicontinuous, $S\cap\operatorname{dom} f\neq\emptyset$, and $f(x)\ge0$ for all $x\in S\cap\operatorname{dom} f$.
--
--   **Assumption 2.** $g: H\to\mathbb R$ is positive on $S$, continuous on an open set containing $S$, and either weakly convex with modulus $\beta$ on an open convex set containing $S$, or regular at every point of $S$ and weakly convex with modulus $\beta$ on $S$.
--
--   **(BC).** There are $m,M>0$ with $m\le g(x)\le M$ for all $x\in S\cap\operatorname{dom} f$.
--
--   **Algorithm 1 (e-PSG).** Choose $x_{-1}=x_0\in S\cap\operatorname{dom} f$, $\delta>0$, $\zeta>0$ with $1-\sqrt\beta\,\zeta>0$, and, if (BC) holds,
--   $$\bar\mu\in\Big[0,\tfrac{\delta(1-\sqrt\beta\zeta)\sqrt{mM}}{2M}\Big),\qquad \bar\kappa\in\Big[0,\sqrt{\tfrac{m\delta(1-\sqrt\beta\zeta)}{\ell M}-\tfrac{2m\bar\mu}{\ell\sqrt{mM}}}\Big);$$
--   otherwise $\bar\mu=\bar\kappa=0$. At step $n$ set $\theta_n=f(x_n)/g(x_n)$, pick $g_n\in\partial_L g(x_n)$ and $0<\tau_n\le 1/\max\{\sqrt\beta\,\theta_n/\zeta,\delta\}$, let $u_n=x_n+\kappa_n(x_n-x_{n-1})$ with $\kappa_n\in[0,\bar\kappa]$ and $v_n=x_n+\mu_n(x_n-x_{n-1})$ with $\mu_n\in[0,\bar\mu\tau_n]$, and take
--   $$x_{n+1}\in\operatorname*{argmin}_{x\in S}\Big(f^{\mathsf n}(x)+f^{\mathsf s}(u_n)+\langle\nabla f^{\mathsf s}(u_n),x-u_n\rangle+\frac1{2\tau_n}\|x-v_n-\tau_n\theta_n g_n\|^2+\frac\ell2\|x-u_n\|^2\Big).$$
--
--   **Constants (14) and $S_0$.** $S_0=\{x\in S: f(x)/g(x)\le f(x_0)/g(x_0)\}$. Under (BC), $c=\frac{\ell\bar\kappa^2}{2m}+\frac{\bar\mu}{2\sqrt{mM}}$ and $\alpha=\frac{\delta(1-\sqrt\beta\zeta)}{2M}-\frac{\bar\mu}{\sqrt{mM}}-\frac{\ell\bar\kappa^2}{2m}$; otherwise $c=0$ and $\alpha=\frac{\delta(1-\sqrt\beta\zeta)}{2M'}$ with $M'=\sup_{x\in S_0}g(x)$.
--
--   These objects are the data, the method and the merit-function constants of the subsequential convergence theorem for e-PSG.
--
--   **Formalization Note** A run is a predicate `IsEPSGRun` on the sequences $(x_n)$, $(g_n)$, $(\tau_n)$, $(\kappa_n)$, $(\mu_n)$: the argmin step and the choice of $g_n$ are selections (no uniqueness, existence assumed by the run). $x_{-1}$ is `xPrev x 0 = x 0`. $f$ is `EReal`-valued, $\theta_n$ is `(f x_n).toReal / g x_n` (all iterates lie in $\operatorname{dom} f$), and the subproblem objective is $f^{\mathsf n}(y)$ plus a real number. $g$ is real-valued on all of $H$: only its values and limiting subgradients at points of $S$ enter, and these depend only on $g$ near $S$, where the paper's $g$ is finite. The $\bar\kappa$-range is written as $\ell\bar\kappa^2<\frac{m\delta(1-\sqrt\beta\zeta)}{M}-\frac{2m\bar\mu}{\sqrt{mM}}$, which is the printed interval for $\ell>0$ and avoids division by $\ell$ (for $\ell=0$ any $\bar\kappa\ge0$ is allowed). "Continuously differentiable" is `ContDiff ℝ 1`; the Lipschitz gradient is $\|\nabla f^{\mathsf s}(x)-\nabla f^{\mathsf s}(y)\|\le\ell\|x-y\|$. $M'$ is a real `sSup`, finite because $S_0$ is bounded and $g$ is continuous near the closed set $S$.
-- source:
--   Boţ, Dao, Li, Extrapolated Proximal Subgradient Algorithms for Nonconvex and Nonsmooth Fractional Programs, arXiv:2003.04124v2, p. 8 (Assumptions 1, 2, (BC)), p. 9 (Algorithm 1), p. 10 (Theorem 4.5, S₀ and (14))

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_FracPSG_Subseq_Basic

open Filter Topology
open scoped InnerProductSpace

namespace FracPSG.Subseq

open NonconvexSplitting.Shared

/-- The numerator `f = fˢ + fⁿ` of problem (P) (Assumption 1, p. 8), with `fˢ` real-valued and
`fⁿ` extended-real-valued. -/
noncomputable def objF {N : ℕ} (fs : EuclideanSpace ℝ (Fin N) → ℝ)
    (fn : EuclideanSpace ℝ (Fin N) → EReal) (x : EuclideanSpace ℝ (Fin N)) : EReal :=
  (fs x : EReal) + fn x

/-- The ratio `f(x)/g(x)` as a real number (meaningful for `x ∈ S ∩ dom f`). -/
noncomputable def ratio {N : ℕ} (f : EuclideanSpace ℝ (Fin N) → EReal)
    (g : EuclideanSpace ℝ (Fin N) → ℝ) (x : EuclideanSpace ℝ (Fin N)) : ℝ :=
  (f x).toReal / g x

/-- Assumption 1 (p. 8) together with the standing hypotheses of problem (P) on the numerator:
`fˢ` is continuously differentiable and convex with an `ℓ`-Lipschitz gradient, `fⁿ` is proper and
lower semicontinuous, `S ∩ dom f ≠ ∅`, and `f ≥ 0` on `S ∩ dom f`. -/
structure Assumption1 {N : ℕ} (S : Set (EuclideanSpace ℝ (Fin N)))
    (fs : EuclideanSpace ℝ (Fin N) → ℝ) (fn : EuclideanSpace ℝ (Fin N) → EReal) (ℓ : ℝ) :
    Prop where
  fs_contDiff : ContDiff ℝ 1 fs
  fs_convex : ConvexOn ℝ Set.univ fs
  ell_nonneg : 0 ≤ ℓ
  grad_lipschitz : ∀ x y, ‖gradient fs x - gradient fs y‖ ≤ ℓ * ‖x - y‖
  fn_proper : IsProperFn fn
  fn_lsc : LowerSemicontinuous fn
  dom_nonempty : ∃ x ∈ S, objF fs fn x ≠ ⊤
  nonneg : ∀ x ∈ S, objF fs fn x ≠ ⊤ → 0 ≤ objF fs fn x

/-- Assumption 2 (p. 8) for a real-valued denominator `g`: `g` is positive on `S`, continuous on
an open set containing `S`, and either weakly convex with modulus `β` on an open convex set
containing `S`, or regular (at every point of `S`) and weakly convex with modulus `β` on `S`. -/
structure Assumption2 {N : ℕ} (S : Set (EuclideanSpace ℝ (Fin N)))
    (g : EuclideanSpace ℝ (Fin N) → ℝ) (β : ℝ) : Prop where
  pos : ∀ x ∈ S, 0 < g x
  continuous_near : ∃ O, IsOpen O ∧ S ⊆ O ∧ ContinuousOn g O
  weakly_convex :
    (∃ C, IsOpen C ∧ Convex ℝ C ∧ S ⊆ C ∧ IsWeaklyConvexOn C g β) ∨
    ((∀ x ∈ S, IsRegularAt (fun y => (g y : EReal)) x) ∧ IsWeaklyConvexOn S g β)

/-- The boundedness condition (BC) (p. 8): `m, M > 0` and `m ≤ g ≤ M` on `S ∩ dom f`. -/
def BC {N : ℕ} (S : Set (EuclideanSpace ℝ (Fin N))) (f : EuclideanSpace ℝ (Fin N) → EReal)
    (g : EuclideanSpace ℝ (Fin N) → ℝ) (m M : ℝ) : Prop :=
  0 < m ∧ 0 < M ∧ ∀ x ∈ S, f x ≠ ⊤ → m ≤ g x ∧ g x ≤ M

/-- Step 1 of Algorithm 1 (p. 9) when (BC) holds with constants `m, M`:
`μ̄ ∈ [0, δ(1 − √β ζ)√(mM)/(2M))` and
`κ̄ ∈ [0, √(mδ(1 − √β ζ)/(ℓM) − 2mμ̄/(ℓ√(mM))))`, the latter written in the multiplied-out form
`ℓκ̄² < mδ(1 − √β ζ)/M − 2mμ̄/√(mM)` (equivalent for `ℓ > 0`; no division by `ℓ`). -/
def ParamsBC {N : ℕ} (S : Set (EuclideanSpace ℝ (Fin N))) (f : EuclideanSpace ℝ (Fin N) → EReal)
    (g : EuclideanSpace ℝ (Fin N) → ℝ) (ℓ β δ ζ μbar κbar m M : ℝ) : Prop :=
  BC S f g m M ∧
  0 ≤ μbar ∧ μbar < δ * (1 - Real.sqrt β * ζ) * Real.sqrt (m * M) / (2 * M) ∧
  0 ≤ κbar ∧
  ℓ * κbar ^ 2 < m * δ * (1 - Real.sqrt β * ζ) / M - 2 * m * μbar / Real.sqrt (m * M)

/-- Step 1 of Algorithm 1 (p. 9) in the absence of (BC): `μ̄ = 0` and `κ̄ = 0`. -/
def ParamsNoBC (μbar κbar : ℝ) : Prop :=
  μbar = 0 ∧ κbar = 0

/-- The previous iterate, with the convention `x₋₁ = x₀` of Step 1. -/
def xPrev {N : ℕ} (x : ℕ → EuclideanSpace ℝ (Fin N)) (n : ℕ) : EuclideanSpace ℝ (Fin N) :=
  if n = 0 then x 0 else x (n - 1)

/-- The extrapolated point `xₙ + κₙ(xₙ − xₙ₋₁)` (used for `uₙ` and, with `μₙ`, for `vₙ`). -/
def extrap {N : ℕ} (x : ℕ → EuclideanSpace ℝ (Fin N)) (κ : ℕ → ℝ) (n : ℕ) :
    EuclideanSpace ℝ (Fin N) :=
  x n + κ n • (x n - xPrev x n)

/-- The objective of the subproblem in Step 2 of Algorithm 1 at a point `y`:
`fⁿ(y) + fˢ(u) + ⟨∇fˢ(u), y − u⟩ + (1/(2τ))‖y − v − τθ g‖² + (ℓ/2)‖y − u‖²`. -/
noncomputable def subObj {N : ℕ} (fs : EuclideanSpace ℝ (Fin N) → ℝ)
    (fn : EuclideanSpace ℝ (Fin N) → EReal) (ℓ τ θ : ℝ) (u v gn y : EuclideanSpace ℝ (Fin N)) :
    EReal :=
  fn y + ((fs u + ⟪gradient fs u, y - u⟫_ℝ + 1 / (2 * τ) * ‖y - v - (τ * θ) • gn‖ ^ 2
    + ℓ / 2 * ‖y - u‖ ^ 2 : ℝ) : EReal)

/-- A run of Algorithm 1 (the e-PSG algorithm, p. 9) with data `(S, fˢ, fⁿ, g, ℓ, β)` and
parameters `(δ, ζ, μ̄, κ̄)`: iterates `x`, subgradients `gs n = gₙ ∈ ∂_L g(xₙ)`, step sizes `τ`, and
extrapolation weights `κ`, `μ`. Here `x₋₁ = x₀ ∈ S ∩ dom f`, `θₙ = f(xₙ)/g(xₙ)`,
`0 < τₙ ≤ 1/max{√β θₙ/ζ, δ}`, `κₙ ∈ [0, κ̄]`, `μₙ ∈ [0, μ̄ τₙ]`, `uₙ = xₙ + κₙ(xₙ − xₙ₋₁)`,
`vₙ = xₙ + μₙ(xₙ − xₙ₋₁)`, and `xₙ₊₁` is some minimizer over `S` of the Step 2 subproblem. -/
structure IsEPSGRun {N : ℕ} (S : Set (EuclideanSpace ℝ (Fin N)))
    (fs : EuclideanSpace ℝ (Fin N) → ℝ) (fn : EuclideanSpace ℝ (Fin N) → EReal)
    (g : EuclideanSpace ℝ (Fin N) → ℝ) (ℓ β δ ζ μbar κbar : ℝ)
    (x gs : ℕ → EuclideanSpace ℝ (Fin N)) (τ κ μ : ℕ → ℝ) : Prop where
  start_mem : x 0 ∈ S
  start_dom : objF fs fn (x 0) ≠ ⊤
  subgrad : ∀ n, gs n ∈ LimitingSubdiff (fun y => (g y : EReal)) (x n)
  step_pos : ∀ n, 0 < τ n
  step_le : ∀ n,
    τ n ≤ 1 / max (Real.sqrt β * ratio (objF fs fn) g (x n) / ζ) δ
  kappa_mem : ∀ n, κ n ∈ Set.Icc 0 κbar
  mu_mem : ∀ n, μ n ∈ Set.Icc 0 (μbar * τ n)
  next_mem : ∀ n, x (n + 1) ∈ S
  next_argmin : ∀ n, ∀ y ∈ S,
    subObj fs fn ℓ (τ n) (ratio (objF fs fn) g (x n)) (extrap x κ n) (extrap x μ n) (gs n)
        (x (n + 1)) ≤
      subObj fs fn ℓ (τ n) (ratio (objF fs fn) g (x n)) (extrap x κ n) (extrap x μ n) (gs n) y

/-- The sublevel set `S₀ = {x ∈ S : f(x)/g(x) ≤ f(x₀)/g(x₀)}` of Theorem 4.5 (p. 10); points
with `f(x) = +∞` have ratio `+∞` and are excluded. -/
def S0 {N : ℕ} (S : Set (EuclideanSpace ℝ (Fin N))) (f : EuclideanSpace ℝ (Fin N) → EReal)
    (g : EuclideanSpace ℝ (Fin N) → ℝ) (x0 : EuclideanSpace ℝ (Fin N)) :
    Set (EuclideanSpace ℝ (Fin N)) :=
  {y | y ∈ S ∧ f y ≠ ⊤ ∧ ratio f g y ≤ ratio f g x0}

/-- The constant `c = ℓκ̄²/(2m) + μ̄/(2√(mM))` of (14) when (BC) holds. -/
noncomputable def cBC (ℓ μbar κbar m M : ℝ) : ℝ :=
  ℓ * κbar ^ 2 / (2 * m) + μbar / (2 * Real.sqrt (m * M))

/-- The constant `α = δ(1 − √β ζ)/(2M) − μ̄/√(mM) − ℓκ̄²/(2m)` of (14) when (BC) holds. -/
noncomputable def αBC (ℓ β δ ζ μbar κbar m M : ℝ) : ℝ :=
  δ * (1 - Real.sqrt β * ζ) / (2 * M) - μbar / Real.sqrt (m * M) - ℓ * κbar ^ 2 / (2 * m)

/-- The constant `α = δ(1 − √β ζ)/(2M′)` of (14) without (BC), where
`M′ = sup_{x ∈ S₀} g(x)`. -/
noncomputable def αNoBC {N : ℕ} (S : Set (EuclideanSpace ℝ (Fin N)))
    (f : EuclideanSpace ℝ (Fin N) → EReal) (g : EuclideanSpace ℝ (Fin N) → ℝ)
    (β δ ζ : ℝ) (x0 : EuclideanSpace ℝ (Fin N)) : ℝ :=
  δ * (1 - Real.sqrt β * ζ) / (2 * sSup (g '' S0 S f g x0))

end FracPSG.Subseq


