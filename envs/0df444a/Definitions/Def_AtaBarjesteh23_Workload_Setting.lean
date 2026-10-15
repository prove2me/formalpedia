-- Prove2me | Definitions.Def_AtaBarjesteh23_Workload_Setting
-- name    : AtaBarjesteh23_Workload_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:39:50.554293+00:00
-- url     : https://prove2.me/theorems/fe66963b-4114-463d-a24a-79c2836700d1
-- title:
--   §5–§6, pp. 14–20 — the equivalent workload formulation: primitives, h⋆, b⋆, κ, c, h, the Riccati problems (50)–(53), γ⋆, v (54), f (55), θ (56)
-- statement:
--   This file fixes the deterministic data of the equivalent workload formulation (EWF) of Ata and Barjesteh, and the objects §6 constructs to solve it.
--
--   **Primitives.** There are $K$ products. Product $k$ has mean production time $m_k$ and holding, backorder and outsourcing cost rates $h_k$, $b_k$, $r_k$. The matrix $H\in\mathbb R^{K\times K}$ is (minus one half of) the Hessian of the revenue rate at the static optimum. The workload Brownian motion has drift $\mu$ and variance $\sigma^2$.
--
--   **Standing assumptions** (the predicate `Standing`, a hypothesis of every theorem of the mission):
--   1. $K\ge 1$;
--   2. $m_k,h_k,b_k,r_k>0$ for every $k$;
--   3. $H$ is symmetric positive definite;
--   4. $\mu\ge 0$ and $\sigma>0$.
--
--   **Effective costs** ((27)–(28) and p. 15). With $a:=m'H^{-1}m$,
--   $$h^\star=\min_k \frac{h_k}{m_k},\qquad b^\star=\min_k\frac{b_k}{m_k},\qquad \kappa=\min_k\frac{r_k}{m_k},$$
--   $$c(x)=\min\{\zeta'H\zeta:\ m'\zeta=x,\ \zeta\in\mathbb R^K\},\qquad h(w)=\begin{cases}h^\star w,& w\ge 0,\\ -b^\star w,& w<0.\end{cases}$$
--
--   **Riccati problems** (p. 19). For $\gamma\ge0$ let $l_\gamma=-\frac1{b^\star}\big(\gamma+\mu\kappa+\frac a4\kappa^2\big)$ and $u_\gamma=\gamma/h^\star$. A function $v$ *solves (50)–(51)* if it is continuous on $[l_\gamma,0]$, $v(l_\gamma)=-\kappa$, and at every $w\in[l_\gamma,0]$ it has the one-sided derivative
--   $$v'(w)=\frac{a}{2\sigma^2}\big(v^2(w)-\kappa^2\big)-\frac{2\mu}{\sigma^2}\big(v(w)+\kappa\big)+\frac{2(h(l_\gamma)-h(w))}{\sigma^2};$$
--   it *solves (52)–(53)* if it is continuous on $[0,u_\gamma]$, $v(u_\gamma)=0$, and at every $w\in[0,u_\gamma]$
--   $$v'(w)=\frac{a}{2\sigma^2}v^2(w)-\frac{2\mu}{\sigma^2}v(w)+\frac{2(h(u_\gamma)-h(w))}{\sigma^2}.$$
--   $\Gamma^-$ and $\Gamma^+$ are the sets of $\gamma\ge0$ for which a solution exists; $v^-_\gamma$ and $v^+_\gamma$ denote a chosen solution.
--
--   **Constructed solution.** $\gamma^\star$ is a chosen $\gamma\in\Gamma^-\cap\Gamma^+$ with $v^-_\gamma(0)=v^+_\gamma(0)$ (Corollary 1), and
--   $$v(w)=\begin{cases}v^-_{\gamma^\star}(w),& w\le 0,\\ v^+_{\gamma^\star}(w),& w>0,\end{cases}\qquad f(w)=\int_{l_{\gamma^\star}}^w v(x)\,dx,\qquad \theta(w)=\frac a2 v(w). \tag{54–56}$$
--
--   **Bellman equations.** $(l,u,\gamma,v)$ solves (43)–(45) when $l<u$, $v\in C^1([l,u])$,
--   $$v'(w)=\frac{a}{2\sigma^2}v^2(w)-\frac{2\mu}{\sigma^2}v(w)+\frac{2(\gamma-h(w))}{\sigma^2},\quad w\in(l,u),$$
--   $v(l)=-\kappa$, $v(u)=0$, $v'(l)=v'(u)=0$. $(l,u,\gamma,f)$ solves (37)–(39) when $l<u$, $f\in C^2([l,u])$, for every $w\in(l,u)$ the minimum over $x\in\mathbb R$ of $\frac12\sigma^2f''(w)+\mu f'(w)-xf'(w)+c(x)+h(w)$ is attained and equals $\gamma$, $f'(l)=-\kappa$, $f'(u)=0$ and $f''(l)=f''(u)=0$.
--
--   These are the objects every theorem of the mission is about: the milestones show that the choices above are forced (uniqueness) and that $(l_{\gamma^\star},u_{\gamma^\star},\gamma^\star,v)$ and $f$ solve the Bellman equations.
--
--   **Formalization Note** The minima (27)–(28) are `iInf` over `Fin K` (attained because $K\ge1$). $c$ is the infimum of the set, not its closed form, which is Lemma 1. $v^\pm_\gamma$ and $\gamma^\star$ are `Classical.epsilon` choices; they are meaningful only where a solution exists, which the milestones establish (§6.3, Lemma 4, Corollary 1). The paper states that solutions of (50)–(51), (52)–(53) exist for every $\gamma\ge0$; this fails for large $\gamma$ (finite-time blow-up), so the existence sets $\Gamma^\pm$ are explicit. Derivatives at the ends of the closed intervals are one-sided (`HasDerivWithinAt`, `derivWithin`, `iteratedDerivWithin` on $[l,u]$); $C^1$ and $C^2$ up to the boundary are `ContDiffOn` on the closed interval. The requirement $l<u$ in the Bellman predicates is implicit in the paper ($C^1([l,u])$, Definition 1).
-- source:
--   Ata and Barjesteh, An Approximate Analysis of Dynamic Pricing, Outsourcing, and Scheduling Policies for a Multiclass Make-to-Stock Queue in the Heavy Traffic Regime, accepted manuscript (SSRN 3464763; published in Operations Research 71(1):341–357, 2023, doi:10.1287/opre.2022.2361), pp. 14–20, (27)–(28), Lemma 1's c, (37)–(39), (43)–(45), (49)–(56)

import Mathlib

open Matrix Set

namespace AtaBarjesteh23.Workload

/-- The primitives of the equivalent workload formulation (EWF), Ata–Barjesteh §5, pp. 14–15:
`K` products with mean production times `m k`, holding, backorder and outsourcing cost rates
`h k`, `b k`, `r k` (15), the matrix `H = -∇²Π(λ⋆)/2`, and the drift `μ` and standard deviation `σ`
of the workload Brownian motion `B`. -/
structure Model where
  K : ℕ
  m : Fin K → ℝ
  h : Fin K → ℝ
  b : Fin K → ℝ
  r : Fin K → ℝ
  H : Matrix (Fin K) (Fin K) ℝ
  μ : ℝ
  σ : ℝ

namespace Model

variable (M : Model)

/-- The standing assumptions of the paper (implicit in §3–§5): at least one product, positive
production times and cost rates, `H` symmetric positive definite (Assumption 2), `μ ≥ 0`, `σ > 0`. -/
def Standing : Prop :=
  0 < M.K ∧ (∀ k, 0 < M.m k) ∧ (∀ k, 0 < M.h k) ∧ (∀ k, 0 < M.b k) ∧ (∀ k, 0 < M.r k) ∧
    M.H.PosDef ∧ 0 ≤ M.μ ∧ 0 < M.σ

/-- `h⋆ = min_k h_k / m_k` (27). -/
noncomputable def hStar : ℝ := ⨅ k : Fin M.K, M.h k / M.m k

/-- `b⋆ = min_k b_k / m_k` (27). -/
noncomputable def bStar : ℝ := ⨅ k : Fin M.K, M.b k / M.m k

/-- `κ = min_k r_k / m_k` (28). -/
noncomputable def kappa : ℝ := ⨅ k : Fin M.K, M.r k / M.m k

/-- `a = m′H⁻¹m`. -/
noncomputable def a : ℝ := M.m ⬝ᵥ (M.H⁻¹ *ᵥ M.m)

/-- The drift cost `c(x) = min {ζ′Hζ : m′ζ = x, ζ ∈ ℝ^K}` (p. 15), defined as an infimum
(its closed form is Lemma 1). -/
noncomputable def cost (x : ℝ) : ℝ :=
  sInf {q : ℝ | ∃ ζ : Fin M.K → ℝ, M.m ⬝ᵥ ζ = x ∧ q = ζ ⬝ᵥ (M.H *ᵥ ζ)}

/-- The effective holding cost `h(w) = h⋆ w` for `w ≥ 0` and `-b⋆ w` for `w < 0` (27). -/
noncomputable def hcost (w : ℝ) : ℝ := if 0 ≤ w then M.hStar * w else -(M.bStar * w)

/-- `l_γ = -(1/b⋆)(γ + μκ + (m′H⁻¹m/4)κ²)` (p. 19). -/
noncomputable def lgam (γ : ℝ) : ℝ :=
  -(1 / M.bStar) * (γ + M.μ * M.kappa + M.a / 4 * M.kappa ^ 2)

/-- `u_γ = γ / h⋆` (p. 19). -/
noncomputable def ugam (γ : ℝ) : ℝ := γ / M.hStar

/-- Right side of the lower Riccati equation with left end `l` ((50), and Corollary 6):
`(m′H⁻¹m/2σ²)(y² - κ²) - (2μ/σ²)(y + κ) + 2(h(l) - h(w))/σ²`. -/
noncomputable def rhsLower (l w y : ℝ) : ℝ :=
  M.a / (2 * M.σ ^ 2) * (y ^ 2 - M.kappa ^ 2) - 2 * M.μ / M.σ ^ 2 * (y + M.kappa)
    + 2 * (M.hcost l - M.hcost w) / M.σ ^ 2

/-- Right side of the upper Riccati equation with right end `u` ((52)):
`(m′H⁻¹m/2σ²) y² - (2μ/σ²) y + 2(h(u) - h(w))/σ²`. -/
noncomputable def rhsUpper (u w y : ℝ) : ℝ :=
  M.a / (2 * M.σ ^ 2) * y ^ 2 - 2 * M.μ / M.σ ^ 2 * y + 2 * (M.hcost u - M.hcost w) / M.σ ^ 2

/-- `v` is a continuously differentiable solution of (50)–(51) on `[l_γ, 0]`. -/
def SolvesMinus (γ : ℝ) (v : ℝ → ℝ) : Prop :=
  ContinuousOn v (Icc (M.lgam γ) 0) ∧ v (M.lgam γ) = -M.kappa ∧
    ∀ w ∈ Icc (M.lgam γ) 0,
      HasDerivWithinAt v (M.rhsLower (M.lgam γ) w (v w)) (Icc (M.lgam γ) 0) w

/-- `v` is a continuously differentiable solution of (52)–(53) on `[0, u_γ]`. -/
def SolvesPlus (γ : ℝ) (v : ℝ → ℝ) : Prop :=
  ContinuousOn v (Icc 0 (M.ugam γ)) ∧ v (M.ugam γ) = 0 ∧
    ∀ w ∈ Icc 0 (M.ugam γ),
      HasDerivWithinAt v (M.rhsUpper (M.ugam γ) w (v w)) (Icc 0 (M.ugam γ)) w

/-- `Γ⁻`: the parameters `γ ≥ 0` for which (50)–(51) has a solution. -/
def GammaMinus : Set ℝ := {γ | 0 ≤ γ ∧ ∃ v, M.SolvesMinus γ v}

/-- `Γ⁺`: the parameters `γ ≥ 0` for which (52)–(53) has a solution. -/
def GammaPlus : Set ℝ := {γ | 0 ≤ γ ∧ ∃ v, M.SolvesPlus γ v}

/-- `v⁻_γ`, the solution of (50)–(51) (chosen; unique on `[l_γ, 0]` by the §6.3 milestone). -/
noncomputable def vMinus (γ : ℝ) : ℝ → ℝ := Classical.epsilon (M.SolvesMinus γ)

/-- `v⁺_γ`, the solution of (52)–(53) (chosen; unique on `[0, u_γ]` by the §6.3 milestone). -/
noncomputable def vPlus (γ : ℝ) : ℝ → ℝ := Classical.epsilon (M.SolvesPlus γ)

/-- `γ⋆`, the parameter with `v⁻_γ⋆(0) = v⁺_γ⋆(0)` (Corollary 1). -/
noncomputable def gammaStar : ℝ :=
  Classical.epsilon (fun γ => γ ∈ M.GammaMinus ∧ γ ∈ M.GammaPlus ∧ M.vMinus γ 0 = M.vPlus γ 0)

/-- The lower barrier `l_γ⋆`. -/
noncomputable def lStar : ℝ := M.lgam M.gammaStar

/-- The upper barrier `u_γ⋆`. -/
noncomputable def uStar : ℝ := M.ugam M.gammaStar

/-- `v(w) = v⁻_γ⋆(w)` for `w ≤ 0` and `v⁺_γ⋆(w)` for `w > 0` (54). -/
noncomputable def vStar (w : ℝ) : ℝ :=
  if w ≤ 0 then M.vMinus M.gammaStar w else M.vPlus M.gammaStar w

/-- `f(w) = ∫_{l_γ⋆}^w v(x) dx` (55). -/
noncomputable def fStar (w : ℝ) : ℝ := ∫ x in M.lStar..w, M.vStar x

/-- The candidate drift `θ(w) = (m′H⁻¹m/2) v(w)` (56). -/
noncomputable def thetaStar (w : ℝ) : ℝ := M.a / 2 * M.vStar w

/-- `(l, u, γ, v)` solves the Bellman equation in Riccati form (43)–(45), `v ∈ C¹([l, u])`. -/
def BellmanV (l u γ : ℝ) (v : ℝ → ℝ) : Prop :=
  l < u ∧ ContDiffOn ℝ 1 v (Icc l u) ∧
    (∀ w ∈ Ioo l u, deriv v w =
      M.a / (2 * M.σ ^ 2) * v w ^ 2 - 2 * M.μ / M.σ ^ 2 * v w + 2 * (γ - M.hcost w) / M.σ ^ 2) ∧
    v l = -M.kappa ∧ v u = 0 ∧
    derivWithin v (Icc l u) l = 0 ∧ derivWithin v (Icc l u) u = 0

/-- `(l, u, γ, f)` solves the Bellman equation (37) with boundary conditions (38) and smooth
pasting conditions (39), `f ∈ C²([l, u])`; the minimum in (37) is attained. -/
def BellmanF (l u γ : ℝ) (f : ℝ → ℝ) : Prop :=
  l < u ∧ ContDiffOn ℝ 2 f (Icc l u) ∧
    (∀ w ∈ Ioo l u, IsLeast (range fun x : ℝ =>
        M.σ ^ 2 / 2 * iteratedDerivWithin 2 f (Icc l u) w + M.μ * derivWithin f (Icc l u) w
          - x * derivWithin f (Icc l u) w + M.cost x + M.hcost w) γ) ∧
    derivWithin f (Icc l u) l = -M.kappa ∧ derivWithin f (Icc l u) u = 0 ∧
    iteratedDerivWithin 2 f (Icc l u) l = 0 ∧ iteratedDerivWithin 2 f (Icc l u) u = 0

end Model

end AtaBarjesteh23.Workload


