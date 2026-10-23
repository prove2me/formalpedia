-- Prove2me | Definitions.Def_GreedyAdvEq_Existence_Algorithm1
-- name    : GreedyAdvEq_Existence_Algorithm1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:32:15.687547+00:00
-- url     : https://prove2.me/theorems/b2f48806-c6fd-495f-951f-1b929b47d0a7
-- title:
--   Algorithm 1, p. 20, and §7.1, §7.5, pp. 22–26 — greedy-path iteration, its output, h_ε (20), the truncations 𝕙, 𝕘, smoothings 𝔥, 𝔤 and ℋ (31)
-- statement:
--   This file encodes Algorithm 1 of Mangoubi and Vishnoi (p. 20), which computes a greedy path for the max-player, and the auxiliary functions built from it in §7.1 and §7.5.
--
--   **Eigen-oracle** (line 7). An oracle returns, at every $(x,y)$, a pair $(\lambda,v)$ with $\|v\|=1$, $\nabla_y^2 f(x,y)\,v=\lambda v$ and $\lambda\ge\lambda_{\max}(\nabla_y^2 f(x,y))-\mu_4$.
--
--   **Algorithm 1** (inputs $x, y^0, \varepsilon'$; hyperparameters $\mu_1,\mu_3$). From the current point $y^\ell$:
--   1. if $\|\nabla_y f(x,y^\ell)\|>\varepsilon'$, set $y^{\ell+1}=y^\ell+\mu_1\nabla_y f(x,y^\ell)$;
--   2. otherwise, with $(\lambda,v)$ the oracle's pair at $(x,y^\ell)$, if $\lambda>\sqrt{L\varepsilon'}$, set $y^{\ell+1}=y^\ell+\mu_3 a v$, where $a\in\{-1,1\}$ is chosen with $a\,v^\top\nabla_y f(x,y^\ell)\ge0$;
--   3. otherwise stop and return $y_{\mathrm{LocalMax}}=y^\ell$.
--
--   $\ell_{\max}$ is the first index at which the algorithm stops.
--
--   **The lower bound $h$** ((20), p. 22). For $\varepsilon^\circ>0$,
--   $$h_{\varepsilon^\circ}(x,y)=f(x,\mathcal Y),$$
--   where $\mathcal Y$ is the output of Algorithm 1 with inputs $x$, $y^0=y$, $\varepsilon'=(1+\delta)\varepsilon^\circ$.
--
--   **Polygonal path** (proof of Proposition 7.4, p. 30). Given points $p^0,p^1,\dots$, the knots are $t_\ell=\sum_{s<\ell}\|p^{s+1}-p^s\|$ and the polygonal path through $p^0,\dots,p^n$ is $\phi_t=p^\ell+(t-t_\ell)v_\ell$ on $[t_\ell,t_{\ell+1}]$, with $v_\ell=(p^{\ell+1}-p^\ell)/\|p^{\ell+1}-p^\ell\|$; it is parametrized by arc length on $[0,t_n]$.
--
--   **Truncations, smoothings and the stochastic gradient** (§7.5, p. 26). For $\hat x\in\mathbb R^d$,
--   $$\mathbb h^{\hat x}_{\varepsilon^\circ}(x,y)=\min\big(h_{\varepsilon^\circ}(x,y),h_{\varepsilon^\circ}(\hat x,y)\big),\qquad \mathbb g^{\hat x}_{\varepsilon^\circ}(x,y)=\min\big(g_{\varepsilon^\circ}(x,y),g_{\varepsilon^\circ}(\hat x,y)\big),$$
--   $\mathfrak h^{\hat x}_{\varepsilon^\circ,\sigma}(x,y)=\mathbb E_{\zeta\sim N(0,I_d)}[\mathbb h^{\hat x}_{\varepsilon^\circ}(x+\sigma\zeta,y)]$, $\mathfrak g^{\hat x}_{\varepsilon^\circ,\sigma}(x,y)=\mathbb E_{\zeta}[\mathbb g^{\hat x}_{\varepsilon^\circ}(x+\sigma\zeta,y)]$, and
--   $$\mathcal H^{\hat x}_{\varepsilon^\circ}(x,y)=\frac{\zeta}{\sigma}\Big(\mathbb h^{\hat x}_{\varepsilon^\circ}(x+\sigma\zeta,y)-\mathbb h^{\hat x}_{\varepsilon^\circ}(x,y)\Big),\qquad\zeta\sim N(0,I_d). \tag{31}$$
--
--   These are the objects of the milestones: Algorithm 1's output is an approximate local maximum (Lemma 7.2), its path is greedy (Proposition 7.4), $h\le g$ (Proposition 7.5), and the smoothed truncated $h$ controls the smoothed truncated $g$ (Lemma 7.3).
--
--   **Formalization Note.** The oracle is a function $(x,y)\mapsto(\lambda,v)$; "$\lambda\ge\lambda_{\max}-\mu_4$" is the quadratic-form bound $u^\top\nabla_y^2f\,u\le(\lambda+\mu_4)\|u\|^2$. The sign in line 9 is taken in $\{-1,1\}$ as on p. 11 (Lean's `Real.sign 0 = 0` would stall the algorithm). The iterates are defined by recursion; once stopped the point is kept. If Algorithm 1 never stops, `alg1Len` is $0$ and the output is $y^0$ (a junk value); every milestone that reads the output either assumes or proves termination. The hyperparameters $\delta,\mu_1,\mu_3,\mu_4$ are parameters, not §7.1's printed formulas; each milestone assumes exactly the inequalities its proof uses. $\mathcal H$ is a function of $\zeta$; expectations are integrals against `stdGaussian`.
-- source:
--   Mangoubi, Vishnoi, Greedy Adversarial Equilibrium, arXiv:2006.12363v4, p. 20, Algorithm 1; p. 22, (20); p. 26, §7.5, (31); p. 30, proof of Proposition 7.4

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing
import Definitions.Def_GreedyAdvEq_Existence_Setting

namespace GreedyAdvEq.Existence

open MeasureTheory ProbabilityTheory

/-- Line 7 of Algorithm 1, p. 20: `Eig x y = (λ, v)` is an eigenvalue–eigenvector pair of
`∇²_y f(x, y)` with `‖v‖ = 1` and `λ ≥ λ_max(∇²_y f(x, y)) − μ₄`, for every `(x, y)`. -/
def IsEigOracle {d : ℕ} (f : E d → E d → ℝ) (Eig : E d → E d → ℝ × E d) (μ₄ : ℝ) : Prop :=
  ∀ x y : E d,
    ‖(Eig x y).2‖ = 1 ∧
    (∀ w : E d, hessY f x y (Eig x y).2 w = (Eig x y).1 * inner ℝ (Eig x y).2 w) ∧
    ∀ u : E d, hessY f x y u u ≤ ((Eig x y).1 + μ₄) * ‖u‖ ^ 2

/-- The stopping test of Algorithm 1 at the current point `y` (lines 3 and 8 both fail):
`‖∇_y f(x, y)‖ ≤ ε′` and `λ ≤ √(Lε′)`. -/
def alg1Stop {d : ℕ} (f : E d → E d → ℝ) (L : ℝ) (Eig : E d → E d → ℝ × E d)
    (x : E d) (ε' : ℝ) (y : E d) : Prop :=
  ‖gradY f x y‖ ≤ ε' ∧ (Eig x y).1 ≤ Real.sqrt (L * ε')

/-- One pass of the While loop of Algorithm 1 (lines 3–13): a gradient step of size `μ₁` if
`‖∇_y f(x, y)‖ > ε′`, otherwise a step `μ₃ a v` along the oracle's eigenvector if `λ > √(Lε′)`,
where `a ∈ {−1, 1}` has `a vᵀ∇_y f(x, y) ≥ 0` (p. 11); otherwise the point is kept (stop). -/
noncomputable def alg1Step {d : ℕ} (f : E d → E d → ℝ) (L : ℝ) (Eig : E d → E d → ℝ × E d)
    (μ₁ μ₃ : ℝ) (x : E d) (ε' : ℝ) (y : E d) : E d :=
  if ε' < ‖gradY f x y‖ then y + μ₁ • gradY f x y
  else if Real.sqrt (L * ε') < (Eig x y).1 then
    y + (μ₃ * (if 0 ≤ inner ℝ (gradY f x y) (Eig x y).2 then (1 : ℝ) else -1)) • (Eig x y).2
  else y

/-- The iterates `y^ℓ` of Algorithm 1 with inputs `x, y⁰, ε′` (once stopped, the point is kept). -/
noncomputable def alg1Iter {d : ℕ} (f : E d → E d → ℝ) (L : ℝ) (Eig : E d → E d → ℝ × E d)
    (μ₁ μ₃ : ℝ) (x y0 : E d) (ε' : ℝ) : ℕ → E d
  | 0 => y0
  | ℓ + 1 => alg1Step f L Eig μ₁ μ₃ x ε' (alg1Iter f L Eig μ₁ μ₃ x y0 ε' ℓ)

/-- Algorithm 1 terminates: the stopping test holds at some iterate. -/
def Alg1Terminates {d : ℕ} (f : E d → E d → ℝ) (L : ℝ) (Eig : E d → E d → ℝ × E d)
    (μ₁ μ₃ : ℝ) (x y0 : E d) (ε' : ℝ) : Prop :=
  ∃ ℓ : ℕ, alg1Stop f L Eig x ε' (alg1Iter f L Eig μ₁ μ₃ x y0 ε' ℓ)

/-- `ℓ_max`, the number of iterations of the While loop of Algorithm 1 (the first stopping index);
`0` if Algorithm 1 does not terminate. -/
noncomputable def alg1Len {d : ℕ} (f : E d → E d → ℝ) (L : ℝ) (Eig : E d → E d → ℝ × E d)
    (μ₁ μ₃ : ℝ) (x y0 : E d) (ε' : ℝ) : ℕ := by
  classical
  exact if h : Alg1Terminates f L Eig μ₁ μ₃ x y0 ε' then Nat.find h else 0

/-- The output `y_LocalMax = y^{ℓ_max}` of Algorithm 1 (line 14); `y⁰` if it does not terminate. -/
noncomputable def alg1Out {d : ℕ} (f : E d → E d → ℝ) (L : ℝ) (Eig : E d → E d → ℝ × E d)
    (μ₁ μ₃ : ℝ) (x y0 : E d) (ε' : ℝ) : E d :=
  alg1Iter f L Eig μ₁ μ₃ x y0 ε' (alg1Len f L Eig μ₁ μ₃ x y0 ε')

/-- (20), p. 22: `h_{ε°}(x, y) = f(x, 𝒴)`, where `𝒴` is the output of Algorithm 1 with inputs
`x ← x`, `y⁰ ← y`, `ε′ ← (1 + δ) ε°`. -/
noncomputable def hEps {d : ℕ} (f : E d → E d → ℝ) (L : ℝ) (Eig : E d → E d → ℝ × E d)
    (δ μ₁ μ₃ ε : ℝ) (x y : E d) : ℝ :=
  f x (alg1Out f L Eig μ₁ μ₃ x y ((1 + δ) * ε))

/-- The arc-length knots `t_ℓ = Σ_{s<ℓ} ‖p^{s+1} − p^s‖` of the polygonal path through `p⁰, p¹, …`. -/
noncomputable def knot {d : ℕ} (p : ℕ → E d) (ℓ : ℕ) : ℝ :=
  ∑ s ∈ Finset.range ℓ, ‖p (s + 1) - p s‖

/-- The unit-speed polygonal path through `p⁰, …, pⁿ` (segments `[p^ℓ, p^{ℓ+1}]`), parametrized by
arc length: on `[t_ℓ, t_{ℓ+1}]` it is `p^ℓ + (t − t_ℓ) v_ℓ` with `v_ℓ = (p^{ℓ+1} − p^ℓ)/‖p^{ℓ+1} − p^ℓ‖`
(proof of Proposition 7.4, p. 30). -/
noncomputable def polygonalPath {d : ℕ} (p : ℕ → E d) (n : ℕ) (t : ℝ) : E d :=
  p 0 + ∑ s ∈ Finset.range n,
    (max 0 (min (t - knot p s) ‖p (s + 1) - p s‖) / ‖p (s + 1) - p s‖) • (p (s + 1) - p s)

/-- §7.5, p. 26: `𝕙^{x̂}_{ε°}(x, y) = min(h_{ε°}(x, y), h_{ε°}(x̂, y))`. -/
noncomputable def hTrunc {d : ℕ} (f : E d → E d → ℝ) (L : ℝ) (Eig : E d → E d → ℝ × E d)
    (δ μ₁ μ₃ ε : ℝ) (xh x y : E d) : ℝ :=
  min (hEps f L Eig δ μ₁ μ₃ ε x y) (hEps f L Eig δ μ₁ μ₃ ε xh y)

/-- §7.5, p. 26: `𝕘^{x̂}_{ε°}(x, y) = min(g_{ε°}(x, y), g_{ε°}(x̂, y))`. -/
noncomputable def gTrunc {d : ℕ} (f : E d → E d → ℝ) (L ε : ℝ) (xh x y : E d) : ℝ :=
  min (greedyMax f L ε x y) (greedyMax f L ε xh y)

/-- §7.5, p. 26: `𝔥^{x̂}_{ε°,σ}(x, y) = E_{ζ∼N(0,I_d)}[𝕙^{x̂}_{ε°}(x + σζ, y)]`. -/
noncomputable def hSmooth {d : ℕ} (f : E d → E d → ℝ) (L : ℝ) (Eig : E d → E d → ℝ × E d)
    (δ μ₁ μ₃ ε σ : ℝ) (xh x y : E d) : ℝ :=
  RandomGradFree.Shared.smoothing (fun z => hTrunc f L Eig δ μ₁ μ₃ ε xh z y) σ x

/-- §7.5, p. 26: `𝔤^{x̂}_{ε°,σ}(x, y) = E_{ζ∼N(0,I_d)}[𝕘^{x̂}_{ε°}(x + σζ, y)]`. -/
noncomputable def gSmooth {d : ℕ} (f : E d → E d → ℝ) (L ε σ : ℝ) (xh x y : E d) : ℝ :=
  RandomGradFree.Shared.smoothing (fun z => gTrunc f L ε xh z y) σ x

/-- (31), p. 26: the stochastic gradient
`ℋ^{x̂}_{ε°}(x, y) = (ζ/σ) (𝕙^{x̂}_{ε°}(x + σζ, y) − 𝕙^{x̂}_{ε°}(x, y))`, as a function of `ζ`. -/
noncomputable def stochGrad {d : ℕ} (f : E d → E d → ℝ) (L : ℝ) (Eig : E d → E d → ℝ × E d)
    (δ μ₁ μ₃ ε σ : ℝ) (xh x y ζ : E d) : E d :=
  ((1 / σ) * (hTrunc f L Eig δ μ₁ μ₃ ε xh (x + σ • ζ) y - hTrunc f L Eig δ μ₁ μ₃ ε xh x y)) • ζ

end GreedyAdvEq.Existence


