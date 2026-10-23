-- Prove2me | Definitions.Def_DecBilevel_SLDBO_Setting
-- name    : DecBilevel_SLDBO_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:04:45.462552+00:00
-- url     : https://prove2.me/theorems/c8833f63-417b-4d0c-a837-e0f6ddc0df2e
-- title:
--   Problem (6), (7), Assumptions 2.1–2.2, (8), BOX 1, Algorithm 1, pp. 3–6 — decentralized bilevel problem, hypergradient and the SLDBO run
-- statement:
--   This module fixes the objects of Dong, Ma, Yang and Yin's decentralized bilevel problem and of their single-loop algorithm SLDBO.
--
--   1. **Problem (6).** There are $n$ agents. Agent $i$ holds an upper-level function $F_i$ and a lower-level function $f_i$ on $\mathbb R^p\times\mathbb R^q$ (both spaces carry the Euclidean norm). With $F=\frac1n\sum_i F_i$ and $f=\frac1n\sum_i f_i$, the problem is
--   $$\min_{x\in\mathbb R^p}\ \Phi(x)=F(x,y^*(x))=\frac1n\sum_{i=1}^n F_i(x,y^*(x))\quad\text{s.t.}\quad y^*(x)=\arg\min_{y\in\mathbb R^q} f(x,y).$$
--   The solution map $y^*$ is a parameter of the module; the theorems that use it assume that $y^*(x)$ minimizes $f(x,\cdot)$ for every $x$.
--   2. **Derivatives.** $\nabla_1 g(x,y)$ and $\nabla_2 g(x,y)$ are the gradients of $g$ in $x$ and in $y$. $\nabla^2_{22}g(x,y)$ is the derivative in $y$ of $\nabla_2 g$, a linear map $\mathbb R^q\to\mathbb R^q$. $\nabla^2_{12}g(x,y)$ is the derivative in $y$ of $\nabla_1 g$, a linear map $\mathbb R^q\to\mathbb R^p$.
--   3. **Hypergradient (7).** With $v^*(x)=\big[\tfrac1n\sum_i\nabla^2_{22}f_i(x,y^*(x))\big]^{-1}\tfrac1n\sum_i\nabla_2F_i(x,y^*(x))$ (p. 7),
--   $$\nabla\Phi(x)=\frac1n\sum_{i=1}^n\nabla_1F_i(x,y^*(x))-\Big[\frac1n\sum_{i=1}^n\nabla^2_{12}f_i(x,y^*(x))\Big]v^*(x).$$
--   In the module this formula is a definition, `hypergrad`. That it is the gradient of $\Phi$ is the separate milestone (7).
--   4. **Assumption 2.1.** The constants are $\sigma>0$ and $L_{F,0},L_{F,1},L_{f,1},L_{f,2}\ge0$. For every $i$: (a) $f_i(x,\cdot)$ is $\sigma$-strongly convex for every $x$; (b) $F_i$ is differentiable and $L_{F,0}$-Lipschitz, and $\nabla F_i=(\nabla_1F_i,\nabla_2F_i)$ is $L_{F,1}$-Lipschitz; (c) $f_i$ is twice continuously differentiable, $\nabla f_i$ is $L_{f,1}$-Lipschitz, and the Hessian blocks $\nabla^2_{12}f_i$ and $\nabla^2_{22}f_i$ are $L_{f,2}$-Lipschitz in the operator norm. All Lipschitz conditions use the Euclidean distance $\sqrt{\|x-x'\|^2+\|y-y'\|^2}$ on $\mathbb R^p\times\mathbb R^q$.
--   5. **Assumption 2.2.** The weight matrix $W=(w_{ij})\in\mathbb R^{n\times n}$ is nonnegative and symmetric with $W\mathbf 1_n=\mathbf 1_n$. The number $\rho\in[0,1)$ satisfies $\|Wu\|\le\rho\|u\|$ for every $u\in\mathbb R^n$ with $\sum_iu_i=0$.
--   6. **Constants (8) and (17).** $r_v=L_{F,0}/\sigma$, $L_1=L_{F,1}+L_{f,2}r_v$, $L_v=L_1(1+L_{f,1}/\sigma)$, $L_\Phi=L_1(1+L_{f,1}/\sigma)^2$, $C_1=3\max\{(L_{F,1}+r_vL_{f,2})^2,L_{f,1}^2\}$ and $C_2=L_{f,1}^2$.
--   7. **Projection.** $\mathcal P_r[z]=z$ if $\|z\|\le r$ and $\mathcal P_r[z]=\frac{r}{\|z\|}z$ otherwise. For $r\ge0$ this is $\arg\min_{\|z'\|\le r}\|z'-z\|$, the Euclidean projection onto the closed ball of radius $r$.
--   8. **Algorithm 1 with BOX 1.** Every agent starts at common points $x^0,y^0,v^0$, with $t^{-1}=d^{-1}=0$. For $k\ge0$ and every agent $i$,
--   $$d^k_{y,i}=\nabla_2f_i(x^k_i,y^k_i),\quad d^k_{v,i}=\nabla_2F_i(x^k_i,y^k_i)-\nabla^2_{22}f_i(x^k_i,y^k_i)v^k_i,\quad d^k_{x,i}=\nabla_1F_i(x^k_i,y^k_i)-\nabla^2_{12}f_i(x^k_i,y^k_i)v^k_i,$$
--   $$t^k_{\star,i}=\sum_jw_{ij}t^{k-1}_{\star,j}+d^k_{\star,i}-d^{k-1}_{\star,i}\quad(\star\in\{x,y,v\}),$$
--   $$y^{k+1}_i=\sum_jw_{ij}(y^k_j-\beta t^k_{y,j}),\quad v^{k+1}_i=\mathcal P_{r}\Big[\sum_jw_{ij}(v^k_j+\eta t^k_{v,j})\Big],\quad x^{k+1}_i=\sum_jw_{ij}(x^k_j-\alpha t^k_{x,j}).$$
--   The state at index $k$ holds $(x^k,y^k,v^k,t^{k-1},d^{k-1})$, so $t^k$ and $d^k$ are read off the state at index $k+1$. Averages are $\bar z=\frac1n\sum_iz_i$.
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note.** Vectors live in `EuclideanSpace ℝ (Fin d)`. Three choices differ from the page, and none of them weakens a theorem. First, the paper requires the full Hessian $\nabla^2f_i$ to be $L_{f,2}$-Lipschitz in the Frobenius norm. Here only the two blocks the paper uses are required to be Lipschitz, and in the operator norm, which is a weaker hypothesis. Second, the paper defines $\rho=\max\{|\lambda_2|,|\lambda_n|\}$ with $1=\lambda_1>\lambda_2$. Here $\rho$ is any bound of $W$ on $\mathbf 1_n^\perp$, and the paper's $\rho$ is the least one. The clause "$w_{ij}=0$ when agents $i,j$ are not connected" only names the graph, so it is dropped. Third, $L_\Phi$ is (8) with the printed $L_{F,0}^2$ corrected to $L_{F,0}$ (see the milestone on the Lipschitz continuity of $\nabla\Phi$). BOX 1's points $x^0_i=x^{-1}_i$, $y^0_i=y^{-1}_i$, $v^0_i=v^{-1}_i$ are the common initial points; the paper's equalities hold because $t^{-1}=0$ and $\|v^{-1}\|\le r_v$, which the theorems assume. $v^*$ uses `ContinuousLinearMap.inverse`, whose value on a non-invertible map is $0$; under Assumption 2.1(a) the averaged $\nabla^2_{22}f$ is invertible.
-- source:
--   Dong, Ma, Yang, Yin, A Single-Loop Algorithm for Decentralized Bilevel Optimization, arXiv:2311.08945v3, pp. 3–7, (6), (7), Assumptions 2.1–2.2, (8), BOX 1, Algorithm 1, v*(x) p. 7, (16)–(17) p. 13

import Mathlib

namespace DecBilevel.SLDBO

/-- The Euclidean space `ℝ^d` (with the `ℓ₂` norm). -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

section Derivatives

variable {p q : ℕ}

/-- `∇₁g(x, y)`: the gradient of `x ↦ g(x, y)` at `x` (Notation, p. 4). -/
noncomputable def grad1 (g : E p → E q → ℝ) (x : E p) (y : E q) : E p :=
  gradient (fun x' => g x' y) x

/-- `∇₂g(x, y)`: the gradient of `y ↦ g(x, y)` at `y` (Notation, p. 4). -/
noncomputable def grad2 (g : E p → E q → ℝ) (x : E p) (y : E q) : E q :=
  gradient (fun y' => g x y') y

/-- `∇²₂₂g(x, y)`: the Hessian of `g` with respect to `y`, i.e. the derivative in `y` of `∇₂g`
(Notation, p. 4), as a linear map `ℝ^q → ℝ^q`. -/
noncomputable def hess22 (g : E p → E q → ℝ) (x : E p) (y : E q) : E q →L[ℝ] E q :=
  fderiv ℝ (fun y' => grad2 g x y') y

/-- `∇²₁₂g(x, y)`: the Jacobian of `∇₁g` with respect to `y` (Notation, p. 4), as a linear map
`ℝ^q → ℝ^p`. -/
noncomputable def hess12 (g : E p → E q → ℝ) (x : E p) (y : E q) : E q →L[ℝ] E p :=
  fderiv ℝ (fun y' => grad1 g x y') y

/-- The Euclidean distance `√(‖x − x'‖² + ‖y − y'‖²)` between `(x, y)` and `(x', y')` in
`ℝ^p × ℝ^q` (the `ℓ₂` norm of the stacked vector, not Lean's sup norm on a product). -/
noncomputable def pdist (x x' : E p) (y y' : E q) : ℝ :=
  Real.sqrt (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2)

end Derivatives

section Averages

variable {n p q : ℕ}

/-- The average `(1/n) ∑ᵢ zᵢ` of `n` vectors. -/
noncomputable def avg {d : ℕ} (z : Fin n → E d) : E d := (1 / (n : ℝ)) • ∑ i, z i

/-- The lower-level objective `f(x, y) = (1/n) ∑ᵢ fᵢ(x, y)` of problem (6). -/
noncomputable def avgf (f : Fin n → E p → E q → ℝ) (x : E p) (y : E q) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, f i x y

/-- `(1/n) ∑ᵢ ∇₁Fᵢ(x, y)`. -/
noncomputable def avgGrad1 (F : Fin n → E p → E q → ℝ) (x : E p) (y : E q) : E p :=
  (1 / (n : ℝ)) • ∑ i, grad1 (F i) x y

/-- `(1/n) ∑ᵢ ∇₂Fᵢ(x, y)`. -/
noncomputable def avgGrad2 (F : Fin n → E p → E q → ℝ) (x : E p) (y : E q) : E q :=
  (1 / (n : ℝ)) • ∑ i, grad2 (F i) x y

/-- `(1/n) ∑ᵢ ∇²₂₂fᵢ(x, y)`. -/
noncomputable def avgHess22 (f : Fin n → E p → E q → ℝ) (x : E p) (y : E q) : E q →L[ℝ] E q :=
  (1 / (n : ℝ)) • ∑ i, hess22 (f i) x y

/-- `(1/n) ∑ᵢ ∇²₁₂fᵢ(x, y)`. -/
noncomputable def avgHess12 (f : Fin n → E p → E q → ℝ) (x : E p) (y : E q) : E q →L[ℝ] E p :=
  (1 / (n : ℝ)) • ∑ i, hess12 (f i) x y

/-- The upper-level objective `Φ(x) = F(x, y*(x)) = (1/n) ∑ᵢ Fᵢ(x, y*(x))` of problem (6), for a
given lower-level solution map `ystar`. -/
noncomputable def Phi (F : Fin n → E p → E q → ℝ) (ystar : E p → E q) (x : E p) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, F i x (ystar x)

/-- `v*(x) = [∇²₂₂f(x, y*(x))]⁻¹ ∇₂F(x, y*(x))` (p. 7), with `f, F` the averages, through
`ContinuousLinearMap.inverse`. -/
noncomputable def vstar (F f : Fin n → E p → E q → ℝ) (ystar : E p → E q) (x : E p) : E q :=
  (avgHess22 f x (ystar x)).inverse (avgGrad2 F x (ystar x))

/-- The hypergradient formula (7):
`∇Φ(x) = (1/n)∑∇₁Fᵢ(x,y*(x)) − [(1/n)∑∇²₁₂fᵢ(x,y*(x))][(1/n)∑∇²₂₂fᵢ(x,y*(x))]⁻¹(1/n)∑∇₂Fᵢ(x,y*(x))`. -/
noncomputable def hypergrad (F f : Fin n → E p → E q → ℝ) (ystar : E p → E q) (x : E p) : E p :=
  avgGrad1 F x (ystar x) - avgHess12 f x (ystar x) (vstar F f ystar x)

end Averages

/-- Assumption 2.1 (p. 5) for `Fᵢ, fᵢ : ℝ^p × ℝ^q → ℝ`, `i = 1, …, n`, with constants
`σ, L_{F,0}, L_{F,1}, L_{f,1}, L_{f,2}`. Lipschitz conditions are with respect to the Euclidean
norm of `(x, y)`; the Hessian condition is imposed on the two blocks `∇²₁₂fᵢ`, `∇²₂₂fᵢ` in the
operator norm. -/
structure Assumption21 {n p q : ℕ} (F f : Fin n → E p → E q → ℝ) (σ LF0 LF1 Lf1 Lf2 : ℝ) :
    Prop where
  sigma_pos : 0 < σ
  LF0_nonneg : 0 ≤ LF0
  LF1_nonneg : 0 ≤ LF1
  Lf1_nonneg : 0 ≤ Lf1
  Lf2_nonneg : 0 ≤ Lf2
  /-- (a) for every fixed `x`, `fᵢ(x, ·)` is `σ`-strongly convex. -/
  strongConvex : ∀ i x, StrongConvexOn Set.univ σ (f i x)
  /-- (b) `Fᵢ` is differentiable on `ℝ^p × ℝ^q`. -/
  F_diff : ∀ i, Differentiable ℝ (fun z : E p × E q => F i z.1 z.2)
  /-- (b) `Fᵢ` is `L_{F,0}`-Lipschitz. -/
  F_lip : ∀ i x x' y y', |F i x y - F i x' y'| ≤ LF0 * pdist x x' y y'
  /-- (b) `∇Fᵢ = (∇₁Fᵢ, ∇₂Fᵢ)` is `L_{F,1}`-Lipschitz. -/
  gradF_lip : ∀ i x x' y y',
    Real.sqrt (‖grad1 (F i) x y - grad1 (F i) x' y'‖ ^ 2 +
      ‖grad2 (F i) x y - grad2 (F i) x' y'‖ ^ 2) ≤ LF1 * pdist x x' y y'
  /-- (c) `fᵢ` is twice continuously differentiable. -/
  f_contDiff : ∀ i, ContDiff ℝ 2 (fun z : E p × E q => f i z.1 z.2)
  /-- (c) `∇fᵢ = (∇₁fᵢ, ∇₂fᵢ)` is `L_{f,1}`-Lipschitz. -/
  gradf_lip : ∀ i x x' y y',
    Real.sqrt (‖grad1 (f i) x y - grad1 (f i) x' y'‖ ^ 2 +
      ‖grad2 (f i) x y - grad2 (f i) x' y'‖ ^ 2) ≤ Lf1 * pdist x x' y y'
  /-- (c) the Hessian block `∇²₁₂fᵢ` is `L_{f,2}`-Lipschitz (operator norm). -/
  hess12_lip : ∀ i x x' y y', ‖hess12 (f i) x y - hess12 (f i) x' y'‖ ≤ Lf2 * pdist x x' y y'
  /-- (c) the Hessian block `∇²₂₂fᵢ` is `L_{f,2}`-Lipschitz (operator norm). -/
  hess22_lip : ∀ i x x' y y', ‖hess22 (f i) x y - hess22 (f i) x' y'‖ ≤ Lf2 * pdist x x' y y'

/-- Assumption 2.2 (p. 5): `W` is nonnegative, symmetric and doubly stochastic, and `ρ ∈ [0, 1)`
bounds the action of `W` on the consensus-orthogonal subspace `1ₙ^⊥`:
`‖Wu‖₂ ≤ ρ‖u‖₂` whenever `∑ᵢ uᵢ = 0`. (The paper's `ρ = max{|λ₂|, |λₙ|}` is the least such bound.) -/
structure Assumption22 {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ W i j
  symm : W.transpose = W
  row_sum : ∀ i, ∑ j, W i j = 1
  rho_nonneg : 0 ≤ ρ
  rho_lt_one : ρ < 1
  contract : ∀ u : Fin n → ℝ, ∑ i, u i = 0 →
    Real.sqrt (∑ i, (∑ j, W i j * u j) ^ 2) ≤ ρ * Real.sqrt (∑ i, u i ^ 2)

section Constants

/-- `r_v := L_{F,0}/σ` ((8), p. 5). -/
noncomputable def rv (σ LF0 : ℝ) : ℝ := LF0 / σ

/-- `L₁ := L_{F,1} + L_{f,2} r_v` ((8), p. 5). -/
noncomputable def L1 (σ LF0 LF1 Lf2 : ℝ) : ℝ := LF1 + Lf2 * rv σ LF0

/-- `L_v := (L_{F,1} + L_{f,2} r_v)(1 + L_{f,1}/σ)` ((8), p. 5). -/
noncomputable def Lv (σ LF0 LF1 Lf1 Lf2 : ℝ) : ℝ := L1 σ LF0 LF1 Lf2 * (1 + Lf1 / σ)

/-- The Lipschitz constant of `∇Φ`, `L_Φ := L₁ (1 + L_{f,1}/σ)²`. This is (8)'s `L_Φ` with the
printed `L²_{F,0}` corrected to `L_{F,0}` (see the natural-language statement). -/
noncomputable def LPhi (σ LF0 LF1 Lf1 Lf2 : ℝ) : ℝ := L1 σ LF0 LF1 Lf2 * (1 + Lf1 / σ) ^ 2

/-- `C₁ := 3 max{(L_{F,1} + r_v L_{f,2})², L²_{f,1}}` ((17), p. 13). -/
noncomputable def C1 (σ LF0 LF1 Lf1 Lf2 : ℝ) : ℝ :=
  3 * max ((LF1 + rv σ LF0 * Lf2) ^ 2) (Lf1 ^ 2)

/-- `C₂ := L²_{f,1}` ((17), p. 13). -/
noncomputable def C2 (Lf1 : ℝ) : ℝ := Lf1 ^ 2

end Constants

/-- `P_r[z] := argmin_{‖z'‖ ≤ r} ‖z' − z‖` (p. 5), in closed form for `r ≥ 0`. -/
noncomputable def ballProj {d : ℕ} (r : ℝ) (z : E d) : E d :=
  if ‖z‖ ≤ r then z else (r / ‖z‖) • z

/-- The state of Algorithm 1 at index `k`: the local iterates `xᵢᵏ, yᵢᵏ, vᵢᵏ` and the previous
trackers `t^{k−1}_{x,i}, t^{k−1}_{y,i}, t^{k−1}_{v,i}` and directions
`d^{k−1}_{x,i}, d^{k−1}_{y,i}, d^{k−1}_{v,i}` of every agent `i`. -/
structure State (n p q : ℕ) where
  x : Fin n → E p
  y : Fin n → E q
  v : Fin n → E q
  tx : Fin n → E p
  ty : Fin n → E q
  tv : Fin n → E q
  dx : Fin n → E p
  dy : Fin n → E q
  dv : Fin n → E q

section Algorithm

variable {n p q : ℕ}

/-- One iteration `k → k + 1` of Algorithm 1 (p. 6) with mixing matrix `W`, step sizes `α, β, η`
and projection radius `r`: the directions (9)–(11), the trackers and updates (12)–(14). -/
noncomputable def step (W : Matrix (Fin n) (Fin n) ℝ) (F f : Fin n → E p → E q → ℝ)
    (α β η r : ℝ) (s : State n p q) : State n p q :=
  -- directions (9)–(11) at the current iterates
  let dy : Fin n → E q := fun i => grad2 (f i) (s.x i) (s.y i)
  let dv : Fin n → E q := fun i =>
    grad2 (F i) (s.x i) (s.y i) - hess22 (f i) (s.x i) (s.y i) (s.v i)
  let dx : Fin n → E p := fun i =>
    grad1 (F i) (s.x i) (s.y i) - hess12 (f i) (s.x i) (s.y i) (s.v i)
  -- gradient tracking (12)–(14)
  let ty : Fin n → E q := fun i => (∑ j, W i j • s.ty j) + dy i - s.dy i
  let tv : Fin n → E q := fun i => (∑ j, W i j • s.tv j) + dv i - s.dv i
  let tx : Fin n → E p := fun i => (∑ j, W i j • s.tx j) + dx i - s.dx i
  { x := fun i => ∑ j, W i j • (s.x j - α • tx j)
    y := fun i => ∑ j, W i j • (s.y j - β • ty j)
    v := fun i => ballProj r (∑ j, W i j • (s.v j + η • tv j))
    tx := tx, ty := ty, tv := tv, dx := dx, dy := dy, dv := dv }

/-- The sequence of states generated by Algorithm 1 from BOX 1 (p. 6): every agent starts at the
common points `x⁰, y⁰, v⁰`, and `t^{−1} = d^{−1} = 0`. `run … k` holds
`(xᵏ, yᵏ, vᵏ, t^{k−1}, d^{k−1})`. -/
noncomputable def run (W : Matrix (Fin n) (Fin n) ℝ) (F f : Fin n → E p → E q → ℝ)
    (α β η r : ℝ) (x0 : E p) (y0 v0 : E q) : ℕ → State n p q
  | 0 => { x := fun _ => x0, y := fun _ => y0, v := fun _ => v0,
           tx := 0, ty := 0, tv := 0, dx := 0, dy := 0, dv := 0 }
  | k + 1 => step W F f α β η r (run W F f α β η r x0 y0 v0 k)

/-- The tracker `t^k_{x,i}` of a run `s` (computed in step `k → k + 1`). -/
def trX (s : ℕ → State n p q) (k : ℕ) : Fin n → E p := (s (k + 1)).tx
/-- The tracker `t^k_{y,i}` of a run `s`. -/
def trY (s : ℕ → State n p q) (k : ℕ) : Fin n → E q := (s (k + 1)).ty
/-- The tracker `t^k_{v,i}` of a run `s`. -/
def trV (s : ℕ → State n p q) (k : ℕ) : Fin n → E q := (s (k + 1)).tv
/-- The direction `d^k_{x,i}` (11) of a run `s`. -/
def dirX (s : ℕ → State n p q) (k : ℕ) : Fin n → E p := (s (k + 1)).dx
/-- The direction `d^k_{y,i}` (9) of a run `s`. -/
def dirY (s : ℕ → State n p q) (k : ℕ) : Fin n → E q := (s (k + 1)).dy
/-- The direction `d^k_{v,i}` (10) of a run `s`. -/
def dirV (s : ℕ → State n p q) (k : ℕ) : Fin n → E q := (s (k + 1)).dv

end Algorithm

end DecBilevel.SLDBO


