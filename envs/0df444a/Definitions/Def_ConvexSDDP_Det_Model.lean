-- Prove2me | Definitions.Def_ConvexSDDP_Det_Model
-- name    : ConvexSDDP_Det_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:08:49.828235+00:00
-- url     : https://prove2.me/theorems/45efd33c-87f7-4e1c-816d-10e884cd31bd
-- title:
--   (1), (H1), (2)–(12), pp. 4–8 — deterministic convex control problem, its Bellman functions, and runs of the cutting-plane method
-- statement:
--   The deterministic multistage convex control problem of §2 and the cutting-plane method that approximates its Bellman functions.
--
--   **Data (problem (1), p. 4).** A horizon $T\in\mathbb N$; state sets $\mathcal X_t\subseteq\mathbb R^d$; control multifunctions $\mathcal U_t:\mathbb R^d\rightrightarrows\mathbb R^p$; stage costs $C_t:\mathbb R^d\times\mathbb R^p\to\overline{\mathbb R}$; linear dynamics $f_t:\mathbb R^d\times\mathbb R^p\to\mathbb R^d$; a final cost $V_T:\mathbb R^d\to\overline{\mathbb R}$; an initial state $x_0$; and radii $\delta_t$. Write $B_t(\delta_t)=\{y\in\operatorname{dir}\operatorname{Aff}(\mathcal X_t):\ \|y\|<\delta_t\}$, where $\operatorname{dir}\operatorname{Aff}(\mathcal X_t)$ is the linear space parallel to the affine hull of $\mathcal X_t$, and $\mathcal X'_t=\mathcal X_t+B_t(\delta_t)$.
--
--   **Assumptions (H₁)** (`Model.H1`), for $t=0,\dots,T-1$: $\mathcal U_t$ is a convex multifunction with convex compact values; $C_t$ (jointly in $(x,u)$) and $V_T$ are convex, lower semicontinuous and proper; $V_T$ is finite and Lipschitz continuous on $\mathcal X_T$; and (ERCR) $\delta_t>0$, $C_t(x,u)<\infty$ for $x\in\mathcal X'_t$, $u\in\mathcal U_t(x)$, and $f_t(x,\mathcal U_t(x))\cap\mathcal X_{t+1}\neq\emptyset$ for $x\in\mathcal X'_t$. `H1` also contains the standing assumptions $T>0$, $\mathcal X_t$ convex and compact for $t=0,\dots,T$, and $x_0\in\mathcal X_0$.
--
--   **Bellman functions.** $\tilde{\mathcal U}_t(x)=\{u\in\mathcal U_t(x): f_t(x,u)\in\mathcal X_{t+1}\}$ (4). The value functions of the DP equation (2) are
--   $$V_t(x)=\begin{cases}\inf_{u\in\mathcal U_t(x)} C_t(x,u)+V_{t+1}(f_t(x,u)), & x\in\mathcal X_t,\\ +\infty,&\text{otherwise,}\end{cases}\qquad t<T,$$
--   with $V_T$ extended by $+\infty$ outside $\mathcal X_T$. Further $W_t(x,u)=C_t(x,u)+V_{t+1}(f_t(x,u))$ (8) and $\tilde V_t(x)=\inf_{u\in\mathcal U_t(x)}W_t(x,u)$ for all $x$ (11), with $\tilde V_T=V_T$.
--
--   **Cutting-plane approximations.** Given numbers $\theta^k_t\in\overline{\mathbb R}$ and vectors $\beta^k_t,x^k_t$, the approximations are $V^0_t\equiv-\infty$ and
--   $$V^{k}_t(y)=\max\big(V^{k-1}_t(y),\ \theta^k_t+\langle\beta^k_t,y-x^k_t\rangle\big)\qquad(6)$$
--   for $t<T$, and $V^k_T=V_T$ for every $k$. Then $W^k_t(x,u)=C_t(x,u)+V^k_{t+1}(f_t(x,u))$ (7) and the stage value $\hat V^k_t(y)=\inf_{u\in\tilde{\mathcal U}_t(y)}W^{k-1}_t(y,u)$ (p. 8).
--
--   **Runs (3)–(6).** A run is a family $(x^k_t,u^k_t,\theta^k_t,\beta^k_t)$ such that for every iteration $k\ge1$: $x^k_0=x_0$, and for every $t<T$, $u^k_t\in\tilde{\mathcal U}_t(x^k_t)$ minimizes $W^{k-1}_t(x^k_t,\cdot)$ over $\tilde{\mathcal U}_t(x^k_t)$, $\theta^k_t=W^{k-1}_t(x^k_t,u^k_t)$ is the optimal value (9), $x^k_{t+1}=f_t(x^k_t,u^k_t)$, and $\beta^k_t$ is a Lagrange multiplier of the constraint $x=x^k_t$ in the sense of (12): $\beta^k_t$ lies in the direction space of $\operatorname{Aff}(\mathcal X_t)$ and
--   $$\theta^k_t+\langle\beta^k_t,y-x^k_t\rangle\le\hat V^k_t(y)\qquad\text{for all }y\in\operatorname{Aff}(\mathcal X_t).$$
--
--   **Formalization Note** In Lean the iteration index is shifted: `approx k` is $V^k$, and iteration $k+1$ of `IsRun` uses `approx k` = $V^{k}$ where the paper's iteration $k$ uses $V^{k-1}$; the data of iteration 0 are unconstrained and never used. All minima are `EReal` infima ($+\infty$ over an empty set); attainment is a separate statement (Lemma 5.1). $V_t$ is defined by recursion on $T-t$. "$y\in\operatorname{Aff}(\mathcal X_t)$" in $B_t(\delta)$ and "$\beta^k_t\in\operatorname{Aff}(\mathcal X_t)$" are read as membership in the direction space `vectorSpan ℝ (X t)`, as forced by "we can always move from $\mathcal X_t$ a distance of $\delta_t/2$ in any direction" (p. 5) and Remark 2.1. A run is a predicate, not a function: every minimizer and every multiplier is allowed.
-- source:
--   Girardeau, Leclère & Philpott, On the Convergence of Decomposition Methods for Multistage Stochastic Convex Programs, author's version hal-01208295v1, pp. 4–8, problem (1), (H1), (2)–(9), (11), (12)

import Mathlib
import Definitions.Def_ConvexSDDP_Det_Basic

namespace ConvexSDDP.Det

/-- The data of the deterministic optimal control problem (1), p. 4: horizon `T`, state sets
`X t ⊆ ℝ^d`, control multifunctions `U t : ℝ^d ⇒ ℝ^p`, stage costs `C t`, linear dynamics
`f t`, final cost `VT`, initial state `x0`, and the ERCR radii `δ t` of (H1)(6). -/
structure Model (d p : ℕ) where
  T : ℕ
  X : ℕ → Set (EuclideanSpace ℝ (Fin d))
  U : ℕ → EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin p))
  C : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin p) → EReal
  f : ℕ → (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin p)) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)
  VT : EuclideanSpace ℝ (Fin d) → EReal
  x0 : EuclideanSpace ℝ (Fin d)
  δ : ℕ → ℝ

namespace Model

open Classical

noncomputable section

variable {d p : ℕ} (M : Model d p)

/-- `B_t(δ_t)` (p. 4): the vectors of the direction space of `Aff(𝒳_t)` of norm `< δ_t`. -/
def ball (t : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {y | y ∈ vectorSpan ℝ (M.X t) ∧ ‖y‖ < M.δ t}

/-- `𝒳′_t := 𝒳_t + B_t(δ_t)` ((H1)(6), p. 4). -/
def Xp (t : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {y | ∃ a ∈ M.X t, ∃ b ∈ M.ball t, y = a + b}

/-- Assumptions (H1), p. 4, together with the standing assumptions of §2 used by its proofs:
`0 < T`, every `𝒳_t` (`t ≤ T`) convex and compact, and `x0 ∈ 𝒳_0`. -/
def H1 : Prop :=
  0 < M.T ∧
  (∀ t ≤ M.T, Convex ℝ (M.X t) ∧ IsCompact (M.X t)) ∧
  M.x0 ∈ M.X 0 ∧
  -- (H1)(2): `𝒰_t` convex, with convex compact values
  (∀ t < M.T, ConvexMultifunction (M.U t) ∧ ∀ x, Convex ℝ (M.U t x) ∧ IsCompact (M.U t x)) ∧
  -- (H1)(3): `C_t` and `V_T` convex, lower semicontinuous and proper
  (∀ t < M.T, EProper (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin p) => M.C t z.1 z.2) ∧
    LowerSemicontinuous (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin p) => M.C t z.1 z.2) ∧
    EConvex (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin p) => M.C t z.1 z.2)) ∧
  (EProper M.VT ∧ LowerSemicontinuous M.VT ∧ EConvex M.VT) ∧
  -- (H1)(5): `V_T` finite valued and Lipschitz continuous on `𝒳_T`
  (∀ x ∈ M.X M.T, M.VT x ≠ ⊤) ∧
  (∃ L : ℝ, ∀ x ∈ M.X M.T, ∀ y ∈ M.X M.T,
    |(M.VT x).toReal - (M.VT y).toReal| ≤ L * ‖x - y‖) ∧
  -- (H1)(6): extended relatively complete recourse (ERCR)
  (∀ t < M.T, 0 < M.δ t ∧
    (∀ x ∈ M.Xp t, ∀ u ∈ M.U t x, M.C t x u < ⊤) ∧
    (∀ x ∈ M.Xp t, ∃ u ∈ M.U t x, M.f t (x, u) ∈ M.X (t + 1)))

/-- `𝒰̃_t(x) := {u ∈ 𝒰_t(x) | f_t(x, u) ∈ 𝒳_{t+1}}`, (4), p. 5. -/
def Ut (t : ℕ) (x : EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin p)) :=
  {u | u ∈ M.U t x ∧ M.f t (x, u) ∈ M.X (t + 1)}

/-- The Bellman value functions `V_t` of the DP equation (2), p. 5:
`V_t(x) = min_{u ∈ 𝒰_t(x)} C_t(x, u) + V_{t+1}(f_t(x, u))` for `x ∈ 𝒳_t`, `+∞` otherwise;
for `t ≥ T` it is `V_T` on `𝒳_T` and `+∞` off `𝒳_T`. The minimum is an `EReal` infimum. -/
def V (t : ℕ) (x : EuclideanSpace ℝ (Fin d)) : EReal :=
  if t < M.T then
    (if x ∈ M.X t then ⨅ u ∈ M.U t x, (M.C t x u + V (t + 1) (M.f t (x, u))) else ⊤)
  else
    (if x ∈ M.X M.T then M.VT x else ⊤)
termination_by M.T - t

/-- `W_t(x, u) := C_t(x, u) + V_{t+1}(f_t(x, u))`, (8), p. 6. -/
def W (t : ℕ) (x : EuclideanSpace ℝ (Fin d)) (u : EuclideanSpace ℝ (Fin p)) : EReal :=
  M.C t x u + M.V (t + 1) (M.f t (x, u))

/-- The extended value function `Ṽ_t(x) = inf_{u ∈ 𝒰_t(x)} W_t(x, u)` of (11), p. 7,
for all `x ∈ ℝ^d`, with `Ṽ_T = V_T`. -/
def Vtilde (t : ℕ) (x : EuclideanSpace ℝ (Fin d)) : EReal :=
  if M.T ≤ t then M.V M.T x else ⨅ u ∈ M.U t x, M.W t x u

/-- The cutting-plane approximations `V^k_t` of (6), p. 6, built from the run data
`θ k t`, `β k t`, `x k t` (iteration `k`, stage `t`): `V^0_t ≡ -∞` for `t < T`,
`V^{k+1}_t(y) = max (V^k_t(y), θ^{k+1}_t + ⟨β^{k+1}_t, y - x^{k+1}_t⟩)`, and `V^k_T = V_T`
(extended by `+∞` off `𝒳_T`) for every `k`. -/
def approx (θ : ℕ → ℕ → EReal) (β x : ℕ → ℕ → EuclideanSpace ℝ (Fin d)) :
    ℕ → ℕ → EuclideanSpace ℝ (Fin d) → EReal
  | 0, t, y => if M.T ≤ t then M.V M.T y else ⊥
  | k + 1, t, y =>
    if M.T ≤ t then M.V M.T y
    else max (approx θ β x k t y)
      (θ (k + 1) t + ((inner ℝ (β (k + 1) t) (y - x (k + 1) t) : ℝ) : EReal))

/-- `W^k_t(x, u) := C_t(x, u) + V^k_{t+1}(f_t(x, u))`, (7), p. 6. -/
def Wapprox (θ : ℕ → ℕ → EReal) (β x : ℕ → ℕ → EuclideanSpace ℝ (Fin d)) (k t : ℕ)
    (y : EuclideanSpace ℝ (Fin d)) (u : EuclideanSpace ℝ (Fin p)) : EReal :=
  M.C t y u + M.approx θ β x k (t + 1) (M.f t (y, u))

/-- The optimal value of the stage problem (5) as a function of the state,
`V̂^{k+1}_t(y) = min_{u ∈ 𝒰̃_t(y)} W^k_t(y, u)` (p. 8), as an `EReal` infimum. -/
def stageValue (θ : ℕ → ℕ → EReal) (β x : ℕ → ℕ → EuclideanSpace ℝ (Fin d)) (k t : ℕ)
    (y : EuclideanSpace ℝ (Fin d)) : EReal :=
  ⨅ u ∈ M.Ut t y, M.Wapprox θ β x k t y u

/-- A run of the cutting-plane method (3)–(6), pp. 5–6. Iteration `k + 1` (the paper's
iterations are `k ≥ 1`) starts at `x0`; at each stage `t < T` the control `u^{k+1}_t` is a
minimizer of `W^k_t(x^{k+1}_t, ·)` over `𝒰̃_t(x^{k+1}_t)`, `θ^{k+1}_t` is the optimal value,
the next state is `f_t(x^{k+1}_t, u^{k+1}_t)`, and `β^{k+1}_t` is a Lagrange multiplier of the
constraint `x = x^{k+1}_t`: a vector of the direction space of `Aff(𝒳_t)` that is a subgradient
of the stage value on `Aff(𝒳_t)` at `x^{k+1}_t`, (12). Iteration `0` is unconstrained. -/
def IsRun (x : ℕ → ℕ → EuclideanSpace ℝ (Fin d)) (u : ℕ → ℕ → EuclideanSpace ℝ (Fin p))
    (θ : ℕ → ℕ → EReal) (β : ℕ → ℕ → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ k, x (k + 1) 0 = M.x0 ∧ ∀ t < M.T,
    (u (k + 1) t ∈ M.Ut t (x (k + 1) t) ∧
      ∀ v ∈ M.Ut t (x (k + 1) t),
        M.Wapprox θ β x k t (x (k + 1) t) (u (k + 1) t) ≤ M.Wapprox θ β x k t (x (k + 1) t) v) ∧
    θ (k + 1) t = M.Wapprox θ β x k t (x (k + 1) t) (u (k + 1) t) ∧
    x (k + 1) (t + 1) = M.f t (x (k + 1) t, u (k + 1) t) ∧
    (β (k + 1) t ∈ vectorSpan ℝ (M.X t) ∧
      ∀ y ∈ affineSpan ℝ (M.X t),
        θ (k + 1) t + ((inner ℝ (β (k + 1) t) (y - x (k + 1) t) : ℝ) : EReal) ≤
          M.stageValue θ β x k t y)

end

end Model

end ConvexSDDP.Det


