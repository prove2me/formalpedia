-- Prove2me | Definitions.Def_DirKKTBilevel_VP_Model
-- name    : DirKKTBilevel_VP_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:49.298196+00:00
-- url     : https://prove2.me/theorems/b30ed7d6-d373-4424-bad5-5f43a35e7f1f
-- title:
--   §1–§3, §5, pp. 2–9, 22 — directional neighbourhoods, directional subdifferentials, directional calmness, the bilevel program and its value-function reformulation
-- statement:
--   This module fixes the objects of Bai and Ye's directional KKT theory for bilevel programs.
--
--   **General objects.** Let $X$ be a real inner product space (in the paper $X=\mathbb R^n$) and write $\mathbb B$ for its **open** unit ball.
--
--   1. *Directional neighbourhood* (p. 3). For $d\in X$ and $\varepsilon,\delta>0$,
--   $$\mathcal V_{\varepsilon,\delta}(d)=\{z\in\varepsilon\mathbb B \mid \big\|\|d\|z-\|z\|d\big\|\le\delta\|z\|\|d\|\}.$$
--   For $d=0$ this is the open ball $\varepsilon\mathbb B$.
--   2. *Directional derivative* (Definition 2.4). A map $h:X\to Y$ has directional derivative $h'(x;u)=d$ if $(h(x+tu)-h(x))/t\to d$ as $t\downarrow0$.
--   3. *Directional Lipschitz continuity* (Definition 2.4). $h$ is directionally Lipschitz at $\bar x$ in direction $u$ if there are $L,\varepsilon,\delta>0$ with $\|h(x)-h(x')\|\le L\|x-x'\|$ for all $x,x'\in\bar x+\mathcal V_{\varepsilon,\delta}(u)$. For an extended-real function (such as the value function) the definition also requires $h$ to be finite on $\bar x+\mathcal V_{\varepsilon,\delta}(u)$.
--   4. *Directional limiting subdifferential* (Definition 2.6). For $\varphi:X\to[-\infty,+\infty]$ finite at $\bar x$,
--   $$\partial\varphi(\bar x;u)=\{\xi \mid \exists\, t_k\downarrow0,\ u^k\to u,\ \xi^k\to\xi\ \text{with}\ \varphi(\bar x+t_ku^k)\to\varphi(\bar x),\ \xi^k\in\widehat\partial\varphi(\bar x+t_ku^k)\},$$
--   where $\widehat\partial$ is the Fréchet (regular) subdifferential of Definition 2.5.
--   5. *Problem (P)* $\min_z \varphi(z)$ s.t. $\phi(z)\le0$ with $\varphi:X\to\mathbb R$, $\phi:X\to\mathbb R^q$ (p. 7). It is *calm at $\bar z$ in direction $u$* (Definition 3.1) if there are $\varepsilon,\delta,\rho>0$ such that $\varphi(z)-\varphi(\bar z)+\rho\|\alpha\|\ge0$ for every $\alpha\in\varepsilon\mathbb B$ and every $z\in\bar z+\mathcal V_{\varepsilon,\delta}(u)$ with $\phi(z)+\alpha\le0$. The active set is $I_\phi(\bar z)=\{j\mid\phi_j(\bar z)=0\}$, and $u$ lies in the critical cone $C(\bar z)$ (p. 8) if $\phi_j'(\bar z;u)\le0$ for $j\in I_\phi(\bar z)$ and $\nabla\varphi(\bar z)u\le0$. The positive part $\phi_+$ is taken componentwise.
--
--   **Bilevel objects.** Let $F,f:\mathbb R^n\times\mathbb R^m\to\mathbb R$, $g:\mathbb R^n\times\mathbb R^m\to\mathbb R^p$, $G:\mathbb R^n\times\mathbb R^m\to\mathbb R^q$.
--
--   1. The lower level feasible set $\{y\mid g(x,y)\le0\}$, the solution map $S(x)$ of $(P_x)\ \min_y f(x,y)$ s.t. $g(x,y)\le0$, and the value function (p. 2)
--   $$V(x)=\inf_y\{f(x,y)\mid g(x,y)\le0\}\in[-\infty,+\infty].$$
--   2. (BP) $\min F(x,y)$ s.t. $y\in S(x)$, $G(x,y)\le0$ (p. 1); a local minimizer is a feasible point at which $F$ is minimal among feasible points of a neighbourhood.
--   3. Calmness of (VP) $\min F$ s.t. $f(x,y)-V(x)\le0$, $g\le0$, $G\le0$ at $(\bar x,\bar y)$ in direction $d\in\mathbb R^{n+m}$ (p. 3): there are $\varepsilon,\delta,\rho>0$ such that $F(x,y)-F(\bar x,\bar y)+\rho\|\alpha\|\ge0$ for every $\alpha=(a,b,c)\in\mathbb R^{1+p+q}$ with $\|\alpha\|<\varepsilon$ and every $(x,y)\in(\bar x,\bar y)+\mathcal V_{\varepsilon,\delta}(d)$ with $f(x,y)-V(x)+a\le0$, $g(x,y)+b\le0$, $G(x,y)+c\le0$.
--   4. The critical cone of (VP) (p. 22), given $V'(\bar x;u)$: $(u,v)\in C(\bar x,\bar y)$ iff $\nabla f(\bar x,\bar y)(u,v)\le V'(\bar x;u)$, $\nabla g_i(\bar x,\bar y)(u,v)\le0$ for $i\in I_g(\bar x,\bar y)$, $\nabla G_i(\bar x,\bar y)(u,v)\le0$ for $i\in I_G(\bar x,\bar y)$, and $\nabla F(\bar x,\bar y)(u,v)\le0$.
--
--   These are the hypotheses and the conclusion of Theorem 3.1 and Theorem 5.1, the directional KKT conditions under directional calmness.
--
--   **Formalization Note** Vectors of constraint values live in `EuclideanSpace ℝ (Fin q)` and the pair $(x,y)$ in `WithLp 2 (E n × E m)`, so every norm is Euclidean, as in the paper. The value function is an `EReal`-valued infimum, so it takes the value $+\infty$ on an infeasible lower level and $-\infty$ on an unbounded one; the constraint $f-V\le0$ is evaluated in `EReal`. In the directional subdifferential, $t_k\downarrow0$ is encoded as $t_k>0$, $t_k\to0$, and "$\bar x\in\operatorname{dom}\varphi$" as $\varphi(\bar x)$ finite. Directional derivatives are passed as an explicit value (`HasDirDerivAt h x u d`), and the critical cones take that value as a parameter. The Fréchet subgradient is the published `NonconvexSplitting.Shared.IsRegularSubgrad`; `E n` comes from the published `SetConstrSOC.Directional.VarAnalysis`. A printed slip is read as intended: the critical cone of (VP) on p. 22 writes "$F(\bar x,\bar y)(u,v)\le0$" for $\nabla F(\bar x,\bar y)(u,v)\le0$, and the critical cone on p. 8 writes $C(z)$, $\nabla\varphi(z)$ for $C(\bar z)$, $\nabla\varphi(\bar z)$.
-- source:
--   Bai, Ye, Directional necessary optimality conditions for bilevel programs, arXiv:2004.01783v3, pp. 1–3, 5–8, 22, (BP), (P_x), (VP), V_{ε,δ}(d), Definitions 2.4–2.6, (P), Definition 3.1, C(z̄), C(x̄,ȳ)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_SetConstrSOC_Directional_VarAnalysis

namespace DirKKTBilevel.VP

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional

noncomputable section

/-! ### General objects (§1–§3), on a real inner product space `X` -/

section General

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- The directional neighbourhood of p. 3 (Bai–Ye, arXiv:2004.01783v3):
`V_{ε,δ}(d) = {z ∈ ε𝔹 | ‖‖d‖z − ‖z‖d‖ ≤ δ‖z‖‖d‖}`, with `𝔹` the **open** unit ball (p. 5).
For `d = 0` it is the open ball of radius `ε`. -/
def dirNbhd (ε δ : ℝ) (d : X) : Set X :=
  {z | ‖z‖ < ε ∧ ‖‖d‖ • z - ‖z‖ • d‖ ≤ δ * ‖z‖ * ‖d‖}

/-- Definition 2.6, p. 6: the limiting subdifferential of `φ` at `x` in direction `u`,
`∂φ(x; u) = {ξ | ∃ t_k ↓ 0, u^k → u, ξ^k → ξ, φ(x + t_k u^k) → φ(x), ξ^k ∈ ∂̂φ(x + t_k u^k)}`,
for `x ∈ dom φ` (here: `φ x` finite). `t_k ↓ 0` is encoded as `t_k > 0`, `t_k → 0`; `∂̂` is the
published Fréchet subgradient `IsRegularSubgrad` (Definition 2.5). -/
def dirSubdiff (φ : X → EReal) (x u : X) : Set X :=
  {ξ | φ x ≠ ⊤ ∧ φ x ≠ ⊥ ∧ ∃ (t : ℕ → ℝ) (us ξs : ℕ → X), (∀ k, 0 < t k) ∧
    Tendsto t atTop (𝓝 0) ∧ Tendsto us atTop (𝓝 u) ∧ Tendsto ξs atTop (𝓝 ξ) ∧
    Tendsto (fun k => φ (x + t k • us k)) atTop (𝓝 (φ x)) ∧
    ∀ k, IsRegularSubgrad φ (x + t k • us k) (ξs k)}

/-- Definition 2.4, p. 6: `h` has directional derivative `d` at `x` in direction `u`,
`h'(x; u) = lim_{t↓0} (h(x + tu) − h(x))/t = d`. -/
def HasDirDerivAt {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (h : X → Y) (x u : X) (d : Y) : Prop :=
  Tendsto (fun t : ℝ => t⁻¹ • (h (x + t • u) - h x)) (𝓝[>] 0) (𝓝 d)

/-- Definition 2.4, p. 6: `h` is directionally Lipschitz continuous at `x` in direction `u`:
there are `L, ε, δ > 0` with `‖h z − h z'‖ ≤ L‖z − z'‖` for all `z, z' ∈ x + V_{ε,δ}(u)`. -/
def DirLipschitzAt {Y : Type*} [NormedAddCommGroup Y] (h : X → Y) (x u : X) : Prop :=
  ∃ L ε δ : ℝ, 0 < L ∧ 0 < ε ∧ 0 < δ ∧
    ∀ z z', z - x ∈ dirNbhd ε δ u → z' - x ∈ dirNbhd ε δ u → ‖h z - h z'‖ ≤ L * ‖z - z'‖

/-- Definition 2.4, p. 6, for an extended-real-valued function such as the value function:
`h` is finite on `x + V_{ε,δ}(u)` and Lipschitz there with constant `L`, for some `L, ε, δ > 0`. -/
def DirLipschitzAtEReal (h : X → EReal) (x u : X) : Prop :=
  ∃ L ε δ : ℝ, 0 < L ∧ 0 < ε ∧ 0 < δ ∧
    (∀ z, z - x ∈ dirNbhd ε δ u → h z ≠ ⊥ ∧ h z ≠ ⊤) ∧
    ∀ z z', z - x ∈ dirNbhd ε δ u → z' - x ∈ dirNbhd ε δ u →
      |(h z).toReal - (h z').toReal| ≤ L * ‖z - z'‖

/-- The componentwise positive part `w₊ = (max(w_j, 0))_j` of a vector of `ℝ^q` (as in `ϕ₊`, p. 3, p. 10). -/
def posPart {q : ℕ} (w : E q) : E q := WithLp.toLp 2 (fun j => max (w j) 0)

/-- Definition 3.1, p. 8, with explicit constants: for problem (P) `min obj(z)` s.t. `con(z) ≤ 0`,
for every `α ∈ ε𝔹` and every `z ∈ z̄ + V_{ε,δ}(u)` with `con(z) + α ≤ 0`,
`obj(z) − obj(z̄) + ρ‖α‖ ≥ 0`. -/
def IsCalmDirWith {q : ℕ} (obj : X → ℝ) (con : X → E q) (z u : X) (ε δ ρ : ℝ) : Prop :=
  ∀ α : E q, ‖α‖ < ε → ∀ w, w - z ∈ dirNbhd ε δ u → (∀ j, con w j + α j ≤ 0) →
    0 ≤ obj w - obj z + ρ * ‖α‖

/-- Definition 3.1, p. 8: (P) is (Clarke) calm at `z` in direction `u`: there are positive
`ε, δ, ρ` for which `IsCalmDirWith` holds. -/
def IsCalmDir {q : ℕ} (obj : X → ℝ) (con : X → E q) (z u : X) : Prop :=
  ∃ ε δ ρ : ℝ, 0 < ε ∧ 0 < δ ∧ 0 < ρ ∧ IsCalmDirWith obj con z u ε δ ρ

/-- p. 8: the active index set `I_ϕ(z̄) = {j | ϕ_j(z̄) = 0}`. -/
def activeSet {q : ℕ} (con : X → E q) (z : X) : Set (Fin q) := {j | con z j = 0}

/-- p. 8: `u ∈ C(z̄)`, where `d = ϕ'(z̄; u)` is the directional derivative of the constraint map:
`d_j ≤ 0` for every active `j`, and `∇obj(z̄)u ≤ 0`. -/
def criticalCone {q : ℕ} (obj : X → ℝ) (con : X → E q) (z u : X) (d : E q) : Prop :=
  (∀ j ∈ activeSet con z, d j ≤ 0) ∧ fderiv ℝ obj z u ≤ 0

end General

/-! ### The bilevel program (BP) and its value-function reformulation (VP) (§1, §5) -/

section Bilevel

/-- The space `ℝⁿ × ℝᵐ` of the bilevel variable `(x, y)`, with the Euclidean norm of `ℝ^{n+m}`. -/
abbrev Z (n m : ℕ) := WithLp 2 (E n × E m)

variable {n m p q : ℕ}

/-- The feasible set `{y | g(x, y) ≤ 0}` of the lower level program `(P_x)`, p. 2. -/
def feasLL (g : Z n m → E p) (x : E n) : Set (E m) :=
  {y | ∀ i, g (WithLp.toLp 2 (x, y)) i ≤ 0}

/-- The solution set `S(x)` of the lower level program `(P_x)`, p. 2. -/
def solMap (f : Z n m → ℝ) (g : Z n m → E p) (x : E n) : Set (E m) :=
  {y | y ∈ feasLL g x ∧
    ∀ y' ∈ feasLL g x, f (WithLp.toLp 2 (x, y)) ≤ f (WithLp.toLp 2 (x, y'))}

/-- The value function `V(x) = inf_y {f(x, y) | g(x, y) ≤ 0}`, p. 2, as an extended real
(`+∞` when the lower level program is infeasible, `−∞` when it is unbounded below). -/
def valueFn (f : Z n m → ℝ) (g : Z n m → E p) (x : E n) : EReal :=
  ⨅ y ∈ feasLL g x, ((f (WithLp.toLp 2 (x, y)) : ℝ) : EReal)

/-- Feasibility for (BP), p. 1: `y ∈ S(x)` and `G(x, y) ≤ 0`. -/
def FeasBP (f : Z n m → ℝ) (g : Z n m → E p) (G : Z n m → E q) (z : Z n m) : Prop :=
  (WithLp.ofLp z).2 ∈ solMap f g (WithLp.ofLp z).1 ∧ ∀ j, G z j ≤ 0

/-- `(x, y)` is a local minimizer of (BP), p. 1: it is feasible, and `F(x, y) ≤ F(x', y')` for
every feasible `(x', y')` in a neighbourhood of `(x, y)`. -/
def IsLocalMinBP (F f : Z n m → ℝ) (g : Z n m → E p) (G : Z n m → E q) (x : E n) (y : E m) :
    Prop :=
  FeasBP f g G (WithLp.toLp 2 (x, y)) ∧
    ∀ᶠ z in 𝓝 (WithLp.toLp 2 (x, y)), FeasBP f g G z → F (WithLp.toLp 2 (x, y)) ≤ F z

/-- p. 3: (VP) is calm at `(x, y)` in direction `d ∈ ℝ^{n+m}`: there are `ε, δ, ρ > 0` such that
for every `α = (a, b, c) ∈ ℝ^{1+p+q}` with `‖α‖ < ε` and every `z ∈ (x, y) + V_{ε,δ}(d)` with
`f(z) − V(z_x) + a ≤ 0`, `g(z) + b ≤ 0`, `G(z) + c ≤ 0`, one has `F(z) − F(x, y) + ρ‖α‖ ≥ 0`.
`‖α‖ = √(a² + ‖b‖² + ‖c‖²)` is the Euclidean norm; the first constraint is evaluated in `EReal`. -/
def IsCalmDirVP (F f : Z n m → ℝ) (g : Z n m → E p) (G : Z n m → E q) (x : E n) (y : E m)
    (d : Z n m) : Prop :=
  ∃ ε δ ρ : ℝ, 0 < ε ∧ 0 < δ ∧ 0 < ρ ∧ ∀ (a : ℝ) (b : E p) (c : E q),
    Real.sqrt (a ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) < ε →
    ∀ z : Z n m, z - WithLp.toLp 2 (x, y) ∈ dirNbhd ε δ d →
      ((f z : EReal) - valueFn f g (WithLp.ofLp z).1 + (a : EReal) ≤ 0) →
      (∀ i, g z i + b i ≤ 0) → (∀ j, G z j + c j ≤ 0) →
      0 ≤ F z - F (WithLp.toLp 2 (x, y)) + ρ * Real.sqrt (a ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2)

/-- p. 22: `w = (u, v) ∈ C(x̄, ȳ)`, the critical cone of (VP), where `dV = V'(x̄; u)`:
`∇f(x̄,ȳ)w ≤ V'(x̄;u)`, `∇g_i(x̄,ȳ)w ≤ 0` for active `i`, `∇G_j(x̄,ȳ)w ≤ 0` for active `j`,
and `∇F(x̄,ȳ)w ≤ 0`. -/
def criticalConeVP (F f : Z n m → ℝ) (g : Z n m → E p) (G : Z n m → E q) (x : E n) (y : E m)
    (dV : ℝ) (w : Z n m) : Prop :=
  fderiv ℝ f (WithLp.toLp 2 (x, y)) w ≤ dV ∧
  (∀ i, g (WithLp.toLp 2 (x, y)) i = 0 →
    fderiv ℝ (fun z => g z i) (WithLp.toLp 2 (x, y)) w ≤ 0) ∧
  (∀ j, G (WithLp.toLp 2 (x, y)) j = 0 →
    fderiv ℝ (fun z => G z j) (WithLp.toLp 2 (x, y)) w ≤ 0) ∧
  fderiv ℝ F (WithLp.toLp 2 (x, y)) w ≤ 0

end Bilevel

end

end DirKKTBilevel.VP


