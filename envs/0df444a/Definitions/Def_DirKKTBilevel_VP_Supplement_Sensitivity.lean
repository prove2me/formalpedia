-- Prove2me | Definitions.Def_DirKKTBilevel_VP_Supplement_Sensitivity
-- name    : DirKKTBilevel_VP_Supplement_Sensitivity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T04:20:48.517324+00:00
-- url     : https://prove2.me/theorems/5a17bcab-2199-4010-908a-f09e3f3ad30a
-- title:
--   §4–§5, pp. 12–26 — Λ, L, D₊𝓕, S(x̄;u), restricted inf-compactness, inner semi-continuity, RCR, RS, Σ, W, Θ, quasi-normality and KKT for (VP)
-- statement:
--   Let $f:\mathbb R^n\times\mathbb R^m\to\mathbb R$, $g:\mathbb R^n\times\mathbb R^m\to\mathbb R^p$, $G:\mathbb R^n\times\mathbb R^m\to\mathbb R^q$ be the bilevel data of the base model, $\mathcal F(x)=\{y\mid g(x,y)\le0\}$, $S(x)$ the lower-level solution set and $V$ the (extended-real) value function.
--
--   1. $I_g(x,y)=\{i\mid g_i(x,y)=0\}$, $\mathcal L(x,y;\lambda)=f(x,y)+g(x,y)^T\lambda$ and $\Lambda(x,y)=\{\lambda\ge0\mid\nabla_y\mathcal L(x,y;\lambda)=0,\ g(x,y)^T\lambda=0\}$ (p. 12).
--   2. $L(\bar x,\bar y;u)=\{v\mid\nabla g_i(\bar x,\bar y)(u,v)\le0,\ i\in I_g(\bar x,\bar y)\}$ and the lower Dini derivative $D_+\mathcal F(\bar x,\bar y;u)=\{v\mid\bar y+tv+o(t)\in\mathcal F(\bar x+tu)\text{ for all small }t>0\}$ (p. 15).
--   3. $S(\bar x;u)=\{y\in S(\bar x)\mid\exists t_k\downarrow0,u_k\to u,y_k\to y,\ y_k\in S(\bar x+t_ku_k)\}$ (Definition 4.5).
--   4. $S$ is **inner semi-continuous** at $(\bar x,\bar y)$, $\bar y\in S(\bar x)$, in direction $u$ if $\bar y\in\liminf_{x\xrightarrow{u}\bar x}S(x)$ (Definition 4.4).
--   5. **Restricted inf-compactness** at $\bar x$ in direction $u$ with compact $\Omega_u\subseteq\mathbb R^m$: $V(\bar x)$ is finite and for some $\varepsilon,\delta>0$, $S(x)\cap\Omega_u\neq\emptyset$ whenever $x\in\bar x+V_{\varepsilon,\delta}(u)$ and $V(x)<V(\bar x)+\varepsilon$ (Definition 4.1).
--   6. **RCR regularity** at $(\bar x,\bar y)\in\operatorname{gph}\mathcal F$: for some $\delta>0$ and every $K\subseteq I_g(\bar x,\bar y)$, the family $\{\nabla_yg_j(x,y)\}_{j\in K}$ has the same rank at all $(x,y)\in B_\delta(\bar x,\bar y)$ (Definition 4.6).
--   7. **Robinson stability** at $(\bar x,\bar y)\in\operatorname{gph}\mathcal F$ in direction $u$: for some $\kappa,\varepsilon,\delta>0$, $\operatorname{dist}(y,\mathcal F(x))\le\kappa\|g_+(x,y)\|$ for all $x\in\bar x+V_{\varepsilon,\delta}(u)$, $y\in B_\varepsilon(\bar y)$ (Definition 4.7); $u=0$ gives RS.
--   8. With $V'(x;u)$: $\Sigma(x,y,u)=\{v\in L(x,y;u)\mid V'(x;u)=\nabla f(x,y)(u,v)\}$ (25), $W(x,y,u,v)=\{\nabla_xf(x,y)+\nabla_xg(x,y)^T\lambda\mid\lambda\in\Lambda(x,y)\cap\{\nabla g(x,y)(u,v)\}^\perp\}$ (p. 22), and
--   $$\Theta(\bar x;u)=\bigcup_{\tilde y\in S(\bar x;u)\cap\Omega_u}\ \bigcup_{v\in\Sigma(\bar x,\tilde y,u)}W(\bar x,\tilde y,u,v)\qquad(27).$$
--   9. The directional quasi-normality (35)–(38) of Theorem 5.2 with an arbitrary set $D$ in place of $\partial^cV(\bar x;u)$, the directional KKT condition of Theorem 5.1, and its form $0\in\nabla F+\lambda_V\nabla f-\lambda_VD\times\{0\}+\nabla g^T\lambda_g+\nabla G^T\lambda_G$ with the sign, complementarity and directional orthogonality conditions.
--
--   These are the objects of the sensitivity results of §4 and the optimality conditions of §5.
--
--   **Formalization Note** Gradients are taken on $\mathbb R^{n+m}$ with its Euclidean norm (`WithLp 2`); $\nabla_x,\nabla_y$ are its blocks. Distances are extended (`infEDist`, $+\infty$ to an empty set). `HasDirDerivAtE` records $V'(\bar x;u)$ together with finiteness of $V$ at $\bar x$ and along $\bar x+tu$ for small $t>0$. `IsMinOfMins`/`IsMinOfMaxs` encode attained min–min and min–max values. The printed $\Omega_u\subseteq\mathbb R^n$ is read as $\mathbb R^m$.
-- source:
--   Bai, Ye, Directional necessary optimality conditions for bilevel programs, arXiv:2004.01783v3, pp. 12–26, §4 (p. 12), Definitions 4.1, 4.4–4.7, p. 15, (25), (27), Theorem 4.3, Theorems 5.1–5.2

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model
import Definitions.Def_DirKKTBilevel_VP_Supplement_Variational

namespace DirKKTBilevel.VP.Supplement

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional DirKKTBilevel.VP

noncomputable section

variable {n m p q : ℕ}

/-! ### Lower-level data (§4, p. 12) -/

/-- The partial gradient `∇ₓh(x, y)`: the `x`-block of the gradient of `h` on `ℝⁿ × ℝᵐ`. -/
def gradX (h : Z n m → ℝ) (z : Z n m) : E n := (WithLp.ofLp (gradient h z)).1

/-- The partial gradient `∇_y h(x, y)`: the `y`-block of the gradient of `h` on `ℝⁿ × ℝᵐ`. -/
def gradY (h : Z n m → ℝ) (z : Z n m) : E m := (WithLp.ofLp (gradient h z)).2

/-- p. 12: the active index set `I_g(x, y) = {i | g_i(x, y) = 0}`. -/
def activeLL (g : Z n m → E p) (x : E n) (y : E m) : Set (Fin p) :=
  {i | g (WithLp.toLp 2 (x, y)) i = 0}

/-- p. 12: the lower-level multiplier set
`Λ(x, y) = {λ ∈ ℝᵖ | ∇_y L(x, y; λ) = 0, g(x, y)ᵀλ = 0, λ ≥ 0}`, `L = f + gᵀλ`. -/
def lagMult (f : Z n m → ℝ) (g : Z n m → E p) (x : E n) (y : E m) : Set (E p) :=
  {l | (∀ i, 0 ≤ l i) ∧ ∑ i, l i * g (WithLp.toLp 2 (x, y)) i = 0 ∧
    gradY f (WithLp.toLp 2 (x, y)) + ∑ i, l i • gradY (fun z => g z i) (WithLp.toLp 2 (x, y)) = 0}

/-- p. 12: `∇ₓL(x, y; λ)u = ∇ₓf(x, y)u + Σᵢ λᵢ ∇ₓgᵢ(x, y)u`. -/
def lagDerivX (f : Z n m → ℝ) (g : Z n m → E p) (x : E n) (y : E m) (l : E p) (u : E n) : ℝ :=
  fderiv ℝ f (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, 0)) +
    ∑ i, l i * fderiv ℝ (fun z => g z i) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, 0))

/-- p. 15: the `y`-projection of the linearization cone,
`L(x̄, ȳ; u) = {v | ∇gᵢ(x̄, ȳ)(u, v) ≤ 0, i ∈ I_g(x̄, ȳ)}`. -/
def linLL (g : Z n m → E p) (x : E n) (y : E m) (u : E n) : Set (E m) :=
  {v | ∀ i, g (WithLp.toLp 2 (x, y)) i = 0 →
    fderiv ℝ (fun z => g z i) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, v)) ≤ 0}

/-- p. 15: the lower Dini directional derivative of the feasible map `𝓕(x) = {y | g(x, y) ≤ 0}`,
`D₊𝓕(x̄, ȳ; u) = liminf_{t↓0} (𝓕(x̄ + tu) − ȳ)/t = {v | ∃ o(t), ȳ + tv + o(t) ∈ 𝓕(x̄ + tu)}`
(for all small `t > 0`). -/
def diniFeas (g : Z n m → E p) (x : E n) (y : E m) (u : E n) : Set (E m) :=
  {v | ∃ r : ℝ → E m, Tendsto (fun t => t⁻¹ • r t) (𝓝[>] 0) (𝓝 0) ∧
    ∀ᶠ t in 𝓝[>] (0 : ℝ), y + t • v + r t ∈ feasLL g (x + t • u)}

/-- Definition 4.5, p. 14: the directional solution set
`S(x̄; u) = {y ∈ S(x̄) | ∃ t_k ↓ 0, u_k → u, y_k → y, y_k ∈ S(x̄ + t_k u_k)}`. -/
def dirSol (f : Z n m → ℝ) (g : Z n m → E p) (x u : E n) : Set (E m) :=
  solMap f g x ∩ dirLimsup (solMap f g) x u

/-- Definition 4.4, p. 13: for `ȳ ∈ S(x̄)`, the solution map is inner semi-continuous at `(x̄, ȳ)`
in direction `u`: every `t_k ↓ 0`, `u_k → u` admits `y_k ∈ S(x̄ + t_k u_k)` with `y_k → ȳ`. -/
def IsDirInnerSemicont (f : Z n m → ℝ) (g : Z n m → E p) (x : E n) (y : E m) (u : E n) : Prop :=
  y ∈ solMap f g x ∧ y ∈ dirLiminf (solMap f g) x u

/-- Definition 4.1, p. 13: restricted inf-compactness at `x̄` in direction `u` with the compact set
`Ω ⊆ ℝᵐ`: `V(x̄)` is finite and there are `ε, δ > 0` such that `S(x) ∩ Ω ≠ ∅` for every
`x ∈ x̄ + V_{ε,δ}(u)` with `V(x) < V(x̄) + ε`. -/
def IsRestrInfCompactDir (f : Z n m → ℝ) (g : Z n m → E p) (x u : E n) (Ω : Set (E m)) : Prop :=
  IsCompact Ω ∧ valueFn f g x ≠ ⊤ ∧ valueFn f g x ≠ ⊥ ∧
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ ∀ x', x' - x ∈ dirNbhd ε δ u →
      valueFn f g x' < valueFn f g x + (ε : EReal) → (solMap f g x' ∩ Ω).Nonempty

/-- Definition 4.6, p. 14: the feasible map is relaxed constant rank (RCR) regular at the feasible
`(x̄, ȳ)`: there is `δ > 0` such that for every `K ⊆ I_g(x̄, ȳ)` the family
`{∇_y g_j(x, y) | j ∈ K}` has the same rank at every `(x, y) ∈ B_δ(x̄, ȳ)`. -/
def IsRCR (g : Z n m → E p) (x : E n) (y : E m) : Prop :=
  y ∈ feasLL g x ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ K ⊆ activeLL g x y,
    ∀ z ∈ Metric.ball (WithLp.toLp 2 (x, y) : Z n m) δ,
      Module.finrank ℝ (Submodule.span ℝ ((fun j => gradY (fun w => g w j) z) '' K)) =
        Module.finrank ℝ (Submodule.span ℝ
          ((fun j => gradY (fun w => g w j) (WithLp.toLp 2 (x, y))) '' K))

/-- Definition 4.7, p. 14: the feasible map satisfies Robinson stability (RS) at `(x̄, ȳ) ∈ gph 𝓕`
in direction `u`: there are `κ, ε, δ > 0` with `dist(y, 𝓕(x)) ≤ κ‖g₊(x, y)‖` for all
`x ∈ x̄ + V_{ε,δ}(u)` and `y ∈ B_ε(ȳ)`. With `u = 0` this is (ordinary) RS. The distance is the
extended distance `infEDist` (`+∞` to an empty set). -/
def IsRSDir (g : Z n m → E p) (x : E n) (y : E m) (u : E n) : Prop :=
  y ∈ feasLL g x ∧ ∃ κ ε δ : ℝ, 0 < κ ∧ 0 < ε ∧ 0 < δ ∧
    ∀ x', x' - x ∈ dirNbhd ε δ u → ∀ y' ∈ Metric.ball y ε,
      Metric.infEDist y' (feasLL g x') ≤
        ENNReal.ofReal (κ * ‖posPart (g (WithLp.toLp 2 (x', y')))‖)

/-- Definition 2.4, p. 6, for the extended-real value function: `V` is finite at `x̄` and at
`x̄ + tu` for all small `t > 0`, and `V'(x̄; u) = lim_{t↓0} (V(x̄ + tu) − V(x̄))/t = d`. -/
def HasDirDerivAtE (V : E n → EReal) (x u : E n) (d : ℝ) : Prop :=
  V x ≠ ⊤ ∧ V x ≠ ⊥ ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), V (x + t • u) ≠ ⊤ ∧ V (x + t • u) ≠ ⊥) ∧
    HasDirDerivAt (fun x' => (V x').toReal) x u d

/-- The values `{∇f(x̄, y)(u, v) | v ∈ L(x̄, y; u)}` minimized in (17). -/
def linVals (f : Z n m → ℝ) (g : Z n m → E p) (x u : E n) (y : E m) : Set ℝ :=
  {r | ∃ v ∈ linLL g x y u, r = fderiv ℝ f (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, v))}

/-- The values `{∇ₓL(x̄, y; λ)u | λ ∈ Λ(x̄, y)}` maximized in (17). -/
def lagVals (f : Z n m → ℝ) (g : Z n m → E p) (x u : E n) (y : E m) : Set ℝ :=
  {r | ∃ l ∈ lagMult f g x y, r = lagDerivX f g x y l u}

/-- `d = min_{y ∈ Y} min A(y)`, all minima attained: every `A(y)` (`y ∈ Y`) has a least element,
and `d` is the least of these least elements. -/
def IsMinOfMins (Y : Set (E m)) (A : E m → Set ℝ) (d : ℝ) : Prop :=
  (∀ y ∈ Y, ∃ r, IsLeast (A y) r) ∧ IsLeast {r | ∃ y ∈ Y, IsLeast (A y) r} d

/-- `d = min_{y ∈ Y} max A(y)`, all extrema attained: every `A(y)` (`y ∈ Y`) has a greatest
element, and `d` is the least of these greatest elements. -/
def IsMinOfMaxs (Y : Set (E m)) (A : E m → Set ℝ) (d : ℝ) : Prop :=
  (∀ y ∈ Y, ∃ r, IsGreatest (A y) r) ∧ IsLeast {r | ∃ y ∈ Y, IsGreatest (A y) r} d

/-- Equation (25), p. 19, with `dV = V'(x; u)`: `Σ(x, y, u) = {v ∈ L(x, y; u) | V'(x; u) = ∇f(x, y)(u, v)}`. -/
def sigmaSet (f : Z n m → ℝ) (g : Z n m → E p) (x : E n) (y : E m) (u : E n) (dV : ℝ) :
    Set (E m) :=
  {v | v ∈ linLL g x y u ∧ dV = fderiv ℝ f (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, v))}

/-- Theorem 4.3, p. 22: `W(x, y, u, v) = {∇ₓf(x, y) + ∇ₓg(x, y)ᵀλ | λ ∈ Λ(x, y) ∩ {∇g(x, y)(u, v)}^⊥}`. -/
def Wset (f : Z n m → ℝ) (g : Z n m → E p) (x : E n) (y : E m) (u : E n) (v : E m) :
    Set (E n) :=
  {ξ | ∃ l ∈ lagMult f g x y,
    ∑ i, l i * fderiv ℝ (fun z => g z i) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, v)) = 0 ∧
    ξ = gradX f (WithLp.toLp 2 (x, y)) + ∑ i, l i • gradX (fun z => g z i) (WithLp.toLp 2 (x, y))}

/-- Equation (27), p. 20, with `dV = V'(x̄; u)` and the compact set `Ω` of restricted
inf-compactness: `Θ(x̄; u) = ⋃_{ỹ ∈ S(x̄;u) ∩ Ω} ⋃_{v ∈ Σ(x̄,ỹ,u)} W(x̄, ỹ, u, v)`. -/
def Theta (f : Z n m → ℝ) (g : Z n m → E p) (x u : E n) (Ω : Set (E m)) (dV : ℝ) : Set (E n) :=
  ⋃ y ∈ dirSol f g x u ∩ Ω, ⋃ v ∈ sigmaSet f g x y u dV, Wset f g x y u v

/-! ### Directional quasi-normality and KKT conditions for (VP) (§5) -/

/-- Theorem 5.2, (35)–(38), p. 25, with the set `D ⊆ ℝⁿ` in place of `∂ᶜV(x̄; u)` (Theorems 5.3
and 5.4 use `co Θ(x̄; u)` and `W(x̄, ȳ, u, v)`): there is no nonzero `(α, ν_g, ν_G) ≥ 0` with
`0 ∈ α∇f(x̄,ȳ) − αD × {0} + ∇g(x̄,ȳ)ᵀν_g + ∇G(x̄,ȳ)ᵀν_G` (35),
`ν_g ⊥ g(x̄,ȳ)`, `ν_g ⊥ ∇g(x̄,ȳ)(u,v)`, `ν_G ⊥ G(x̄,ȳ)`, `ν_G ⊥ ∇G(x̄,ȳ)(u,v)` (36), and common
sequences `t_k ↓ 0`, `(u_k, v_k) → (u, v)` with `f − V > 0` at `(x̄ + t_k u_k, ȳ + t_k v_k)` if
`α > 0` (37), and `g_i > 0` (resp. `G_i > 0`) there for active `i` with `(ν_g)_i > 0`
(resp. `(ν_G)_i > 0`) (38). -/
def IsDirQNVP (f : Z n m → ℝ) (g : Z n m → E p) (G : Z n m → E q) (x : E n) (y : E m)
    (u : E n) (v : E m) (D : Set (E n)) : Prop :=
  ¬ ∃ (α : ℝ) (νg : E p) (νG : E q), ¬ (α = 0 ∧ νg = 0 ∧ νG = 0) ∧
    0 ≤ α ∧ (∀ i, 0 ≤ νg i) ∧ (∀ j, 0 ≤ νG j) ∧
    (∃ ξ ∈ D, α • gradient f (WithLp.toLp 2 (x, y)) - α • (WithLp.toLp 2 (ξ, 0) : Z n m)
        + ∑ i, νg i • gradient (fun z => g z i) (WithLp.toLp 2 (x, y))
        + ∑ j, νG j • gradient (fun z => G z j) (WithLp.toLp 2 (x, y)) = 0) ∧
    ∑ i, νg i * g (WithLp.toLp 2 (x, y)) i = 0 ∧
    ∑ i, νg i * fderiv ℝ (fun z => g z i) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, v)) = 0 ∧
    ∑ j, νG j * G (WithLp.toLp 2 (x, y)) j = 0 ∧
    ∑ j, νG j * fderiv ℝ (fun z => G z j) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, v)) = 0 ∧
    ∃ (t : ℕ → ℝ) (us : ℕ → E n) (vs : ℕ → E m), (∀ k, 0 < t k) ∧ Tendsto t atTop (𝓝 0) ∧
      Tendsto us atTop (𝓝 u) ∧ Tendsto vs atTop (𝓝 v) ∧
      ∀ k, (0 < α → valueFn f g (x + t k • us k) <
              ((f (WithLp.toLp 2 (x + t k • us k, y + t k • vs k)) : ℝ) : EReal)) ∧
        (∀ i, g (WithLp.toLp 2 (x, y)) i = 0 → 0 < νg i →
          0 < g (WithLp.toLp 2 (x + t k • us k, y + t k • vs k)) i) ∧
        (∀ j, G (WithLp.toLp 2 (x, y)) j = 0 → 0 < νG j →
          0 < G (WithLp.toLp 2 (x + t k • us k, y + t k • vs k)) j)

/-- The directional KKT condition of Theorem 5.1, p. 22: there are `λ_V, λ_g, λ_G` and
`ξ ∈ ∂(−V)(x̄; u)` with `0 = ∇F + λ_V∇f + λ_V(ξ, 0) + ∇gᵀλ_g + ∇Gᵀλ_G` at `(x̄, ȳ)`, `λ_V ≥ 0`,
`0 ≤ λ_g ⊥ g(x̄,ȳ)`, `λ_g ⊥ ∇g(x̄,ȳ)(u,v)`, `0 ≤ λ_G ⊥ G(x̄,ȳ)`, `λ_G ⊥ ∇G(x̄,ȳ)(u,v)`. -/
def DirKKTVP (F f : Z n m → ℝ) (g : Z n m → E p) (G : Z n m → E q) (x : E n) (y : E m)
    (u : E n) (v : E m) : Prop :=
  ∃ (lV : ℝ) (lg : E p) (lG : E q) (ξ : E n),
    ξ ∈ dirSubdiff (fun x' => -(valueFn f g x')) x u ∧
    gradient F (WithLp.toLp 2 (x, y)) + lV • gradient f (WithLp.toLp 2 (x, y))
        + lV • (WithLp.toLp 2 (ξ, 0) : Z n m)
        + ∑ i, lg i • gradient (fun z => g z i) (WithLp.toLp 2 (x, y))
        + ∑ j, lG j • gradient (fun z => G z j) (WithLp.toLp 2 (x, y)) = 0 ∧
    0 ≤ lV ∧
    (∀ i, 0 ≤ lg i) ∧ ∑ i, lg i * g (WithLp.toLp 2 (x, y)) i = 0 ∧
    ∑ i, lg i * fderiv ℝ (fun z => g z i) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, v)) = 0 ∧
    (∀ j, 0 ≤ lG j) ∧ ∑ j, lG j * G (WithLp.toLp 2 (x, y)) j = 0 ∧
    ∑ j, lG j * fderiv ℝ (fun z => G z j) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, v)) = 0

/-- The KKT form of Theorem 5.2, p. 25, with the set `D` in place of `∂ᶜV(x̄; u)`: there are
`λ_V, λ_g, λ_G` with `0 ∈ ∇F + λ_V∇f − λ_V D × {0} + ∇gᵀλ_g + ∇Gᵀλ_G` at `(x̄, ȳ)`, `λ_V ≥ 0`,
`0 ≤ λ_g ⊥ g(x̄,ȳ)`, `λ_g ⊥ ∇g(x̄,ȳ)(u,v)`, `0 ≤ λ_G ⊥ G(x̄,ȳ)`, `λ_G ⊥ ∇G(x̄,ȳ)(u,v)`. -/
def DirKKTVPWith (F f : Z n m → ℝ) (g : Z n m → E p) (G : Z n m → E q) (x : E n) (y : E m)
    (u : E n) (v : E m) (D : Set (E n)) : Prop :=
  ∃ (lV : ℝ) (lg : E p) (lG : E q), ∃ ξ ∈ D,
    gradient F (WithLp.toLp 2 (x, y)) + lV • gradient f (WithLp.toLp 2 (x, y))
        - lV • (WithLp.toLp 2 (ξ, 0) : Z n m)
        + ∑ i, lg i • gradient (fun z => g z i) (WithLp.toLp 2 (x, y))
        + ∑ j, lG j • gradient (fun z => G z j) (WithLp.toLp 2 (x, y)) = 0 ∧
    0 ≤ lV ∧
    (∀ i, 0 ≤ lg i) ∧ ∑ i, lg i * g (WithLp.toLp 2 (x, y)) i = 0 ∧
    ∑ i, lg i * fderiv ℝ (fun z => g z i) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, v)) = 0 ∧
    (∀ j, 0 ≤ lG j) ∧ ∑ j, lG j * G (WithLp.toLp 2 (x, y)) j = 0 ∧
    ∑ j, lG j * fderiv ℝ (fun z => G z j) (WithLp.toLp 2 (x, y)) (WithLp.toLp 2 (u, v)) = 0

end

end DirKKTBilevel.VP.Supplement


