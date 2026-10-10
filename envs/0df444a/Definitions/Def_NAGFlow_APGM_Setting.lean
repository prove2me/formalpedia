-- Prove2me | Definitions.Def_NAGFlow_APGM_Setting
-- name    : NAGFlow_APGM_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T16:30:31.110484+00:00
-- url     : https://prove2.me/theorems/f95ff6d2-07cd-4ee7-8be1-68d679d94668
-- title:
--   (2)–(3), (8) p. 2, (105) p. 26, (110)–(111) pp. 28–29, (74) p. 16, (84) p. 20, (115) and Algorithm 2 p. 30 — S^{1,1}_{μ,L}, proper closed convex g, prox, ∂g, G_f, ℒ_k, ℒ̂_k and Semi-APGM
-- statement:
--   This file fixes the objects of §7.2 of Luo and Chen. Throughout, $V$ is a real Hilbert space with inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$, and the problem is the composite minimisation (110),
--   $$\min_{x\in V} f(x):=\min_{x\in V}\,[h(x)+g(x)].$$
--
--   1. **The smooth part.** $h:V\to\mathbb R$ with gradient map $\nabla h$ lies in $\mathcal S^1_\mu$ if $\mu\ge0$, $h$ is continuously differentiable and $\mu$-convex,
--   $$h(x)-h(y)-\langle\nabla h(y),x-y\rangle\ \ge\ \frac\mu2\|x-y\|^2\qquad\forall\,x,y\in V,$$
--   and in $\mathcal S^{1,1}_{\mu,L}$ if moreover $0<L<\infty$, $\mu\le L$ and $\|\nabla h(x)-\nabla h(y)\|\le L\|x-y\|$ for all $x,y$.
--   2. **The nonsmooth part.** $g:V\to\mathbb R\cup\{+\infty\}$ is proper, closed and convex. It is described by its effective domain $D=\operatorname{dom} g$ and its finite values on $D$: $D$ is nonempty, $g$ is convex on the convex set $D$, and the epigraph $\{(x,t): x\in D,\ g(x)\le t\}$ is closed in $V\times\mathbb R$.
--   3. **Subdifferential (105).** $p\in\partial g(x)$ iff $x\in D$ and $g(y)\ge g(x)+\langle p,y-x\rangle$ for all $y\in D$.
--   4. **Proximal operator (8).** $p=\operatorname{prox}_{\eta g}(z)$ means that $p\in D$ minimises $g(y)+\frac{1}{2\eta}\|y-z\|^2$ over $y\in D$.
--   5. **Gradient mapping (111).** $S_f(x,\eta)=\operatorname{prox}_{\eta g}(x-\eta\nabla h(x))$ and $\mathcal G_f(x,\eta)=(x-S_f(x,\eta))/\eta$; with $\eta=1/L$, $\mathcal G_f(x)=L(x-S_f(x))$.
--   6. **Lyapunov functions (74), (84).** For a reference point $x^*$,
--   $$\mathcal L_k=f(x_k)-f(x^*)+\frac{\gamma_k}{2}\|v_k-x^*\|^2,\qquad \widehat{\mathcal L}_k=f(y_k)-f(x^*)+\frac{\gamma_{k+1}}{2}\|v_{k+1}-x^*\|^2 .$$
--   7. **Algorithm 2 (Semi-APGM).** Given $x_0,v_0\in V$, $\gamma_0>0$ and $\eta=1/L$, for $k=0,1,\dots$: choose $\alpha_k>0$ with $L\alpha_k^2=\gamma_k(1+\alpha_k)$; set $\gamma_{k+1}=(\gamma_k+\mu\alpha_k)/(1+\alpha_k)$, $y_k=(x_k+\alpha_kv_k)/(1+\alpha_k)$, $w_k=(\gamma_kv_k+\mu\alpha_ky_k)/(\gamma_k+\mu\alpha_k)$, $x_{k+1}=\operatorname{prox}_{\eta g}(y_k-\eta\nabla h(y_k))$ and $v_{k+1}=w_k+\frac{\gamma_k}{\gamma_{k+1}}\frac{x_{k+1}-y_k}{\alpha_k}$.
--   8. **The semi-implicit scheme (115).** With $\gamma_0>0$ and any $\alpha_k>0$, for every $k$
--   $$\frac{y_k-x_k}{\alpha_k}=v_k-y_k,\quad x_{k+1}=S_f(y_k),\quad \frac{v_{k+1}-v_k}{\alpha_k}=\frac{\mu}{\gamma_k}(y_k-v_{k+1})-\frac1{\gamma_k}\mathcal G_f(y_k),\quad \frac{\gamma_{k+1}-\gamma_k}{\alpha_k}=\mu-\gamma_{k+1}.$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** The paper's duality pairing and dual norm are the inner product and norm of $V$ (Riesz). $\nabla h$ is an explicit map with `HasGradientAt` at every point, not Mathlib's `gradient`. The extended-valued $g$ is encoded by the pair $(g,D)$ with $g:V\to\mathbb R$; values of $g$ off $D$ are never used and stand for $+\infty$, so every statement evaluates $g$ only on $D$ (or, in (117), on both sides with the same coefficient). Closedness is closedness of the epigraph, which does not force $D$ to be closed. The prox and $S_f$ are predicates on a named output: existence and uniqueness of the prox are theorems, not part of the definition. Algorithm 2's updates are written in the paper's solved form; (115) is written in difference-quotient form.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, (2)–(3) and (8), p. 2; (74), p. 16; (84), p. 20; (105), p. 26; (110), p. 28; (111), p. 29; (115) and Algorithm 2, p. 30

import Mathlib
import Definitions.Def_NAGFlow_PredCorr_Setting

namespace NAGFlow.APGM

/-- `g : V → ℝ ∪ {+∞}` is proper, closed and convex ((110), p. 28). The extended-valued `g` is
encoded by its effective domain `D = dom g` and its real values `g : V → ℝ` on `D`; the values of
`g` off `D` are never used and stand for `+∞`.
* proper: `D` is nonempty (and `g` is real, so never `−∞`, on `D`);
* convex: `ConvexOn ℝ D g` (which includes convexity of `D`);
* closed: the epigraph `{(x, t) | x ∈ D, g x ≤ t}` is closed in `V × ℝ`. -/
structure IsProperClosedConvex {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (g : V → ℝ) (D : Set V) : Prop where
  dom_nonempty : D.Nonempty
  convex : ConvexOn ℝ D g
  epi_closed : IsClosed {p : V × ℝ | p.1 ∈ D ∧ g p.1 ≤ p.2}

/-- The subdifferential (105), p. 26, of the extended-valued `g` encoded by `(g, D)`:
`p ∈ ∂g(x)` iff `x ∈ dom g` and `g(y) ≥ g(x) + ⟪p, y − x⟫` for every `y ∈ dom g`. (For `y ∉ dom g`
the inequality holds trivially since `g(y) = +∞`; for `x ∉ dom g` and `g` proper, `∂g(x) = ∅`.) -/
def subdiff {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (g : V → ℝ) (D : Set V) (x : V) : Set V :=
  {p | x ∈ D ∧ ∀ y ∈ D, g x + inner ℝ p (y - x) ≤ g y}

/-- The proximal operator (8), p. 2: `p = prox_{ηg}(z) := argmin_{y ∈ V} {g(y) + (1/(2η))‖y − z‖²}`.
Since `g = +∞` off `D`, `IsProx g D η z p` says that `p ∈ D` and `p` minimises
`g(y) + (1/(2η))‖y − z‖²` over `y ∈ D`. Existence and uniqueness of `p` are not part of the
definition. -/
def IsProx {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (g : V → ℝ) (D : Set V) (η : ℝ) (z p : V) : Prop :=
  p ∈ D ∧ ∀ y ∈ D, g p + 1 / (2 * η) * ‖p - z‖ ^ 2 ≤ g y + 1 / (2 * η) * ‖y - z‖ ^ 2

/-- The proximal-gradient point of (111), p. 29: `s = S_f(x, η) := prox_{ηg}(x − η∇h(x))`, as a
predicate on the output `s`. -/
def IsSf {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (gradh : V → V) (g : V → ℝ) (D : Set V) (η : ℝ) (x s : V) : Prop :=
  IsProx g D η (x - η • gradh x) s

/-- The composite gradient mapping (111), p. 29: `G_f(x, η) := (x − S_f(x, η))/η`, written in terms
of the point `x` and the proximal-gradient output `s = S_f(x, η)`. With `η = 1/L` this is the
page's `G_f(x) = G_f(x, 1/L) = L(x − S_f(x))`. -/
noncomputable def gradMap {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (η : ℝ) (x s : V) : V :=
  (1 / η) • (x - s)

/-- A run of Algorithm 2 (Semi-APGM, p. 30) for `min_{x ∈ V} h(x) + g(x)` with constants `μ, L`
and `η = 1/L`:
* Input: `x₀, v₀ ∈ V`, `γ₀ > 0`;
* step 2: `α_k > 0` and `Lα_k² = γ_k(1 + α_k)`;
* step 3: `γ_{k+1} = (γ_k + μα_k)/(1 + α_k)`;
* step 4: `y_k = (x_k + α_k v_k)/(1 + α_k)` and `w_k = (γ_k v_k + μα_k y_k)/(γ_k + μα_k)`;
* step 5: `x_{k+1} = prox_{ηg}(y_k − η∇h(y_k))` (`IsSf` with `η = 1/L`);
* step 6: `v_{k+1} = w_k + (γ_k/γ_{k+1})(x_{k+1} − y_k)/α_k`. -/
structure IsAPGMRun {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (gradh : V → V) (g : V → ℝ) (D : Set V) (μ L : ℝ) (α γ : ℕ → ℝ) (x y w v : ℕ → V) :
    Prop where
  gamma0_pos : 0 < γ 0
  alpha_pos : ∀ k, 0 < α k
  step_rel : ∀ k, L * α k ^ 2 = γ k * (1 + α k)
  gamma_eq : ∀ k, γ (k + 1) = (γ k + μ * α k) / (1 + α k)
  y_eq : ∀ k, y k = (1 / (1 + α k)) • (x k + α k • v k)
  w_eq : ∀ k, w k = (1 / (γ k + μ * α k)) • (γ k • v k + (μ * α k) • y k)
  x_eq : ∀ k, IsSf gradh g D (1 / L) (y k) (x (k + 1))
  v_eq : ∀ k, v (k + 1) = w k + (γ k / γ (k + 1)) • ((1 / α k) • (x (k + 1) - y k))

/-- A run of the semi-implicit scheme (115), p. 30, in difference-quotient form, with `γ₀ > 0` and
step sizes `α_k > 0` (no step-size rule): for every `k`,
* `(y_k − x_k)/α_k = v_k − y_k`;
* `x_{k+1} = S_f(y_k) = prox_{g/L}(y_k − ∇h(y_k)/L)`;
* `(v_{k+1} − v_k)/α_k = (μ/γ_k)(y_k − v_{k+1}) − (1/γ_k)G_f(y_k)`, with `G_f(y_k) = L(y_k − x_{k+1})`;
* `(γ_{k+1} − γ_k)/α_k = μ − γ_{k+1}`. -/
structure IsSemiImplicitRun {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (gradh : V → V) (g : V → ℝ) (D : Set V) (μ L : ℝ) (α γ : ℕ → ℝ) (x y v : ℕ → V) :
    Prop where
  gamma0_pos : 0 < γ 0
  alpha_pos : ∀ k, 0 < α k
  y_eq : ∀ k, (1 / α k) • (y k - x k) = v k - y k
  x_eq : ∀ k, IsSf gradh g D (1 / L) (y k) (x (k + 1))
  v_eq : ∀ k, (1 / α k) • (v (k + 1) - v k) =
    (μ / γ k) • (y k - v (k + 1)) - (1 / γ k) • gradMap (1 / L) (y k) (x (k + 1))
  gamma_eq : ∀ k, (γ (k + 1) - γ k) / α k = μ - γ (k + 1)

end NAGFlow.APGM


