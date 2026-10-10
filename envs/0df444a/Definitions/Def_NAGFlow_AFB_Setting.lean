-- Prove2me | Definitions.Def_NAGFlow_AFB_Setting
-- name    : NAGFlow_AFB_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:40:25.360982+00:00
-- url     : https://prove2.me/theorems/e44f4e69-acb7-48cc-9e73-d11e1fe4a6d6
-- title:
--   (2)–(3) p. 2, (104)–(105) p. 26, Algorithm 4 p. 33 — S^{1,1}_{μ,L}(Q), the composite problem min_Q h + g, ∂g, the Semi-AFB method and ℒ_k
-- statement:
--   This file fixes the objects of Section 7.3 of Luo and Chen. Throughout, $V$ is a real Hilbert space with inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$.
--
--   **The classes (2)–(3) on a set.** Let $\Omega\subseteq V$, let $h:V\to\mathbb R$ and let $\nabla h:V\to V$ be a map. We say $h\in\mathcal S^1_\mu(\Omega)$ if $\mu\ge0$, $h$ is continuously differentiable on $\Omega$ (at every $x\in\Omega$, $\nabla h(x)$ is a gradient of $h$ at $x$ relative to $\Omega$, and $\nabla h$ is continuous on $\Omega$), and
--   $$h(x)-h(y)-\langle\nabla h(y),x-y\rangle\ \ge\ \frac{\mu}{2}\|x-y\|^2\qquad\forall\,x,y\in\Omega.$$
--   We say $h\in\mathcal S^{1,1}_{\mu,L}(\Omega)$ if moreover $0<L<\infty$, $\mu\le L$, and $\|\nabla h(x)-\nabla h(y)\|\le L\|x-y\|$ for all $x,y\in\Omega$. Nothing is required of $h$ outside $\Omega$.
--
--   **The problem (104).** We minimise $f=h+g$ over $Q$, where $Q\subseteq V$ is closed and convex, $h\in\mathcal S^{1,1}_{\mu,L}(Q)$ with $0\le\mu\le L<\infty$, and $g:V\to\mathbb R\cup\{+\infty\}$ is proper, closed and convex with $Q\cap\operatorname{dom}g\ne\emptyset$. The function $g$ is described by its effective domain $D=\operatorname{dom}g$ and its finite values on $D$: convexity of $g$ is convexity of $D$ together with convexity of $g$ on $D$, and closedness of $g$ is closedness of its epigraph $\{(x,t)\in V\times\mathbb R: x\in D,\ g(x)\le t\}$. A point $x^*$ is a minimiser if $x^*\in Q\cap D$ and $f(x^*)\le f(z)$ for all $z\in Q\cap D$.
--
--   **The subdifferential (105).** $p\in\partial g(x)$ means $x\in D$ and $g(y)\ge g(x)+\langle p,y-x\rangle$ for every $y\in D$.
--
--   **Algorithm 4 (Semi-AFB).** Given $x_0,v_0\in Q$, $\gamma_0>0$ and $L>0$, for $k=0,1,\dots$: choose $\alpha_k>0$ with $L\alpha_k^2=\gamma_k(1+\alpha_k)$; set
--   $$\gamma_{k+1}=\frac{\gamma_k+\mu\alpha_k}{1+\alpha_k},\qquad y_k=\frac{x_k+\alpha_kv_k}{1+\alpha_k},\qquad w_k=\frac{\gamma_kv_k+\mu\alpha_ky_k}{\gamma_k+\mu\alpha_k};$$
--   let $v_{k+1}$ minimise over $Q$
--   $$\varphi_k(v)=g(v)+\langle\nabla h(y_k),v\rangle+\frac{\gamma_k+\mu\alpha_k}{2\alpha_k}\|v-w_k\|^2;$$
--   and set $x_{k+1}=(x_k+\alpha_kv_{k+1})/(1+\alpha_k)$.
--
--   **The Lyapunov function.** $\mathcal L_k=f(x_k)-f(x^*)+\frac{\gamma_k}{2}\|v_k-x^*\|^2$.
--
--   These objects are shared by every statement of the mission: the goal (Theorem 7.3) and its milestones all quantify over runs of Algorithm 4 for an instance of (104).
--
--   **Formalization Note.** $V^*$ is identified with $V$ (Riesz), so the duality pairing and the inner product coincide. Since $g$ may take the value $+\infty$, the Lean encoding is a pair `(g, D)` with `g : V → ℝ`; the values of `g` off `D` are never used. Step 5's argmin over $Q$ of a function that is $+\infty$ off $D$ is encoded as: $v_{k+1}\in Q\cap D$ and $\varphi_k(v_{k+1})\le\varphi_k(u)$ for all $u\in Q\cap D$. The scheme is a hypothesis on given sequences (`IsAFBRun`); $\alpha_k$ is any positive solution of the step relation, not a formula. The gradient of $h$ is an explicit map with a within-$Q$ derivative (`HasGradientWithinAt`), never Mathlib's `gradient`.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, (2)–(3) p. 2, (104)–(105) p. 26, (119) p. 32, Algorithm 4 and Theorem 7.3 (definition of ℒ_k) p. 33

import Mathlib

namespace NAGFlow.AFB

/-- `h ∈ S¹_μ(Ω)` (Luo & Chen, (2), p. 2): on the set `Ω`, `h` is continuously differentiable, with
gradient map `gradh` (`∇h`) taken within `Ω`, and μ-convex:
`h x − h y − ⟪∇h(y), x − y⟫ ≥ (μ/2)‖x − y‖²` for all `x, y ∈ Ω`, with `μ ≥ 0`. Nothing is required of
`h` or `gradh` outside `Ω`. -/
structure IsS1On {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (h : V → ℝ) (gradh : V → V) (μ : ℝ) (Ω : Set V) : Prop where
  mu_nonneg : 0 ≤ μ
  hasGrad : ∀ x ∈ Ω, HasGradientWithinAt h (gradh x) Ω x
  grad_cont : ContinuousOn gradh Ω
  mu_convex : ∀ x ∈ Ω, ∀ y ∈ Ω, h x - h y - inner ℝ (gradh y) (x - y) ≥ μ / 2 * ‖x - y‖ ^ 2

/-- `h ∈ S^{1,1}_{μ,L}(Ω)` (Luo & Chen, (2)–(3), p. 2, with `0 ≤ μ ≤ L < ∞` as in (104), p. 26):
`h ∈ S¹_μ(Ω)` and `∇h` is `L`-Lipschitz on `Ω`, `‖∇h(x) − ∇h(y)‖ ≤ L‖x − y‖` for `x, y ∈ Ω`,
with `0 < L`. -/
structure IsS11On {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (h : V → ℝ) (gradh : V → V) (μ L : ℝ) (Ω : Set V) : Prop extends IsS1On h gradh μ Ω where
  L_pos : 0 < L
  mu_le_L : μ ≤ L
  grad_lip : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖gradh x - gradh y‖ ≤ L * ‖x - y‖

/-- The data of the composite problem (104), p. 26: `min_{x ∈ Q} h(x) + g(x)`.
The extended-valued `g : V → ℝ ∪ {+∞}` is encoded by its effective domain `D = dom g` and its
real values `g : V → ℝ` on `D` (values of `g` off `D` are never used and stand for `+∞`).
* `Q` is closed and convex;
* `h ∈ S^{1,1}_{μ,L}(Q)`;
* `g` is proper (`D` nonempty, implied by the last field, and `g` real on `D`), convex
  (`ConvexOn ℝ D g`, which includes convexity of `D`) and closed (its epigraph
  `{(x, t) | x ∈ D, g x ≤ t}` is closed in `V × ℝ`);
* `Q ∩ dom g ≠ ∅`. -/
structure IsAFBProblem {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (h : V → ℝ) (gradh : V → V) (g : V → ℝ) (D Q : Set V) (μ L : ℝ) : Prop where
  Q_convex : Convex ℝ Q
  Q_closed : IsClosed Q
  h_class : IsS11On h gradh μ L Q
  g_convex : ConvexOn ℝ D g
  g_closed : IsClosed {p : V × ℝ | p.1 ∈ D ∧ g p.1 ≤ p.2}
  QD_nonempty : (Q ∩ D).Nonempty

/-- The objective `f = h + g` of (104), p. 26 (meaningful on `D`). -/
def fObj {V : Type*} (h g : V → ℝ) (x : V) : ℝ := h x + g x

/-- `x*` is a minimiser of `f = h + g` over `Q`, i.e. over `Q ∩ dom g` (p. 2: argmin f is assumed
nonempty). -/
def IsMinimizer {V : Type*} (h g : V → ℝ) (D Q : Set V) (xstar : V) : Prop :=
  xstar ∈ Q ∩ D ∧ ∀ z ∈ Q ∩ D, fObj h g xstar ≤ fObj h g z

/-- `p ∈ ∂g(x)` (the subdifferential (105), p. 26) for the extended-valued `g` encoded by
`(g, D)`: `x ∈ dom g` and `g(y) ≥ g(x) + ⟪p, y − x⟫` for every `y ∈ dom g` (for `y ∉ dom g` the
inequality holds trivially since `g(y) = +∞`; for `x ∉ dom g` the subdifferential of a proper `g`
is empty). -/
def IsSubgrad {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (g : V → ℝ) (D : Set V) (x p : V) : Prop :=
  x ∈ D ∧ ∀ y ∈ D, g x + inner ℝ p (y - x) ≤ g y

/-- The function minimised in step 5 of Algorithm 4 (p. 33), equivalently in (119), p. 32:
`φ(u) = g(u) + ⟪∇h(y_k), u⟫ + ((γ_k + μα_k)/(2α_k))‖u − w_k‖²`, here written for data
`(αk, γk, gy, wk)` with `gy = ∇h(y_k)`. -/
noncomputable def afbObj {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (g : V → ℝ) (μ αk γk : ℝ) (gy wk u : V) : ℝ :=
  g u + inner ℝ gy u + (γk + μ * αk) / (2 * αk) * ‖u - wk‖ ^ 2

/-- A run of Algorithm 4 (Semi-AFB, p. 33) for the problem (104), with constants `μ, L`:
* Input: `x₀, v₀ ∈ Q`, `γ₀ > 0` (and `L > 0`, part of `IsAFBProblem`);
* step 2: `α_k > 0` and `Lα_k² = γ_k(1 + α_k)`;
* step 3: `γ_{k+1} = (γ_k + μα_k)/(1 + α_k)`;
* step 4: `y_k = (x_k + α_k v_k)/(1 + α_k)` and `w_k = (γ_k v_k + μα_k y_k)/(γ_k + μα_k)`;
* step 5: `v_{k+1}` is a minimiser over `Q` of `g(v) + ⟪∇h(y_k), v⟫ + ((γ_k + μα_k)/(2α_k))‖v − w_k‖²`,
  where `g = +∞` off `D`, i.e. `v_{k+1} ∈ Q ∩ D` minimises that function over `Q ∩ D`;
* step 6: `x_{k+1} = (x_k + α_k v_{k+1})/(1 + α_k)`. -/
structure IsAFBRun {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (gradh : V → V) (g : V → ℝ) (D Q : Set V) (μ L : ℝ) (α γ : ℕ → ℝ) (x y w v : ℕ → V) :
    Prop where
  x0_mem : x 0 ∈ Q
  v0_mem : v 0 ∈ Q
  gamma0_pos : 0 < γ 0
  alpha_pos : ∀ k, 0 < α k
  step_rel : ∀ k, L * α k ^ 2 = γ k * (1 + α k)
  gamma_eq : ∀ k, γ (k + 1) = (γ k + μ * α k) / (1 + α k)
  y_eq : ∀ k, y k = (1 / (1 + α k)) • (x k + α k • v k)
  w_eq : ∀ k, w k = (1 / (γ k + μ * α k)) • (γ k • v k + (μ * α k) • y k)
  v_mem : ∀ k, v (k + 1) ∈ Q ∩ D
  v_argmin : ∀ k, ∀ u ∈ Q ∩ D,
    afbObj g μ (α k) (γ k) (gradh (y k)) (w k) (v (k + 1)) ≤
      afbObj g μ (α k) (γ k) (gradh (y k)) (w k) u
  x_eq : ∀ k, x (k + 1) = (1 / (1 + α k)) • (x k + α k • v (k + 1))

/-- The Lyapunov function of Theorem 7.3 (p. 33), the same as (74), p. 16, for `f = h + g`:
`ℒ_k := f(x_k) − f(x*) + (γ_k/2)‖v_k − x*‖²`. -/
noncomputable def lyap {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (h g : V → ℝ) (xstar : V) (x v : ℕ → V) (γ : ℕ → ℝ) (k : ℕ) : ℝ :=
  fObj h g (x k) - fObj h g xstar + γ k / 2 * ‖v k - xstar‖ ^ 2

end NAGFlow.AFB


