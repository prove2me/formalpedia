-- Prove2me | Definitions.Def_SONATA_Undir_Setting
-- name    : SONATA_Undir_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:17.376045+00:00
-- url     : https://prove2.me/theorems/08773c24-1968-4cac-aaba-4a0086377154
-- title:
--   Assumptions A–D, (1), (15), (20), (23), (24), Algorithm 1 — problem (P), surrogates, the SONATA run and its error quantities
-- statement:
--   This module fixes Problem (P), the standing assumptions and the SONATA algorithm over undirected graphs (Algorithm 1) of Sun, Daneshmand and Scutari.
--
--   **Problem (P).** Agents $i=1,\dots,m$ hold functions $f_i$ on $\mathbb R^d$; with $F=\frac1m\sum_i f_i$ and a convex, possibly nonsmooth $G$, the network solves
--   $$\min_{\mathbf x\in\mathcal K}\ U(\mathbf x)=F(\mathbf x)+G(\mathbf x).$$
--   The Hessian $\nabla^2\varphi(\mathbf x)$ is the derivative of the gradient map, and $\mathbf A\preceq\mathbf B$ is the order of quadratic forms.
--
--   1. **Assumption A.** (A1) $\emptyset\ne\mathcal K\subseteq\mathbb R^d$ is closed and convex; (A2) each $f_i$ is twice differentiable on an open set $\mathcal O\supseteq\mathcal K$ and convex; (A3) $\mu\mathbf I\preceq\nabla^2F(\mathbf x)\preceq L\mathbf I$ for all $\mathbf x\in\mathcal K$, with $\mu>0$ and $0<L<\infty$; (A4) $G$ is convex on $\mathcal K$.
--   2. **Display (1).** Constants $\mu_i\ge0$, $0<L_i<\infty$ with $\mu_i\mathbf I\preceq\nabla^2f_i(\mathbf x)\preceq L_i\mathbf I$ for all $\mathbf x\in\mathcal K$; $L_{\rm mx}=\max_iL_i$ (4).
--   3. **Assumption B.** The undirected graph $\mathcal G$ on the agents is connected.
--   4. **Assumption C.** Each surrogate $\tilde f_i(\cdot\,;\cdot)$ is $C^2$ on $\mathcal O\times\mathcal O$ and, writing $\nabla\tilde f_i(\mathbf x;\mathbf z)$ for its gradient in the first argument: (i) $\nabla\tilde f_i(\mathbf x;\mathbf x)=\nabla f_i(\mathbf x)$ for $\mathbf x\in\mathcal K$; (ii) $\nabla\tilde f_i(\cdot\,;\mathbf x)$ is $\tilde L_i$-Lipschitz on $\mathcal K$ for every $\mathbf x\in\mathcal K$; (iii) $\tilde f_i(\cdot\,;\mathbf x)$ is $\tilde\mu_i$-strongly convex on $\mathcal K$ for every $\mathbf x\in\mathcal K$.
--   5. **Display (15).** Constants $D_i^\ell\le D_i^u$ with $D_i^\ell\mathbf I\preceq\nabla^2\tilde f_i(\mathbf x,\mathbf y)-\nabla^2F(\mathbf x)\preceq D_i^u\mathbf I$ for all $\mathbf x,\mathbf y\in\mathcal K$ (Hessian of $\tilde f_i$ in its first argument at $\mathbf x$, anchor $\mathbf y$), and $D_i=\max\{|D_i^\ell|,|D_i^u|\}$.
--   6. **Constants (24).** $\tilde\mu_{\rm mn}=\min_i\tilde\mu_i$, $\tilde L_{\rm mx}=\max_i\tilde L_i$, $D^\ell_{\rm mn}=\min_iD_i^\ell$, $D_{\rm mx}=\max_iD_i$.
--   7. **Assumption D** for $\mathbf W$ on $\mathcal G$ (module `SONATA.Undir.Network`), and $\mathbf x^\star\in\mathcal K$ minimizing $U$ over $\mathcal K$. The bundle of A, B, C, (15), D and $\mathbf x^\star$ is the standing hypothesis of §3.3.
--   8. **SONATA (Algorithm 1)** with step size $\alpha$. From $\mathbf x_i^0\in\mathcal K$ and $\mathbf y_i^0=\nabla f_i(\mathbf x_i^0)$, for $\nu=0,1,\dots$ each agent computes
--   $$\hat{\mathbf x}_i^\nu\in\operatorname*{argmin}_{\mathbf x_i\in\mathcal K}\ \tilde f_i(\mathbf x_i;\mathbf x_i^\nu)+\big(\mathbf y_i^\nu-\nabla f_i(\mathbf x_i^\nu)\big)^\top(\mathbf x_i-\mathbf x_i^\nu)+G(\mathbf x_i),\qquad(11\mathrm a)$$
--   $\mathbf d_i^\nu=\hat{\mathbf x}_i^\nu-\mathbf x_i^\nu$, $\mathbf x_i^{\nu+1/2}=\mathbf x_i^\nu+\alpha\mathbf d_i^\nu$ (11b), and
--   $$\mathbf x_i^{\nu+1}=\sum_jw_{ij}\mathbf x_j^{\nu+1/2},\qquad \mathbf y_i^{\nu+1}=\sum_jw_{ij}\big(\mathbf y_j^\nu+\nabla f_j(\mathbf x_j^{\nu+1})-\nabla f_j(\mathbf x_j^\nu)\big).\qquad(11\mathrm c,\ 11\mathrm d)$$
--   9. **Error quantities.** The tracking error $\boldsymbol\delta_i^\nu=\nabla F(\mathbf x_i^\nu)-\mathbf y_i^\nu$ (23) and the optimality gap $p^\nu=\sum_i\big(U(\mathbf x_i^\nu)-U(\mathbf x^\star)\big)$ (20).
--
--   Every statement of the mission is about these runs and these quantities.
--
--   **Formalization Note.** A run is a relation on the sequences $(\mathbf x^\nu,\mathbf y^\nu,\hat{\mathbf x}^\nu)$: $\hat{\mathbf x}_i^\nu$ is *some* minimizer of (11a), and $\mathbf x^\star$ is *a* minimizer of $U$ over $\mathcal K$ (uniqueness is a consequence). Assumption A gives no lower semicontinuity of $G$, so neither minimizer need exist in general; the paper assumes both, and so does this encoding, without adding a hypothesis on $G$. Time is 0-based ("Iterate $\nu=1,2,\dots$" consumes $\mathbf x^0$). "$f_i$ convex" is read as convexity on $\mathcal K$ together with a positive semidefinite Hessian at every point of $\mathcal O$ ($\mathcal O$ need not be convex). $G$ is a function on $\mathbb R^d$ convex on $\mathcal K$; its values off $\mathcal K$ never enter. Strong convexity uses Mathlib's `StrongConvexOn` (modulus $\tilde\mu_i/2\,\|\cdot\|^2$), with $\tilde\mu_i>0$; $\tilde L_i\ge0$. The constants (4), (24) are minima and maxima over the agents, a nonempty finite set since $\mathcal G$ is connected. The constants $D_i^\ell, D_i^u$ of (15) and $L_i$ of (1) are parameters: every statement holds for every valid choice.
-- source:
--   Sun, Daneshmand & Scutari, Distributed Optimization Based on Gradient-tracking Revisited, arXiv:1905.02637v2, pp. 1, 7, 8, 10–15, Problem (P), Assumptions A–D, (1), (4), Algorithm 1 (11a)–(11d), (15), (20), (23), (24)

import Mathlib
import Definitions.Def_SONATA_Undir_Network

namespace SONATA.Undir

/-- The Hessian `∇²φ(x)`, the derivative of the gradient map, as a linear operator on `ℝᵈ`. -/
noncomputable def hess {d : ℕ} (φ : E d → ℝ) (x : E d) : E d →L[ℝ] E d :=
  fderiv ℝ (gradient φ) x

/-- `F = (1/m) ∑ᵢ fᵢ`, the smooth part of Problem (P) (p. 1). -/
noncomputable def Fobj {m d : ℕ} (f : Fin m → E d → ℝ) (x : E d) : ℝ :=
  (m : ℝ)⁻¹ * ∑ i, f i x

/-- `U = F + G`, the objective of Problem (P) (p. 1). -/
noncomputable def Uobj {m d : ℕ} (f : Fin m → E d → ℝ) (G : E d → ℝ) (x : E d) : ℝ :=
  Fobj f x + G x

/-- Assumption A (p. 7).
* A1 `∅ ≠ K ⊆ ℝᵈ` is closed and convex;
* A2 each `fᵢ` is twice differentiable on the open set `O ⊇ K` and convex (read as: convex on `K`,
  and locally convex on `O`, i.e. its Hessian is positive semidefinite at every point of `O`; `O`
  need not be convex);
* A3 `μI ⪯ ∇²F(x) ⪯ LI` for all `x ∈ K`, with `μ > 0` and `0 < L < ∞`;
* A4 `G` is convex on `K` (its values off `K` play no role). -/
structure AssumptionA {m d : ℕ} (K O : Set (E d)) (f : Fin m → E d → ℝ) (G : E d → ℝ)
    (μ L : ℝ) : Prop where
  K_nonempty : K.Nonempty
  K_closed : IsClosed K
  K_convex : Convex ℝ K
  O_open : IsOpen O
  K_sub_O : K ⊆ O
  f_diff : ∀ i, DifferentiableOn ℝ (f i) O
  grad_diff : ∀ i, DifferentiableOn ℝ (gradient (f i)) O
  f_convex : ∀ i, ConvexOn ℝ K (f i)
  f_locConvex : ∀ i, ∀ x ∈ O, ∀ u : E d, 0 ≤ inner ℝ (hess (f i) x u) u
  mu_pos : 0 < μ
  L_pos : 0 < L
  hess_bounds : ∀ x ∈ K, ∀ u : E d,
    μ * ‖u‖ ^ 2 ≤ inner ℝ (hess (Fobj f) x u) u ∧ inner ℝ (hess (Fobj f) x u) u ≤ L * ‖u‖ ^ 2
  G_convex : ConvexOn ℝ K G

/-- Display (1) (p. 7): constants `μᵢ ≥ 0` and `0 < Lᵢ < ∞` with
`μᵢ I ⪯ ∇²fᵢ(x) ⪯ Lᵢ I` for all `x ∈ K` and all `i`. -/
def Eq1 {m d : ℕ} (K : Set (E d)) (f : Fin m → E d → ℝ) (μi Li : Fin m → ℝ) : Prop :=
  ∀ i, 0 ≤ μi i ∧ 0 < Li i ∧ ∀ x ∈ K, ∀ u : E d,
    μi i * ‖u‖ ^ 2 ≤ inner ℝ (hess (f i) x u) u ∧ inner ℝ (hess (f i) x u) u ≤ Li i * ‖u‖ ^ 2

/-- The partial gradient `∇f̃ᵢ(x; z)` of a surrogate `f̃ᵢ(·; ·)` with respect to its first
argument, at `(x, z)` (Assumption C, p. 11). -/
noncomputable def pgrad {d : ℕ} (ft : E d → E d → ℝ) (x z : E d) : E d :=
  gradient (fun w => ft w z) x

/-- The partial Hessian `∇²f̃ᵢ(x, z)` of a surrogate with respect to its first argument, at `x`,
with the second argument (the anchor) fixed at `z` ((15), p. 12). -/
noncomputable def phess {d : ℕ} (ft : E d → E d → ℝ) (x z : E d) : E d →L[ℝ] E d :=
  fderiv ℝ (fun w => gradient (fun v => ft v z) w) x

/-- Assumption C (p. 11): each surrogate `f̃ᵢ : O × O → ℝ` is `C²` and
* (i) `∇f̃ᵢ(x; x) = ∇fᵢ(x)` for all `x ∈ K`;
* (ii) `∇f̃ᵢ(•; x)` is `L̃ᵢ`-Lipschitz continuous on `K`, for all `x ∈ K` (`L̃ᵢ ≥ 0`);
* (iii) `f̃ᵢ(•; x)` is `μ̃ᵢ`-strongly convex on `K`, for all `x ∈ K` (`μ̃ᵢ > 0`; Mathlib's
  `StrongConvexOn K μ̃` has the modulus convention `μ̃/2 ‖·‖²`).
`ft i w z` is `f̃ᵢ(w; z)`: first argument the variable, second the anchor. -/
structure AssumptionC {m d : ℕ} (K O : Set (E d)) (f : Fin m → E d → ℝ)
    (ft : Fin m → E d → E d → ℝ) (μt Lt : Fin m → ℝ) : Prop where
  smooth : ∀ i, ContDiffOn ℝ 2 (fun q : E d × E d => ft i q.1 q.2) (O ×ˢ O)
  grad_match : ∀ i, ∀ x ∈ K, pgrad (ft i) x x = gradient (f i) x
  Lt_nonneg : ∀ i, 0 ≤ Lt i
  lipschitz : ∀ i, ∀ x ∈ K, ∀ w ∈ K, ∀ w' ∈ K,
    ‖pgrad (ft i) w x - pgrad (ft i) w' x‖ ≤ Lt i * ‖w - w'‖
  mut_pos : ∀ i, 0 < μt i
  strongly_convex : ∀ i, ∀ x ∈ K, StrongConvexOn K (μt i) (fun w => ft i w x)

/-- Display (15) (p. 12): constants `Dᵢˡ ≤ Dᵢᵘ` with
`Dᵢˡ I ⪯ ∇²f̃ᵢ(x, y) − ∇²F(x) ⪯ Dᵢᵘ I` for all `x, y ∈ K`. -/
def Eq15 {m d : ℕ} (K : Set (E d)) (f : Fin m → E d → ℝ) (ft : Fin m → E d → E d → ℝ)
    (Dl Du : Fin m → ℝ) : Prop :=
  ∀ i, Dl i ≤ Du i ∧ ∀ x ∈ K, ∀ y ∈ K, ∀ u : E d,
    Dl i * ‖u‖ ^ 2 ≤ inner ℝ ((phess (ft i) x y - hess (Fobj f) x) u) u ∧
      inner ℝ ((phess (ft i) x y - hess (Fobj f) x) u) u ≤ Du i * ‖u‖ ^ 2

/-- `Dᵢ = max{|Dᵢˡ|, |Dᵢᵘ|}` ((15), p. 12). -/
noncomputable def Dcoef {m : ℕ} (Dl Du : Fin m → ℝ) (i : Fin m) : ℝ := max |Dl i| |Du i|

/-- `μ̃_mn = minᵢ μ̃ᵢ` ((24), p. 14). -/
noncomputable def mutmn {m : ℕ} (μt : Fin m → ℝ) : ℝ := ⨅ i, μt i

/-- `L̃_mx = maxᵢ L̃ᵢ` ((24), p. 14). -/
noncomputable def Ltmx {m : ℕ} (Lt : Fin m → ℝ) : ℝ := ⨆ i, Lt i

/-- `D^ℓ_mn = minᵢ Dᵢˡ` ((24), p. 14). -/
noncomputable def Dlmn {m : ℕ} (Dl : Fin m → ℝ) : ℝ := ⨅ i, Dl i

/-- `D_mx = maxᵢ Dᵢ` ((24), p. 14). -/
noncomputable def Dmx {m : ℕ} (Dl Du : Fin m → ℝ) : ℝ := ⨆ i, Dcoef Dl Du i

/-- `L_mx = maxᵢ Lᵢ` ((4), p. 8), for the constants `Lᵢ` of (1). -/
noncomputable def Lmx {m : ℕ} (Li : Fin m → ℝ) : ℝ := ⨆ i, Li i

/-- The standing assumptions of §3.3 (p. 15: "We will tacitly assume that Assumptions A, B, C,
and D are satisfied"), together with (15) and the optimal solution `x*` of Problem (P):
* Assumption A with constants `μ`, `L`;
* Assumption B (p. 10): the undirected graph `𝒢` on the agents `{1, …, m}` is connected;
* Assumption C with constants `μ̃ᵢ`, `L̃ᵢ`;
* (15) with constants `Dᵢˡ`, `Dᵢᵘ`;
* Assumption D for the weight matrix `W` on `𝒢`;
* `x* ∈ K` minimizes `U` over `K` ((20), p. 13). -/
structure Standing {m d : ℕ} (K O : Set (E d)) (f : Fin m → E d → ℝ) (G : E d → ℝ) (μ L : ℝ)
    (ft : Fin m → E d → E d → ℝ) (μt Lt Dl Du : Fin m → ℝ) (Gr : SimpleGraph (Fin m))
    (W : Matrix (Fin m) (Fin m) ℝ) (xstar : E d) : Prop where
  A : AssumptionA K O f G μ L
  B : Gr.Connected
  C : AssumptionC K O f ft μt Lt
  eq15 : Eq15 K f ft Dl Du
  D : AssumptionD Gr W
  xstar_mem : xstar ∈ K
  xstar_min : IsMinOn (Uobj f G) K xstar

/-- The direction `dᵢ^ν = x̂ᵢ^ν − xᵢ^ν` of (11b) (p. 11). -/
def dir {m d : ℕ} (x xh : ℕ → Stack m d) (ν : ℕ) : Stack m d := fun i => xh ν i - x ν i

/-- The intermediate iterate `xᵢ^{ν+1/2} = xᵢ^ν + α dᵢ^ν` of (11b) (p. 11). -/
def xhalf {m d : ℕ} (α : ℝ) (x xh : ℕ → Stack m d) (ν : ℕ) : Stack m d :=
  fun i => x ν i + α • dir x xh ν i

/-- The objective of the local problem (11a) (p. 11) of agent `i` at iteration `ν`:
`F̃ᵢ(w; xᵢ^ν) + G(w) = f̃ᵢ(w; xᵢ^ν) + (yᵢ^ν − ∇fᵢ(xᵢ^ν))ᵀ(w − xᵢ^ν) + G(w)`. -/
noncomputable def localObj {m d : ℕ} (f : Fin m → E d → ℝ) (G : E d → ℝ)
    (ft : Fin m → E d → E d → ℝ) (i : Fin m) (xi yi : E d) (w : E d) : ℝ :=
  ft i w xi + inner ℝ (yi - gradient (f i) xi) (w - xi) + G w

/-- A run of SONATA over undirected graphs (Algorithm 1, p. 11) with step size `α`, as a relation
on the sequences `x^ν`, `y^ν`, `x̂^ν` (time `ν = 0, 1, …`; the paper's "Iterate ν = 1, 2, …"
consumes `x⁰`):
* Data: `xᵢ⁰ ∈ K` and `yᵢ⁰ = ∇fᵢ(xᵢ⁰)`;
* [S.1] (11a): `x̂ᵢ^ν ∈ K` is a minimizer over `K` of the local objective `localObj`;
  (11b) `xᵢ^{ν+1/2} = xᵢ^ν + α dᵢ^ν` is `xhalf`;
* [S.2] (11c) `xᵢ^{ν+1} = ∑ⱼ wᵢⱼ xⱼ^{ν+1/2}`;
  (11d) `yᵢ^{ν+1} = ∑ⱼ wᵢⱼ (yⱼ^ν + ∇fⱼ(xⱼ^{ν+1}) − ∇fⱼ(xⱼ^ν))`. -/
structure IsRun {m d : ℕ} (K : Set (E d)) (f : Fin m → E d → ℝ) (G : E d → ℝ)
    (ft : Fin m → E d → E d → ℝ) (W : Matrix (Fin m) (Fin m) ℝ) (α : ℝ)
    (x y xh : ℕ → Stack m d) : Prop where
  init_mem : ∀ i, x 0 i ∈ K
  init_y : ∀ i, y 0 i = gradient (f i) (x 0 i)
  xh_mem : ∀ ν i, xh ν i ∈ K
  xh_min : ∀ ν i, IsMinOn (localObj f G ft i (x ν i) (y ν i)) K (xh ν i)
  consensus : ∀ ν i, x (ν + 1) i = ∑ j, W i j • xhalf α x xh ν j
  tracking : ∀ ν i, y (ν + 1) i =
    ∑ j, W i j • (y ν j + gradient (f j) (x (ν + 1) j) - gradient (f j) (x ν j))

/-- The tracking error `δᵢ^ν = ∇F(xᵢ^ν) − yᵢ^ν` ((23), p. 14). -/
noncomputable def delta {m d : ℕ} (f : Fin m → E d → ℝ) (x y : ℕ → Stack m d) (ν : ℕ) :
    Stack m d :=
  fun i => gradient (Fobj f) (x ν i) - y ν i

/-- The optimality gap `p^ν = ∑ᵢ (U(xᵢ^ν) − U(x*))` ((20), p. 13). -/
noncomputable def pgap {m d : ℕ} (f : Fin m → E d → ℝ) (G : E d → ℝ) (xstar : E d)
    (x : ℕ → Stack m d) (ν : ℕ) : ℝ :=
  ∑ i, (Uobj f G (x ν i) - Uobj f G xstar)

end SONATA.Undir


