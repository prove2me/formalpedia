-- Prove2me | Definitions.Def_SONATA_Push_Problem
-- name    : SONATA_Push_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:12:34.762085+00:00
-- url     : https://prove2.me/theorems/b28dbf4f-1924-460d-a52f-11a12f4a2722
-- title:
--   Problem (P), Assumptions A and C, (1), (15), (24), (41)–(42) — composite problem, surrogates, constants, σ(α), η(α)
-- statement:
--   This file fixes the optimization problem, the surrogate functions and the scalar constants used by SONATA over directed graphs.
--
--   **Problem (P).** There are $m$ agents. Agent $i$ holds a function $f_i:\mathbb R^d\to\mathbb R$, and the agents solve
--   $$\min_{x\in\mathcal K}\; U(x) \triangleq F(x)+G(x),\qquad F\triangleq\frac1m\sum_{i=1}^m f_i .$$
--   The Hessian of a function $\varphi$ is $\nabla^2\varphi(x)$, the derivative of its gradient.
--
--   **Assumption A.**
--   1. A1: $\emptyset\ne\mathcal K\subseteq\mathbb R^d$ is closed and convex.
--   2. A2: each $f_i$ is twice differentiable on an open set $\mathcal O\supseteq\mathcal K$ and convex.
--   3. A3: $\mu I\preceq\nabla^2F(x)\preceq LI$ for all $x\in\mathcal K$, with $\mu>0$ and $0<L<\infty$.
--   4. A4: $G$ is convex on $\mathcal K$, possibly nonsmooth.
--
--   **The bounds (1).** Constants $\mu_i\ge0$ and $0<L_i<\infty$ with $\mu_iI\preceq\nabla^2f_i(x)\preceq L_iI$ for all $x\in\mathcal K$; $L_{\rm mx}\triangleq\max_iL_i$.
--
--   **Assumption C.** Each surrogate $\tilde f_i:\mathcal O\times\mathcal O\to\mathbb R$, written $\tilde f_i(x;z)$, is $C^2$, and with $\nabla\tilde f_i(x;z)$ the partial gradient in the first argument:
--   1. $\nabla\tilde f_i(x;x)=\nabla f_i(x)$ for all $x\in\mathcal K$;
--   2. $\nabla\tilde f_i(\cdot;x)$ is $\tilde L_i$-Lipschitz continuous on $\mathcal K$ for all $x\in\mathcal K$;
--   3. $\tilde f_i(\cdot;x)$ is $\tilde\mu_i$-strongly convex on $\mathcal K$ for all $x\in\mathcal K$, with $\tilde\mu_i>0$.
--
--   **The constants (15).** Numbers $D^\ell_i\le D^u_i$ with
--   $$D^\ell_iI\preceq\nabla^2\tilde f_i(x;y)-\nabla^2F(x)\preceq D^u_iI\qquad\forall x,y\in\mathcal K,$$
--   where $\nabla^2\tilde f_i(x;y)$ is the Hessian in the first argument; $D_i\triangleq\max\{|D^\ell_i|,|D^u_i|\}$.
--
--   **The constants (24).** $\tilde\mu_{\rm mn}=\min_i\tilde\mu_i$, $D^\ell_{\rm mn}=\min_iD^\ell_i$, $D_{\rm mx}=\max_iD_i$.
--
--   **$\sigma(\alpha)$ and $\eta(\alpha)$ (41)–(42).** For a step size $\alpha$ and a parameter $\epsilon_{opt}$, let $a\triangleq(1-\frac\alpha2)\tilde\mu_{\rm mn}+\frac{D^\ell_{\rm mn}}2\alpha-\frac12\epsilon_{opt}$ (the bracket of (34)). Then
--   $$\sigma(\alpha)\triangleq1-\frac{\alpha\,a}{D_{\rm mx}^2/\mu+a},\qquad \eta(\alpha)\triangleq\frac{\frac12\epsilon_{opt}^{-1}\,\alpha\,D_{\rm mx}^2/\mu+\frac\alpha\mu\,a}{D_{\rm mx}^2/\mu+a}.$$
--
--   **Standing hypotheses on the problem.** At least one agent, Assumptions A and C, the constants (15), and a point $x^\star\in\mathcal K$ that minimizes $U$ over $\mathcal K$; $U^\star=U(x^\star)$.
--
--   These are the objects about which every statement of the mission is made.
--
--   **Formalization Note** The variable space is `EuclideanSpace ℝ (Fin d)`. Convexity of $f_i$ on $\mathcal O$ (A2) is read as convexity on $\mathcal K$ together with local convexity on $\mathcal O$ (a positive semidefinite Hessian at every point of $\mathcal O$), since $\mathcal O$ need not be convex; this is what makes A2–A3 imply the bounds (1), as the paper states. Loewner bounds are quadratic-form inequalities for every direction $u$. Strong convexity uses Mathlib's `StrongConvexOn` (modulus $\frac m2r^2$, the paper's convention). Minima and maxima over the agents are `⨅`/`⨆` over `Fin m`, which are the true min/max because $m\ge1$ is a standing hypothesis. The existence of $x^\star$ is assumed, not derived. The constants $D^\ell_i,D^u_i$ are parameters: the statements hold for every valid choice.
-- source:
--   Sun, Daneshmand & Scutari, Distributed Optimization Based on Gradient-tracking Revisited, arXiv:1905.02637v2, pp. 1, 7, 11–12, 14, 16, 18, Problem (P), Assumption A, (1), Assumption C, (15), (24), (34), (41)–(42)

import Mathlib
import Definitions.Def_SONATA_Undir_Network
import Definitions.Def_SONATA_Undir_Setting

namespace SONATA.Push

open scoped RealInnerProductSpace

/-- `F = (1/m) Σ_i f_i`, the smooth part of Problem (P) (p. 1). -/
noncomputable def Fsum {m d : ℕ} (f : Fin m → SONATA.Undir.E d → ℝ) : SONATA.Undir.E d → ℝ :=
  fun x => (1 / (m : ℝ)) * ∑ i, f i x

/-- `U = F + G`, the objective of Problem (P) (p. 1). -/
noncomputable def U {m d : ℕ} (f : Fin m → SONATA.Undir.E d → ℝ) (G : SONATA.Undir.E d → ℝ) : SONATA.Undir.E d → ℝ :=
  fun x => Fsum f x + G x

/-- Assumption A (p. 7).
A1: `K` is nonempty, closed and convex.
A2: `O ⊇ K` is open; each `f_i` is twice differentiable on `O` (it and its gradient are differentiable
on `O`) and convex: convex on `K`, and locally convex on `O` (its Hessian is positive semidefinite at
every point of `O`; `O` need not be convex).
A3: `μ I ⪯ ∇²F(x) ⪯ L I` for all `x ∈ K`, with `μ > 0` and `0 < L`.
A4: `G` is convex on `K`. -/
def AssumptionA {m d : ℕ} (K O : Set (SONATA.Undir.E d)) (f : Fin m → SONATA.Undir.E d → ℝ) (G : SONATA.Undir.E d → ℝ) (μ L : ℝ) : Prop :=
  K.Nonempty ∧ IsClosed K ∧ Convex ℝ K ∧
  IsOpen O ∧ K ⊆ O ∧
  (∀ i, DifferentiableOn ℝ (f i) O ∧ DifferentiableOn ℝ (gradient (f i)) O ∧ ConvexOn ℝ K (f i) ∧
    ∀ x ∈ O, ∀ u : SONATA.Undir.E d, 0 ≤ ⟪SONATA.Undir.hess (f i) x u, u⟫) ∧
  0 < μ ∧ 0 < L ∧
  (∀ x ∈ K, ∀ u : SONATA.Undir.E d,
    μ * ‖u‖ ^ 2 ≤ ⟪SONATA.Undir.hess (Fsum f) x u, u⟫ ∧ ⟪SONATA.Undir.hess (Fsum f) x u, u⟫ ≤ L * ‖u‖ ^ 2) ∧
  ConvexOn ℝ K G

/-- The bounds (1) (p. 7): `μ_i I ⪯ ∇²f_i(x) ⪯ L_i I` for all `x ∈ K`, with `μ_i ≥ 0` and `0 < L_i`. -/
def HessBounds {m d : ℕ} (K : Set (SONATA.Undir.E d)) (f : Fin m → SONATA.Undir.E d → ℝ) (μi Li : Fin m → ℝ) : Prop :=
  ∀ i, 0 ≤ μi i ∧ 0 < Li i ∧
    ∀ x ∈ K, ∀ u : SONATA.Undir.E d,
      μi i * ‖u‖ ^ 2 ≤ ⟪SONATA.Undir.hess (f i) x u, u⟫ ∧ ⟪SONATA.Undir.hess (f i) x u, u⟫ ≤ Li i * ‖u‖ ^ 2

/-- Assumption C (p. 11). Each surrogate `f̃_i : O × O → ℝ` (`ft i x z = f̃_i(x; z)`) is `C²` and
(i) `∇f̃_i(x; x) = ∇f_i(x)` for all `x ∈ K`;
(ii) `∇f̃_i(·; x)` is `L̃_i`-Lipschitz continuous on `K`, for all `x ∈ K`;
(iii) `f̃_i(·; x)` is `μ̃_i`-strongly convex on `K`, for all `x ∈ K` (with `μ̃_i > 0`). -/
def AssumptionC {m d : ℕ} (K O : Set (SONATA.Undir.E d)) (f : Fin m → SONATA.Undir.E d → ℝ) (ft : Fin m → SONATA.Undir.E d → SONATA.Undir.E d → ℝ)
    (μt Lt : Fin m → ℝ) : Prop :=
  ∀ i,
    ContDiffOn ℝ 2 (fun q : SONATA.Undir.E d × SONATA.Undir.E d => ft i q.1 q.2) (O ×ˢ O) ∧
    (∀ x ∈ K, SONATA.Undir.pgrad (ft i) x x = gradient (f i) x) ∧
    (∀ x ∈ K, ∀ w ∈ K, ∀ w' ∈ K, ‖SONATA.Undir.pgrad (ft i) w x - SONATA.Undir.pgrad (ft i) w' x‖ ≤ Lt i * ‖w - w'‖) ∧
    0 < μt i ∧ (∀ x ∈ K, StrongConvexOn K (μt i) (fun w => ft i w x))

/-- The constants of (15) (p. 12): `D^ℓ_i ≤ D^u_i` and
`D^ℓ_i I ⪯ ∇²f̃_i(x; y) − ∇²F(x) ⪯ D^u_i I` for all `x, y ∈ K`. -/
def HessGap {m d : ℕ} (K : Set (SONATA.Undir.E d)) (f : Fin m → SONATA.Undir.E d → ℝ) (ft : Fin m → SONATA.Undir.E d → SONATA.Undir.E d → ℝ)
    (Dl Du : Fin m → ℝ) : Prop :=
  ∀ i, Dl i ≤ Du i ∧
    ∀ x ∈ K, ∀ y ∈ K, ∀ u : SONATA.Undir.E d,
      Dl i * ‖u‖ ^ 2 ≤ ⟪(SONATA.Undir.phess (ft i) x y - SONATA.Undir.hess (Fsum f) x) u, u⟫ ∧
      ⟪(SONATA.Undir.phess (ft i) x y - SONATA.Undir.hess (Fsum f) x) u, u⟫ ≤ Du i * ‖u‖ ^ 2

/-- `D_i = max{|D^ℓ_i|, |D^u_i|}` (15). -/
noncomputable def Dcon {m : ℕ} (Dl Du : Fin m → ℝ) (i : Fin m) : ℝ := max |Dl i| |Du i|

/-- The bracket `(1 − α/2) μ̃_mn + (D^ℓ_mn/2) α − ½ ε_opt` of (34) and (41)–(42). -/
noncomputable def aCoef (mut_mn Dl_mn α ε : ℝ) : ℝ :=
  (1 - α / 2) * mut_mn + Dl_mn / 2 * α - ε / 2

/-- `σ(α)` of (41): `1 − α a / (D²_mx/μ + a)` with `a` the bracket `aCoef`. -/
noncomputable def sigma (μ mut_mn Dl_mn D_mx α ε : ℝ) : ℝ :=
  1 - α * aCoef mut_mn Dl_mn α ε / (D_mx ^ 2 / μ + aCoef mut_mn Dl_mn α ε)

/-- `η(α)` of (42): `(½ ε_opt⁻¹ α D²_mx/μ + (α/μ) a) / (D²_mx/μ + a)` with `a` the bracket `aCoef`. -/
noncomputable def eta (μ mut_mn Dl_mn D_mx α ε : ℝ) : ℝ :=
  ((1 / 2) * ε⁻¹ * α * (D_mx ^ 2 / μ) + α / μ * aCoef mut_mn Dl_mn α ε) /
    (D_mx ^ 2 / μ + aCoef mut_mn Dl_mn α ε)

/-- The standing hypotheses on the problem and the surrogates: at least one agent, Assumption A,
Assumption C, the constants (15), and `x⋆ ∈ K` minimizing `U` over `K` (the solution of (P)). -/
def ProblemHyp {m d : ℕ} (K O : Set (SONATA.Undir.E d)) (f : Fin m → SONATA.Undir.E d → ℝ) (G : SONATA.Undir.E d → ℝ) (μ L : ℝ)
    (ft : Fin m → SONATA.Undir.E d → SONATA.Undir.E d → ℝ) (μt Lt Dl Du : Fin m → ℝ) (xstar : SONATA.Undir.E d) : Prop :=
  0 < m ∧ AssumptionA K O f G μ L ∧ AssumptionC K O f ft μt Lt ∧ HessGap K f ft Dl Du ∧
    xstar ∈ K ∧ IsMinOn (U f G) K xstar

end SONATA.Push


