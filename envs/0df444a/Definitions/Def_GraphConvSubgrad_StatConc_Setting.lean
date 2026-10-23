-- Prove2me | Definitions.Def_GraphConvSubgrad_StatConc_Setting
-- name    : GraphConvSubgrad_StatConc_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:04:36.895308+00:00
-- url     : https://prove2.me/theorems/3966280f-56ed-4249-914c-adcf636b5f8b
-- title:
--   §2.1, §3, §3.2, pp. 6–13 — Legendre functions, Bregman divergence, relative weak convexity, Φ-proximal map and envelope, regularized risks, assumptions (A1)–(A3)
-- statement:
--   This file fixes the objects of Sections 2–4 of Davis and Drusvyatskiy, *Graphical Convergence of Subgradients in Nonconvex Optimization and Learning*.
--
--   Throughout, $E$ is a finite-dimensional real normed space with norm $\|\cdot\|$ (the paper's $\mathbb R^d$ with an arbitrary norm), and the dual norm $\|\cdot\|_*$ is the operator norm on $E^*$. An **extended-valued function** $g: E\to\mathbb R\cup\{+\infty\}$ is recorded as its effective domain $\operatorname{dom} g$ together with its finite values there. It is **closed** if it is lower semicontinuous as an extended-valued function (value $+\infty$ off the domain).
--
--   1. **Legendre function** (§2.1, p. 6). $\Phi$ is proper, closed and strictly convex; $\operatorname{int}(\operatorname{dom}\Phi)\neq\emptyset$; $\Phi$ is differentiable on $\operatorname{int}(\operatorname{dom}\Phi)$; and $\|\nabla\Phi(x_k)\|\to\infty$ whenever interior points $x_k$ converge to a boundary point of $\operatorname{dom}\Phi$.
--   2. **Bregman divergence** (p. 6) and its symmetrization (p. 7):
--   $$D_\Phi(y,x)=\Phi(y)-\Phi(x)-\langle\nabla\Phi(x),y-x\rangle,\qquad D^{\mathrm{sym}}_\Phi(x,y)=D_\Phi(x,y)+D_\Phi(y,x),$$
--   used for $x\in\operatorname{int}(\operatorname{dom}\Phi)$, $y\in\operatorname{dom}\Phi$.
--   3. **Compatibility** (p. 7): $\operatorname{ri}(\operatorname{dom} g)\subseteq\operatorname{int}(\operatorname{dom}\Phi)$. **Relative weak convexity** (p. 7): $g$ is $\rho$-weakly convex relative to $\Phi$ if $x\mapsto g(x)+\rho\Phi(x)$ is convex on $\operatorname{dom} g\cap\operatorname{dom}\Phi$.
--   4. **Φ-proximal map and Φ-envelope** (§3.2, p. 10), with $\lambda=1/\bar\rho$:
--   $$\operatorname{prox}^\Phi_{g/\bar\rho}(x)=\operatorname*{argmin}_{y}\{g(y)+\bar\rho D_\Phi(y,x)\},\qquad g^\Phi_{1/\bar\rho}(x)=\inf_y\{g(y)+\bar\rho D_\Phi(y,x)\},$$
--   both over $y\in\operatorname{dom} g\cap\operatorname{dom}\Phi$. The proximal map is recorded as the set of minimizers.
--   5. **Local dual norm** (p. 11): $\|v\|^*_y=\|\nabla^2\Phi(y)^{-1}v\|$, where the Hessian $\nabla^2\Phi(y):E\to E^*$ is invertible.
--   6. **Risks** ((3.1), p. 7 and (1.2), p. 2). For a probability space $(\Omega,P)$, a loss $f(x,z)$ and a regularizer $r$, the population risk is $\varphi=\mathbb E_{z\sim P}f(\cdot,z)+r$ and the empirical risk of a sample $S=(z_1,\dots,z_m)$ is $\varphi_S=\frac1m\sum_{i=1}^m f(\cdot,z_i)+r$, both with domain $\operatorname{dom} r$.
--   7. **Symmetrized log-moment generating function** (p. 13): for a random variable $X$ and an independent Rademacher sign $\varepsilon$, $\psi_{\varepsilon X}(\lambda)=\log\mathbb E e^{\lambda\varepsilon X}=\log\mathbb E\cosh(\lambda X)$.
--   8. **Assumptions (A1)–(A3)** (p. 8). (A1) $\Phi$ is Legendre, $\operatorname{ri}(\operatorname{dom} r)\subseteq\operatorname{int}(\operatorname{dom}\Phi)$, and $\frac\alpha2\|y-x\|^2\le D_\Phi(x,y)$ for all $x,y\in\operatorname{dom} r\cap\operatorname{int}(\operatorname{dom}\Phi)$, with $\alpha>0$. (A2) For $P$-a.e. $z$, $f(\cdot,z)+r$ is $\rho$-weakly convex relative to $\Phi$ and bounded below. (A3) A nonnegative square-integrable $L$ satisfies $|f(x,z)-f(y,z)|\le L(z)\sqrt{D^{\mathrm{sym}}_\Phi(x,y)}$ for all $x,y\in\operatorname{int}(\operatorname{dom}\Phi)\cap\operatorname{dom} r$ and all $z$, and $\sqrt{\mathbb E L^2}\le\sigma$.
--
--   These are the objects of every statement of the mission: Theorem 3.1 and Lemma 4.3 are about the proximal map and envelope of a general function, and Theorems 4.1 and 4.4 are about $\varphi$ and $\varphi_S$ under (A1)–(A3).
--
--   **Formalization Note** Extended-valued functions are pairs (domain, real values), so no arithmetic in $\pm\infty$ occurs; `EReal` appears only to state lower semicontinuity. The gradient $\nabla\Phi(x)$ is the Fréchet derivative, and $\langle\nabla\Phi(x),v\rangle$ is its evaluation at $v$. The envelope is a real infimum: it is the paper's value wherever the infimum is attained, which Theorem 3.1 guarantees wherever it is used (on an empty or unbounded-below image the real infimum is $0$). $\psi_{\varepsilon X}$ is used only at $\lambda$ with $\cosh(\lambda X)$ integrable. Besides (A1)–(A3), the assumptions bundle record the following, which the paper uses without stating: $r$ is proper with convex domain, $f(x,\cdot)$ is measurable and integrable for every $x$ (presupposed by (3.1)), $f(\cdot,z)+r$ is closed for a.e. $z$, and $\varphi$ is closed and bounded below. The last three are the hypotheses of Theorem 3.1, which the paper applies to $\varphi$ and $\varphi_S$ "under the assumptions (A1)–(A3)" (p. 11).
-- source:
--   Davis, Drusvyatskiy, Graphical Convergence of Subgradients in Nonconvex Optimization and Learning, arXiv:1810.07590v2, pp. 6–13, §2.1, §3, (3.1), (A1)–(A3), §3.2, p. 13 (ψ, ψ⋆)

import Mathlib

namespace GraphConvSubgrad.StatConc

open MeasureTheory Filter Topology

/-- An extended-valued function `E → ℝ ∪ {+∞}`, recorded as its effective domain `dom` and its
(finite) values `val` on it; `val` outside `dom` is irrelevant. -/
structure ExtFn (E : Type*) where
  dom : Set E
  val : E → ℝ

section Analytic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open scoped Classical in
/-- `g` is closed: the extended function (`+∞` off `dom g`) is lower semicontinuous.
`EReal` is used only as an order here, never for arithmetic. -/
def ExtFn.IsClosed (g : ExtFn E) : Prop :=
  LowerSemicontinuous (fun x => if x ∈ g.dom then (g.val x : EReal) else ⊤)

/-- §2.1, p. 6: `Φ` is a Legendre function — proper, closed, strictly convex, with a domain of
nonempty interior, differentiable on that interior, and essentially smooth: the norm of the
gradient blows up along interior points approaching any boundary point of the domain. -/
structure IsLegendre (Φ : ExtFn E) : Prop where
  proper : Φ.dom.Nonempty
  closed : Φ.IsClosed
  strictConvex : StrictConvexOn ℝ Φ.dom Φ.val
  interior_nonempty : (interior Φ.dom).Nonempty
  differentiableOn : DifferentiableOn ℝ Φ.val (interior Φ.dom)
  essSmooth : ∀ b ∈ frontier Φ.dom,
    Tendsto (fun x => ‖fderiv ℝ Φ.val x‖) (𝓝[interior Φ.dom] b) atTop

/-- §2.1, p. 6: the Bregman divergence `D_Φ(y, x) = Φ(y) − Φ(x) − ⟨∇Φ(x), y − x⟩`; meaningful for
`x ∈ int (dom Φ)`, `y ∈ dom Φ`, where it is used. -/
noncomputable def bregman (Φ : ExtFn E) (y x : E) : ℝ :=
  Φ.val y - Φ.val x - fderiv ℝ Φ.val x (y - x)

/-- p. 7: the symmetrized divergence `D^sym_Φ(x, y) = D_Φ(x, y) + D_Φ(y, x)`. -/
noncomputable def bregmanSym (Φ : ExtFn E) (x y : E) : ℝ :=
  bregman Φ x y + bregman Φ y x

/-- p. 7: `g` is compatible with `Φ`: `ri (dom g) ⊆ int (dom Φ)`. -/
def Compatible (Φ g : ExtFn E) : Prop :=
  intrinsicInterior ℝ g.dom ⊆ interior Φ.dom

/-- p. 7: `g` is `ρ`-weakly convex relative to `Φ`: `x ↦ g(x) + ρ Φ(x)` is convex (on its
domain `dom g ∩ dom Φ`). -/
def WeaklyConvexRel (Φ g : ExtFn E) (ρ : ℝ) : Prop :=
  ConvexOn ℝ (g.dom ∩ Φ.dom) (fun x => g.val x + ρ * Φ.val x)

/-- §3.2, p. 10: the `Φ`-proximal set `prox^Φ_{g/ρ̄}(x)` (that is, `prox^Φ_{λ g}(x)` with
`λ = 1/ρ̄`): the minimizers over `dom g ∩ dom Φ` of `y ↦ g(y) + ρ̄ D_Φ(y, x)`. The candidate is the
first argument of `D_Φ`, the centre `x` the second. -/
def proxSet (Φ g : ExtFn E) (rhoBar : ℝ) (x : E) : Set E :=
  {p | p ∈ g.dom ∩ Φ.dom ∧
    IsMinOn (fun y => g.val y + rhoBar * bregman Φ y x) (g.dom ∩ Φ.dom) p}

/-- §3.2, p. 10: the `Φ`-envelope `g^Φ_{1/ρ̄}(x) = inf_y {g(y) + ρ̄ D_Φ(y, x)}`, the infimum over
`dom g ∩ dom Φ`. (A real `sInf`: it equals the infimum whenever that is attained, which is the only
case in which it is used.) -/
noncomputable def envelope (Φ g : ExtFn E) (rhoBar : ℝ) (x : E) : ℝ :=
  sInf ((fun y => g.val y + rhoBar * bregman Φ y x) '' (g.dom ∩ Φ.dom))

/-- The Hessian `∇²Φ(y)`, viewed as a map `E → E*`, is invertible. -/
def HessInvertible (Φ : ExtFn E) (y : E) : Prop :=
  (fderiv ℝ (fderiv ℝ Φ.val) y).IsInvertible

/-- p. 11: the local dual norm `‖v‖*_y = ‖∇²Φ(y)⁻¹ v‖`, used only where `HessInvertible Φ y`. -/
noncomputable def localDualNorm (Φ : ExtFn E) (y : E) (v : E →L[ℝ] ℝ) : ℝ :=
  ‖(fderiv ℝ (fderiv ℝ Φ.val) y).inverse v‖

end Analytic

section Risk

variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace Ω]

/-- (3.1), p. 7: the regularized population risk `φ = E_{z∼P} f(·, z) + r`, with `dom φ = dom r`. -/
noncomputable def popRisk (P : Measure Ω) (r : ExtFn E) (f : E → Ω → ℝ) : ExtFn E :=
  ⟨r.dom, fun x => (∫ z, f x z ∂P) + r.val x⟩

/-- (1.2), p. 2: the regularized empirical risk `φ_S = (1/m) ∑ᵢ f(·, zᵢ) + r` of a sample
`S = (z₁, …, z_m)`, with `dom φ_S = dom r`. -/
noncomputable def empRisk {m : ℕ} (r : ExtFn E) (f : E → Ω → ℝ) (S : Fin m → Ω) : ExtFn E :=
  ⟨r.dom, fun x => (1 / (m : ℝ)) * ∑ i, f x (S i) + r.val x⟩

/-- The single-sample function `f(·, z) + r`, with domain `dom r`. -/
def sampleFn (r : ExtFn E) (f : E → Ω → ℝ) (z : Ω) : ExtFn E :=
  ⟨r.dom, fun x => f x z + r.val x⟩

/-- (A2), p. 8, for one sample point `z`: `f(·, z) + r` is `ρ`-weakly convex relative to `Φ` and
bounded below; and (added, disclosed) closed. -/
structure GoodSample (Φ r : ExtFn E) (f : E → Ω → ℝ) (ρ : ℝ) (z : Ω) : Prop where
  closed : (sampleFn r f z).IsClosed
  weaklyConvex : WeaklyConvexRel Φ (sampleFn r f z) ρ
  bddBelow : BddBelow ((sampleFn r f z).val '' r.dom)

/-- p. 13: `ψ_{εX}(λ) = log E e^{λ ε X}` for a Rademacher sign `ε` independent of `X`, which equals
`log E cosh(λ X)`. Used only at `λ` with `cosh(λ X)` integrable. -/
noncomputable def logMGFSym {α : Type*} [MeasurableSpace α] (μ : Measure α) (X : α → ℝ)
    (lam : ℝ) : ℝ :=
  Real.log (∫ a, Real.cosh (lam * X a) ∂μ)

/-- Assumptions (A1)–(A3), p. 8, plus the disclosed additions (`r` proper with convex domain, the
loss measurable and integrable in `z`, and `φ` closed and bounded below so that Theorem 3.1
applies to it). -/
structure Assumptions (P : Measure Ω) (Φ r : ExtFn E) (f : E → Ω → ℝ) (L : Ω → ℝ)
    (ρ α σ : ℝ) : Prop where
  legendre : IsLegendre Φ
  -- (A1)
  compatible : Compatible Φ r
  alpha_pos : 0 < α
  strongConvex : ∀ x ∈ r.dom ∩ interior Φ.dom, ∀ y ∈ r.dom ∩ interior Φ.dom,
    α / 2 * ‖y - x‖ ^ 2 ≤ bregman Φ x y
  -- (A2)
  goodSample : ∀ᵐ z ∂P, GoodSample Φ r f ρ z
  -- (A3)
  L_nonneg : ∀ z, 0 ≤ L z
  L_memLp : MemLp L 2 P
  lipschitz : ∀ x ∈ interior Φ.dom ∩ r.dom, ∀ y ∈ interior Φ.dom ∩ r.dom, ∀ z,
    |f x z - f y z| ≤ L z * Real.sqrt (bregmanSym Φ x y)
  sigma_bound : Real.sqrt (∫ z, L z ^ 2 ∂P) ≤ σ
  -- added (disclosed)
  r_proper : r.dom.Nonempty
  r_dom_convex : Convex ℝ r.dom
  f_measurable : ∀ x, Measurable (f x)
  f_integrable : ∀ x, Integrable (f x) P
  pop_closed : (popRisk P r f).IsClosed
  pop_bddBelow : BddBelow ((popRisk P r f).val '' r.dom)

end Risk

end GraphConvSubgrad.StatConc


