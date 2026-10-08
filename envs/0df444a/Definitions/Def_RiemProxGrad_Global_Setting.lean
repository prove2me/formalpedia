-- Prove2me | Definitions.Def_RiemProxGrad_Global_Setting
-- name    : RiemProxGrad_Global_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:25.745273+00:00
-- url     : https://prove2.me/theorems/e82079f9-9f80-40f1-a8dd-65ba1f60251b
-- title:
--   Riemannian Clarke subdifferential, Assumptions 3.1–3.2 and the RPG run (Algorithm 1)
-- statement:
--   This file sets up problem (1.1) of Huang and Wei,
--   $$\min_{x\in\mathcal M} F(x) = f(x) + g(x),$$
--   on a finite-dimensional Riemannian manifold $\mathcal M$ with metric $\langle\cdot,\cdot\rangle_x$ and induced norm $\|\cdot\|_x$ on each tangent space $T_x\mathcal M$, together with the Riemannian proximal gradient method (RPG, Algorithm 1). Retractions $R$, the vector transport by differentiated retraction $\mathcal T_{\eta_x} = DR_x(\eta_x)$ and Riemannian gradients come from the published definitions `RiemOpt.BFGS.Setting` and `RiemOpt.FR.Setting`.
--
--   1. **Clarke generalized directional derivative and subdifferential** (p. 5). For $h : V\to\mathbb R$ on a real inner-product space $V$, $\eta, v\in V$,
--   $$h^\circ(\eta; v) = \limsup_{\xi\to\eta,\ t\downarrow 0} \frac{h(\xi + t v) - h(\xi)}{t}\in[-\infty,+\infty],\qquad \partial h(\eta) = \{\zeta\in V \mid \langle\zeta, v\rangle \le h^\circ(\eta; v)\ \text{for all } v\in V\}.$$
--   2. **Riemannian subdifferential** (p. 5). For $h:\mathcal M\to\mathbb R$ and $x\in\mathcal M$, with the pull-back $\hat h_x = h\circ R_x$ on the Hilbert space $T_x\mathcal M$: $\partial h(x) = \partial\hat h_x(0_x)$. A point $x$ is **stationary** for $h$ if $0\in\partial h(x)$.
--   3. **Smooth retraction** (p. 4): $R$ is a retraction ($R_x(0_x) = x$, $DR_x(0_x) = \mathrm{id}$) and $(x,\eta)\mapsto R_x(\eta)$ is smooth on the tangent bundle $T\mathcal M$.
--   4. **Adjoint and inverse-adjoint of the transport** (p. 4): $\mathcal T^\sharp_{\eta_x} : T_y\mathcal M\to T_x\mathcal M$, $y = R_x(\eta_x)$, with $\langle \xi_y, \mathcal T_{\eta_x}\zeta_x\rangle_y = \langle \mathcal T^\sharp_{\eta_x}\xi_y, \zeta_x\rangle_x$, and $\mathcal T^{-\sharp}_{\eta_x} = (\mathcal T^{-1}_{\eta_x})^\sharp : T_x\mathcal M\to T_y\mathcal M$.
--   5. **Assumption 3.1** (p. 6): $F$ is bounded from below and $\Omega_{x_0} = \{x\in\mathcal M \mid F(x)\le F(x_0)\}$ is compact.
--   6. **Definition 3.1** (p. 7): $h$ is $L$-retraction-smooth with respect to $R$ in $\mathcal N\subseteq\mathcal M$ if, for every $x\in\mathcal N$ and every $\eta\in T_x\mathcal M$ with $R_x(\eta)\in\mathcal N$,
--   $$h(R_x(\eta)) \le h(x) + \langle \operatorname{grad} h(x), \eta\rangle_x + \frac L2\|\eta\|_x^2 .\qquad(3.2)$$
--   7. **Assumption 3.2** (p. 7), in the reading used by the proof of Lemma 3.1: (3.2) holds for $f$ at every $x\in\Omega_{x_0}$ and for **every** $\eta\in T_x\mathcal M$.
--   8. **Standing assumptions**: $R$ is a smooth retraction; $f$ is continuously differentiable with Riemannian gradient $\operatorname{grad} f$; $g$ is continuous and each pull-back $g\circ R_x$ is locally Lipschitz on $T_x\mathcal M$.
--   9. **RPG run** (Algorithm 1, p. 6). With $\tilde L$ given and
--   $$\ell_x(\eta) = \langle \operatorname{grad} f(x), \eta\rangle_x + \frac{\tilde L}{2}\|\eta\|_x^2 + g(R_x(\eta)),$$
--   a run from $x_0$ is a sequence $x_k\in\mathcal M$ with steps $\eta^*_{x_k}\in T_{x_k}\mathcal M$ such that, for every $k$, $\eta^*_{x_k}$ is a stationary point of $\ell_{x_k}$ on $T_{x_k}\mathcal M$ ($0\in\partial\ell_{x_k}(\eta^*_{x_k})$), $\ell_{x_k}(0)\ge\ell_{x_k}(\eta^*_{x_k})$ (condition (3.1)), and $x_{k+1} = R_{x_k}(\eta^*_{x_k})$.
--
--   These are the objects on which Lemmas 3.1–3.2, the displays (3.6), (3.8), (3.9) and Theorem 3.1 are stated.
--
--   **Formalization Note** The manifold is modelled on a finite-dimensional real inner-product space $E$; $T_x\mathcal M$ carries the inner product of the `RiemannianBundle` instance, and two instances record that each $T_x\mathcal M$ is finite-dimensional and complete, so that Mathlib's `ContinuousLinearMap.adjoint` gives $\mathcal T^\sharp$. The Clarke limit superior is taken in `EReal` along $\mathcal N(\eta)\times\mathcal N_{>0}(0)$, so it never takes a default value. $\mathcal T^{-1}$ is Mathlib's `ContinuousLinearMap.inverse`, which is $0$ where $\mathcal T$ is not invertible; statements use $\mathcal T^{-\sharp}$ only where $\mathcal T$ is invertible or in a limit along the zero section. Assumption 3.2 is stated in the strengthened reading because, read literally, Definition 3.1 only constrains $\eta$ with $R_x(\eta)\in\Omega_{x_0}$, and the proof of Lemma 3.1 applies (3.2) before it knows $x_{k+1}\in\Omega_{x_0}$; the literal reading makes Lemma 3.1 false. The paper's own sufficient condition ([16, Lemma 2.7], (3.3) with $\mathcal N = \mathcal M$) gives the strengthened reading. Local Lipschitzness of $g\circ R_x$ is made explicit from p. 5, where the subdifferential is defined for Lipschitz functions; continuity of $\operatorname{grad} f$ (from $f\in C^1$) is used by the proof of Theorem 3.1 when it applies Lemma 3.2 to $\xi = \operatorname{grad} f$.
-- source:
--   Huang, Wei, Riemannian proximal gradient methods, arXiv:1909.06065v4, pp. 1, 4–7, (1.1), §2 (retraction, vector transport, adjoint, inverse, Riemannian gradient, Clarke generalized subdifferential), Algorithm 1, (3.1), Assumption 3.1, Definition 3.1, Assumption 3.2

import Mathlib
import Definitions.Def_RiemOpt_BFGS_Setting
import Definitions.Def_RiemOpt_FR_Setting

open Bundle Manifold Filter Topology
open scoped ContDiff

namespace RiemProxGrad.Global

section Clarke

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Clarke generalized directional derivative (Huang–Wei, p. 5) of `h : V → ℝ` at `η ∈ V`
in the direction `v ∈ V`:
`h°(η; v) = limsup_{ξ → η, t ↓ 0} (h(ξ + t v) − h(ξ)) / t`,
the limit superior taken jointly as `ξ → η` and `t → 0⁺`, with values in `EReal`. -/
noncomputable def clarkeDirDeriv (h : V → ℝ) (η v : V) : EReal :=
  Filter.limsup (fun q : V × ℝ => (((h (q.1 + q.2 • v) - h q.1) / q.2 : ℝ) : EReal))
    (𝓝 η ×ˢ 𝓝[>] (0 : ℝ))

/-- The Clarke generalized subdifferential (p. 5) of `h : V → ℝ` at `η ∈ V`:
`∂h(η) = {ζ ∈ V | ⟨ζ, v⟩ ≤ h°(η; v) for all v ∈ V}`. -/
def clarkeSubdiff (h : V → ℝ) (η : V) : Set V :=
  {ζ | ∀ v : V, ((inner ℝ ζ v : ℝ) : EReal) ≤ clarkeDirDeriv h η v}

end Clarke

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]

/-- Each tangent space `T_xM` of a manifold modelled on a finite-dimensional `E` is
finite-dimensional. -/
instance instFiniteDimensionalTangentSpace [FiniteDimensional ℝ E] (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, E) x) :=
  inferInstanceAs (FiniteDimensional ℝ E)

/-- Each tangent space `T_xM`, with the Riemannian norm, is complete (it is finite-dimensional),
so it is a Hilbert space and adjoints of linear maps between tangent spaces exist. -/
instance instCompleteSpaceTangentSpace [FiniteDimensional ℝ E] (x : M) :
    CompleteSpace (TangentSpace 𝓘(ℝ, E) x) :=
  FiniteDimensional.complete ℝ _

/-- A retraction in the sense of p. 4: a smooth (`C^∞`) map `R : TM → M`, `(x, η) ↦ R_x(η)`, on the
tangent bundle, with `R_x(0_x) = x` and `DR_x(0_x) = id` (`RiemOpt.BFGS.IsRetraction`, which also
asks each `R_x` to be smooth). -/
def IsSmoothRetraction (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) : Prop :=
  RiemOpt.BFGS.IsRetraction R ∧
    ContMDiff 𝓘(ℝ, E).tangent 𝓘(ℝ, E) ∞ (fun p : TangentBundle 𝓘(ℝ, E) M => R p.1 p.2)

/-- The Riemannian generalized subdifferential (p. 5) of `h : M → ℝ` at `x ∈ M` with respect to
the retraction `R`: `∂h(x) = ∂ĥ_x(0_x)`, the Clarke subdifferential at the origin of the pull-back
`ĥ_x = h ∘ R_x : T_xM → ℝ`, where `T_xM` carries the Riemannian inner product `⟨·,·⟩_x`. -/
def riemSubdiff (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (h : M → ℝ) (x : M) :
    Set (TangentSpace 𝓘(ℝ, E) x) :=
  clarkeSubdiff (fun η : TangentSpace 𝓘(ℝ, E) x => h (R x η)) 0

/-- `x` is a stationary point of `h` (proof of Theorem 3.1, p. 8): `0 ∈ ∂h(x)`. -/
def IsStationary (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (h : M → ℝ) (x : M) : Prop :=
  (0 : TangentSpace 𝓘(ℝ, E) x) ∈ riemSubdiff R h x

/-- The adjoint `T^♯_{η_x} : T_yM → T_xM`, `y = R_x(η_x)`, of the vector transport by differentiated
retraction `T_{η_x} = DR_x(η_x) : T_xM → T_yM` (p. 4):
`⟨ξ_y, T_{η_x} ζ_x⟩_y = ⟨T^♯_{η_x} ξ_y, ζ_x⟩_x`. -/
noncomputable def transportAdj [FiniteDimensional ℝ E] (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M)
    (x : M) (η : TangentSpace 𝓘(ℝ, E) x) :
    TangentSpace 𝓘(ℝ, E) (R x η) →L[ℝ] TangentSpace 𝓘(ℝ, E) x :=
  ContinuousLinearMap.adjoint (RiemOpt.BFGS.transport R x η)

/-- `T^{−♯}_{η_x} : T_xM → T_yM`, `y = R_x(η_x)`, the adjoint of the inverse `T^{−1}_{η_x}` of the
vector transport by differentiated retraction (p. 4). It is meaningful where `T_{η_x}` is
invertible (Mathlib's `ContinuousLinearMap.inverse` is `0` otherwise). -/
noncomputable def transportInvAdj [FiniteDimensional ℝ E]
    (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (x : M) (η : TangentSpace 𝓘(ℝ, E) x) :
    TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) (R x η) :=
  ContinuousLinearMap.adjoint (ContinuousLinearMap.inverse (RiemOpt.BFGS.transport R x η))

/-- The sublevel set `Ω_{x₀} = {x ∈ M | F(x) ≤ F(x₀)}` of Assumption 3.1 (p. 6). -/
def sublevel (F : M → ℝ) (x₀ : M) : Set M :=
  {x | F x ≤ F x₀}

/-- Assumption 3.1 (p. 6) for `F = f + g`: `F` is bounded from below and the sublevel set
`Ω_{x₀}` is compact. -/
def Assumption31 (f g : M → ℝ) (x₀ : M) : Prop :=
  BddBelow (Set.range (f + g)) ∧ IsCompact (sublevel (f + g) x₀)

/-- Definition 3.1 (p. 7): `h` is `L`-retraction-smooth with respect to `R` in `N ⊆ M` (with
Riemannian gradient field `grad`) if for any `x ∈ N` and any `S_x ⊆ T_xM` with `R_x(S_x) ⊆ N`,
`h(R_x(η)) ≤ h(x) + ⟨grad h(x), η⟩_x + (L/2)‖η‖²_x` for all `η ∈ S_x`; equivalently, (3.2) holds
for every `x ∈ N` and every `η ∈ T_xM` with `R_x(η) ∈ N`. -/
def IsLRetractionSmooth (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (h : M → ℝ)
    (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x) (L : ℝ) (N : Set M) : Prop :=
  ∀ x ∈ N, ∀ η : TangentSpace 𝓘(ℝ, E) x, R x η ∈ N →
    h (R x η) ≤ h x + inner ℝ (grad x) η + L / 2 * ‖η‖ ^ 2

/-- Assumption 3.2 (p. 7) in the reading used by the proof of Lemma 3.1: inequality (3.2) for `f`
holds at every `x` of the sublevel set `Ω_{x₀}` of `F = f + g` and for **every** `η ∈ T_xM`,
`f(R_x(η)) ≤ f(x) + ⟨grad f(x), η⟩_x + (L/2)‖η‖²_x`. This strengthens
`IsLRetractionSmooth R f grad L Ω_{x₀}`, which only constrains `η` with `R_x(η) ∈ Ω_{x₀}`. -/
def Assumption32 (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (f g : M → ℝ)
    (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x) (L : ℝ) (x₀ : M) : Prop :=
  ∀ x ∈ sublevel (f + g) x₀, ∀ η : TangentSpace 𝓘(ℝ, E) x,
    f (R x η) ≤ f x + inner ℝ (grad x) η + L / 2 * ‖η‖ ^ 2

/-- The standing assumptions on problem (1.1), `min F(x) = f(x) + g(x)` (pp. 1, 4–5):
* `R` is a smooth retraction on the tangent bundle (p. 4);
* `f` is continuously differentiable with Riemannian gradient field `grad` (p. 5);
* `g` is continuous (p. 1) and every pull-back `g ∘ R_x` is locally Lipschitz on `T_xM` (p. 5,
  where the subdifferential of `g` is defined "since `ĝ_x = g ∘ R_x` is a Lipschitz continuous
  function"). -/
structure Standing (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (f g : M → ℝ)
    (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x) : Prop where
  retraction : IsSmoothRetraction R
  f_contMDiff : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 f
  isGradient : RiemOpt.FR.IsGradient f grad
  g_continuous : Continuous g
  g_locallyLipschitz : ∀ x : M, LocallyLipschitz (fun η : TangentSpace 𝓘(ℝ, E) x => g (R x η))

/-- The model of the RPG subproblem at `x` (Algorithm 1, step 2, p. 6):
`ℓ_x(η) = ⟨grad f(x), η⟩_x + (L̃/2)‖η‖²_x + g(R_x(η))`. -/
noncomputable def ell (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (g : M → ℝ)
    (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x) (Lt : ℝ) (x : M) (η : TangentSpace 𝓘(ℝ, E) x) : ℝ :=
  inner ℝ (grad x) η + Lt / 2 * ‖η‖ ^ 2 + g (R x η)

/-- A run of Algorithm 1 (RPG, p. 6) with constant `L̃` from the initial iterate `x 0`: for every
`k`, `η*_{x_k} = η k ∈ T_{x_k}M` satisfies (3.1) — it is a stationary point of `ℓ_{x_k}` on
`T_{x_k}M`, i.e. `0 ∈ ∂ℓ_{x_k}(η*_{x_k})` (Clarke subdifferential on the Hilbert space
`T_{x_k}M`), and `ℓ_{x_k}(0) ≥ ℓ_{x_k}(η*_{x_k})` — and `x_{k+1} = R_{x_k}(η*_{x_k})` (step 4). -/
structure IsRPGRun (R : (x : M) → TangentSpace 𝓘(ℝ, E) x → M) (g : M → ℝ)
    (grad : (x : M) → TangentSpace 𝓘(ℝ, E) x) (Lt : ℝ) (x : ℕ → M)
    (η : (k : ℕ) → TangentSpace 𝓘(ℝ, E) (x k)) : Prop where
  stationary : ∀ k, (0 : TangentSpace 𝓘(ℝ, E) (x k)) ∈ clarkeSubdiff (ell R g grad Lt (x k)) (η k)
  decrease : ∀ k, ell R g grad Lt (x k) (η k) ≤ ell R g grad Lt (x k) 0
  step : ∀ k, x (k + 1) = R (x k) (η k)

end RiemProxGrad.Global


