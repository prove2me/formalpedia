-- Prove2me | Definitions.Def_NoHair_spacetime
-- name    : NoHair_spacetime
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-04T18:52:42.089189+00:00
-- url     : https://prove2.me/theorems/bb86f59e-bd9c-4837-b65b-49b71e8d0e7b
-- title:
--   No-hair: spacetimes, causal structure, stationary black holes
-- statement:
--   Spacetimes, causal structure and stationary black holes.
--
--   A **spacetime** is a $C^\infty$ manifold $M$ modelled on $\mathbb R^4$, carrying a field $g$ of bilinear forms on the tangent spaces (the metric), a field $F$ of bilinear forms (the electromagnetic field) and a vector field $T$. Components of a bilinear field $B$ along a map $\psi:\mathbb R^4\to M$ are $(\psi^*B)_{\mu\nu}(y)=B_{\psi(y)}(d\psi_y\partial_\mu,d\psi_y\partial_\nu)$; along the inverse of a chart these are the usual coordinate components. The notions defined are:
--
--   1. $g$ is **Lorentzian** if at each point some basis of the tangent space has $g$-Gram matrix $\mathrm{diag}(-1,1,1,1)$; $B$ is **smooth** (resp. **analytic**) if its components are $C^\infty$ (resp. $C^\omega$) in every chart; $F$ is a **2-form** if antisymmetric; $T$ is a **time orientation** if continuous and everywhere timelike.
--   2. A tangent vector $v$ is future timelike if $g(v,v)<0$, $g(v,T)<0$, and future causal if $v\neq0$, $g(v,v)\le0$, $g(v,T)<0$. Chronological and causal futures/pasts $I^\pm_U(p)$, $J^\pm_U(p)$ inside $U\subseteq M$ are defined by $C^1$ curves on $[0,1]$ lying in $U$ with future timelike (resp. causal) velocity; $J^\pm_U(p)$ contain $p$. For a set $S$, $I^\pm(S)=\bigcup_{p\in S}I^\pm_M(p)$.
--   3. $U$ is **globally hyperbolic** if it contains no closed future causal curve and every causal diamond $J^+_U(p)\cap J^-_U(q)$, $p,q\in U$, is compact.
--   4. $(g,F)$ is **electrovacuum** if the Einstein–Maxwell system holds at every point of every chart.
--   5. A **symmetry flow** is a smooth $\mathbb R$-action $\varphi_t$ on $M$ preserving $g$ and $F$; its generator is $X(x)=\frac{d}{dt}\big|_{t=0}\varphi_t(x)$.
--   6. A **stationary asymptotically flat end** consists of $R>0$, $C\in\mathbb R$ and a diffeomorphism $\psi$ from $\{(t,\vec x):|\vec x|>R\}$ onto an open set $M_{\rm ext}\subseteq M$ with $\psi(y+s\partial_t)=\varphi_s(\psi(y))$, $|g_{\mu\nu}-\eta_{\mu\nu}|\le C/|\vec x|$, $|\partial_\sigma g_{\mu\nu}|\le C/|\vec x|^2$ and $|F_{\mu\nu}|\le C/|\vec x|^2$ in these coordinates.
--   7. The **domain of outer communications** is $\langle\langle M_{\rm ext}\rangle\rangle=I^+(M_{\rm ext})\cap I^-(M_{\rm ext})$, the **black-hole region** is $M\setminus I^-(M_{\rm ext})$ and the **future event horizon** is $\partial I^-(M_{\rm ext})$.
--   8. **Stationary black hole** (the standing hypotheses): $g$ Lorentzian and smooth, $F$ a smooth 2-form, $T$ a time orientation, $(g,F)$ electrovacuum, $\varphi$ a symmetry flow with an asymptotically flat end as in 6, $\langle\langle M_{\rm ext}\rangle\rangle$ globally hyperbolic, nonempty black-hole region and connected event horizon.
--   9. A set $D\subseteq M$ **is a Kerr–Newman domain of outer communications** with parameters $(m,a,e)$ if there are $\beta\in\mathbb R$ and a diffeomorphism $\Psi$ from $\{r>r_+\}$ onto $D$ with $\Psi^*g=g^{KN}$ and $\Psi^*F=\cos\beta\,F^{KN}+\sin\beta\,\star F^{KN}$ (constant duality rotation).
--   10. Auxiliary hypotheses used by the milestones: **static** on $D$ (the stationary generator $K$ satisfies $K\wedge dK=0$ there), **axial symmetry** (a $2\pi$-periodic symmetry flow commuting with $\varphi$, with a fixed point and not the identity), and **non-degenerate horizon** (a symmetry flow whose generator $X$ is null on $H\cap\overline D$, nonzero somewhere there, and satisfies $\partial_\mu(g(X,X))=-2\kappa X_\mu$ there with a constant $\kappa\neq0$).
--
--   These notions make the informal phrases of the no-hair theorem ("stationary", "black hole", "event horizon", "described by the Kerr–Newman metric") precise.
--
--   **Formalization Note** Tangent spaces are Mathlib's `TangentSpace 𝓘(ℝ, ℝ⁴) x` (identified with $\mathbb R^4$); derivatives of maps are `mfderiv`, which returns $0$ at points of non-differentiability, so all statements that use it also impose smoothness.
-- source:
--   Wikipedia, "No-hair theorem" (revision oldid=1353599195), https://en.wikipedia.org/w/index.php?title=No-hair_theorem&oldid=1353599195

import Mathlib
import Definitions.Def_NoHair_coordinates

/-!
# No-hair mission: spacetimes, causal structure, stationary black holes

A spacetime is a smooth manifold `M` modelled on `ℝ⁴`. Tangent spaces `T_xM` are identified
with `ℝ⁴` through Mathlib's convention (components in the preferred chart at `x`); every notion
below is chart-independent because it is expressed through `mfderiv` or through the components
in *every* chart of the atlas.
-/

noncomputable section

open scoped ContDiff Manifold BigOperators
open Set

namespace NoHair

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M]

/-- A field of bilinear forms on the tangent spaces of `M` (used for the metric `g` and for the
electromagnetic field `F`). -/
abbrev BilinField (M : Type*) [TopologicalSpace M] [ChartedSpace E4 M] :=
  ∀ x : M, TangentSpace 𝓘(ℝ, E4) x →L[ℝ] TangentSpace 𝓘(ℝ, E4) x →L[ℝ] ℝ

/-- A vector field on `M`. -/
abbrev VecField (M : Type*) [TopologicalSpace M] [ChartedSpace E4 M] :=
  ∀ x : M, TangentSpace 𝓘(ℝ, E4) x

/-- Components of the pull-back of a bilinear field `B` along a map `ψ : ℝ⁴ → M` at `y`:
`(ψ^* B)_{μν}(y) = B_{ψ y}(dψ_y ∂_μ, dψ_y ∂_ν)`. For `ψ = e.symm` with `e` a chart this is the
coordinate matrix of `B` in that chart. -/
def pullbackCoeffs (B : BilinField M) (ψ : E4 → M) (y : E4) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun μ ν => B (ψ y) (mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) ψ y (coordBasis μ))
    (mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) ψ y (coordBasis ν))

/-- Components `X_μ = g(X, ∂_μ)` of the covector `g(X, ·)` along a map `ψ : ℝ⁴ → M`. -/
def loweredCoeffs (g : BilinField M) (X : VecField M) (ψ : E4 → M) (y : E4) : Fin 4 → ℝ :=
  fun μ => g (ψ y) (X (ψ y)) (mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) ψ y (coordBasis μ))

/-- `B` has smooth components in every chart of the atlas. -/
def IsSmoothBilinField (B : BilinField M) : Prop :=
  ∀ e ∈ atlas E4 M, ∀ μ ν : Fin 4,
    ContDiffOn ℝ ∞ (fun y => pullbackCoeffs B e.symm y μ ν) e.target

/-- `B` has real-analytic components in every chart of the atlas. -/
def IsAnalyticBilinField (B : BilinField M) : Prop :=
  ∀ e ∈ atlas E4 M, ∀ μ ν : Fin 4,
    ContDiffOn ℝ ω (fun y => pullbackCoeffs B e.symm y μ ν) e.target

/-- `g` is a Lorentzian metric of signature `(-,+,+,+)`: at every point there is a basis of the
tangent space in which `g` has components `diag(-1,1,1,1)`. -/
def IsLorentzian (g : BilinField M) : Prop :=
  ∀ x : M, ∃ b : Module.Basis (Fin 4) ℝ (TangentSpace 𝓘(ℝ, E4) x),
    ∀ μ ν, g x (b μ) (b ν) = minkowski μ ν

/-- `F` is a 2-form (antisymmetric at every point). -/
def IsTwoForm (F : BilinField M) : Prop := ∀ x v w, F x v w = - F x w v

/-- `T` is a time orientation for `g`: a continuous, everywhere timelike vector field. -/
def IsTimeOrientation (g : BilinField M) (T : VecField M) : Prop :=
  Continuous (fun x => (⟨x, T x⟩ : TangentBundle 𝓘(ℝ, E4) M)) ∧ ∀ x, g x (T x) (T x) < 0

/-- A tangent vector is future-directed timelike. -/
def IsFutureTimelike (g : BilinField M) (T : VecField M) (x : M)
    (v : TangentSpace 𝓘(ℝ, E4) x) : Prop :=
  g x v v < 0 ∧ g x v (T x) < 0

/-- A tangent vector is future-directed causal (nonzero, timelike or null, future-pointing). -/
def IsFutureCausal (g : BilinField M) (T : VecField M) (x : M)
    (v : TangentSpace 𝓘(ℝ, E4) x) : Prop :=
  v ≠ 0 ∧ g x v v ≤ 0 ∧ g x v (T x) < 0

/-- Velocity `γ'(t)` of a curve `γ : ℝ → M`. -/
def velocity (γ : ℝ → M) (t : ℝ) : TangentSpace 𝓘(ℝ, E4) (γ t) :=
  mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E4) γ t (1 : ℝ)

/-- `γ` restricted to `[0,1]` is a `C¹` future-directed timelike curve lying in `U`. -/
def IsFutureTimelikeCurveIn (g : BilinField M) (T : VecField M) (U : Set M) (γ : ℝ → M) :
    Prop :=
  ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E4) 1 γ ∧
    ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U ∧ IsFutureTimelike g T (γ t) (velocity γ t)

/-- `γ` restricted to `[0,1]` is a `C¹` future-directed causal curve lying in `U`. -/
def IsFutureCausalCurveIn (g : BilinField M) (T : VecField M) (U : Set M) (γ : ℝ → M) : Prop :=
  ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E4) 1 γ ∧
    ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U ∧ IsFutureCausal g T (γ t) (velocity γ t)

/-- Chronological future `I⁺_U(p)` of `p` inside `U`. -/
def chronoFuture (g : BilinField M) (T : VecField M) (U : Set M) (p : M) : Set M :=
  {q | ∃ γ : ℝ → M, IsFutureTimelikeCurveIn g T U γ ∧ γ 0 = p ∧ γ 1 = q}

/-- Chronological past `I⁻_U(p)` of `p` inside `U`. -/
def chronoPast (g : BilinField M) (T : VecField M) (U : Set M) (p : M) : Set M :=
  {q | p ∈ chronoFuture g T U q}

/-- Causal future `J⁺_U(p)` of `p` inside `U` (contains `p`). -/
def causalFuture (g : BilinField M) (T : VecField M) (U : Set M) (p : M) : Set M :=
  {p} ∪ {q | ∃ γ : ℝ → M, IsFutureCausalCurveIn g T U γ ∧ γ 0 = p ∧ γ 1 = q}

/-- Causal past `J⁻_U(p)` of `p` inside `U` (contains `p`). -/
def causalPast (g : BilinField M) (T : VecField M) (U : Set M) (p : M) : Set M :=
  {q | p ∈ causalFuture g T U q}

/-- Chronological future of a set, `I⁺(S) = ⋃_{p ∈ S} I⁺(p)` (curves in all of `M`). -/
def chronoFutureSet (g : BilinField M) (T : VecField M) (S : Set M) : Set M :=
  ⋃ p ∈ S, chronoFuture g T univ p

/-- Chronological past of a set, `I⁻(S) = ⋃_{p ∈ S} I⁻(p)` (curves in all of `M`). -/
def chronoPastSet (g : BilinField M) (T : VecField M) (S : Set M) : Set M :=
  ⋃ p ∈ S, chronoPast g T univ p

/-- The open set `U` with the restricted metric is globally hyperbolic: it is causal (no closed
future-directed causal curve in `U`) and all causal diamonds `J⁺_U(p) ∩ J⁻_U(q)` are compact. -/
def IsGloballyHyperbolicOn (g : BilinField M) (T : VecField M) (U : Set M) : Prop :=
  (∀ p ∈ U, ¬ ∃ γ : ℝ → M, IsFutureCausalCurveIn g T U γ ∧ γ 0 = p ∧ γ 1 = p) ∧
  ∀ p ∈ U, ∀ q ∈ U, IsCompact (causalFuture g T U p ∩ causalPast g T U q)

/-- `(g, F)` solves the Einstein–Maxwell equations (electrovacuum) in every chart of the atlas. -/
def IsElectrovac (g F : BilinField M) : Prop :=
  ∀ e ∈ atlas E4 M, ∀ y ∈ e.target,
    EinsteinMaxwellAt (pullbackCoeffs g e.symm) (pullbackCoeffs F e.symm) y

/-- `φ` is a smooth one-parameter group of diffeomorphisms (an `ℝ`-action) of `M` preserving
the metric `g` and the field `F`. -/
def IsSymmetryFlow (g F : BilinField M) (φ : ℝ → M → M) : Prop :=
  (∀ x, φ 0 x = x) ∧ (∀ s t x, φ (s + t) x = φ s (φ t x)) ∧
  ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E4)) 𝓘(ℝ, E4) ∞ (fun p : ℝ × M => φ p.1 p.2) ∧
  (∀ t x v w, g (φ t x) (mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) (φ t) x v)
      (mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) (φ t) x w) = g x v w) ∧
  (∀ t x v w, F (φ t x) (mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) (φ t) x v)
      (mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) (φ t) x w) = F x v w)

/-- The infinitesimal generator `X(x) = d/dt|_{t=0} φ_t(x)` of a flow (a Killing field when `φ`
is a symmetry flow). -/
def flowGenerator (φ : ℝ → M → M) : VecField M :=
  fun x => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E4) (fun t => φ t x) 0 (1 : ℝ)

/-- The asymptotic region `{(t, x⃗) : |x⃗| > R}` of coordinate space. -/
def exteriorRegion (R : ℝ) : Set E4 := {y | R < spatialRadius y}

/-- `ψ` maps the open set `S ⊆ ℝ⁴` diffeomorphically onto `D ⊆ M`. -/
def IsDiffeoOnto (ψ : E4 → M) (S : Set E4) (D : Set M) : Prop :=
  ∃ χ : M → E4, MapsTo ψ S D ∧ MapsTo χ D S ∧ LeftInvOn χ ψ S ∧ RightInvOn χ ψ D ∧
    ContMDiffOn 𝓘(ℝ, E4) 𝓘(ℝ, E4) ∞ ψ S ∧ ContMDiffOn 𝓘(ℝ, E4) 𝓘(ℝ, E4) ∞ χ D

/-- A stationary asymptotically flat end for `(g, F)` adapted to the stationary flow `φ`:
coordinates `ψ` identify `{|x⃗| > R}` (with `R > 0`) with an open subset of `M` such that
1. the stationary flow is time translation: `ψ(y + s ∂_t) = φ_s(ψ y)`;
2. `|g_{μν} - η_{μν}| ≤ C/|x⃗|` and `|∂_σ g_{μν}| ≤ C/|x⃗|²`;
3. `|F_{μν}| ≤ C/|x⃗|²`. -/
structure AsymptoticallyFlatEnd (g F : BilinField M) (φ : ℝ → M → M) where
  /-- Radius of the asymptotic region. -/
  R : ℝ
  /-- Asymptotic coordinates. -/
  ψ : E4 → M
  /-- Decay constant. -/
  C : ℝ
  R_pos : 0 < R
  diffeo : IsDiffeoOnto ψ (exteriorRegion R) (ψ '' exteriorRegion R)
  isOpen_image : IsOpen (ψ '' exteriorRegion R)
  equivariant : ∀ s : ℝ, ∀ y ∈ exteriorRegion R, ψ (y + s • coordBasis 0) = φ s (ψ y)
  metric_decay : ∀ y ∈ exteriorRegion R, ∀ μ ν,
    |pullbackCoeffs g ψ y μ ν - minkowski μ ν| ≤ C / spatialRadius y
  metric_deriv_decay : ∀ y ∈ exteriorRegion R, ∀ μ ν σ,
    |coordPartial (fun z => pullbackCoeffs g ψ z μ ν) σ y| ≤ C / spatialRadius y ^ 2
  field_decay : ∀ y ∈ exteriorRegion R, ∀ μ ν,
    |pullbackCoeffs F ψ y μ ν| ≤ C / spatialRadius y ^ 2

/-- The asymptotic region `M_ext = ψ({|x⃗| > R})` of an end. -/
def AsymptoticallyFlatEnd.region {g F : BilinField M} {φ : ℝ → M → M}
    (E : AsymptoticallyFlatEnd g F φ) : Set M :=
  E.ψ '' exteriorRegion E.R

/-- Domain of outer communications `⟨⟨M_ext⟩⟩ = I⁺(M_ext) ∩ I⁻(M_ext)`. -/
def domainOfOuterCommunications (g : BilinField M) (T : VecField M) (Mext : Set M) : Set M :=
  chronoFutureSet g T Mext ∩ chronoPastSet g T Mext

/-- Black-hole region `M \ I⁻(M_ext)`. -/
def blackHoleRegion (g : BilinField M) (T : VecField M) (Mext : Set M) : Set M :=
  (chronoPastSet g T Mext)ᶜ

/-- Future event horizon `∂ I⁻(M_ext)`. -/
def futureEventHorizon (g : BilinField M) (T : VecField M) (Mext : Set M) : Set M :=
  frontier (chronoPastSet g T Mext)

/-- The standing hypotheses of the no-hair (black-hole uniqueness) problem:
`(M, g, F, T)` is a smooth, time-oriented, 4-dimensional Lorentzian electrovacuum spacetime,
stationary under the symmetry flow `φ`, with a stationary asymptotically flat end `E`, whose
domain of outer communications is globally hyperbolic, which contains a black hole
(nonempty black-hole region) with a connected future event horizon. -/
structure IsStationaryBlackHole (g F : BilinField M) (T : VecField M) (φ : ℝ → M → M)
    (E : AsymptoticallyFlatEnd g F φ) : Prop where
  lorentzian : IsLorentzian g
  smooth_metric : IsSmoothBilinField g
  smooth_field : IsSmoothBilinField F
  twoForm : IsTwoForm F
  timeOrientation : IsTimeOrientation g T
  electrovac : IsElectrovac g F
  stationary : IsSymmetryFlow g F φ
  globallyHyperbolic :
    IsGloballyHyperbolicOn g T (domainOfOuterCommunications g T E.region)
  blackHole_nonempty : (blackHoleRegion g T E.region).Nonempty
  horizon_connected : IsConnected (futureEventHorizon g T E.region)

/-- The open set `D ⊆ M`, with the restrictions of `(g, F)`, is isometric to the Kerr–Newman
domain of outer communications with parameters `(m, a, e)`, the electromagnetic field
matching the Kerr–Newman field up to a constant duality rotation by angle `β`:
there is a diffeomorphism `Ψ` from `{r > r₊}` (Kerr–Schild coordinates) onto `D` with
`Ψ^* g = g_KN` and `Ψ^* F = cos β · F_KN + sin β · ⋆F_KN`. -/
def IsKerrNewmanDOC (g F : BilinField M) (D : Set M) (m a e : ℝ) : Prop :=
  ∃ β : ℝ, ∃ Ψ : E4 → M, IsDiffeoOnto Ψ (kerrNewmanDOC m a e) D ∧
    ∀ y ∈ kerrNewmanDOC m a e,
      pullbackCoeffs g Ψ y = kerrNewmanMetric m a e y ∧
      pullbackCoeffs F Ψ y = Real.cos β • kerrNewmanField a e y
        + Real.sin β • hodgeDual (kerrNewmanMetric m a e y) (kerrNewmanField a e y)

/-- The stationary flow is *static* on `D`: its generator `K` is hypersurface-orthogonal there,
`K ∧ dK = 0`, i.e. `K_[λ ∂_μ K_ν] = 0` in every chart. -/
def IsStaticOn (g : BilinField M) (φ : ℝ → M → M) (D : Set M) : Prop :=
  ∀ e ∈ atlas E4 M, ∀ y ∈ e.target, e.symm y ∈ D → ∀ l μ ν : Fin 4,
    let k := fun z => loweredCoeffs g (flowGenerator φ) e.symm z
    k y l * (coordPartial (fun z => k z ν) μ y - coordPartial (fun z => k z μ) ν y)
    + k y μ * (coordPartial (fun z => k z l) ν y - coordPartial (fun z => k z ν) l y)
    + k y ν * (coordPartial (fun z => k z μ) l y - coordPartial (fun z => k z l) μ y) = 0

/-- `ρ` is an axial symmetry commuting with the stationary flow `φ`: a `2π`-periodic symmetry
flow of `(g, F)` commuting with `φ`, with a nonempty fixed-point set (the axis) and not the
identity. -/
def IsAxialSymmetry (g F : BilinField M) (φ ρ : ℝ → M → M) : Prop :=
  IsSymmetryFlow g F ρ ∧ (∀ x, ρ (2 * Real.pi) x = x) ∧
  (∀ s t x, ρ s (φ t x) = φ t (ρ s x)) ∧
  (∃ x, ∀ s, ρ s x = x) ∧ (∃ s x, ρ s x ≠ x)

/-- The event horizon `H` is a non-degenerate Killing horizon: there is a symmetry flow `χ` of
`(g, F)` whose generator `X` is null on `H ∩ cl(D)`, not identically zero there, and satisfies
`∂_μ (g(X,X)) = -2κ X_μ` on `H ∩ cl(D)` for a constant surface gravity `κ ≠ 0`. -/
def IsNondegenerateHorizon (g F : BilinField M) (H D : Set M) : Prop :=
  ∃ χ : ℝ → M → M, ∃ κ : ℝ, IsSymmetryFlow g F χ ∧ κ ≠ 0 ∧
    (∃ x ∈ H ∩ closure D, flowGenerator χ x ≠ 0) ∧
    ∀ x ∈ H ∩ closure D,
      g x (flowGenerator χ x) (flowGenerator χ x) = 0 ∧
      ∀ e ∈ atlas E4 M, ∀ y ∈ e.target, e.symm y = x → ∀ μ : Fin 4,
        coordPartial (fun z => g (e.symm z) (flowGenerator χ (e.symm z))
          (flowGenerator χ (e.symm z))) μ y
          = -2 * κ * loweredCoeffs g (flowGenerator χ) e.symm y μ

end NoHair


