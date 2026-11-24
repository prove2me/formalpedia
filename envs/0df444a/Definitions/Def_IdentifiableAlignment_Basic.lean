-- Prove2me | Definitions.Def_IdentifiableAlignment_Basic
-- name    : IdentifiableAlignment_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T03:15:14.59481+00:00
-- url     : https://prove2.me/theorems/29349b56-d1e5-4981-8a06-11c8bb9bb665
-- title:
--   Data and latent metric measure spaces, couplings and alignment objectives
-- statement:
--   Objects of Sections 2–4 and Appendices A–B of Syrota, Lopez i Serrano, Franck and Hauberg (2026).
--
--   1. **Manifolds.** Every manifold is a smooth manifold of dimension $d\ge1$, possibly with smooth boundary (modelled on the half-space $\mathbb{H}^d$), with a smooth Riemannian metric $g$; its distance is the Riemannian (shortest-path) distance $d_g(x,y)=\inf_\gamma\int\sqrt{g(\dot\gamma,\dot\gamma)}$, and it carries its Borel $\sigma$-algebra. $g_z(v,w)$ denotes the Riemannian inner product on $T_z$.
--   2. **Data and latent mm-spaces (H1, H2).** The data manifold $\mathcal M$ is compact and connected, and $P_{\mathcal M}$ is a probability measure with a smooth positive density: $P_{\mathcal M}=\rho\,\mathrm{dVol}_g$ with $\rho\in C^\infty_{>0}(\mathcal M)$. A model is a diffeomorphism $f:\mathcal Z\to\mathcal M$ such that the Riemannian metric of the latent space $\mathcal Z$ is the pullback $f^*g^{\mathcal M}$, i.e. $g_z(v,w)=g^{\mathcal M}_{f(z)}(df_z v,df_z w)$; the latent distance $d_a$ is the Riemannian distance of this metric and $P_a=(f_a^{-1})_\#P_{\mathcal M}$. The alignment map is $A=f_b^{-1}\circ f_a$ (Definition 2.1).
--   3. **Isomorphisms and symmetries.** $T:X\to Y$ is an isomorphism of mm-spaces $(X,d_X,\mu)\to(Y,d_Y,\nu)$ if it is a distance-preserving bijection with $T_\#\mu=\nu$. A symmetry of $(X,d_X,\mu)$ is an isomorphism of the space with itself. **C1** (symmetry breaking): the identity is the only symmetry of $(\mathcal M,d_{\mathcal M},P_{\mathcal M})$.
--   4. **Couplings and objectives.** $\Pi(\mu,\nu)$ is the set of measures on $X\times Y$ with marginals $\mu,\nu$; $(\mathrm{id}\times T)_\#\mu$ is the coupling induced by $T$. The Gromov–Wasserstein objective is $J_{\mathrm{GW}}(\eta)=\iint|d_X(x,x')-d_Y(y,y')|^2\,d\eta(x,y)\,d\eta(x',y')$ (eq. 2).
--   5. **LDDs.** The local distance distribution of $x$ is $\Phi(x,r)=\mu(\bar B(x,r))$, the distribution function of $d_X(x,X')$, $X'\sim\mu$. $W_2^2(\alpha,\beta)=\inf_{\gamma\in\Pi(\alpha,\beta)}\int(s-s')^2d\gamma$ for laws on $\mathbb R$, $W_2=(W_2^2)^{1/2}$. The LDD-LP cost is $c(x,y)=W_2^2(\Phi_X(x,\cdot),\Phi_Y(y,\cdot))$, $J_{\mathrm{LDD}}(\eta)=\int c\,d\eta$ (eq. 3), and $J_\beta=(1-\beta)J_{\mathrm{GW}}+\beta J_{\mathrm{LDD}}$ (eq. 4). **C2** (distinguishable points): the collision set $\mathcal C=\{x:\Phi(x',\cdot)=\Phi(x,\cdot)\text{ for some }x'\neq x\}$ is $P_{\mathcal M}$-null.
--   6. **Samples.** The empirical distribution of $z_1,\dots,z_n$ is $\frac1n\sum_i\delta_{z_i}$. Weak convergence means $\int f\,d\eta_n\to\int f\,d\eta$ for all bounded continuous $f$. The fitting objective is $F_\eta(T)=\int d_Y(T(x),y)^2d\eta(x,y)$.
--   7. **Quantitative objects (Appendix B.3).** $W_1(\mu,\nu)=\inf_{\gamma\in\Pi(\mu,\nu)}\int d\,d\gamma$; the margin $m(t)=\inf\{\|\Phi(x,\cdot)-\Phi(x',\cdot)\|_\infty:d(x,x')\ge t\}$ (Definition 4.3); the Lipschitz condition $|\Phi(x,r)-\Phi(x,r')|\le K|r-r'|$ for $r,r'\ge0$ (eq. 11); the LDD estimation error $\delta=\sup_zW_2(\hat\Phi_a(z,\cdot),\Phi_a(z,\cdot))+\sup_wW_2(\hat\Phi_b(w,\cdot),\Phi_b(w,\cdot))$.
--   8. **Densities (Proposition 3.2).** $C^\infty_{>0}(\mathcal M)$ is the set of smooth positive functions, $\rho\,\mathrm{dVol}_g$ the associated measure, and $\mathcal D_{\mathrm{rigid}}$ the set of $\rho\in C^\infty_{>0}(\mathcal M)$ for which $\mathrm{Aut}(\mathcal M,d_g,\rho\,\mathrm{dVol}_g)=\{\mathrm{id}\}$. $\rho_n\to\rho$ in the Whitney $C^\infty$ topology if, in every chart, every derivative of $\rho_n$ converges uniformly on compact subsets of the chart image to that of $\rho$ (Definition A.23).
--
--   **Formalization Note** The data manifold is an abstract compact connected Riemannian manifold rather than a submanifold of $\mathbb R^D$; by the Nash embedding theorem the two settings describe the same metric measure spaces, and none of the statements refers to the ambient space. The reference measure $\mathrm{dVol}_g$ is taken to be the $d$-dimensional Hausdorff measure of the Riemannian distance, which is a positive constant (depending only on $d$) times the Riemannian volume; this changes neither "has a smooth positive density" nor any automorphism group. All costs are valued in $[0,\infty]$. The margin is used only for $0<t\le\operatorname{diam}\mathcal M$.
-- source:
--   Syrota, Lopez i Serrano, Franck and Hauberg, Identifiable alignment of unpaired representations, arXiv:2611.11460v1 (2026), Section 2 (H1, H2, Definition 2.1), Section 3 (C1), Section 4 (eqs. (2)-(5), C2, Definition 4.3), Appendix A (Definitions A.9, A.18, A.23), Appendix B.3 (eq. (13))

import Mathlib

/-!
Syrota, Lopez i Serrano, Franck and Hauberg, *Identifiable alignment of unpaired representations*,
arXiv:2611.11460v1 (2026): the data and latent metric measure spaces of Section 2 (hypotheses H1,
H2, Definition 2.1), the symmetry-breaking and distinguishable-points conditions C1 and C2 of
Sections 3 and 4.1, the Gromov--Wasserstein, LDD-LP and fused objectives (equations (2), (3), (4)),
the margin (Definition 4.3, eq. (5)), the growth bound of eq. (11), and the Whitney topology on densities (Appendix A, Definition A.23).

Manifolds are smooth, of dimension `d ≥ 1`, possibly with boundary, modelled on the Euclidean
half-space `𝓡∂ d`; their distance is the Riemannian distance (`IsRiemannianManifold`).
-/

open MeasureTheory Set Filter Topology Bundle
open scoped ENNReal ContDiff Manifold

noncomputable section

namespace IdentifiableAlignment

section MetricMeasure

variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [MetricSpace Y] [MeasurableSpace Y]

/-- Appendix A, Definition A.9: `T` is an isomorphism of the mm-spaces `(X, d_X, μ)` and
`(Y, d_Y, ν)`: a distance-preserving bijection with `T_# μ = ν`. -/
def IsMMIso (μ : Measure X) (ν : Measure Y) (T : X → Y) : Prop :=
  Function.Bijective T ∧ Isometry T ∧ μ.map T = ν

/-- Section 3 (p. 4) and Definition A.9: a symmetry of `(X, d_X, μ)`, i.e. an element of
`Aut(X, d_X, μ)`: a distance-preserving bijection of `X` that preserves `μ`. -/
def IsSymmetry (μ : Measure X) (S : X → X) : Prop :=
  IsMMIso μ μ S

/-- Condition C1 (symmetry breaking, Section 3, p. 5): the identity is the only symmetry. -/
def SymmetryBreaking (μ : Measure X) : Prop :=
  ∀ S : X → X, IsSymmetry μ S → S = id

/-- Section 4 (p. 5) and Appendix A, Definition A.18: the couplings `Π(μ, ν)`, the measures on
`X × Y` with marginals `μ` and `ν`. -/
def couplings {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X)
    (ν : Measure Y) : Set (Measure (X × Y)) :=
  {η | η.map Prod.fst = μ ∧ η.map Prod.snd = ν}

/-- `η` is an optimal coupling of the problem `min_{η ∈ Π(μ, ν)} J(η)`. -/
def IsOptimalCoupling (J : Measure (X × Y) → ℝ≥0∞) (μ : Measure X) (ν : Measure Y)
    (η : Measure (X × Y)) : Prop :=
  η ∈ couplings μ ν ∧ ∀ η' ∈ couplings μ ν, J η ≤ J η'

/-- Section 4 (p. 5): the coupling `(id × T)_# μ` induced by a map `T`. -/
def inducedCoupling (μ : Measure X) (T : X → Y) : Measure (X × Y) :=
  μ.map (fun x => (x, T x))

/-- Equation (2), Section 4, p. 5: the Gromov--Wasserstein objective
`J_GW(η) = ∬ |d_X(x, x') - d_Y(y, y')|² dη(x, y) dη(x', y')`. -/
def gwCost (η : Measure (X × Y)) : ℝ≥0∞ :=
  ∫⁻ p, ∫⁻ q, ENNReal.ofReal ((dist p.1 q.1 - dist p.2 q.2) ^ 2) ∂η ∂η

/-- Section 4.1, p. 6: the local distance distribution (LDD) `Φ(x, r) = μ(B̄(x, r))`. -/
def ldd (μ : Measure X) (x : X) (r : ℝ) : ℝ :=
  (μ (Metric.closedBall x r)).toReal

/-- The law of `d_X(x, x')` for `x' ∼ μ`; its distribution function is `ldd μ x`. -/
def distLaw (μ : Measure X) (x : X) : Measure ℝ :=
  μ.map (fun y => dist x y)

/-- The squared quadratic Wasserstein distance between two laws on `ℝ`,
`W₂²(α, β) = inf_{γ ∈ Π(α, β)} ∫ (s - s')² dγ(s, s')`. -/
def w2sq (α β : Measure ℝ) : ℝ≥0∞ :=
  ⨅ γ ∈ couplings α β, ∫⁻ p, ENNReal.ofReal ((p.1 - p.2) ^ 2) ∂γ

/-- The quadratic Wasserstein distance `W₂` between two laws on `ℝ`. -/
def w2 (α β : Measure ℝ) : ℝ≥0∞ :=
  w2sq α β ^ (1 / 2 : ℝ)

/-- Equation (3), Section 4.1, p. 6: the LDD-LP cost `c(x, y) = W₂²(Φ_X(x, ·), Φ_Y(y, ·))`, where
`Φ_X` and `Φ_Y` are the LDDs of `μ` and `ν`. -/
def lddCost (μ : Measure X) (ν : Measure Y) (x : X) (y : Y) : ℝ≥0∞ :=
  w2sq (distLaw μ x) (distLaw ν y)

/-- Equation (3), Section 4.1, p. 6: the LDD-LP objective `J_LDD(η) = ∫ c dη`, with the LDDs of
`μ` and `ν`. -/
def lddLP (μ : Measure X) (ν : Measure Y) (η : Measure (X × Y)) : ℝ≥0∞ :=
  ∫⁻ p, lddCost μ ν p.1 p.2 ∂η

/-- Equation (4), Section 4.1, p. 6: the fused objective `J_β = (1 - β) J_GW + β J_LDD`. -/
def fusedCost (β : ℝ) (μ : Measure X) (ν : Measure Y) (η : Measure (X × Y)) : ℝ≥0∞ :=
  ENNReal.ofReal (1 - β) * gwCost η + ENNReal.ofReal β * lddLP μ ν η

/-- Condition C2, Section 4.1, p. 6: the collision set
`C = {x : Φ(x', ·) = Φ(x, ·) for some x' ≠ x}`. -/
def collisionSet (μ : Measure X) : Set X :=
  {x | ∃ x', x' ≠ x ∧ ldd μ x' = ldd μ x}

/-- Condition C2 (distinguishable points, Section 4.1, p. 6): the collision set is `μ`-null. -/
def DistinguishablePoints (μ : Measure X) : Prop :=
  μ (collisionSet μ) = 0

/-- Section 4.2, p. 7: the empirical distribution `(1/n) ∑ᵢ δ_{zᵢ}` of a sample `z₁, …, zₙ`. -/
def empMeasure {Z : Type*} [MeasurableSpace Z] {n : ℕ} (z : Fin n → Z) : Measure Z :=
  (n : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (z i)

/-- Weak convergence of measures: `∫ f dηₙ → ∫ f dη` for every bounded continuous `f`. -/
def WeakTendsto (ηs : ℕ → Measure X) (η : Measure X) : Prop :=
  ∀ f : BoundedContinuousFunction X ℝ, Tendsto (fun n => ∫ x, f x ∂(ηs n)) atTop (𝓝 (∫ x, f x ∂η))

/-- Proposition B.14 (iii), p. 28: the fitting objective `F_η(T) = ∫ d_Y(T(x), y)² dη(x, y)`. -/
def fitCost (η : Measure (X × Y)) (T : X → Y) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (dist (T p.1) p.2 ^ 2) ∂η

/-- Proposition B.14 (iii), p. 28: `T` minimises `F_η` over the class `𝒯`. -/
def IsFitMinimizer (𝒯 : Set C(X, Y)) (η : Measure (X × Y)) (T : C(X, Y)) : Prop :=
  T ∈ 𝒯 ∧ ∀ T' ∈ 𝒯, fitCost η T ≤ fitCost η T'

/-- Proposition B.15, p. 30: the Wasserstein distance `W₁(μ, ν) = inf_{γ ∈ Π(μ, ν)} ∫ d dγ`. -/
def w1 (μ ν : Measure X) : ℝ≥0∞ :=
  ⨅ γ ∈ couplings μ ν, ∫⁻ p, edist p.1 p.2 ∂γ

/-- The supremum distance `‖Φ(x, ·) - Φ(x', ·)‖_∞` between two LDDs. -/
def lddSupDist (μ : Measure X) (x x' : X) : ℝ :=
  ⨆ r : ℝ, |ldd μ x r - ldd μ x' r|

/-- Definition 4.3, eq. (5), p. 6: the margin
`m(t) = inf {‖Φ(x, ·) - Φ(x', ·)‖_∞ : d(x, x') ≥ t}` (used for `0 < t ≤ diam`). -/
def margin (μ : Measure X) (t : ℝ) : ℝ :=
  ⨅ p : {p : X × X // t ≤ dist p.1 p.2}, lddSupDist μ p.1.1 p.1.2

/-- Equation (11), Appendix B.3, p. 30: ball masses grow at rate at most `K`,
`|Φ(x, r) - Φ(x, r')| ≤ K |r - r'|` for all `x` and `r, r' ≥ 0`. -/
def IsLddLipschitz (μ : Measure X) (K : ℝ) : Prop :=
  ∀ x r r', 0 ≤ r → 0 ≤ r' → |ldd μ x r - ldd μ x r'| ≤ K * |r - r'|

/-- Appendix B.3, p. 30: the LDD estimation error
`δ = sup_x W₂(Φ̂_X(x, ·), Φ_X(x, ·)) + sup_y W₂(Φ̂_Y(y, ·), Φ_Y(y, ·))`, where `Φ_X, Φ̂_X` are the
LDDs of `μ, μhat` and `Φ_Y, Φ̂_Y` those of `ν, νhat`. -/
def lddEstError (μ μhat : Measure X) (ν νhat : Measure Y) : ℝ≥0∞ :=
  (⨆ x, w2 (distLaw μhat x) (distLaw μ x)) + ⨆ y, w2 (distLaw νhat y) (distLaw ν y)

end MetricMeasure

section Riemannian

variable {d : ℕ} [NeZero d]

/-- The Riemannian inner product `g_z(v, w)` on the tangent space `T_z Z`. -/
def riemInner {Z : Type*} [TopologicalSpace Z] [ChartedSpace (EuclideanHalfSpace d) Z]
    [IsManifold (𝓡∂ d) ∞ Z] [RiemannianBundle (fun z : Z => TangentSpace (𝓡∂ d) z)]
    (z : Z) (v w : TangentSpace (𝓡∂ d) z) : ℝ :=
  (RiemannianBundle.g (E := fun z : Z => TangentSpace (𝓡∂ d) z)).inner z v w

variable {Z Z' M : Type*}
  [TopologicalSpace Z] [ChartedSpace (EuclideanHalfSpace d) Z] [IsManifold (𝓡∂ d) ∞ Z]
  [RiemannianBundle (fun z : Z => TangentSpace (𝓡∂ d) z)]
  [TopologicalSpace Z'] [ChartedSpace (EuclideanHalfSpace d) Z'] [IsManifold (𝓡∂ d) ∞ Z']
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace d) M] [IsManifold (𝓡∂ d) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓡∂ d) x)]

/-- Hypothesis H2 (model coordinates, Section 2, p. 3) and the pullback metric
`g_Z = f^* g^M` (Section 2, "Latent metric measure spaces", p. 4): `f : Z → M` is a diffeomorphism and the Riemannian metric of
the latent space `Z` is `g_Z(v, w) = g^M(df v, df w)`. -/
def IsModelCoordinates (f : Z ≃ₘ^∞⟮𝓡∂ d, 𝓡∂ d⟯ M) : Prop :=
  ∀ (z : Z) (v w : TangentSpace (𝓡∂ d) z),
    riemInner z v w =
      riemInner (f z) (mfderiv (𝓡∂ d) (𝓡∂ d) f z v) (mfderiv (𝓡∂ d) (𝓡∂ d) f z w)

/-- Definition 2.1, eq. (1), p. 3: the alignment map `A = f_b⁻¹ ∘ f_a : Z_a → Z_b`. -/
def alignMap (fa : Z ≃ₘ^∞⟮𝓡∂ d, 𝓡∂ d⟯ M) (fb : Z' ≃ₘ^∞⟮𝓡∂ d, 𝓡∂ d⟯ M) : Z → Z' :=
  fb.symm ∘ fa

variable [MeasurableSpace Z] [MeasurableSpace M]

/-- Section 2, p. 4: the distribution of representations `P_a = (f_a⁻¹)_# P_M`. -/
def latentLaw (P : Measure M) (f : Z ≃ₘ^∞⟮𝓡∂ d, 𝓡∂ d⟯ M) : Measure Z :=
  P.map f.symm

end Riemannian

section Densities

variable (d : ℕ) [NeZero d] (M : Type*) [MetricSpace M] [ChartedSpace (EuclideanHalfSpace d) M]
  [MeasurableSpace M] [BorelSpace M]

/-- Hypothesis H1 (ii) and Proposition 3.2: the measure `ρ dVol_g` of a density `ρ`. The reference
measure is the `d`-dimensional Hausdorff measure of the Riemannian distance, which equals the
Riemannian volume `dVol_g` up to a positive factor depending only on `d`. -/
def densityMeasure {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] (ρ : M → ℝ) :
    Measure M :=
  (μH[(d : ℝ)] : Measure M).withDensity (fun x => ENNReal.ofReal (ρ x))

/-- Proposition 3.2, p. 5: the smooth positive functions `C^∞_{>0}(M)`. -/
def smoothPosDensities : Set (M → ℝ) :=
  {ρ | ContMDiff (𝓡∂ d) 𝓘(ℝ) ∞ ρ ∧ ∀ x, 0 < ρ x}

/-- Hypothesis H1 (ii), Section 2, p. 3: `P` has a smooth positive density on `M`. -/
def HasSmoothPosDensity {M : Type*} [MetricSpace M] [ChartedSpace (EuclideanHalfSpace d) M]
    [MeasurableSpace M] [BorelSpace M] (P : Measure M) : Prop :=
  ∃ ρ ∈ smoothPosDensities d M, P = densityMeasure d ρ

/-- Proposition B.8, p. 23: `D_rigid`, the smooth positive densities `ρ` for which
`Aut(M, g, ρ dVol_g)` is trivial. -/
def rigidDensities : Set (M → ℝ) :=
  {ρ | ρ ∈ smoothPosDensities d M ∧ SymmetryBreaking (densityMeasure d ρ)}

/-- Definition A.23, p. 20: convergence `ρₙ → ρ` in the Whitney `C^∞` topology of the compact
manifold `M`: in every chart, every derivative converges uniformly on every compact subset of the
chart's image. -/
def CinfTendsto {M : Type*} [MetricSpace M] [ChartedSpace (EuclideanHalfSpace d) M]
    (ρs : ℕ → M → ℝ) (ρ : M → ℝ) : Prop :=
  ∀ (x : M) (k : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))), IsCompact K →
    K ⊆ (extChartAt (𝓡∂ d) x).target →
    TendstoUniformlyOn
      (fun n y => iteratedFDerivWithin ℝ k (ρs n ∘ (extChartAt (𝓡∂ d) x).symm)
        (extChartAt (𝓡∂ d) x).target y)
      (fun y => iteratedFDerivWithin ℝ k (ρ ∘ (extChartAt (𝓡∂ d) x).symm)
        (extChartAt (𝓡∂ d) x).target y)
      atTop K

end Densities

end IdentifiableAlignment


