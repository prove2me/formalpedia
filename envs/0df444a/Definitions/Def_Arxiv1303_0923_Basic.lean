-- Prove2me | Definitions.Def_Arxiv1303_0923_Basic
-- name    : Arxiv1303_0923_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T09:28:36.723112+00:00
-- url     : https://prove2.me/theorems/bcb7bcd5-3ceb-4367-87a2-438721a8e897
-- title:
--   Setting, potentials, point-source and distributed-source scattering problems of Klibanov's phaseless inverse scattering paper
-- statement:
--   Objects of Sections 1, 2, 3.1 and 5.1 of Klibanov, *Phaseless inverse scattering problems in 3-d* (arXiv:1303.0923v1).
--
--   1. **Geometry (Section 1).** $\Omega,G,G_1\subset\mathbb{R}^3$ are bounded domains (nonempty, connected, bounded, open) with $\Omega\subset G_1\subset G$. $G_1$ is convex and its boundary $S=\partial G_1$ is of class $C^1$: near every $y\in S$, $G_1=\{\varphi<0\}$ for a $C^1$ function $\varphi$ with $\nabla\varphi(y)\neq0$. A number $\varepsilon\in(0,1)$ satisfies $\operatorname{dist}(S,\partial G)>2\varepsilon$ and $\operatorname{dist}(S,\partial\Omega)>2\varepsilon$. $B_\omega(y)$ is the open ball of radius $\omega$ about $y$ and $P_\omega(y)=\mathbb{R}^3\setminus B_\omega(y)$.
--   2. **Potentials (eqs. (3), (4)).** $q\in C^m(\mathbb{R}^3)$ is real, $q=0$ outside $G$, and $q\ge0$; $m=2$ for Theorems 1, 2 and $m=4$ for Theorems 3, 4. For $x,x_0\in\mathbb{R}^3$, $\int_{L(x,x_0)}q\,ds=|x-x_0|\int_0^1q(x_0+t(x-x_0))\,dt$ is the integral of $q$ over the segment joining $x_0$ and $x$ with respect to arc length.
--   3. **Point source (eqs. (5)-(9)).** For a real wavenumber $k$ and a source $x_0$, $u(\cdot,x_0,k)$ solves $\Delta u+k^2u-qu=-\delta(x-x_0)$ in $\mathbb{R}^3$ with the radiation conditions $u=O(|x-x_0|^{-1})$ and $\sum_j\frac{x_j-x_{0,j}}{|x-x_0|}\partial_{x_j}u-iku=o(|x-x_0|^{-1})$ as $|x|\to\infty$, and $u=u_0+u_s$ with the incident spherical wave $u_0=\dfrac{e^{ik|x-x_0|}}{4\pi|x-x_0|}$ and the scattered wave $u_s$ of class $C^{m+1}$ away from $x_0$. The formula for $u_0$ is also used for complex $k$.
--   4. **Distributed source (eqs. (13)-(17)).** $g\in C^4(\mathbb{R}^3)$ is real, $g=0$ outside $G$ and $g\neq0$ on $\overline{G_1}$. For real $k$, $v(\cdot,k)\in C^5(\mathbb{R}^3)$ solves $\Delta v+k^2v-qv=-g$ with $v=O(|x|^{-1})$ and $\sum_j\frac{x_j}{|x|}\partial_{x_j}v-ikv=o(|x|^{-1})$. The background field is $v_0(x,k)=\int_G\frac{e^{ik|x-\xi|}}{4\pi|x-\xi|}g(\xi)\,d\xi$ (also for complex $k$), and $v_s=v-v_0$.
--   5. **Cauchy problem (eqs. (68), (69), (74)).** $V(x,t)$, $x\in\mathbb{R}^3$, is a function of $t\in\mathbb{R}$ whose values for $t<0$ play no role and are unconstrained; it is $C^4$ on $\mathbb{R}^3\times[0,\infty)$ and solves $V_{tt}=\Delta V-qV$ for $t>0$, $V(x,0)=0$, $V_t(x,0)=g(x)$. Its time Fourier transform is $F(V)(x,k)=\int_0^\infty V(x,t)e^{ikt}\,dt$ for complex $k$.
--   6. **Half-planes and continuation.** $\mathbb{C}_+=\{k\in\mathbb{C}:\operatorname{Im}k\ge0\}$. A function $F$ is an analytic continuation of a function $f$ of the real variable $k$ to $\{\operatorname{Im}k>-\gamma\}$ if $F$ is holomorphic there and $F(k)=f(k)$ for all real $k$.
--
--   **Formalization Note** The $\delta$-source in (5) is encoded without distributions: the equation is required classically for $x\neq x_0$, and the scattered wave $u-u_0$ is required to be continuous on all of $\mathbb{R}^3$, which rules out any additional singular term at $x_0$. The Hölder exponent $\alpha$ in (9) and in $v\in C^{5+\alpha}$ is dropped (only $C^{m+1}$ and $C^5$ are required); within these classes the solutions are still unique, so the solution sets are the same. The paper calls $\operatorname{dist}(M,N)$ the Hausdorff distance; the deduction of (1), (2) from it only works for the usual distance $\inf\{|y-z|:y\in M,z\in N\}$, which is used here. Condition (74), $V\in C^4(\overline\Phi\times[0,T])$ for every bounded $\Phi$ and $T>0$, is written as $V\in C^4(\mathbb{R}^3\times[0,\infty))$, with one-sided derivatives at $t=0$.
-- source:
--   M. V. Klibanov, Phaseless inverse scattering problems in 3-d, arXiv:1303.0923v1 (2013), https://arxiv.org/abs/1303.0923, Section 1 (eqs. (1)-(9)), Section 2 (eqs. (13)-(17), definition of v_0), Section 3.1 (segment L(x,x_0), Fourier transform F), Section 5.1 (eqs. (68), (69), (74), (76))

import Mathlib

/-!
M. V. Klibanov, *Phaseless inverse scattering problems in 3-d*, arXiv:1303.0923v1 (2013):
the geometric setting and the potentials of Section 1 (eqs. (1)-(4)), the point-source problem
(5)-(9) of Section 1.1, the distributed-source problem (13)-(17) and the background field `v_0`
of Section 2, the line integrals over the segments `L(x, x_0)` of Section 3.1, and the Cauchy
problem (68)-(69) with its time Fourier transform (76) of Section 5.1.
-/

open MeasureTheory

noncomputable section

namespace Arxiv1303_0923

/-- Section 1: the physical space `ℝ³`. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- Section 1, p. 1: a bounded domain of `ℝ³`, i.e. a nonempty, connected, bounded open set. -/
def IsBoundedDomain (D : Set R3) : Prop :=
  IsOpen D ∧ IsConnected D ∧ Bornology.IsBounded D

/-- Section 1, p. 1 ("its boundary `S ∈ C¹`"): near each boundary point `y`, the set `D` is the
sublevel set `{φ < 0}` of a `C¹` function `φ` whose differential at `y` is nonzero. -/
def HasC1Boundary (D : Set R3) : Prop :=
  ∀ y ∈ frontier D, ∃ U ∈ nhds y, ∃ φ : R3 → ℝ, ContDiff ℝ 1 φ ∧ fderiv ℝ φ y ≠ 0 ∧
    D ∩ U = {x | φ x < 0} ∩ U

/-- Section 1, p. 1: the standing geometric setting. `Om` (the paper's `Ω`), `G` and `G1` are
bounded domains with `Ω ⊂ G₁ ⊂ G`, `G₁` is convex with `C¹` boundary `S = ∂G₁`, `ε ∈ (0,1)`, and
`dist(S, ∂G) > 2ε`, `dist(S, ∂Ω) > 2ε`, where `dist` is the distance between two sets (the
infimum of the distances of their points). -/
structure Geometry where
  /-- The domain `Ω` where the potential is unknown. -/
  Om : Set R3
  /-- The domain `G` outside which the potential vanishes. -/
  G : Set R3
  /-- The convex domain `G₁` whose boundary carries the sources and receivers. -/
  G1 : Set R3
  /-- The number `ε`. -/
  eps : ℝ
  Om_domain : IsBoundedDomain Om
  G_domain : IsBoundedDomain G
  G1_domain : IsBoundedDomain G1
  G1_convex : Convex ℝ G1
  G1_boundary : HasC1Boundary G1
  Om_subset : Om ⊆ G1
  G1_subset : G1 ⊆ G
  eps_pos : 0 < eps
  eps_lt_one : eps < 1
  dist_S_G : ∃ δ : ℝ, 2 * eps < δ ∧ ∀ y ∈ frontier G1, ∀ z ∈ frontier G, δ ≤ dist y z
  dist_S_Om : ∃ δ : ℝ, 2 * eps < δ ∧ ∀ y ∈ frontier G1, ∀ z ∈ frontier Om, δ ≤ dist y z

/-- Section 1, p. 1: the surface `S = ∂G₁` carrying the sources and the receivers. -/
def Geometry.S (geo : Geometry) : Set R3 := frontier geo.G1

/-- Section 1, p. 1: `P_ω(y) = ℝ³ \ B_ω(y)`, the complement of the open ball of radius `ω`. -/
def Pset (om : ℝ) (y : R3) : Set R3 := (Metric.ball y om)ᶜ

/-- Section 1, eqs. (3), (4): an admissible potential, `q ∈ Cᵐ(ℝ³)`, `q = 0` outside `G`,
`q ≥ 0`. -/
def IsPotential (G : Set R3) (m : ℕ) (q : R3 → ℝ) : Prop :=
  ContDiff ℝ m q ∧ (∀ x, x ∉ G → q x = 0) ∧ ∀ x, 0 ≤ q x

/-- Section 3.1, eq. (27): `∫_{L(x,x₀)} q(ξ) ds`, the integral of `q` with respect to arc length
over the straight segment `L(x, x₀)` joining `x₀` and `x`. -/
def segInt (q : R3 → ℝ) (x x0 : R3) : ℝ :=
  ‖x - x0‖ * ∫ t in (0 : ℝ)..1, q (x0 + t • (x - x0))

/-- Section 1.1, eq. (9): the incident spherical wave `u₀ = exp(ik|x-x₀|) / (4π|x-x₀|)`, written
for a complex wavenumber `k` so that it can be compared with analytic continuations in `k`. -/
def incWave (x x0 : R3) (k : ℂ) : ℂ :=
  Complex.exp (Complex.I * k * (‖x - x0‖ : ℂ)) / (4 * (Real.pi : ℂ) * (‖x - x0‖ : ℂ))

/-- Section 1.1, eqs. (6), (7) (and, with `x₀ = 0`, Section 2, eqs. (16), (17)): the radiation
conditions `u = O(1/|x-x₀|)` and `Σⱼ (xⱼ - x₀,ⱼ)/|x-x₀| ∂ₓⱼ u - iku = o(1/|x-x₀|)` as
`|x| → ∞`. -/
def IsRadiating (x0 : R3) (k : ℝ) (u : R3 → ℂ) : Prop :=
  Asymptotics.IsBigO (Bornology.cobounded R3) u (fun x => ‖x - x0‖⁻¹) ∧
    Asymptotics.IsLittleO (Bornology.cobounded R3)
      (fun x => fderiv ℝ u x (‖x - x0‖⁻¹ • (x - x0)) - Complex.I * (k : ℂ) * u x)
      (fun x => ‖x - x0‖⁻¹)

/-- Section 1.1, eqs. (5)-(9): `u = u(·, x₀, k)` is the solution of
`Δu + k²u - q u = -δ(x - x₀)` with the radiation conditions (6), (7), of the form `u = u₀ + u_s`
with `u_s ∈ C^{m+1}` away from `x₀`. The point source is encoded by requiring the scattered wave
`u_s = u - u₀` to be continuous on all of `ℝ³` (so that `u - u₀` carries no singularity at `x₀`)
and the equation to hold classically for `x ≠ x₀`. -/
def IsPointSourceSolution (m : ℕ) (q : R3 → ℝ) (x0 : R3) (k : ℝ) (u : R3 → ℂ) : Prop :=
  Continuous (fun x => u x - incWave x x0 k) ∧
    ContDiffOn ℝ (m + 1 : ℕ) (fun x => u x - incWave x x0 k) {x0}ᶜ ∧
    (∀ x, x ≠ x0 → Laplacian.laplacian u x + (k : ℂ) ^ 2 * u x - (q x : ℂ) * u x = 0) ∧
    IsRadiating x0 k u

/-- Section 2, eqs. (13), (14): the source function, `g ∈ C⁴(ℝ³)`, `g = 0` outside `G`, and
`g ≠ 0` on the closure of `G₁`. -/
def IsSourceTerm (geo : Geometry) (g : R3 → ℝ) : Prop :=
  ContDiff ℝ 4 g ∧ (∀ x, x ∉ geo.G → g x = 0) ∧ ∀ x ∈ closure geo.G1, g x ≠ 0

/-- Section 2, eqs. (15)-(17): `v = v(·, k) ∈ C⁵(ℝ³)` solves `Δv + k²v - q v = -g` on `ℝ³` with
the radiation conditions `v = O(1/|x|)` and `Σⱼ xⱼ/|x| ∂ₓⱼ v - ikv = o(1/|x|)` as `|x| → ∞`. -/
def IsSourceSolution (q g : R3 → ℝ) (k : ℝ) (v : R3 → ℂ) : Prop :=
  ContDiff ℝ 5 v ∧
    (∀ x, Laplacian.laplacian v x + (k : ℂ) ^ 2 * v x - (q x : ℂ) * v x = -(g x : ℂ)) ∧
    IsRadiating 0 k v

/-- Section 2, p. 6: the background field `v₀(x,k) = ∫_G exp(ik|x-ξ|)/(4π|x-ξ|) g(ξ) dξ`, the
solution of (15)-(17) for `q ≡ 0`, written for a complex wavenumber `k`. -/
def bgField (G : Set R3) (g : R3 → ℝ) (x : R3) (k : ℂ) : ℂ :=
  ∫ ξ in G, incWave x ξ k * (g ξ : ℂ)

/-- Section 5.1, eqs. (68), (69), (74): `V` solves the Cauchy problem `V_tt = ΔV - q V` on
`ℝ³ × (0,∞)`, `V(x,0) = 0`, `V_t(x,0) = g(x)`, and `V ∈ C⁴(Φ̄ × [0,T])` for every bounded `Φ`
and every `T > 0` (equivalently, `V` is `C⁴` on `ℝ³ × [0,∞)`). -/
def IsCauchySolution (q g : R3 → ℝ) (V : R3 → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 4 (fun p : R3 × ℝ => V p.1 p.2) (Set.univ ×ˢ Set.Ici 0) ∧
    (∀ x : R3, ∀ t : ℝ, 0 < t →
      deriv (deriv (V x)) t = Laplacian.laplacian (fun y => V y t) x - q x * V x t) ∧
    (∀ x, V x 0 = 0) ∧ (∀ x, derivWithin (V x) (Set.Ici 0) 0 = g x)

/-- Section 3.1 (operator `F`) and Section 5.1, eq. (76): the Fourier transform in time
`F(V)(x,k) = ∫₀^∞ V(x,t) e^{ikt} dt`, written for a complex wavenumber `k`. -/
def timeFT (V : R3 → ℝ → ℝ) (x : R3) (k : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), (V x t : ℂ) * Complex.exp (Complex.I * k * (t : ℂ))

/-- Section 1.1, p. 3: the closed upper half-plane `ℂ₊ = {k ∈ ℂ : Im k ≥ 0}`. -/
def upperHalf : Set ℂ := {k | 0 ≤ k.im}

/-- Section 1.1, p. 3: the half-plane `{k ∈ ℂ : Im k > -γ}`. -/
def shiftedHalfPlane (γ : ℝ) : Set ℂ := {k | -γ < k.im}

/-- Sections 1.1 and 3.1: `F` is an analytic continuation of the function `f` of the real
wavenumber `k` from the real line to the half-plane `{Im k > -γ}`. -/
def IsContinuation (γ : ℝ) (f : ℝ → ℂ) (F : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ F (shiftedHalfPlane γ) ∧ ∀ k : ℝ, F k = f k

end Arxiv1303_0923


