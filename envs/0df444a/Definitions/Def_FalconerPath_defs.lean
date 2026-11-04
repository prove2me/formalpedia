-- Prove2me | Definitions.Def_FalconerPath_defs
-- name    : FalconerPath_defs
-- status  : Definition
-- author  : @dangnguyen
-- created : 2026-11-03T20:19:55.775632+00:00
-- url     : https://prove2.me/theorems/49fefbbc-0efa-4365-99aa-f1960d99e6a6
-- title:
--   Measures, directional bounds, regular profiles, and distance-measure assembly
-- statement:
--   This file defines the Euclidean measure-theoretic framework for preparing pair measures and assembling a measure on the original distance set. It includes quantitative ball, cap and plate estimates, dyadic regularity profiles, compatible projections, starting configurations, and Fourier shell approximation. All names below belong to `FalconerPath`. Write $R_N=2^N$ and $\delta_N=2^{-N}$. Numerical upper bounds in the extended nonnegative reals use the positive part of a real number. Directional laws are never divided by their fiber masses. Compared with the paper, the definitions extend the radial map by zero on the diagonal, represent spherical measures in ambient Euclidean space, and express the permitted removal of null fibers by almost-everywhere assertions.
--
--   - `Space`: Euclidean space $\mathbb R^n$ with its usual inner product (Section 2.1, Measures, scales and directions).
--   - `PairSet`: a subset of $\mathbb R^n\times\mathbb R^n$, regarded as a pin and source relation (Section 5.1, Definition 5.1 (Availability), label prep:availability).
--   - `unitSphere`: the unit sphere $S^{n-1}=\{w:|w|=1\}$, with the ambient chordal metric (Section 2.1, Measures, scales and directions).
--   - `Carried`: the assertion $\mu(E^c)=0$, which does not require equality of $E$ with the topological support (Section 2.1, Measures, scales and directions).
--   - `Probability`: the assertion $\mu(X)=1$ (Section 2.1, Measures, scales and directions).
--   - `Subprobability`: the assertion $\mu(X)\le1$ (Section 2.1, Measures, scales and directions).
--   - `FiniteBorel`: finiteness of the total mass, $\mu(X)<\infty$, on the given measurable space, which is the canonical Borel space in Euclidean applications (Section 2.1, Measures, scales and directions).
--   - `ballBound`: the inequalities $\mu(B(z,r))\le\max(Kr^s,0)$ for every center $z$ and every $0<r\le1$ with $r\ge\delta$ (Section 2.1, Measures, scales and directions).
--   - `Frostman`: the all-scale bound $\mu(B(z,r))\le\max(Kr^s,0)$ for $0<r\le1$ (Section 2.2, Frostman paragraph citing Mattila1995, Theorem 8.8).
--   - `energy`: the extended nonnegative Riesz energy $I_s(\mu)=\iint|x-y|^{-s}\,d\mu(x)d\mu(y)$ (Section 2.1, Measures, scales and directions).
--   - `normalizedRestriction`: the scalar multiple $\mu(E)^{-1}\mu|_E$, with inverse taken in the extended nonnegative reals, agreeing with normalization when $0<\mu(E)<\infty$ (Section 2.1, Measures, scales and directions).
--   - `radial`: the map $\pi_x(y)=(y-x)/|y-x|$ for $y\ne x$, extended by zero at $y=x$ (Section 2.1, Measures, scales and directions).
--   - `distanceSet`: $\Delta(E)=\{|x-y|:x,y\in E\}$ (Section 1, Theorem 1.1, label thm:main, and its preceding definition of the distance set).
--   - `firstFiber`: $G_x=\{y:(x,y)\in G\}$ (Section 5.1, Definition 5.1 (Availability), label prep:availability).
--   - `secondFiber`: $G^y=\{x:(x,y)\in G\}$ (Section 5.1, Definition 5.1 (Availability), label prep:availability).
--   - `forwardDirection`: the unnormalized directional measure $\lambda_x^G=(\pi_x)_\#(\rho|_{G_x})$ (Section 5.1, Definition 5.1 (Availability), label prep:availability).
--   - `reverseDirection`: the unnormalized reverse directional measure $\widetilde\lambda_y^G=(\pi_y)_\#(\nu|_{G^y})$ (Section 5.1, Definition 5.1 (Availability), label prep:availability).
--   - `capBound`: $\lambda(B(w,u))\le\max(Ku^q,0)$ for every unit $w$ and $0<u\le1$ with $u\ge\delta$ (Section 2.1, Measures, scales and directions).
--   - `directionalPlate`: $\{w\in S^{n-1}:|w\cdot v|\le u\}$, the width-$u$ neighborhood of the linear hyperplane $v^\perp$ when $v$ is unit (Section 5.1, Definition 5.1 (Availability), label prep:availability).
--   - `plateBound`: mass at most $\max(Cu^\zeta,0)$ in each directional plate with unit normal and $0<u\le1$, $u\ge\delta$ (Section 5.1, Lemma 5.3 (One-scale improvement), label prep:one-scale).
--   - `bothCaps`: the cap bound for $\lambda_x^G$ at $\nu$-almost every $x$ and for $\widetilde\lambda_y^G$ at $\rho$-almost every $y$ (Section 5.1, Definition 5.1 (Availability), label prep:availability).
--   - `bothPlates`: the plate bound in both orientations at almost every pin for the corresponding marginal (Section 5.1, Lemma 5.3 (One-scale improvement), label prep:one-scale).
--   - `bothAtRadius`: mass at most $\max(b,0)$ in every radius-$\delta$ cap in both orientations at almost every pin (Section 5.1, Lemma 5.3 (One-scale improvement), label prep:one-scale).
--   - `scale`: the reciprocal final scale $R_N=2^N$ (Section 2.1, Measures, scales and directions).
--   - `mesh`: the final spatial scale $\delta_N=2^{-N}$ (Section 2.1, Measures, scales and directions).
--   - `Available`: availability of $q$: for every $e>0$ there are $c,C>0$ and $N_0$ such that every $N\ge N_0$ admits a Borel $B_N\subset G_N$ with $(\nu\otimes\rho)(B_N)\le C R_N^{-c}$, and both directional laws on $G_N\setminus B_N$ obey $R_N^e u^q$ cap bounds for all $\delta_N\le u\le1$ at almost every pin (Section 5.1, Definition 5.1 (Availability), label prep:availability).
--   - `BoundedSeparated`: $L,a>0$, both supports contained in $\overline B(0,L)$, and $|x-y|\ge a$ for all cross-support pairs (Section 5.1, Lemma 5.3 (One-scale improvement), label prep:one-scale).
--   - `HasBoundedSeparated`: existence of such positive boundedness and separation constants (Section 5.1, Lemma 5.3 (One-scale improvement), label prep:one-scale).
--   - `NoAffineMass`: zero mass on every affine subspace whose direction space has dimension $r$ (Section 5.2, Lemma 5.6 (Simultaneous projected Frostman bounds), label prep:projections and Section 5.3, Lemma 5.9 (Coarse exclusion of heavy plates), label prep:coarse-filter).
--   - `OrthogonalSurjection`: a continuous linear map $P:\mathbb R^n\to\mathbb R^m$ satisfying $PP^*=I$, expressing an orthogonal projection in target coordinates (Section 5.2, Lemma 5.6 (Simultaneous projected Frostman bounds), label prep:projections).
--   - `sphereMeasure`: $\sigma_n=\mathcal H^{n-1}|_{S^{n-1}}$, with the Hausdorff measure normalization supplied by the library (Section 5.2, Lemma 5.7 (Radial $L^p$ estimate), label prep:radial-lp).
--   - `UniformRadialLp`: existence of jointly measurable nonnegative densities $F(x,w)$ and $H(y,w)$ for the two full radial pushforwards, with each $p$th power integral bounded by $\max(L,0)$ at every pin in the corresponding support (Section 5.2, Lemma 5.7 (Radial $L^p$ estimate), label prep:radial-lp).
--   - `RadialLp`: existence of jointly measurable nonnegative densities for the two full radial laws at almost every pin, with both iterated integrals of their $p$th powers finite (Section 5.2, Lemma 5.7 (Radial $L^p$ estimate), label prep:radial-lp).
--   - `dyadicCell`: the translated half-open cube $Q_j(b)=\prod_i[v_i+b_i2^{-j},v_i+(b_i+1)2^{-j})$ for $b\in\mathbb Z^n$ (Section 2.1, Measures, scales and directions and Section 3, Lemma 3.1 (Regular classes), label reg:regularization).
--   - `rootCube`: the translated unit cube $Q_0(0)$ (Section 3, Lemma 3.1 (Regular classes), label reg:regularization).
--   - `LeafUnion`: expressibility as a finite union of depth-$N$ cubes from that translated grid (Section 3, Lemma 3.1 (Regular classes), label reg:regularization).
--   - `RegularClass`: a Borel leaf union $E$ in the root with $\rho(E)\ge R_N^{-\lambda}$ and normalized law $\eta=\rho|_E/\rho(E)$, together with a nondecreasing $n$-Lipschitz profile $m:[0,1]\to[0,n]$, $m(0)=0$. Every occupied depth-$j$ cube has mass between $R_N^{-m(j/N)-C\lambda}$ and $R_N^{-m(j/N)+C\lambda}$. For occupied nested cubes at depths $a\le b\le N$, their mass ratio lies between $R_N^{-[m(b/N)-m(a/N)]-C\lambda}$ and $R_N^{-[m(b/N)-m(a/N)]+C\lambda}$. For every input ball bound with $0\le s\le n$ and $K\ge1$ down to $\delta_N$, the profile satisfies $m(u)\ge su-C\lambda-\log K/\log R_N$ on $[0,1]$ (Section 3, Lemma 3.1 (Regular classes), label reg:regularization).
--   - `tube`: $\{x:|x|\le L,\ \operatorname{dist}(x,a+\mathbb Rw)\le r\}$ (Section 2.1, Measures, scales and directions and Section 4.5, Corollary 4.8 (Small mass of bad directions), label ang:bad-directions).
--   - `lineDistance`: the perpendicular distance of $z^\prime$ to the full line $x+\mathbb R(z-x)$ (Section 3, Lemma 3.2 (Density pruning and multiplication), label reg:pruning-multiplication).
--   - `badDirections`: unit directions $w$ for which at most $\delta^{-q-c}$ parallel tubes of radius $C\delta$, truncated to $\overline B(0,L)$, capture at least $\delta^c$ of the point law. This is the geometric set before its Borel enlargement (Section 4.5, Corollary 4.8 (Small mass of bad directions), label ang:bad-directions).
--   - `CoarseCellPairs`: a relation equal to $(E_1\times E_2)$ intersected with a finite union of pairs of depth-$j$ grid cells (Section 5.3, Lemma 5.9 (Coarse exclusion of heavy plates), label prep:coarse-filter).
--   - `ProductPartition`: a relation equal to a disjoint union of $\ell\le b$ products $X_i\times Y_i$ of Borel spatial sets (Section 5.4, Proposition 5.10 (Starting pair measures), label prep:starting-pairs).
--   - `PreparedFilters`: a decreasing family of Borel $\Gamma_N\subset E_1\times E_2$ with positive product mass in its intersection, a disjoint product partition of size at most $C R_N^{2d\omega}$ for one $C>0$ independent of $N$, and availability of $d/2$ (Section 5.4, Proposition 5.10 (Starting pair measures), label prep:starting-pairs).
--   - `StartingPair`: compact separated subsets $E_1,E_2\subset E$, probabilities carried by them, common constants $\chi,C>0$ giving $(d/2+\chi)$-Frostman bounds, and a unit direction $w$ such that every original cross direction belongs to $B(w,r)$. After these data are fixed there is $0<\omega_0\le1$ such that every $0<\omega\le\omega_0$ admits prepared filters (Section 5.4, Proposition 5.10 (Starting pair measures), label prep:starting-pairs).
--   - `fourier`: $\widehat\mu(\xi)=\int e^{-ix\cdot\xi}\,d\mu(x)$ (Section 2.1, Measures, scales and directions).
--   - `fourierLine`: $\widehat\mu(r)=\int e^{-irt}\,d\mu(t)$ for a positive measure on the line (Section 2.1, Measures, scales and directions).
--   - `fourierComplex`: the same Fourier transform for a complex measure, using integration against its vector measure (Section 2.1, Measures, scales and directions and Section 11.4, Lemma 11.4 (Monotone measure shell criterion), label asm:monotone-shell).
--   - `totalVariation`: the mass $|\tau|(\mathbb R)$ of the variation of a complex measure (Section 2.1, Measures, scales and directions).
--   - `tvError`: the supremum of $\sum_{A\in\mathcal P}|\mu(A)_{\mathrm{real}}-\tau(A)|$ over finite pairwise disjoint Borel collections $\mathcal P$, where the extended mass is converted to a real number as in Lean. For finite $\mu$ this is $\|\mu-\tau\|_{\mathrm{TV}}$ (Section 11.4, Lemma 11.4 (Monotone measure shell criterion), label asm:monotone-shell).
--   - `shell`: $\{r:R_N/2\le|r|\le2R_N\}$, including both frequency signs (Section 11.3, Proposition 11.3 (Decay of the approximating distance measures), label asm:shell-decay).
--   - `shellL2`: $\int_{R_N/2\le|r|\le2R_N}|\widehat\tau(r)|^2\,dr$ for a complex measure, valued in $[0,\infty]$ (Section 11.4, Lemma 11.4 (Monotone measure shell criterion), label asm:monotone-shell).
--   - `positiveShellL2`: the same extended shell integral for a positive measure on the line (Section 11.3, Proposition 11.3 (Decay of the approximating distance measures), label asm:shell-decay).
--   - `distanceWeight`: the nonnegative weight $W(x,y)=|x-y|^{-(d-1)/2}$ using the original dimension $d$ (Section 11.2, equations labeled asm:endpoint-mask and asm:measures).
--   - `filteredDistance`: $\alpha_N=D_\#(W\mathbf1_{\Gamma_N}(\mu_1\otimes\mu_2))$, where $D(x,y)=|x-y|$ is the original distance map (Section 11.2, equations labeled asm:endpoint-mask and asm:measures).
--   - `maskedDistance`: $\tau_N=D_\#(W\mathbf1_{\Gamma_N}\max(\theta_N,0)(\mu_1\otimes\mu_2))$ (Section 11.2, equations labeled asm:endpoint-mask and asm:measures).
--   - `MaskFamily`: a sequence of real functions $\theta_N$ on original pairs (Section 11.2, equations labeled asm:endpoint-mask and asm:measures).
--   - `PositiveMasks`: each $\theta_N$ is Borel measurable and takes values in $[0,1]$ everywhere (Section 11.2, equations labeled asm:endpoint-mask and asm:measures).
--   - `RestoresMass`: positive masks and constants $\eta,C>0$, $N_0$, such that for $N\ge N_0$ the masked measure is dominated by the filtered measure and the difference of their total masses is at most $C R_N^{-\eta}$ (Section 11.2, Lemma 11.2 (Restoration of mass), label asm:retained-measures).
--   - `ShellDecay`: existence of $\gamma,C>0$ and $N_0$ such that the masked distance measure has squared Fourier shell integral at most $C R_N^{-\gamma}$ for $N\ge N_0$ (Section 11.3, Proposition 11.3 (Decay of the approximating distance measures), label asm:shell-decay).
--   - `LocalFiberBounds`: for every $j<J$, retained witness $(x,z)\in G$, and depth-$a_j$ cube $Q$ containing $z$, the full source mass of $z^\prime\in Q$ with $(x,z^\prime)\in E_j$ passing the local test is at most $\max(f_j,0)\rho(Q)$. The radial test is $|\pi_x(z^\prime)-\pi_x(z)|\le C2^{-a_{j+1}}$. The line test replaces this by $\operatorname{dist}(z^\prime,x+\mathbb R(z-x))\le C2^{-a_{j+1}}$ (Section 3, Lemma 3.2 (Density pruning and multiplication), label reg:pruning-multiplication, equation labeled reg:local-fibre).
--   - `CompatibleProjections`: a finite family of orthogonal surjections $P_i$ from the original space, with $P_0$ an isometry and $P_{i+1}=Q_iP_i$ for orthogonal surjections between successive target spaces (Section 5.2, Lemma 5.6 (Simultaneous projected Frostman bounds), label prep:projections).
--   - `gaussianFrames`: the product probability of $m$ independent standard Gaussian vectors in $\mathbb R^d$, providing a concrete parameterization of a Haar-random $m$-plane (Section 2.2, Lemma 2.1 (Finite energy and projection), label conv:energy, part (iii)).
--   - `framePlane`: the linear span of the vectors in such a frame (Section 2.2, Lemma 2.1 (Finite energy and projection), label conv:energy, part (iii)).
--   - `affinePlate`: the set $\{x:\operatorname{dist}(x,V)\le r\}$ for a nonempty affine subspace $V$. The underlying library uses distance zero for the empty subspace (Section 5.3, Lemma 5.9 (Coarse exclusion of heavy plates), label prep:coarse-filter, opening paragraph defining $H_r$).
--   - `AtMostSubpower`: a positive sequence $f_N$ with $f_N\le R_N^\varepsilon$ eventually for every $\varepsilon>0$ (Section 2.3, Subpower losses and fixed gains).
--   - `AtLeastSubpower`: a positive sequence $f_N$ with $f_N\ge R_N^{-\varepsilon}$ eventually for every $\varepsilon>0$ (Section 2.3, Subpower losses and fixed gains).
--   - `ForwardGain`: the uniform one-orientation assertion: there exist $\varepsilon,c,D>0$ and $N_0$ such that for every $N\ge N_0$, all probabilities in $\mathbb R^{k+1}$ with geometry $L,a$ and $s$-Frostman constant $K$, and every Borel relation with both input cap bounds $\delta_N^{-\varepsilon}u^q$ and plate bounds $Cu^\zeta$, there is a Borel subrelation $H$ deleting at most $DR_N^{-c}$ product mass and giving every radius-$\delta_N$ forward cap mass at most $R_N^{-q-c}$ for almost every pin (Section 5.1, Lemma 5.3 (One-scale improvement), label prep:one-scale, first and last proof paragraphs).
--   - `RadialClassData`: data $N,\nu,\rho,v,m,h,G$ for a normalized regular source in $\mathbb R^{k+1}$. Here $h\ge0$, both laws are probabilities with geometry $L,a$, and $\rho$ is carried by the translated root. On $[0,1]$, $m(0)=0$, $m$ is nondecreasing and $(k+1)$-Lipschitz, and $m(u)\ge su-h$. Occupied depth-$j$ cells have masses between $R_N^{-m(j/N)-h}$ and $R_N^{-m(j/N)+h}$. Occupied nested depth-$b$, depth-$c$ cell ratios have bounds $R_N^{-[m(c/N)-m(b/N)]\pm h}$. The Borel relation $G$ is contained in the support product and its reverse directional laws obey cap bounds $R_N^h u^q$ and plate bounds $Cu^\zeta$ for $\delta_N\le u\le1$ at $\rho$-almost every source pin (Section 5.1, Lemma 5.3 (One-scale improvement), label prep:one-scale, paragraphs on normalized classes and the contradiction sequence).
--   - `contactDepths`: the depths $0,\lfloor AN\rfloor,\lfloor BN\rfloor,N$ at indices $0,1,2,3$, with value $N$ at every later index. Floors are truncated to nonnegative integers (Section 5.1, Lemma 5.3 (One-scale improvement), label prep:one-scale, paragraph choosing the four depths).
--   - `StartingGeometry`: compact subsets $E_1,E_2\subset E$ equal to the supports of carried probabilities $\mu_1,\mu_2$, with common $\chi,C>0$, $(d/2+\chi)$-Frostman bounds, positive cross separation, bounded separated supports, and all original cross directions in one radius-$r$ unit-centered cap. It also records orthogonal surjections $P:\mathbb R^d\to\mathbb R^{k+1}$ and $Q:\mathbb R^{k+1}\to\mathbb R^{h+1}$, with $h+1\le k+1\le d$. Both projected pairs have bounded separated supports and the same Frostman exponent and constant. The smallest projected supports are compact. If $d=2k-1$, the sum of the middle projected laws vanishes on every affine $k$-plane (Section 5.4, Proposition 5.10 (Starting pair measures), label prep:starting-pairs, second and third proof paragraphs).
--   - `supportedPullback`: $(E_1\times E_2)\cap(P\times P)^{-1}(G)$ (Section 5.4, Proposition 5.10 (Starting pair measures), label prep:starting-pairs, final proof paragraph).
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf. Definitions for Sections 1, 2, 5 and 11 of the paper.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Definitions for the path through Section 4 of the Falconer paper.
All measures use the canonical Borel measurable spaces. Direction measures live
in the ambient Euclidean space and are carried by its unit sphere. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev PairSet (n : ℕ) := Set (Space n × Space n)

def unitSphere (n : ℕ) : Set (Space n) := Metric.sphere 0 1

def Carried {X : Type*} [MeasurableSpace X] (μ : Measure X) (E : Set X) : Prop :=
  μ Eᶜ = 0

def Probability {X : Type*} [MeasurableSpace X] (μ : Measure X) : Prop := μ univ = 1

def Subprobability {X : Type*} [MeasurableSpace X] (μ : Measure X) : Prop := μ univ ≤ 1

def FiniteBorel {X : Type*} [MeasurableSpace X] (μ : Measure X) : Prop := μ univ < ∞

def ballBound {n : ℕ} (μ : Measure (Space n)) (s K δ : ℝ) : Prop :=
  ∀ z : Space n, ∀ r : ℝ, 0 < r → δ ≤ r → r ≤ 1 →
    μ (Metric.ball z r) ≤ ENNReal.ofReal (K * r ^ s)

/-- Section 1: an all-scale ball bound, with its constant displayed. -/
def Frostman {n : ℕ} (μ : Measure (Space n)) (s K : ℝ) : Prop :=
  ballBound μ s K 0

def energy {n : ℕ} (s : ℝ) (μ : Measure (Space n)) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, edist x y ^ (-s) ∂μ ∂μ

def normalizedRestriction {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (E : Set X) : Measure X := (μ E)⁻¹ • μ.restrict E

def radial {n : ℕ} (x y : Space n) : Space n := ‖y - x‖⁻¹ • (y - x)

def distanceSet {n : ℕ} (E : Set (Space n)) : Set ℝ :=
  {r | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}

def firstFiber {n : ℕ} (G : PairSet n) (x : Space n) : Set (Space n) :=
  {y | (x, y) ∈ G}

def secondFiber {n : ℕ} (G : PairSet n) (y : Space n) : Set (Space n) :=
  {x | (x, y) ∈ G}

/-- Section 4: neither directional measure is divided by its fiber mass. -/
def forwardDirection {n : ℕ} (ρ : Measure (Space n)) (G : PairSet n)
    (x : Space n) : Measure (Space n) :=
  Measure.map (radial x) (ρ.restrict (firstFiber G x))

def reverseDirection {n : ℕ} (ν : Measure (Space n)) (G : PairSet n)
    (y : Space n) : Measure (Space n) :=
  Measure.map (radial y) (ν.restrict (secondFiber G y))

def capBound {n : ℕ} (lam : Measure (Space n)) (q K δ : ℝ) : Prop :=
  ∀ w ∈ unitSphere n, ∀ u : ℝ, 0 < u → δ ≤ u → u ≤ 1 →
    lam (Metric.ball w u) ≤ ENNReal.ofReal (K * u ^ q)

/-- A linear hyperplane is specified by a unit normal; its distance is |w · v|. -/
def directionalPlate {n : ℕ} (v : Space n) (u : ℝ) : Set (Space n) :=
  {w | w ∈ unitSphere n ∧ |inner ℝ w v| ≤ u}

def plateBound {n : ℕ} (lam : Measure (Space n)) (ζ C δ : ℝ) : Prop :=
  ∀ v ∈ unitSphere n, ∀ u : ℝ, 0 < u → δ ≤ u → u ≤ 1 →
    lam (directionalPlate v u) ≤ ENNReal.ofReal (C * u ^ ζ)

/-- Null fibers may be removed, as explicitly allowed in prep:availability. -/
def bothCaps {n : ℕ} (ν ρ : Measure (Space n)) (G : PairSet n)
    (q K δ : ℝ) : Prop :=
  (∀ᵐ x ∂ν, capBound (forwardDirection ρ G x) q K δ) ∧
  (∀ᵐ y ∂ρ, capBound (reverseDirection ν G y) q K δ)

def bothPlates {n : ℕ} (ν ρ : Measure (Space n)) (G : PairSet n)
    (ζ C δ : ℝ) : Prop :=
  (∀ᵐ x ∂ν, plateBound (forwardDirection ρ G x) ζ C δ) ∧
  (∀ᵐ y ∂ρ, plateBound (reverseDirection ν G y) ζ C δ)

def bothAtRadius {n : ℕ} (ν ρ : Measure (Space n)) (G : PairSet n)
    (δ bound : ℝ) : Prop :=
  (∀ᵐ x ∂ν, ∀ w ∈ unitSphere n,
    forwardDirection ρ G x (Metric.ball w δ) ≤ ENNReal.ofReal bound) ∧
  (∀ᵐ y ∂ρ, ∀ w ∈ unitSphere n,
    reverseDirection ν G y (Metric.ball w δ) ≤ ENNReal.ofReal bound)

def scale (N : ℕ) : ℝ := (2 : ℝ) ^ N

def mesh (N : ℕ) : ℝ := (scale N)⁻¹

/-- prep:availability, with an explicit threshold and constants independent of N. -/
def Available {n : ℕ} (ν ρ : Measure (Space n)) (G : ℕ → PairSet n) (q : ℝ) : Prop :=
  ∀ e : ℝ, 0 < e → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ,
    ∀ N ≥ N₀, ∃ B : PairSet n, MeasurableSet B ∧ B ⊆ G N ∧
      (ν.prod ρ) B ≤ ENNReal.ofReal (C * (scale N) ^ (-c)) ∧
      bothCaps ν ρ (G N \ B) q ((scale N) ^ e) (mesh N)

/-- The bounded support and separation constants which one-scale improvement fixes first. -/
def BoundedSeparated {n : ℕ} (ν ρ : Measure (Space n)) (L a : ℝ) : Prop :=
  0 < L ∧ 0 < a ∧ ν.support ⊆ Metric.closedBall 0 L ∧
    ρ.support ⊆ Metric.closedBall 0 L ∧
    ∀ x ∈ ν.support, ∀ y ∈ ρ.support, a ≤ dist x y

def HasBoundedSeparated {n : ℕ} (ν ρ : Measure (Space n)) : Prop :=
  ∃ L a : ℝ, BoundedSeparated ν ρ L a

def NoAffineMass {n : ℕ} (μ : Measure (Space n)) (r : ℕ) : Prop :=
  ∀ V : AffineSubspace ℝ (Space n), Module.finrank ℝ V.direction = r → μ (V : Set _) = 0

/-- Coordinate representation of an orthogonal projection onto an m-plane. -/
def OrthogonalSurjection {n m : ℕ} (P : Space n →L[ℝ] Space m) : Prop :=
  P.comp P.adjoint = ContinuousLinearMap.id ℝ (Space m)

/-- Surface measure, using Mathlib's Hausdorff measure; normalization is immaterial. -/
def sphereMeasure (n : ℕ) : Measure (Space n) :=
  (Measure.hausdorffMeasure ((n : ℝ) - 1)).restrict (unitSphere n)

/-- Joint densities and their uniform L^p bounds at every pin in the supports. -/
def UniformRadialLp {n : ℕ} (ν ρ : Measure (Space n)) (p L : ℝ) : Prop :=
  ∃ F H : Space n × Space n → ℝ,
    Measurable F ∧ Measurable H ∧ (∀ z, 0 ≤ F z) ∧ (∀ z, 0 ≤ H z) ∧
    (∀ x ∈ ν.support,
      Measure.map (radial x) ρ = (sphereMeasure n).withDensity (fun w => ENNReal.ofReal (F (x,w))) ∧
      (∫⁻ w, ENNReal.ofReal (F (x,w) ^ p) ∂sphereMeasure n) ≤ ENNReal.ofReal L) ∧
    (∀ y ∈ ρ.support,
      Measure.map (radial y) ν = (sphereMeasure n).withDensity (fun w => ENNReal.ofReal (H (y,w))) ∧
      (∫⁻ w, ENNReal.ofReal (H (y,w) ^ p) ∂sphereMeasure n) ≤ ENNReal.ofReal L)

/-- The integrated conclusion before compact good-pin restrictions in prep:radial-lp. -/
def RadialLp {n : ℕ} (ν ρ : Measure (Space n)) (p : ℝ) : Prop :=
  ∃ F H : Space n × Space n → ℝ,
    Measurable F ∧ Measurable H ∧ (∀ z, 0 ≤ F z) ∧ (∀ z, 0 ≤ H z) ∧
    (∀ᵐ x ∂ν, Measure.map (radial x) ρ =
      (sphereMeasure n).withDensity (fun w => ENNReal.ofReal (F (x,w)))) ∧
    (∀ᵐ y ∂ρ, Measure.map (radial y) ν =
      (sphereMeasure n).withDensity (fun w => ENNReal.ofReal (H (y,w)))) ∧
    (∫⁻ x, ∫⁻ w, ENNReal.ofReal (F (x,w) ^ p) ∂sphereMeasure n ∂ν) < ∞ ∧
    (∫⁻ y, ∫⁻ w, ENNReal.ofReal (H (y,w) ^ p) ∂sphereMeasure n ∂ρ) < ∞

/-- Half-open translated dyadic grid, on the whole space. -/
def dyadicCell {n : ℕ} (v : Space n) (j : ℕ) (a : Fin n → ℤ) : Set (Space n) :=
  {x | ∀ i, v i + (a i : ℝ) * mesh j ≤ x i ∧
    x i < v i + ((a i : ℝ) + 1) * mesh j}

def rootCube {n : ℕ} (v : Space n) : Set (Space n) := dyadicCell v 0 0

def LeafUnion {n : ℕ} (v : Space n) (N : ℕ) (E : Set (Space n)) : Prop :=
  ∃ A : Finset (Fin n → ℤ), E = ⋃ a ∈ A, dyadicCell v N a

/-- reg:regularization, including its conditional comparisons and inherited lower profile. -/
def RegularClass {n : ℕ} (v : Space n) (N : ℕ) (lam C : ℝ)
    (ρ : Measure (Space n)) (E : Set (Space n)) (m : ℝ → ℝ) : Prop :=
  let η := normalizedRestriction ρ E
  MeasurableSet E ∧ E ⊆ rootCube v ∧ LeafUnion v N E ∧
  ENNReal.ofReal ((scale N) ^ (-lam)) ≤ ρ E ∧
  MonotoneOn m (Icc 0 1) ∧ LipschitzOnWith (Real.toNNReal n) m (Icc 0 1) ∧
  m 0 = 0 ∧ (∀ u ∈ Icc (0:ℝ) 1, m u ∈ Icc (0:ℝ) (n:ℝ)) ∧
  (∀ j ≤ N, ∀ a : Fin n → ℤ, 0 < η (dyadicCell v j a) →
    ENNReal.ofReal ((scale N) ^ (-m ((j:ℝ)/N) - C*lam)) ≤ η (dyadicCell v j a) ∧
    η (dyadicCell v j a) ≤ ENNReal.ofReal ((scale N) ^ (-m ((j:ℝ)/N) + C*lam))) ∧
  (∀ a b : ℕ, a ≤ b → b ≤ N → ∀ i j : Fin n → ℤ,
    dyadicCell v b j ⊆ dyadicCell v a i → 0 < η (dyadicCell v b j) →
    ENNReal.ofReal ((scale N) ^ (-(m ((b:ℝ)/N)-m ((a:ℝ)/N))-C*lam)) ≤
      η (dyadicCell v b j) / η (dyadicCell v a i) ∧
    η (dyadicCell v b j) / η (dyadicCell v a i) ≤
      ENNReal.ofReal ((scale N) ^ (-(m ((b:ℝ)/N)-m ((a:ℝ)/N))+C*lam))) ∧
  (∀ s K : ℝ, 0 ≤ s → s ≤ n → 1 ≤ K → ballBound ρ s K (mesh N) →
    ∀ u ∈ Icc (0:ℝ) 1, s*u-C*lam-Real.log K / Real.log (scale N) ≤ m u)

/-- A bounded-length tube about a line, in a fixed ambient ball. -/
def tube {n : ℕ} (L : ℝ) (w a : Space n) (r : ℝ) : Set (Space n) :=
  {x | ‖x‖ ≤ L ∧ Metric.infDist x (Set.range (fun t : ℝ => a + t • w)) ≤ r}

def lineDistance {n : ℕ} (x z z' : Space n) : ℝ :=
  Metric.infDist z' (Set.range (fun t : ℝ => x + t • (z - x)))

/-- The original geometric bad set, before the Borel enlargement of ang:bad-directions. -/
def badDirections {n : ℕ} (μ : Measure (Space n)) (L C δ q c : ℝ) : Set (Space n) :=
  {w | w ∈ unitSphere n ∧ ∃ A : Finset (Space n),
    (A.card : ℝ) ≤ δ ^ (-q-c) ∧
    ENNReal.ofReal (δ^c) ≤ μ (⋃ a ∈ A, tube L w a (C*δ))}

/-- prep:coarse-filter: the equality is relative to the actual supported product. -/
def CoarseCellPairs {n : ℕ} (E₁ E₂ : Set (Space n)) (Γ : PairSet n)
    (v : Space n) (j : ℕ) : Prop :=
  ∃ A : Finset ((Fin n → ℤ) × (Fin n → ℤ)),
    Γ = (E₁ ×ˢ E₂) ∩ ⋃ a ∈ A, (dyadicCell v j a.1 ×ˢ dyadicCell v j a.2)

def ProductPartition {n : ℕ} (Γ : PairSet n) (bound : ℝ) : Prop :=
  ∃ l : ℕ, (l : ℝ) ≤ bound ∧ ∃ X Y : Fin l → Set (Space n),
    (∀ i, MeasurableSet (X i) ∧ MeasurableSet (Y i)) ∧
    Pairwise (fun i j => Disjoint (X i ×ˢ Y i) (X j ×ˢ Y j)) ∧
    Γ = ⋃ i, X i ×ˢ Y i

/-- The omega-dependent part of prep:starting-pairs; chi and the laws are fixed first. -/
def PreparedFilters {d : ℕ} (μ₁ μ₂ : Measure (Space d))
    (E₁ E₂ : Set (Space d)) (ω : ℝ) (Γ : ℕ → PairSet d) : Prop :=
  (∀ N, MeasurableSet (Γ N) ∧ Γ N ⊆ E₁ ×ˢ E₂) ∧ Antitone Γ ∧
  0 < (μ₁.prod μ₂) (⋂ N, Γ N) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ N,
    ProductPartition (Γ N) (C * (scale N) ^ (2*(d:ℝ)*ω))) ∧
  Available μ₁ μ₂ Γ ((d:ℝ)/2)

/-- The original starting sets and laws, before omega is chosen. -/
structure StartingPair (d : ℕ) (E : Set (Space d)) (patchRadius : ℝ) where
  E₁ : Set (Space d)
  E₂ : Set (Space d)
  μ₁ : Measure (Space d)
  μ₂ : Measure (Space d)
  χ : ℝ
  C : ℝ
  compact₁ : IsCompact E₁
  compact₂ : IsCompact E₂
  subset₁ : E₁ ⊆ E
  subset₂ : E₂ ⊆ E
  prob₁ : Probability μ₁
  prob₂ : Probability μ₂
  carried₁ : Carried μ₁ E₁
  carried₂ : Carried μ₂ E₂
  gap : 0 < χ
  constant_pos : 0 < C
  frostman₁ : Frostman μ₁ ((d:ℝ)/2+χ) C
  frostman₂ : Frostman μ₂ ((d:ℝ)/2+χ) C
  separated : ∃ a : ℝ, 0 < a ∧ ∀ x ∈ E₁, ∀ y ∈ E₂, a ≤ dist x y
  patch : ∃ w ∈ unitSphere d, ∀ x ∈ E₁, ∀ y ∈ E₂,
    radial x y ∈ Metric.ball w patchRadius
  filters : ∃ ω₀ : ℝ, 0 < ω₀ ∧ ω₀ ≤ 1 ∧ ∀ ω : ℝ, 0 < ω → ω ≤ ω₀ →
    ∃ Γ : ℕ → PairSet d, PreparedFilters μ₁ μ₂ E₁ E₂ ω Γ

/-- Section 1 Fourier convention: no factor 2*pi in the exponential. -/
def fourier {n : ℕ} (μ : Measure (Space n)) (ξ : Space n) : ℂ :=
  ∫ x, Complex.exp (-Complex.I * (inner ℝ x ξ : ℂ)) ∂μ

def fourierLine (μ : Measure ℝ) (r : ℝ) : ℂ :=
  ∫ t, Complex.exp (-Complex.I * (r*t : ℝ)) ∂μ

/-- Complex Fourier transform, via integration against a vector measure. -/
def fourierComplex (μ : ComplexMeasure ℝ) (r : ℝ) : ℂ :=
  VectorMeasure.integral μ (fun t => Complex.exp (-Complex.I * (r*t : ℝ)))
    (ContinuousLinearMap.mul ℝ ℂ)

def totalVariation (μ : ComplexMeasure ℝ) : ℝ≥0∞ := μ.variation univ

attribute [local instance] Classical.propDecidable

/-- Positive measures can be compared to complex ones without requiring a finiteness instance. -/
def tvError (α : Measure ℝ) (τ : ComplexMeasure ℝ) : ℝ≥0∞ :=
  ⨆ p : Finset (Set ℝ),
    if (∀ A ∈ p, MeasurableSet A) ∧ Set.PairwiseDisjoint (↑p : Set (Set ℝ)) id then
      ∑ A ∈ p, ENNReal.ofReal ‖(α A).toReal - τ A‖ else 0

def shell (N : ℕ) : Set ℝ := {r | scale N / 2 ≤ |r| ∧ |r| ≤ 2 * scale N}

def shellL2 (τ : ComplexMeasure ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ r in shell N, ENNReal.ofReal (‖fourierComplex τ r‖ ^ 2) ∂volume

def positiveShellL2 (τ : Measure ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ r in shell N, ENNReal.ofReal (‖fourierLine τ r‖ ^ 2) ∂volume

/-- Section 10's fixed weight and positive pushforwards, in the ORIGINAL dimension. -/
def distanceWeight (d : ℕ) (z : Space d × Space d) : ℝ≥0∞ :=
  ENNReal.ofReal (dist z.1 z.2 ^ (-((d:ℝ)-1)/2))

def filteredDistance {d : ℕ} (μ₁ μ₂ : Measure (Space d)) (Γ : PairSet d) : Measure ℝ :=
  Measure.map (fun z : Space d × Space d => dist z.1 z.2)
    (((μ₁.prod μ₂).restrict Γ).withDensity (distanceWeight d))

def maskedDistance {d : ℕ} (μ₁ μ₂ : Measure (Space d)) (Γ : PairSet d)
    (θ : Space d × Space d → ℝ) : Measure ℝ :=
  Measure.map (fun z : Space d × Space d => dist z.1 z.2)
    (((μ₁.prod μ₂).restrict Γ).withDensity
      (fun z => distanceWeight d z * ENNReal.ofReal (θ z)))

def MaskFamily (d : ℕ) := ℕ → Space d × Space d → ℝ

def PositiveMasks {d : ℕ} (θ : MaskFamily d) : Prop :=
  ∀ N, Measurable (θ N) ∧ ∀ z, θ N z ∈ Icc 0 1

/-- The TV error for positive approximants below alpha equals the lost total mass. -/
def RestoresMass {d : ℕ} (μ₁ μ₂ : Measure (Space d)) (Γ : ℕ → PairSet d)
    (θ : MaskFamily d) : Prop :=
  PositiveMasks θ ∧ ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    maskedDistance μ₁ μ₂ (Γ N) (θ N) ≤ filteredDistance μ₁ μ₂ (Γ N) ∧
    (filteredDistance μ₁ μ₂ (Γ N) univ - maskedDistance μ₁ μ₂ (Γ N) (θ N) univ) ≤
      ENNReal.ofReal (C * (scale N) ^ (-η))

def ShellDecay {d : ℕ} (μ₁ μ₂ : Measure (Space d)) (Γ : ℕ → PairSet d)
    (θ : MaskFamily d) : Prop :=
  ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    positiveShellL2 (maskedDistance μ₁ μ₂ (Γ N) (θ N)) N ≤
      ENNReal.ofReal (C * (scale N) ^ (-γ))

/-- The perpendicular-width and radial-width local tests in reg:pruning-multiplication. -/
def LocalFiberBounds {n : ℕ} (lineTest : Bool) (ρ : Measure (Space n))
    (G : PairSet n) (E : ℕ → PairSet n) (v : Space n)
    (a : ℕ → ℕ) (J : ℕ) (f : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ j < J, ∀ x z : Space n, (x,z) ∈ G → ∀ i : Fin n → ℤ,
    z ∈ dyadicCell v (a j) i →
    ρ {z' | z' ∈ dyadicCell v (a j) i ∧ (x,z') ∈ E j ∧
      (if lineTest then lineDistance x z z' ≤ C*mesh (a (j+1))
        else dist (radial x z') (radial x z) ≤ C*mesh (a (j+1)))} ≤
      ENNReal.ofReal (f j) * ρ (dyadicCell v (a j) i)

/-- Successive composed projections, with the identity expressed by an isometry at depth zero. -/
def CompatibleProjections {d J : ℕ} (dims : Fin (J+1) → ℕ)
    (P : (i : Fin (J+1)) → Space d →L[ℝ] Space (dims i)) : Prop :=
  (∀ i, OrthogonalSurjection (P i)) ∧ Isometry (P 0) ∧
  ∀ i : Fin J, ∃ Q : Space (dims i.castSucc) →L[ℝ] Space (dims i.succ),
    OrthogonalSurjection Q ∧ P i.succ = Q.comp (P i.castSucc)

/-- A Gaussian frame spans a Haar-random m-plane (almost surely full rank).
This is an explicit probability parameterization of Section 1's random planes. -/
def gaussianFrames (d m : ℕ) : Measure (Fin m → Space d) :=
  Measure.pi (fun _ : Fin m => ProbabilityTheory.stdGaussian (Space d))

def framePlane {d m : ℕ} (v : Fin m → Space d) : Submodule ℝ (Space d) :=
  Submodule.span ℝ (Set.range v)

def affinePlate {n : ℕ} (V : AffineSubspace ℝ (Space n)) (r : ℝ) : Set (Space n) :=
  {x | Metric.infDist x (V : Set (Space n)) ≤ r}

/-- Section 1: sequence assertions, not a claim that a fixed loss exponent vanishes. -/
def AtMostSubpower (f : ℕ → ℝ) : Prop :=
  (∀ N, 0 < f N) ∧ ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, f N ≤ (scale N)^ε

def AtLeastSubpower (f : ℕ → ℝ) : Prop :=
  (∀ N, 0 < f N) ∧ ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, (scale N)^(-ε) ≤ f N

/-- The one-orientation uniform assertion used in the proof of prep:one-scale.
The retained relation is measured against the original, unnormalized source. -/
def ForwardGain (k : ℕ) (s q ζ L a K C : ℝ) : Prop :=
  ∃ ε c D : ℝ, 0 < ε ∧ 0 < c ∧ 0 < D ∧ ∃ N₀ : ℕ,
    ∀ N ≥ N₀, ∀ ν ρ : Measure (Space (k+1)),
      Probability ν → Probability ρ → BoundedSeparated ν ρ L a →
      Frostman ν s K → Frostman ρ s K →
      ∀ G : PairSet (k+1), MeasurableSet G →
        bothCaps ν ρ G q ((mesh N)^(-ε)) (mesh N) →
        bothPlates ν ρ G ζ C (mesh N) →
        ∃ H : PairSet (k+1), MeasurableSet H ∧ H ⊆ G ∧
          (ν.prod ρ) (G \ H) ≤ ENNReal.ofReal (D*(scale N)^(-c)) ∧
          ∀ᵐ x ∂ν, ∀ w ∈ unitSphere (k+1),
            forwardDirection ρ H x (Metric.ball w (mesh N)) ≤
              ENNReal.ofReal ((scale N)^(-q-c))

/-- Data for one normalized regular source class in the sequential argument.
The single error bounds comparison losses, input cap losses and the lower
profile error; taking their maximum gives precisely this convention. -/
structure RadialClassData (k : ℕ) (s q ζ L a C : ℝ) where
  N : ℕ
  ν : Measure (Space (k+1))
  ρ : Measure (Space (k+1))
  v : Space (k+1)
  m : ℝ → ℝ
  err : ℝ
  err_nonneg : 0 ≤ err
  probν : Probability ν
  probρ : Probability ρ
  geometry : BoundedSeparated ν ρ L a
  root : Carried ρ (rootCube v)
  zero : m 0 = 0
  mono : MonotoneOn m (Icc 0 1)
  lip : LipschitzOnWith (Real.toNNReal (k+1)) m (Icc 0 1)
  lower : ∀ u ∈ Icc (0:ℝ) 1, s*u-err ≤ m u
  cells : ∀ j ≤ N, ∀ i : Fin (k+1) → ℤ, 0 < ρ (dyadicCell v j i) →
    ENNReal.ofReal ((scale N)^(-m ((j:ℝ)/N)-err)) ≤ ρ (dyadicCell v j i) ∧
    ρ (dyadicCell v j i) ≤ ENNReal.ofReal ((scale N)^(-m ((j:ℝ)/N)+err))
  conditional : ∀ b c : ℕ, b ≤ c → c ≤ N → ∀ i j : Fin (k+1) → ℤ,
    dyadicCell v c j ⊆ dyadicCell v b i → 0 < ρ (dyadicCell v c j) →
    ENNReal.ofReal ((scale N)^(-(m ((c:ℝ)/N)-m ((b:ℝ)/N))-err)) ≤
      ρ (dyadicCell v c j) / ρ (dyadicCell v b i) ∧
    ρ (dyadicCell v c j) / ρ (dyadicCell v b i) ≤
      ENNReal.ofReal ((scale N)^(-(m ((c:ℝ)/N)-m ((b:ℝ)/N))+err))
  G : PairSet (k+1)
  measurable : MeasurableSet G
  supported : G ⊆ ν.support ×ˢ ρ.support
  caps : ∀ᵐ z ∂ρ, capBound (reverseDirection ν G z) q ((scale N)^err) (mesh N)
  plates : ∀ᵐ z ∂ρ, plateBound (reverseDirection ν G z) ζ C (mesh N)

/-- The four endpoint depths, with the paper's integer rounding. -/
def contactDepths (N : ℕ) (A B : ℝ) (j : ℕ) : ℕ :=
  if j = 0 then 0 else if j = 1 then ⌊A*N⌋₊ else if j = 2 then ⌊B*N⌋₊ else N

/-- Original compact patches and the two compatible auxiliary spaces in the
starting-pairs proof, before radial restrictions and before choosing omega.
This contains no pair filters or availability assertion. -/
structure StartingGeometry (d : ℕ) (E : Set (Space d)) (r : ℝ) (h k : ℕ) where
  E₁ : Set (Space d)
  E₂ : Set (Space d)
  μ₁ : Measure (Space d)
  μ₂ : Measure (Space d)
  χ : ℝ
  C : ℝ
  compact₁ : IsCompact E₁
  compact₂ : IsCompact E₂
  subset₁ : E₁ ⊆ E
  subset₂ : E₂ ⊆ E
  support₁ : μ₁.support = E₁
  support₂ : μ₂.support = E₂
  prob₁ : Probability μ₁
  prob₂ : Probability μ₂
  carried₁ : Carried μ₁ E₁
  carried₂ : Carried μ₂ E₂
  gap : 0 < χ
  constant_pos : 0 < C
  frostman₁ : Frostman μ₁ ((d:ℝ)/2+χ) C
  frostman₂ : Frostman μ₂ ((d:ℝ)/2+χ) C
  separated : ∃ a : ℝ, 0 < a ∧ ∀ x ∈ E₁, ∀ y ∈ E₂, a ≤ dist x y
  geometry : HasBoundedSeparated μ₁ μ₂
  patch : ∃ w ∈ unitSphere d, ∀ x ∈ E₁, ∀ y ∈ E₂, radial x y ∈ Metric.ball w r
  P : Space d →L[ℝ] Space (k+1)
  Q : Space (k+1) →L[ℝ] Space (h+1)
  orthP : OrthogonalSurjection P
  orthQ : OrthogonalSurjection Q
  dimP : k+1 ≤ d
  dimQ : h+1 ≤ k+1
  middle_geometry : HasBoundedSeparated (Measure.map P μ₁) (Measure.map P μ₂)
  small_geometry : HasBoundedSeparated
    (Measure.map Q (Measure.map P μ₁)) (Measure.map Q (Measure.map P μ₂))
  middle_frostman₁ : Frostman (Measure.map P μ₁) ((d:ℝ)/2+χ) C
  middle_frostman₂ : Frostman (Measure.map P μ₂) ((d:ℝ)/2+χ) C
  small_frostman₁ : Frostman (Measure.map Q (Measure.map P μ₁)) ((d:ℝ)/2+χ) C
  small_frostman₂ : Frostman (Measure.map Q (Measure.map P μ₂)) ((d:ℝ)/2+χ) C
  small_compact₁ : IsCompact (Measure.map Q (Measure.map P μ₁)).support
  small_compact₂ : IsCompact (Measure.map Q (Measure.map P μ₂)).support
  middle_zero : d = 2*k-1 → NoAffineMass (Measure.map P μ₁ + Measure.map P μ₂) k

/-- Pullback of a pair relation, with the two original supported sets retained. -/
def supportedPullback {d m : ℕ} (P : Space d →L[ℝ] Space m)
    (E₁ E₂ : Set (Space d)) (G : PairSet m) : PairSet d :=
  (E₁ ×ˢ E₂) ∩ ((fun z : Space d × Space d => (P z.1, P z.2)) ⁻¹' G)

end FalconerPath


