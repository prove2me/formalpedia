-- Prove2me | Definitions.Def_CtrlVolMFG_IsC1
-- name    : CtrlVolMFG_IsC1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:19:26.17316+00:00
-- url     : https://prove2.me/theorems/4154a945-e0e3-44ea-ad8d-4cb1e0c2f351
-- title:
--   Spaces, empirical measures and calculus on $\mathcal P_2(\mathbb R^n)$: $C^1$, two Lions derivatives, displacement monotonicity
-- statement:
--   This item fixes the analytic vocabulary of the mission.
--
--   1. The state space is $\mathbb R^n$ with the Euclidean norm, the matrix space $\mathbb R^{n\times d}$ carries the Frobenius norm and the pairing $A\cdot B=\mathrm{tr}(A^\top B)$, and $\mathcal P_2(\mathbb R^n)$ is the space of probability measures with finite second moment $M_2(m)=\int|x|^2m(dx)$, with the Wasserstein distance $\mathcal W_2$ (the published `DisplMonoMFG.WellPosed` definitions).
--   2. For $\mathbf x=(x^1,\dots,x^N)\in(\mathbb R^n)^N$ the empirical measure is $m^N_{\mathbf x}=\frac1N\sum_{i=1}^N\delta_{x^i}$.
--   3. A function $U:\mathbb R^p\times\mathcal P_2(\mathbb R^n)\to F$ is $C^1$ (§2.3) when $D_xU$ exists and is jointly continuous, and there is a jointly continuous $D_mU(x,m,y)$ such that for each $x$, $D_mU(x,\cdot,\cdot)$ is a Lions derivative of $m\mapsto U(x,m)$: the lift $\xi\mapsto U(x,\mathcal L(\xi))$ is Fréchet differentiable on $\mathbb L^2$ with gradient $D_mU(x,\mathcal L(\xi),\xi)$.
--   4. A family $m\mapsto U(x,m)$ admits two Lions derivatives $D_mU(x,m,p)$ and $D_{mm}U(x,m,p,q)=D_m[D_mU(x,\cdot,p)](m,q)$ which are bounded and Lipschitz in $m$, uniformly in $x$ (and in $p,q$).
--   5. For $c\in\mathbb R$, $U:\mathbb R^n\times\mathcal P_2(\mathbb R^n)\to\mathbb R$ is $c$-displacement monotone (1.6) if
--   $$\mathbb E\big[(D_xU(\xi^1,\mathcal L(\xi^1))-D_xU(\xi^2,\mathcal L(\xi^2)))\cdot(\xi^1-\xi^2)\big]\ge c\,\mathbb E|\xi^1-\xi^2|^2$$
--   for all square-integrable $\xi^1,\xi^2$.
--
--   These notions are used by every assumption of the paper.
--
--   **Formalization Note** Lipschitz and continuity conditions use $\mathcal W_2$ in the measure and the max-norm on products of the other arguments. Random variables in (1.6) enter through their joint law $\pi$, and the inequality is required when the integrand is integrable. The empirical measure is an element of $\mathcal P_2$ for $N\ge1$; a default value $\delta_0$ is used only for non-$\mathcal P_2$ measures and never enters a statement.
-- source:
--   Jackson & Tangpi, Quantitative Convergence for Displacement Monotone Mean Field Games with Controlled Volatility, arXiv:2304.04543v2, §2.1 p.9; (1.6) p.3; §2.3 p.11; (2.3) p.12; Assumption 2.20 p.17

import Mathlib
import Definitions.Def_DisplMonoMFG_WellPosed_Space

open MeasureTheory
open scoped ENNReal NNReal

namespace CtrlVolMFG

/-- The state space `ℝⁿ` with its Euclidean norm and inner product
(Jackson & Tangpi, arXiv:2304.04543v2, §2.1, p.9). It is the space `E n` of the published
`DisplMonoMFG.WellPosed` definitions. -/
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The matrix space `ℝ^{n×d}` with the Frobenius norm and the Frobenius inner product
`A·B = tr(AᵀB)` (arXiv:2304.04543v2, §2.1, p.9).

**Formalization Note** A matrix `A` is stored as the vector of its entries `A (r, j)`, an element
of `EuclideanSpace ℝ (Fin n × Fin d)`: the Euclidean norm of that vector is the Frobenius norm
`√tr(AᵀA)`, and its inner product is `tr(AᵀB)`. -/
abbrev Mat (n d : ℕ) := EuclideanSpace ℝ (Fin n × Fin d)

/-- Column `j` of a matrix `A ∈ ℝ^{n×d}`: the vector multiplying `dWʲ` in `A dW`. -/
noncomputable def col {n d : ℕ} (A : Mat n d) (j : Fin d) : Rn n :=
  WithLp.toLp 2 (fun r => A (r, j))

/-- `𝒫₂(ℝⁿ)`, probability measures with finite second moment (arXiv:2304.04543v2, p.9), the
published `DisplMonoMFG.WellPosed.P2`. -/
abbrev P2 (n : ℕ) := DisplMonoMFG.WellPosed.P2 n

/-- The Wasserstein distance `𝒲₂` of (2.1), p.9, the published `DisplMonoMFG.WellPosed.W2`. -/
noncomputable abbrev W2 {n : ℕ} (μ ν : P2 n) : ℝ := DisplMonoMFG.WellPosed.W2 μ ν

/-- The second moment `M₂(m) = ∫ |x|² m(dx)` of `m ∈ 𝒫₂(ℝⁿ)` (arXiv:2304.04543v2, p.9). -/
noncomputable def M2 {n : ℕ} (m : P2 n) : ℝ := ∫ x, ‖x‖ ^ 2 ∂m.1

/-- The point mass at `0`, an element of `𝒫₂(ℝⁿ)`; used only as a default value. -/
noncomputable def diracZero (n : ℕ) : P2 n :=
  ⟨Measure.dirac 0, ⟨inferInstance, by simp⟩⟩

/-- A measure as an element of `𝒫₂(ℝⁿ)`: the measure itself when it is a probability measure
with finite second moment, and the default `δ₀` otherwise.

**Formalization Note** Every use of `toP2` in this mission applies it to a measure that is in
`𝒫₂` (an empirical measure of `N ≥ 1` points, or a marginal of a coupling with finite second
moments); the default never enters a statement. -/
noncomputable def toP2 {n : ℕ} (μ : Measure (Rn n)) : P2 n := by
  classical
  exact if h : DisplMonoMFG.WellPosed.IsP2 μ then ⟨μ, h⟩ else diracZero n

/-- The empirical measure `m^N_x = (1/N) ∑_{i=1}^N δ_{xⁱ}` of `x = (x¹, …, xᴺ) ∈ (ℝⁿ)ᴺ`
(arXiv:2304.04543v2, §2.1 and (2.3), p.12), as a measure.

**Formalization Note** Players are indexed by `Fin N`; the paper's `xⁱ`, `i ∈ {1, …, N}`, is
`x (i - 1)`. -/
noncomputable def empMeasure {n N : ℕ} (x : Fin N → Rn n) : Measure (Rn n) :=
  ((N : ℝ≥0∞)⁻¹) • ∑ i, Measure.dirac (x i)

/-- The empirical measure `m^N_x ∈ 𝒫₂(ℝⁿ)` (arXiv:2304.04543v2, p.12). For `N ≥ 1` it is the
measure `empMeasure x` (the sanity file proves this). -/
noncomputable def empP2 {n N : ℕ} (x : Fin N → Rn n) : P2 n := toP2 (empMeasure x)

/-- Joint continuity of a map `g : X × 𝒫₂(ℝⁿ) → F`, with the norm on `X` and `𝒲₂` on
`𝒫₂(ℝⁿ)` (the continuity required in §2.3, p.11). -/
def JointCont {X F : Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup F] {n : ℕ}
    (g : X → P2 n → F) : Prop :=
  ∀ x m, ∀ ε > 0, ∃ δ > 0, ∀ x' m', ‖x' - x‖ < δ → W2 m m' < δ → ‖g x' m' - g x m‖ < ε

/-- Lipschitz continuity "in all arguments" of `g : X × 𝒫₂(ℝⁿ) → F`: `𝒲₂` on `𝒫₂(ℝⁿ)` and the
norm on the other arguments (Assumptions 2.4, 2.11, 2.17, pp.13–16). Several non-measure
arguments are packed into the product `X`, whose norm is the maximum of the norms. -/
def LipXM {X F : Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup F] {n : ℕ}
    (g : X → P2 n → F) : Prop :=
  ∃ K : ℝ, ∀ x x' m m', ‖g x m - g x' m'‖ ≤ K * (‖x - x'‖ + W2 m m')

/-- Boundedness of `g : X × 𝒫₂(ℝⁿ) → F`. -/
def BddXM {X F : Type*} [SeminormedAddCommGroup F] {n : ℕ} (g : X → P2 n → F) : Prop :=
  ∃ K : ℝ, ∀ x m, ‖g x m‖ ≤ K

/-- The class `C¹` of §2.3 (arXiv:2304.04543v2, p.11) for `f : X × 𝒫₂(ℝⁿ) → F` with a version
`Dm` of its Lions derivative: `D_x f` exists and is jointly continuous; for each fixed `x`,
`Dm x` is a Lions (Wasserstein) derivative of `m ↦ f(x, m)`, in the sense of the published
`DisplMonoMFG.WellPosed.HasLDeriv`; and `(x, m, y) ↦ Dm x m y` is jointly continuous.

**Formalization Note** The vector `D_m f(x, m, y) ∈ ℝⁿ` of a real-valued `f` is represented by
the linear functional `η ↦ D_m f(x, m, y) · η`; a vector-valued `f` is differentiated
componentwise in the paper, which is the same as a linear map `ℝⁿ →L F`. `HasLDeriv` asks the
first-order expansion `f(x, ℒ(ξ + η)) − f(x, ℒ(ξ)) = 𝔼[D_m f(x, ℒ(ξ), ξ)·η] + o(‖η‖₂)` uniformly
over the joint laws of `(ξ, η)` with `ℒ(ξ) = m`; on an atomless probability space this is
Fréchet differentiability of the lift `ξ ↦ f(x, ℒ(ξ))` at every `ξ ∈ 𝕃²` with gradient
`D_m f(x, ℒ(ξ), ξ)`, as §2.3 requires. -/
structure IsC1 {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {n : ℕ}
    (f : X → P2 n → F) (Dm : X → P2 n → Rn n → (Rn n →L[ℝ] F)) : Prop where
  /-- `x ↦ f(x, m)` is differentiable. -/
  diff : ∀ x m, DifferentiableAt ℝ (fun x' => f x' m) x
  /-- `(x, m) ↦ D_x f(x, m)` is jointly continuous. -/
  cont_dx : JointCont (fun x m => fderiv ℝ (fun x' => f x' m) x)
  /-- For each `x`, `Dm x` is a Lions derivative of `m ↦ f(x, m)`. -/
  lions : ∀ x, DisplMonoMFG.WellPosed.HasLDeriv (f x) (Dm x)
  /-- `(x, m, y) ↦ D_m f(x, m, y)` is jointly continuous. -/
  cont_dm : JointCont (fun (q : X × Rn n) m => Dm q.1 m q.2)

/-- For each fixed `x`, the map `m ↦ f(x, m)` admits first and second Lions derivatives
`D_m f(x, m, p) = D_m[f(x, ·)](m, p)` and `D_mm f(x, m, p, q) = D_m[D_m f(x, ·, p)](m, q)` which
are bounded and Lipschitz continuous in `m` (for `𝒲₂`), uniformly in `x` and in the extra
arguments `p, q` (Assumption 2.20, p.17; Theorem 2.23 (2), p.18; Lemma 3.13, p.27).

**Formalization Note** One bound `K` and one Lipschitz constant `K` serve for every `x, p, q`. -/
def TwoLionsUnif {X F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {n : ℕ} (f : X → P2 n → F) : Prop :=
  ∃ (D1 : X → P2 n → Rn n → (Rn n →L[ℝ] F))
    (D2 : X → Rn n → P2 n → Rn n → (Rn n →L[ℝ] (Rn n →L[ℝ] F))) (K : ℝ),
    ∀ x, DisplMonoMFG.WellPosed.HasLDeriv (f x) (D1 x) ∧
      (∀ p, DisplMonoMFG.WellPosed.HasLDeriv (fun m => D1 x m p) (D2 x p)) ∧
      ∀ m m' p q,
        ‖D1 x m p‖ ≤ K ∧ ‖D2 x p m q‖ ≤ K ∧
        ‖D1 x m p - D1 x m' p‖ ≤ K * W2 m m' ∧ ‖D2 x p m q - D2 x p m' q‖ ≤ K * W2 m m'

/-- The gradient `D_x U(x, m)` of `U : ℝⁿ × 𝒫₂(ℝⁿ) → ℝ` in its state variable. -/
noncomputable def Dx {n : ℕ} (U : Rn n → P2 n → ℝ) (x : Rn n) (m : P2 n) : Rn n :=
  gradient (fun x' => U x' m) x

/-- A probability measure `π` on a product `A × A` of Euclidean spaces with finite second
moment: the joint law of a pair of square-integrable random variables. -/
def IsL2Pair {A : Type*} [NormedAddCommGroup A] [MeasurableSpace A] (π : Measure (A × A)) : Prop :=
  IsProbabilityMeasure π ∧ ∫⁻ w, ‖w.1‖ₑ ^ 2 + ‖w.2‖ₑ ^ 2 ∂π < ⊤

/-- `c`-displacement monotonicity (1.6), p.3 (arXiv:2304.04543v2): for all random variables
`ξ¹, ξ²` with joint law `π` (finite second moments),
`𝔼[(D_xU(ξ¹, ℒ(ξ¹)) − D_xU(ξ², ℒ(ξ²)))·(ξ¹ − ξ²)] ≥ c 𝔼|ξ¹ − ξ²|²`. `U` is displacement monotone
when it is `0`-displacement monotone and strictly displacement monotone when it is
`c`-displacement monotone for some `c > 0` (p.3).

**Formalization Note** The pair `(ξ¹, ξ²)` enters only through its joint law `π`, and the laws
`ℒ(ξ¹), ℒ(ξ²)` are the marginals of `π`; on an atomless probability space every coupling with
finite second moments is such a joint law. The page's "sufficiently integrable" is the
integrability of the left-hand integrand, which is required. -/
def IsDisplMono {n : ℕ} (c : ℝ) (U : Rn n → P2 n → ℝ) : Prop :=
  ∀ π : Measure (Rn n × Rn n), IsL2Pair π →
    Integrable (fun w => inner ℝ (Dx U w.1 (toP2 (π.map Prod.fst)) -
      Dx U w.2 (toP2 (π.map Prod.snd))) (w.1 - w.2)) π →
    c * ∫ w, ‖w.1 - w.2‖ ^ 2 ∂π ≤
      ∫ w, inner ℝ (Dx U w.1 (toP2 (π.map Prod.fst)) -
        Dx U w.2 (toP2 (π.map Prod.snd))) (w.1 - w.2) ∂π

end CtrlVolMFG


