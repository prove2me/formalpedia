-- Prove2me | Definitions.Def_KPZ2D_Polymer_Setting
-- name    : KPZ2D_Polymer_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:20.118026+00:00
-- url     : https://prove2.me/theorems/eae3c8ec-a82f-44d8-97df-7c78a070696d
-- title:
--   §§1–2: two-dimensional directed polymer, disorder, windows, fluctuation field and covariance
-- statement:
--   Let $S$ be the four-neighbour simple random walk on $\mathbb Z^2$, started at $x$. Its transition probability is $q_n(z)=P_0(S_n=z)$ and the expected overlap of two independent walks is $R_N=\sum_{n=1}^N\sum_z q_n(z)^2$. For $\hat\beta>0$, set $\beta_N=\hat\beta/\sqrt{R_N}$.
--
--   The disorder consists of independent, identically distributed real variables $\omega(n,z)$ with common law $\mathfrak L$, mean zero, variance one, and a finite exponential moment for every sufficiently small positive argument. Its logarithmic moment generating function is $\lambda(b)=\log\mathbb E[e^{b\omega}]$. Assumption (1.20) additionally gives stretched-exponential concentration, with exponent $\gamma>1$, for every convex Euclidean 1-Lipschitz function of any finite collection of disorder variables, measured from a median.
--
--   For a set $\Lambda$ of space-time sites, $Z_{\Lambda,b}(x)$ averages $\exp\big(\sum_{n=1}^N (b\omega(n,S_n)-\lambda(b))\mathbf1_{(n,S_n)\in\Lambda}\big)$ over the $4^N$ walks of length $N$ from $x$. In particular, $Z_N(x)=Z_{\{1,\ldots,N\}\times\mathbb Z^2,\beta_N}(x)$. The early window $A_N^x$, late window $B_N^{\ge}$, restricted functions $Z_N^A(x)$ and $Z_N^{B\ge}(x)$, remainder $\widehat Z_N^A(x)=Z_N(x)-Z_N^A(x)$, and logarithmic error $O_N(x)$ reproduce (2.2)–(2.11).
--
--   The rescaled field $\mathfrak h_N(t,y)$ is the centred logarithm of $Z_{\lfloor tN\rfloor}(\lfloor\sqrt N y\rfloor)$ divided by $\beta_N$. The Gaussian target has coefficient $c_{\hat\beta}=\sqrt{1/(1-\hat\beta^2)}$ and variance determined by $\sigma_\phi^2(t)=\iint\phi(x)K_t(x,y)\phi(y)\,dx\,dy$, where $K_t(x,y)=\int_0^t(4\pi u)^{-1}e^{-\lVert x-y\rVert^2/(4u)}\,du$.
--
--   These definitions provide a common model for the fluctuation theorem and its moment, approximation and Gaussian-limit milestones.
--
--   **Formalization Note** Lattice vectors are cast into Euclidean space before taking norms. The kernel is extended nonnegative and is infinite on the diagonal; its real value is used in the double integral, whose diagonal has zero area. The time-zero disorder row is unused. The Gaussian field itself is represented through the law of each tested observable.
-- source:
--   Caravenna, Sun, Zygouras, The two-dimensional KPZ equation in the entire subcritical regime, arXiv:1812.03911v3, (1.11)–(1.23), (2.1)–(2.11), pp. 3–9

import Mathlib
import Definitions.Def_PolymerEndpoint_Atomic_Model

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Classical BigOperators ENNReal Topology ContDiff

namespace KPZ2D.Polymer

abbrev Site := Fin 2 → ℤ
abbrev E := EuclideanSpace ℝ (Fin 2)

/-- The Euclidean embedding of a lattice site. -/
noncomputable def toE (z : Site) : E :=
  WithLp.toLp 2 (fun i => (z i : ℝ))

/-- Componentwise floor, as in the extension of the partition function to real space. -/
noncomputable def floorPt (y : E) : Site := fun i => ⌊y i⌋

/-- The transition probability of the four-neighbour simple random walk. -/
noncomputable def q (n : ℕ) (z : Site) : ℝ :=
  ((4 : ℝ) ^ n)⁻¹ *
    ((Finset.univ.filter (fun s : Fin n → PolymerEndpoint.Atomic.Step 2 =>
      PolymerEndpoint.Atomic.pos s n = z)).card : ℝ)

/-- Expected overlap of two independent walks through time `N`, (1.17). -/
noncomputable def R (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ∑' z : Site, q n z ^ 2

/-- The intermediate-disorder strength, (1.18). -/
noncomputable def betaN (βhat : ℝ) (N : ℕ) : ℝ :=
  βhat / Real.sqrt (R N)

/-- The disorder-law requirements in (1.19). -/
def Assumption119 (𝔏 : Measure ℝ) : Prop :=
  MemLp (fun x : ℝ => x) 2 𝔏 ∧
  (∫ x : ℝ, x ∂𝔏) = 0 ∧
  (∫ x : ℝ, x ^ 2 ∂𝔏) = 1 ∧
  ∃ β₀ : ℝ, 0 < β₀ ∧
    ∀ β ∈ Set.Ioo 0 β₀, Integrable (fun x : ℝ => Real.exp (β * x)) 𝔏

/-- A median of `f` under `μ`. -/
def IsMedian {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ) (m : ℝ) : Prop :=
  (1 / 2 : ENNReal) ≤ μ {x | f x ≤ m} ∧
  (1 / 2 : ENNReal) ≤ μ {x | m ≤ f x}

/-- The convex Euclidean Lipschitz concentration assumption (1.20). -/
def Concentration120 (𝔏 : Measure ℝ) (γ C₁ C₂ : ℝ) : Prop :=
  1 < γ ∧ 0 < C₁ ∧ 0 < C₂ ∧
  ∀ (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ),
    ConvexOn ℝ Set.univ f → LipschitzWith 1 f →
    ∀ m : ℝ,
      IsMedian (Measure.pi (fun _ : Fin n => 𝔏))
        (fun w : Fin n → ℝ => f (WithLp.toLp 2 w)) m →
      ∀ t : ℝ, 0 < t →
        (Measure.pi (fun _ : Fin n => 𝔏))
          {w : Fin n → ℝ | t ≤ |f (WithLp.toLp 2 w) - m|} ≤
        ENNReal.ofReal (C₁ * Real.exp (-(t ^ γ) / C₂))

/-- The restricted, start-at-`x`, cumulant-centred partition function (2.1). -/
noncomputable def ZLam (𝔏 : Measure ℝ)
    (w : PolymerEndpoint.Atomic.Cell 2 → ℝ)
    (Λ : Set (PolymerEndpoint.Atomic.Cell 2)) (β : ℝ) (N : ℕ) (x : Site) : ℝ :=
  ((4 : ℝ) ^ N)⁻¹ *
    ∑ s : Fin N → PolymerEndpoint.Atomic.Step 2,
      Real.exp (∑ m : Fin N,
        let u : PolymerEndpoint.Atomic.Cell 2 :=
          ((m : ℕ) + 1, x + PolymerEndpoint.Atomic.pos s ((m : ℕ) + 1))
        if u ∈ Λ then β * w u - PolymerEndpoint.Atomic.logMGF 𝔏 β else 0)

/-- The full polymer partition function (1.22). -/
noncomputable def Z {Ω : Type*} (𝔏 : Measure ℝ)
    (env : PolymerEndpoint.Atomic.Cell 2 → Ω → ℝ) (βhat : ℝ)
    (N : ℕ) (x : Site) (a : Ω) : ℝ :=
  ZLam 𝔏 (fun u => env u a) Set.univ (betaN βhat N) N x

/-- The window scale (2.2). -/
noncomputable def aN (g : ℝ) (N : ℕ) : ℝ :=
  1 / (Real.log N) ^ (1 - g)

/-- The early space-time window (2.3), with time zero excluded. -/
def windowA (g : ℝ) (N : ℕ) (x : Site) :
    Set (PolymerEndpoint.Atomic.Cell 2) :=
  {u | 1 ≤ u.1 ∧ (u.1 : ℝ) ≤ (N : ℝ) ^ (1 - aN g N) ∧
    ‖toE u.2 - toE x‖ < (N : ℝ) ^ (1 / 2 - aN g N / 4)}

/-- The late-time window (2.10). -/
def windowB (g : ℝ) (N : ℕ) : Set (PolymerEndpoint.Atomic.Cell 2) :=
  {u | 1 ≤ u.1 ∧ (N : ℝ) ^ (1 - 9 * aN g N / 40) < (u.1 : ℝ) ∧ u.1 ≤ N}

/-- The partition function restricted to the early window (2.4). -/
noncomputable def ZA {Ω : Type*} (𝔏 : Measure ℝ)
    (env : PolymerEndpoint.Atomic.Cell 2 → Ω → ℝ) (βhat g : ℝ)
    (N : ℕ) (x : Site) (a : Ω) : ℝ :=
  ZLam 𝔏 (fun u => env u a) (windowA g N x) (betaN βhat N) N x

/-- The remainder in (2.5). -/
noncomputable def Zhat {Ω : Type*} (𝔏 : Measure ℝ)
    (env : PolymerEndpoint.Atomic.Cell 2 → Ω → ℝ) (βhat g : ℝ)
    (N : ℕ) (x : Site) (a : Ω) : ℝ :=
  Z 𝔏 env βhat N x a - ZA 𝔏 env βhat g N x a

/-- The partition function restricted to late times (2.11). -/
noncomputable def ZB {Ω : Type*} (𝔏 : Measure ℝ)
    (env : PolymerEndpoint.Atomic.Cell 2 → Ω → ℝ) (βhat g : ℝ)
    (N : ℕ) (x : Site) (a : Ω) : ℝ :=
  ZLam 𝔏 (fun u => env u a) (windowB g N) (betaN βhat N) N x

/-- The error of the logarithmic linearization (2.7). -/
noncomputable def O {Ω : Type*} (𝔏 : Measure ℝ)
    (env : PolymerEndpoint.Atomic.Cell 2 → Ω → ℝ) (βhat g : ℝ)
    (N : ℕ) (x : Site) (a : Ω) : ℝ :=
  Real.log (Z 𝔏 env βhat N x a) - Real.log (ZA 𝔏 env βhat g N x a) -
    Zhat 𝔏 env βhat g N x a / ZA 𝔏 env βhat g N x a

/-- The real-index extension in (1.22), with coordinatewise floor. -/
noncomputable def ZReal {Ω : Type*} (𝔏 : Measure ℝ)
    (env : PolymerEndpoint.Atomic.Cell 2 → Ω → ℝ) (βhat : ℝ)
    (t : ℝ) (y : E) (a : Ω) : ℝ :=
  Z 𝔏 env βhat ⌊t⌋₊ (floorPt y) a

/-- The rescaled centred log-partition field (1.23). -/
noncomputable def hN {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (𝔏 : Measure ℝ) (env : PolymerEndpoint.Atomic.Cell 2 → Ω → ℝ)
    (βhat : ℝ) (N : ℕ) (t : ℝ) (y : E) (a : Ω) : ℝ :=
  (Real.log (ZReal 𝔏 env βhat (t * N) (Real.sqrt N • y) a) -
    ∫ b, Real.log (Z 𝔏 env βhat ⌊t * N⌋₊ 0 b) ∂P) / betaN βhat N

/-- The subcritical noise coefficient (1.11). -/
noncomputable def cBeta (βhat : ℝ) : ℝ :=
  Real.sqrt (1 / (1 - βhat ^ 2))

/-- The extended nonnegative covariance kernel of the two-dimensional additive SHE (1.14).
It is infinite on the diagonal when `t > 0`. -/
noncomputable def K (t : ℝ) (x y : E) : ENNReal :=
  ∫⁻ u in Set.Ioc (0 : ℝ) t,
    ENNReal.ofReal ((4 * Real.pi * u)⁻¹ *
      Real.exp (-‖x - y‖ ^ 2 / (4 * u))) ∂volume

/-- The test-function variance (1.13). -/
noncomputable def sigmaSq (t : ℝ) (φ : E → ℝ) : ℝ :=
  ∫ x : E, ∫ y : E, φ x * (K t x y).toReal * φ y

end KPZ2D.Polymer


