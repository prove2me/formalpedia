-- Prove2me | Definitions.Def_BanKeskin_KnownSparsity_Model
-- name    : BanKeskin_KnownSparsity_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:01:21.773123+00:00
-- url     : https://prove2.me/theorems/d733d2ca-e3a9-45fa-bce6-04f55f8641e9
-- title:
--   The known-support linear demand model and ILSX policy, pp. 5552–5556
-- statement:
--   The seller observes independent, identically distributed customer features $Z_t\in\mathbb R^d$, augments them to $X_t=[1;Z_t]$, and knows a nonempty set $\mathcal S$ of parameter coordinates. A parameter $\theta_{\mathcal S}=(\alpha_{\mathcal S},\beta_{\mathcal S})$ lies in a compact coordinate rectangle $\Theta_{\mathcal S}$. Its linear mean demand at price $p$ is $\alpha_{\mathcal S}\cdot X_{\mathcal S,t}+(\beta_{\mathcal S}\cdot X_{\mathcal S,t})p$, and observed demand adds a martingale-difference shock $\varepsilon_t$.
--
--   At experimental periods $\mathcal M_1=\{L^2:L\ge1\}$ and $\mathcal M_2=\{L^2+1:L\ge1\}$, ILSX charges fixed, distinct prices $m_1,m_2\in[\ell,u]$. At other periods it projects an experimental-data least-squares estimate onto $\Theta_{\mathcal S}$ and charges the linear model's revenue-maximizing price
--
--   $$\varphi(\theta,x)=-\frac{\alpha_{\mathcal S}\cdot x}{2\beta_{\mathcal S}\cdot x}.$$
--
--   The definitions include the least-squares loss $S_t$, information matrix $\widetilde{\mathcal J}_{\mathcal S,t}$, score vector $\mathcal M_{\mathcal S,t}$, deterministic price variation $J_t$, and joint expected regret $\Delta^{\pi}_{\theta_{\mathcal S}}(T)$. They provide the common model for the goal and its milestones.
--
--   **Formalization Note** Periods begin at one. Lean coordinate zero is the paper's intercept coordinate one; $X_{\mathcal S,t}$ restricts the augmented vector to the support. The projection onto the rectangle is coordinatewise clamping. Features have an explicit Euclidean bound and positive-definite covariance; shocks use conditional nonnegative expectations for their second and exponential moments. Regret is a nonnegative integral. The assumption about positive measure in the interior of continuous-feature domains is omitted because the page does not specify a precise domain or reference measure. Nonexperimental pseudo-observations in the estimator history are ignored by $S_t$.
-- source:
--   Ban and Keskin, Personalized Dynamic Pricing with Machine Learning, Management Science 67(9) (2021), pp. 5552–5554, (1)–(5); p. 5555, (7); p. 5556, (8)–(13); p. 5568, endnote 1

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BanKeskin.KnownSparsity

/-- The coordinates in the known union of the supports of the intercept and price slopes. -/
abbrev Parameter (d : ℕ) (S : Finset (Fin (d + 1))) := Fin 2 × ↥S → ℝ

/-- A full augmented covariate, a quoted price, and the corresponding demand. -/
abbrev Observation (d : ℕ) := (Fin (d + 1) → ℝ) × ℝ × ℝ

/-- The square-period experimental schedule (7), with periods numbered from one. -/
def inM1 (t : ℕ) : Prop := ∃ L : ℕ, 1 ≤ L ∧ t = L ^ 2

/-- The periods immediately following the square-period experiments. -/
def inM2 (t : ℕ) : Prop := ∃ L : ℕ, 1 ≤ L ∧ t = L ^ 2 + 1

noncomputable def chi (t : ℕ) : ℝ := by
  classical exact if inM1 t ∨ inM2 t then 1 else 0

noncomputable def experimentCount (i : Fin 2) (t : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 t).filter (fun k => if i = 0 then inM1 k else inM2 k)).card

/-- Restriction of the augmented covariate to the known support. -/
def restrictX {d : ℕ} (S : Finset (Fin (d + 1))) (x : Fin (d + 1) → ℝ) : ↥S → ℝ :=
  fun i => x i.1

/-- The regressor `[1,p] ⊗ x` in compressed coordinates. -/
def regressor {d : ℕ} {S : Finset (Fin (d + 1))} (p : ℝ) (x : ↥S → ℝ) :
    Parameter d S :=
  fun ji => (if ji.1 = 0 then 1 else p) * x ji.2

/-- The finite-dimensional Euclidean dot product, written explicitly to avoid the Pi sup norm. -/
def dot {ι : Type*} [Fintype ι] (v w : ι → ℝ) : ℝ := ∑ i, v i * w i

def sqNorm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ := dot v v

/-- The unconstrained revenue-maximizing price under linear demand (5). -/
noncomputable def phi {d : ℕ} {S : Finset (Fin (d + 1))}
    (θ : Parameter d S) (x : ↥S → ℝ) : ℝ :=
  -(∑ i, θ (0, i) * x i) / (2 * ∑ i, θ (1, i) * x i)

/-- Coordinatewise Euclidean projection onto the compact parameter rectangle. -/
def clamp {d : ℕ} {S : Finset (Fin (d + 1))}
    (lo hi v : Parameter d S) : Parameter d S :=
  fun i => max (lo i) (min (v i) (hi i))

/-- The primitives and standing hypotheses of the known-support linear model in §§2 and 4.1. -/
structure Model (d : ℕ) (S : Finset (Fin (d + 1))) (Ω : Type*)
    [MeasurableSpace Ω] (P : Measure Ω) where
  dimension_pos : 0 < d
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_lt_upper : lower < upper
  m1 : ℝ
  m2 : ℝ
  m1_mem : m1 ∈ Set.Icc lower upper
  m2_mem : m2 ∈ Set.Icc lower upper
  m_ne : m1 ≠ m2
  support_nonempty : 0 < S.card
  lo : Parameter d S
  hi : Parameter d S
  box_nonempty : ∀ i, lo i ≤ hi i
  zmax : ℝ
  zmax_pos : 0 < zmax
  Z : ℕ → Ω → (Fin d → ℝ)
  measurable_Z : ∀ t, 1 ≤ t → Measurable (Z t)
  iid_Z : iIndepFun (fun t : {t : ℕ // 1 ≤ t} => Z t.1) P
  ident_Z : ∀ t, 1 ≤ t → P.map (Z t) = P.map (Z 1)
  bounded_Z : ∀ t ω, 1 ≤ t → Real.sqrt (sqNorm (Z t ω)) ≤ zmax
  integrable_Z : Integrable (Z 1) P
  mean_zero_Z : (∫ ω, Z 1 ω ∂P) = 0
  covariance_pos : ∀ v : Fin d → ℝ, v ≠ 0 →
    0 < ∫ ω, (dot v (Z 1 ω)) ^ 2 ∂P
  eps : ℕ → Ω → ℝ
  measurable_eps : ∀ t, 1 ≤ t → Measurable (eps t)
  integrable_eps : ∀ t, 1 ≤ t → Integrable (eps t) P
  sigma0 : ℝ
  eta0 : ℝ
  sigma0_pos : 0 < sigma0
  eta0_pos : 0 < eta0
  est : (n : ℕ) → (Fin n → Observation d) → Parameter d S
  measurable_est : ∀ n, Measurable (est n)

/-- The augmented feature vector `[1; Z_t]`; Lean coordinate zero is the paper's coordinate one. -/
def Model.X {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (M : Model d S Ω P)
    (t : ℕ) (ω : Ω) : Fin (d + 1) → ℝ := Fin.cons 1 (M.Z t ω)

def Model.Theta {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (M : Model d S Ω P) : Set (Parameter d S) :=
  Set.Icc M.lo M.hi

/-- The sigma-algebra generated by features and shocks observed through period t. -/
def Model.past {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (M : Model d S Ω P)
    (t : ℕ) : MeasurableSpace Ω :=
  (⨆ k ∈ Finset.Icc 1 t, MeasurableSpace.comap (M.X k) inferInstance) ⊔
  (⨆ k ∈ Finset.Icc 1 t, MeasurableSpace.comap (M.eps k) inferInstance)

/-- The paper's filtration contains the next feature X_(t+1) before the next decision. -/
def Model.G {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (M : Model d S Ω P)
    (t : ℕ) : MeasurableSpace Ω :=
  M.past t ⊔ MeasurableSpace.comap (M.X (t + 1)) inferInstance

/-- Shock and fresh-customer assumptions from §2, expressed on the primitives. -/
structure NoiseConditions {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (M : Model d S Ω P) : Prop where
  fresh : ∀ t, 1 ≤ t → Indep (MeasurableSpace.comap (M.X (t + 1)) inferInstance) (M.past t) P
  mean_zero : ∀ t, 1 ≤ t → P[M.eps t | M.G (t - 1)] =ᵐ[P] (fun _ => (0 : ℝ))
  second_moment : ∀ t, 1 ≤ t →
    P⁻[fun ω => ENNReal.ofReal ((M.eps t ω) ^ 2) | M.G (t - 1)] ≤ᵐ[P]
      (fun _ => ENNReal.ofReal (M.sigma0 ^ 2))
  exp_moment : ∀ t, 1 ≤ t → ∀ η : ℝ, |η| < M.eta0 →
    ∀ᵐ ω ∂P, P⁻[fun ω => ENNReal.ofReal (Real.exp (η * M.eps t ω)) |
      M.G (t - 1)] ω < ⊤

/-- Interior-optimum assumptions, restricted to realized covariates. -/
structure InteriorConditions {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (M : Model d S Ω P) : Prop where
  negative_slope : ∀ θ ∈ M.Theta, ∀ t ω, 1 ≤ t →
    ∑ i, θ (1, i) * (restrictX S (M.X t ω)) i < 0
  optimum_interior : ∀ θ ∈ M.Theta, ∀ t ω, 1 ≤ t →
    phi θ (restrictX S (M.X t ω)) ∈ Set.Ioo M.lower M.upper

noncomputable def Model.experimentPrice {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (M : Model d S Ω P) (t : ℕ) : ℝ :=
  by classical exact if inM1 t then M.m1 else M.m2

/-- The least-squares criterion in (8), computed only on experimental periods. -/
noncomputable def Model.loss {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (M : Model d S Ω P)
    (n : ℕ) (h : Fin n → Observation d) (v : Parameter d S) : ℝ :=
  ∑ k : Fin n, chi (k.1 + 1) *
    ((h k).2.2 - dot v (regressor (h k).2.1 (restrictX S (h k).1))) ^ 2

/-- Each selected estimate minimizes the experimental least-squares objective. -/
def Model.IsEstimator {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (M : Model d S Ω P) : Prop :=
  ∀ n, 2 ≤ n → ∀ h v, M.loss n h (M.est n h) ≤ M.loss n h v

/-- A total pseudo-history: nonexperimental entries are ignored by the objective (8). -/
noncomputable def Model.history {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (M : Model d S Ω P)
    (θ : Parameter d S) (n : ℕ) (ω : Ω) : Fin n → Observation d := by
  classical
  exact fun k =>
    let t := k.1 + 1
    let x := M.X t ω
    let p := M.experimentPrice t
    (x, p, if inM1 t ∨ inM2 t then
      dot θ (regressor p (restrictX S x)) + M.eps t ω else 0)

/-- ILSX in (12), with the estimate from the first t-1 periods. -/
noncomputable def Model.price {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (M : Model d S Ω P)
    (θ : Parameter d S) (t : ℕ) (ω : Ω) : ℝ := by
  classical
  exact if inM1 t then M.m1 else if inM2 t then M.m2 else
      phi (clamp M.lo M.hi (M.est (t - 1) (M.history θ (t - 1) ω)))
        (restrictX S (M.X t ω))

/-- Experimental information matrix (10), in coordinates (intercept/price) × support. -/
noncomputable def Model.Jtilde {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (M : Model d S Ω P)
    (t : ℕ) (ω : Ω) : Matrix (Fin 2 × ↥S) (Fin 2 × ↥S) ℝ :=
  ∑ k ∈ Finset.Icc 1 t, chi k •
    Matrix.vecMulVec (regressor (M.experimentPrice k) (restrictX S (M.X k ω)))
      (regressor (M.experimentPrice k) (restrictX S (M.X k ω)))

/-- Noise-weighted experimental score vector from (11). -/
noncomputable def Model.Mvec {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (M : Model d S Ω P)
    (t : ℕ) (ω : Ω) : Parameter d S :=
  ∑ k ∈ Finset.Icc 1 t, (chi k * M.eps k ω) •
    regressor (M.experimentPrice k) (restrictX S (M.X k ω))

/-- Mean experimental price and deterministic price variation (13). -/
noncomputable def Model.meanPrice {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (M : Model d S Ω P) (t : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 t, chi k * M.experimentPrice k) /
    (∑ k ∈ Finset.Icc 1 t, chi k)

noncomputable def Model.J {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (M : Model d S Ω P) (t : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 t, chi k * (M.experimentPrice k - M.meanPrice t) ^ 2

def Model.revenue {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (M : Model d S Ω P)
    (θ : Parameter d S) (p : ℝ) (x : Fin (d + 1) → ℝ) : ℝ :=
  p * dot θ (regressor p (restrictX S x))

/-- The joint expected regret (3)-(4), with nonnegative extended expectation. -/
noncomputable def Model.regret {d : ℕ} {S : Finset (Fin (d + 1))} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (M : Model d S Ω P)
    (θ : Parameter d S) (T : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, ∑ t ∈ Finset.Icc 1 T,
    ENNReal.ofReal (M.revenue θ (phi θ (restrictX S (M.X t ω))) (M.X t ω) -
      M.revenue θ (M.price θ t ω) (M.X t ω)) ∂P

end BanKeskin.KnownSparsity


