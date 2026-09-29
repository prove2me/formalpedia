-- Prove2me | Definitions.Def_LassoDantzig_Oracle_Model
-- name    : LassoDantzig_Oracle_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:07:48.49783+00:00
-- url     : https://prove2.me/theorems/0f127253-f3d0-4c60-825d-b7934c9070dc
-- title:
--   Nonparametric regression with a dictionary: empirical norms, weighted Lasso, RE$(s,c_0)$ and the Gaussian noise event
-- statement:
--   Fix integers $n\ge1$ and $M\ge2$. A dictionary $f_1,\dots,f_M$ evaluated at fixed design points $Z_1,\dots,Z_n$ gives the **design matrix** $X=(f_j(Z_i))_{i,j}\in\mathbb R^{n\times M}$; the unknown regression function $f$ evaluated at the design points gives a vector $f=(f(Z_1),\dots,f(Z_n))^\top\in\mathbb R^n$, and for $\beta\in\mathbb R^M$ the linear combination $f_\beta=\sum_j\beta_jf_j$ evaluated at the design points is $X\beta$.
--
--   **Norms.** For $v\in\mathbb R^n$ the **empirical norm** is $\|v\|_n=\big(\tfrac1n\sum_{i=1}^n v_i^2\big)^{1/2}$ and the Euclidean norm is $|v|_2$. The column norms are $\|f_j\|_n=\|(X_{1j},\dots,X_{nj})\|_n$, and
--   $$f_{\max}=\max_{1\le j\le M}\|f_j\|_n,\qquad f_{\min}=\min_{1\le j\le M}\|f_j\|_n .$$
--   For $\delta\in\mathbb R^M$ and $J\subseteq\{1,\dots,M\}$, $|\delta_J|_1=\sum_{j\in J}|\delta_j|$ and $|\delta_J|_2=(\sum_{j\in J}\delta_j^2)^{1/2}$.
--
--   **Sparsity.** $J(\beta)=\{j:\beta_j\ne0\}$ and $\mathcal M(\beta)=|J(\beta)|$.
--
--   **Lasso** (2.1). Given observations $y\in\mathbb R^n$ and a tuning constant $r$, $\hat\beta$ is a Lasso solution if it minimises over $\beta\in\mathbb R^M$ the criterion
--   $$\frac1n\sum_{i=1}^n\big(y_i-(X\beta)_i\big)^2+2r\sum_{j=1}^M\|f_j\|_n\,|\beta_j| .$$
--   The tuning constant of Lemma B.1 and Theorem 6.1 is $r=A\sigma\sqrt{\log M/n}$ (natural logarithm).
--
--   **Restricted eigenvalues.** For $c_0>0$ the **cone condition** at $J_0$ is $|\delta_{J_0^c}|_1\le c_0|\delta_{J_0}|_1$. Assumption **RE$(s,c_0)$ with witness $\kappa$** means: for every $J_0$ with $|J_0|\le s$ and every $\delta\ne0$ satisfying the cone condition at $J_0$,
--   $$\kappa\,\sqrt n\,|\delta_{J_0}|_2\le|X\delta|_2 .$$
--   The single-set version at a fixed $J_0$ with constant $\gamma$ defines the family $\mathcal J_{s,\gamma,c_0}$ of index sets $J_0$ with $|J_0|\le s$ satisfying it, and $\Lambda_{s,\gamma,c_0}=\{\beta:J(\beta)\in\mathcal J_{s,\gamma,c_0}\}$ (p. 13).
--
--   **Noise.** On a probability space $(\Omega,P)$, $W_1,\dots,W_n$ are measurable, independent, and each $W_i\sim\mathcal N(0,\sigma^2)$; the observations are $y=f+W$. With $V_j=n^{-1}\sum_{i=1}^n X_{ij}W_i$, the **noise event** is
--   $$\mathcal A=\bigcap_{j=1}^M\{2|V_j|\le r\|f_j\|_n\},$$
--   and its deterministic form for a fixed noise vector $w=y-f$ is $2|n^{-1}\sum_i X_{ij}w_i|\le r\|f_j\|_n$ for every $j$.
--
--   These are the objects of Sections 2–3 and Appendix B of the paper on which the sparsity oracle inequality for the Lasso is stated.
--
--   **Formalization Note** Every statement depends on the dictionary and the target only through $X$ and $f$, so they are taken as a matrix and a vector. $f_{\max}$, $f_{\min}$ are the supremum/infimum over the finite nonempty index set (a maximum and minimum since $M\ge2$). RE is stated through a witness $\kappa$ instead of the minimum $\kappa(s,c_0)$: the minimum is attained, so it is itself a witness, every witness is at most it, and every bound of the paper decreases in $\kappa$; this avoids the junk value of a real infimum over an empty set ($J_0=\emptyset$). The Lasso is an argmin predicate, since minimisers need not be unique. The standing assumption $\|f_j\|_n\neq0$ (p. 4) is a hypothesis of each theorem.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, pp. 3–4, Section 2 and Eq. (2.1); p. 7, Assumption RE(s, c0); p. 13, sets J_{s,γ,c0} and Λ_{s,γ,c0}; p. 21, proof of Lemma B.1 (V_j and the event 𝒜)

import Mathlib

namespace LassoDantzig.Oracle

open MeasureTheory ProbabilityTheory

/-- The squared empirical norm `‖v‖_n² = (1/n) ∑ᵢ vᵢ²` of a vector `v ∈ ℝⁿ` of values
`v = (g(Z_1), …, g(Z_n))` (Bickel–Ritov–Tsybakov, p. 3). -/
noncomputable def empSq {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, v i ^ 2

/-- The empirical norm `‖v‖_n = √((1/n) ∑ᵢ vᵢ²)` (p. 3). -/
noncomputable def empNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (empSq v)

/-- The empirical norm `‖f_j‖_n` of the `j`-th dictionary function, i.e. of the `j`-th column of
the design matrix `X = (f_j(Z_i))` (p. 4). -/
noncomputable def colNorm {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (j : Fin M) : ℝ :=
  empNorm (fun i => X i j)

/-- `f_max = max_j ‖f_j‖_n` (p. 4). For `M ≥ 1` the supremum of the finitely many values is
their maximum. -/
noncomputable def fmax {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) : ℝ :=
  ⨆ j : Fin M, colNorm X j

/-- `f_min = min_j ‖f_j‖_n` (p. 4). For `M ≥ 1` the infimum of the finitely many values is
their minimum. -/
noncomputable def fmin {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) : ℝ :=
  ⨅ j : Fin M, colNorm X j

/-- The support `J(β) = {j : β_j ≠ 0}` (p. 4). -/
noncomputable def supp {M : ℕ} (β : Fin M → ℝ) : Finset (Fin M) :=
  Finset.univ.filter (fun j => β j ≠ 0)

/-- The sparsity `𝓜(β) = |J(β)|`, the number of non-zero coordinates of `β` (p. 4). -/
noncomputable def sparsity {M : ℕ} (β : Fin M → ℝ) : ℕ :=
  (supp β).card

/-- `|δ_J|_1 = ∑_{j ∈ J} |δ_j|`. -/
noncomputable def l1On {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) : ℝ :=
  ∑ j ∈ J, |δ j|

/-- `|δ_J|_2 = (∑_{j ∈ J} δ_j²)^{1/2}`. -/
noncomputable def l2On {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) : ℝ :=
  Real.sqrt (∑ j ∈ J, δ j ^ 2)

/-- The Euclidean norm `|v|_2` of a vector `v ∈ ℝⁿ`. -/
noncomputable def euclNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The cone condition `|δ_{J₀ᶜ}|_1 ≤ c₀ |δ_{J₀}|_1` (p. 7, inside Assumption RE(s, c₀)). -/
def ConeCond {M : ℕ} (c0 : ℝ) (J0 : Finset (Fin M)) (δ : Fin M → ℝ) : Prop :=
  l1On δ J0ᶜ ≤ c0 * l1On δ J0

/-- Assumption RE(s, c₀) (p. 7) with witness `κ`: for every `J0` with `|J0| ≤ s` and every
`δ ≠ 0` with `|δ_{J0ᶜ}|_1 ≤ c₀ |δ_{J0}|_1`, `κ √n |δ_{J0}|_2 ≤ |Xδ|_2`.
The paper's `κ(s, c₀)` is the largest such `κ`; Assumption RE(s, c₀) is "`RE X s c0 κ` for
some `κ > 0`". -/
def RE {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s : ℕ) (c0 κ : ℝ) : Prop :=
  ∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ, δ ≠ 0 → ConeCond c0 J0 δ →
    κ * Real.sqrt n * l2On δ J0 ≤ euclNorm (X.mulVec δ)

/-- The single-set restricted eigenvalue inequality with constant `γ` at the index set `J0`:
for every `δ ≠ 0` with `|δ_{J0ᶜ}|_1 ≤ c₀ |δ_{J0}|_1`, `γ √n |δ_{J0}|_2 ≤ |Xδ|_2`, i.e.
`min_{δ ≠ 0, cone} |Xδ|_2 / (√n |δ_{J0}|_2) ≥ γ` (p. 13; the minimum over an empty set is `+∞`). -/
def REAt {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (c0 γ : ℝ) (J0 : Finset (Fin M)) : Prop :=
  ∀ δ : Fin M → ℝ, δ ≠ 0 → ConeCond c0 J0 δ →
    γ * Real.sqrt n * l2On δ J0 ≤ euclNorm (X.mulVec δ)

/-- The index family `𝒥_{s,γ,c₀} = {J0 : |J0| ≤ s, min_{δ ≠ 0, cone} |Xδ|_2/(√n|δ_{J0}|_2) ≥ γ}`
(p. 13). -/
def JFamily {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s : ℕ) (γ c0 : ℝ)
    (J0 : Finset (Fin M)) : Prop :=
  J0.card ≤ s ∧ REAt X c0 γ J0

/-- The set `Λ_{s,γ,c₀} = {β : J(β) ∈ 𝒥_{s,γ,c₀}}` (p. 13). -/
def LambdaSet {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s : ℕ) (γ c0 : ℝ) :
    Set (Fin M → ℝ) :=
  {β | JFamily X s γ c0 (supp β)}

/-- The Lasso criterion (2.1) (p. 4):
`Ŝ(β) + 2r ∑_j ‖f_j‖_n |β_j|` with `Ŝ(β) = (1/n) ∑ᵢ (Y_i − (Xβ)_i)²`. -/
noncomputable def lassoObj {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (β : Fin M → ℝ) : ℝ :=
  empSq (fun i => y i - X.mulVec β i) + 2 * r * ∑ j, colNorm X j * |β j|

/-- `β̂` is a Lasso solution (2.1): it minimises the Lasso criterion over all of `ℝ^M`.
(Minimisers need not be unique; statements are made for every minimiser.) -/
def IsLasso {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (βhat : Fin M → ℝ) : Prop :=
  ∀ β : Fin M → ℝ, lassoObj X y r βhat ≤ lassoObj X y r β

/-- The tuning constant `r = A σ √(log M / n)` of Lemma B.1 and Theorem 6.1 (natural log). -/
noncomputable def tuning (n M : ℕ) (A σ : ℝ) : ℝ :=
  A * σ * Real.sqrt (Real.log M / n)

/-- The noise model of Section 2: `W_1, …, W_n` are measurable, independent, and each
`W_i ∼ N(0, σ²)`. -/
def GaussianNoise {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (W : Fin n → Ω → ℝ) (σ : ℝ) : Prop :=
  (∀ i, Measurable (W i)) ∧ iIndepFun W P ∧
    ∀ i, P.map (W i) = gaussianReal 0 (σ ^ 2).toNNReal

/-- The random variable `V_j = n⁻¹ ∑ᵢ f_j(Z_i) W_i` (p. 21). -/
noncomputable def noiseCorr {Ω : Type*} {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (W : Fin n → Ω → ℝ) (j : Fin M) (ω : Ω) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, X i j * W i ω

/-- The event `𝒜 = ⋂_j {2|V_j| ≤ r_{n,j}}` with `r_{n,j} = r ‖f_j‖_n` (p. 21). -/
def noiseEvent {Ω : Type*} {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (W : Fin n → Ω → ℝ)
    (r : ℝ) : Set Ω :=
  {ω | ∀ j, 2 * |noiseCorr X W j ω| ≤ r * colNorm X j}

/-- The deterministic form of the event `𝒜` for a fixed noise vector `w = y − f`:
`2 |n⁻¹ ∑ᵢ X_{ij} w_i| ≤ r ‖f_j‖_n` for every `j`. -/
def NoiseBound {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (w : Fin n → ℝ) (r : ℝ) : Prop :=
  ∀ j, 2 * |(1 / (n : ℝ)) * ∑ i, X i j * w i| ≤ r * colNorm X j

end LassoDantzig.Oracle


