-- Prove2me | Definitions.Def_DeepONetUniversal_Basic
-- name    : DeepONetUniversal_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T08:31:26.302446+00:00
-- url     : https://prove2.me/theorems/3b08ddf9-8f61-4001-82cf-49345efbac84
-- title:
--   DeepONet: operator networks, Tauber–Wiener functions, sensors and the ODE solution operator
-- statement:
--   Objects of Theorem 1 (eq. (1)), Section 3 and Appendices A and B of Lu, Jin and Karniadakis (2019).
--
--   1. **Networks.** For an activation $\sigma:\mathbb{R}\to\mathbb{R}$, the branch network on sensor values $v\in\mathbb{R}^m$ is $\sum_{i=1}^n c_i\,\sigma\big(\sum_{j=1}^m\xi_{ij}v_j+\theta_i\big)$, and the trunk network on $y\in\mathbb{R}^d$ is $\sigma(w\cdot y+\zeta)$. The stacked operator network of eq. (1) is
--   $$\sum_{k=1}^p\Big[\sum_{i=1}^n c_i^k\,\sigma\Big(\sum_{j=1}^m\xi_{ij}^kv_j+\theta_i^k\Big)\Big]\,\sigma(w_k\cdot y+\zeta_k).$$
--   The network of Theorem 2 is $v\mapsto W_2\,\sigma(W_1v+b_1)+b_2$ with $W_1\in\mathbb{R}^{n\times q}$, $b_1\in\mathbb{R}^n$, $W_2\in\mathbb{R}^{K\times n}$, $b_2\in\mathbb{R}^K$ and $\sigma$ applied componentwise. $\|v\|_2=(\sum_iv_i^2)^{1/2}$ is the Euclidean norm.
--   2. **Activations.** $\sigma$ is a polynomial if $\sigma(x)=q(x)$ for a real polynomial $q$. $\sigma$ is a Tauber–Wiener (TW) function (Definition 1) if for every interval $[a,b]$, every $f$ continuous on $[a,b]$ and every $\varepsilon>0$ there are $N$ and $c_i,\lambda_i,\theta_i$ with $|f(x)-\sum_{i=1}^Nc_i\sigma(\lambda_ix+\theta_i)|<\varepsilon$ on $[a,b]$. $\sigma\in S'(\mathbb{R})$ means that the distribution $\varphi\mapsto\int\sigma\varphi$ on compactly supported test functions extends to a continuous linear functional on the Schwartz space.
--   3. **Compactness in $C(K)$.** A family $V$ of real functions on $K$ is uniformly bounded (Definition 3) if $|f(x)|\le M$ for all $f\in V$, $x\in K$, and equicontinuous (Definition 4) if for every $\varepsilon>0$ there is $\delta>0$ with $|f(x)-f(y)|<\varepsilon$ for all $f\in V$ and $\|x-y\|<\delta$.
--   4. **Sensors and interpolation (Section 3).** On $[a,b]$ the sensors are $x_j=a+j(b-a)/m$, $j=0,\dots,m$. The interpolant $u_m=\mathcal L_m(u)$ is the piecewise-linear function with $u_m(x)=u(x_j)+\frac{u(x_{j+1})-u(x_j)}{x_{j+1}-x_j}(x-x_j)$ for $x_j\le x\le x_{j+1}$. For $V\subset C[a,b]$, $U_m=\{\mathcal L_m(u):u\in V\}$, $W_m=V\cup U_m$ and $W=\bigcup_{i\ge1}W_i$. The sensor values of $u$ are $[u(x_0),\dots,u(x_m)]\in\mathbb{R}^{m+1}$.
--   5. **ODE operator (eq. (3)).** $G$ is the solution operator of $s'=g(s,u,x)$, $s(a)=s_0$, on a set $D$ of inputs: for $u\in D$, $t\mapsto g((Gu)(t),u(t),t)$ is integrable on $[a,b]$ and $(Gu)(x)=s_0+\int_a^xg((Gu)(t),u(t),t)\,dt$ for $x\in[a,b]$.
--   6. **Lipschitz condition (Section 3).** For sets $S\subset\mathbb{R}^K$, $U\subset\mathbb{R}$: $\|g(s_1,u,x)-g(s_2,u,x)\|_2\le c\|s_1-s_2\|_2$ and $\|g(s,u_1,x)-g(s,u_2,x)\|_2\le c|u_1-u_2|$ for all $s,s_1,s_2\in S$, $u,u_1,u_2\in U$, $x\in[a,b]$. The value set of a family of functions on $[a,b]$ is $\{f(t):f\text{ in the family},\ t\in[a,b]\}$.
--
--   **Formalization Note** $C(K)$ is Mathlib's space of continuous maps on the subtype $K$; on compact $K$ its topology is that of the sup norm. Functions in $C[a,b]$ are evaluated at a real point through a helper that returns $0$ off $[a,b]$; every statement evaluates only on $[a,b]$. The segment of $x\in[a,b]$ in the interpolant is $j=\min(\lfloor (x-a)m/(b-a)\rfloor,m-1)$, which agrees with the paper's formula on every closed segment. $\mathbb{R}^d$ is $\mathrm{Fin}\,d\to\mathbb{R}$ with the dot product $w\cdot y=\sum_lw_ly_l$.
-- source:
--   Lu, Jin and Karniadakis, DeepONet: Learning nonlinear operators for identifying differential equations based on the universal approximation theorem of operators, arXiv:1910.03193v3 (2019), Section 1 (Theorem 1, eq. (1)), Section 2.1, Section 3 (eqs. (3)-(4)), Appendix A (Definitions 1-4, Theorem 3) and Appendix B (Lemma 7)

import Mathlib

/-!
Lu, Jin and Karniadakis, *DeepONet: Learning nonlinear operators for identifying differential
equations based on the universal approximation theorem of operators*, arXiv:1910.03193v3 (2019):
the stacked operator network of Theorem 1 (eq. (1)), the Tauber-Wiener functions, uniform
boundedness and equicontinuity of Appendix A, and the sensors, piecewise-linear interpolation,
compact set `W`, ODE operator and Lipschitz condition of Section 3 and Appendix B.
-/

open MeasureTheory

noncomputable section

namespace DeepONetUniversal

/-! ### Networks (Theorem 1, eq. (1); Theorems 4 and 5; Theorem 2) -/

/-- Theorem 1, eq. (1) ("branch"), and Theorem 4: the one-hidden-layer network
`∑_{i=1}^n c_i σ(∑_{j=1}^m ξ_{ij} v_j + θ_i)` applied to the sensor values `v = (u(x_1),…,u(x_m))`. -/
def branchNet {n m : ℕ} (σ : ℝ → ℝ) (c : Fin n → ℝ) (ξ : Fin n → Fin m → ℝ) (θ : Fin n → ℝ)
    (v : Fin m → ℝ) : ℝ :=
  ∑ i, c i * σ (∑ j, ξ i j * v j + θ i)

/-- Theorem 1, eq. (1) ("trunk"): `σ(w · y + ζ)` for `y ∈ ℝ^d`. -/
def trunkNet {d : ℕ} (σ : ℝ → ℝ) (w : Fin d → ℝ) (ζ : ℝ) (y : Fin d → ℝ) : ℝ :=
  σ (∑ l, w l * y l + ζ)

/-- Theorem 1, eq. (1), and Theorem 5 (the stacked DeepONet of Fig. 1C):
`∑_{k=1}^p [∑_{i=1}^n c_i^k σ(∑_{j=1}^m ξ_{ij}^k v_j + θ_i^k)] σ(w_k · y + ζ_k)`. -/
def operatorNet {n m p d : ℕ} (σ : ℝ → ℝ) (c : Fin p → Fin n → ℝ) (ξ : Fin p → Fin n → Fin m → ℝ)
    (θ : Fin p → Fin n → ℝ) (w : Fin p → Fin d → ℝ) (ζ : Fin p → ℝ) (v : Fin m → ℝ)
    (y : Fin d → ℝ) : ℝ :=
  ∑ k, branchNet σ (c k) (ξ k) (θ k) v * trunkNet σ (w k) (ζ k) y

/-- Theorem 2: the network `W₂ · σ(W₁ · v + b₁) + b₂` with `n` hidden units, `σ` applied
componentwise, `W₁ ∈ ℝ^{n×q}`, `b₁ ∈ ℝ^n`, `W₂ ∈ ℝ^{K×n}`, `b₂ ∈ ℝ^K`. -/
def shallowNet {n q K : ℕ} (σ : ℝ → ℝ) (W₁ : Matrix (Fin n) (Fin q) ℝ) (b₁ : Fin n → ℝ)
    (W₂ : Matrix (Fin K) (Fin n) ℝ) (b₂ : Fin K → ℝ) (v : Fin q → ℝ) : Fin K → ℝ :=
  W₂.mulVec (fun i => σ ((W₁.mulVec v) i + b₁ i)) + b₂

/-- The Euclidean norm `‖v‖₂ = (∑ v_i²)^{1/2}` on `ℝ^K` (Section 3, Theorem 2). -/
def eucNorm {K : ℕ} (v : Fin K → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

/-! ### Activation functions (Theorem 1; Appendix A, Definition 1, Theorem 3) -/

/-- Theorem 1: `σ` is a polynomial function, `σ(x) = q(x)` for a real polynomial `q`. -/
def IsPolynomialFun (σ : ℝ → ℝ) : Prop :=
  ∃ q : Polynomial ℝ, ∀ x, σ x = q.eval x

/-- Appendix A, Definition 1 (TW): the linear combinations `∑_{i=1}^N c_i σ(λ_i x + θ_i)` are
dense, in the sup norm, in every `C([a,b])`. -/
def IsTauberWiener (σ : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, ∀ f : ℝ → ℝ, ContinuousOn f (Set.Icc a b) → ∀ ε > 0,
    ∃ N : ℕ, ∃ c lam θ : Fin N → ℝ, ∀ x ∈ Set.Icc a b, |f x - ∑ i, c i * σ (lam i * x + θ i)| < ε

/-- Appendix A, Theorem 3: `σ ∈ S'(ℝ)`, i.e. the distribution `φ ↦ ∫ σ φ` defined by `σ` on
compactly supported test functions extends to a continuous linear functional on the Schwartz
space. -/
def IsTemperedDistribution (σ : ℝ → ℝ) : Prop :=
  ∃ T : SchwartzMap ℝ ℝ →L[ℝ] ℝ, ∀ φ : SchwartzMap ℝ ℝ, HasCompactSupport (φ : ℝ → ℝ) →
    T φ = ∫ x, σ x * φ x

/-! ### Compactness in `C(K)` (Appendix A, Definitions 3 and 4) -/

/-- Appendix A, Definition 3: `V` is uniformly bounded, `|f(x)| ≤ M` for all `f ∈ V`, `x ∈ K`. -/
def IsUniformlyBounded {K : Type*} (V : Set (K → ℝ)) : Prop :=
  ∃ M : ℝ, ∀ f ∈ V, ∀ x, |f x| ≤ M

/-- Appendix A, Definition 4: `V` is equicontinuous, for every `ε > 0` there is `δ > 0` with
`|f(x) - f(y)| < ε` for all `f ∈ V` and all `x, y` at distance `< δ`. -/
def IsEquicontinuousFamily {K : Type*} [PseudoMetricSpace K] (V : Set (K → ℝ)) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ f ∈ V, ∀ x y : K, dist x y < δ → |f x - f y| < ε

/-! ### Sensors and interpolation (Section 3, pp. 5-6) -/

open Classical in
/-- Section 3: the value at a real point `x` of a function `f ∈ C([a,b])` (`0` off `[a,b]`;
statements only evaluate on `[a,b]`). -/
def evalAt {a b : ℝ} {β : Type*} [TopologicalSpace β] [Zero β] (f : C(Set.Icc a b, β))
    (x : ℝ) : β :=
  if hx : x ∈ Set.Icc a b then f ⟨x, hx⟩ else 0

/-- Section 3, p. 6: the uniform sensors `x_j = a + j(b - a)/m`, `j = 0, 1, …, m`. -/
def sensor (a b : ℝ) (m j : ℕ) : ℝ := a + j * (b - a) / m

/-- Section 3, p. 6: the piecewise-linear interpolant
`u_m(x) = u(x_j) + (u(x_{j+1}) - u(x_j))/(x_{j+1} - x_j) · (x - x_j)` for `x_j ≤ x ≤ x_{j+1}`,
`j = 0, …, m-1`; the segment index of `x ∈ [a,b]` is `j = min(⌊(x-a)m/(b-a)⌋, m-1)`. -/
def interp (a b : ℝ) (m : ℕ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  let j : ℕ := min ⌊(x - a) * m / (b - a)⌋₊ (m - 1)
  u (sensor a b m j) + (u (sensor a b m (j + 1)) - u (sensor a b m j)) /
    (sensor a b m (j + 1) - sensor a b m j) * (x - sensor a b m j)

/-- Section 3, p. 6: `U_m = {L_m(u) | u ∈ V}`, the interpolants `u_m` of the functions of `V`,
as elements of `C([a,b])`. -/
def interpSet (a b : ℝ) (m : ℕ) (V : Set C(Set.Icc a b, ℝ)) : Set C(Set.Icc a b, ℝ) :=
  {w | ∃ u ∈ V, ∀ x : Set.Icc a b, w x = interp a b m (evalAt u) x}

/-- Section 3, p. 6, and Lemma 7: `W = ⋃_{i ≥ 1} W_i` with `W_i = V ∪ U_i`. -/
def sensorHull (a b : ℝ) (V : Set C(Set.Icc a b, ℝ)) : Set C(Set.Icc a b, ℝ) :=
  ⋃ (i : ℕ) (_ : 1 ≤ i), (V ∪ interpSet a b i V)

/-- Theorem 2: the sensor values `[u(x_0), …, u(x_m)] ∈ ℝ^{m+1}`. -/
def sensorValues (a b : ℝ) (m : ℕ) (u : C(Set.Icc a b, ℝ)) : Fin (m + 1) → ℝ :=
  fun j => evalAt u (sensor a b m j)

/-! ### The ODE operator (Section 3, eq. (3)) -/

/-- Section 3, eq. (3): on the set `D` of inputs, `G` is the solution operator of
`s' = g(s, u, x)`, `s(a) = s₀`, i.e. `(Gu)(x) = s₀ + ∫_a^x g((Gu)(t), u(t), t) dt` for
`x ∈ [a,b]`, the integrand being integrable on `[a,b]`. -/
def SolvesODE (a b : ℝ) {K : ℕ} (g : (Fin K → ℝ) → ℝ → ℝ → (Fin K → ℝ)) (s₀ : Fin K → ℝ)
    (G : C(Set.Icc a b, ℝ) → C(Set.Icc a b, Fin K → ℝ)) (D : Set C(Set.Icc a b, ℝ)) : Prop :=
  ∀ u ∈ D, IntervalIntegrable (fun t => g (evalAt (G u) t) (evalAt u t) t) volume a b ∧
    ∀ x : Set.Icc a b, G u x = s₀ + ∫ t in a..(x : ℝ), g (evalAt (G u) t) (evalAt u t) t

/-- Section 3, p. 6: the set of values `{f(t) | f ∈ D, t ∈ [a,b]}` taken by a family of functions
on `[a,b]` (used for "on `G(W) × W`"). -/
def valueSet {a b : ℝ} {β : Type*} [TopologicalSpace β] (D : Set C(Set.Icc a b, β)) : Set β :=
  {v | ∃ f ∈ D, ∃ t : Set.Icc a b, f t = v}

/-- Section 3, p. 6: `g(s, u, x)` is Lipschitz with constant `c` in `s` and in `u` for `s ∈ S`,
`u ∈ U`, `x ∈ [a,b]`: `‖g(s₁,u,x) - g(s₂,u,x)‖₂ ≤ c‖s₁ - s₂‖₂`,
`‖g(s,u₁,x) - g(s,u₂,x)‖₂ ≤ c|u₁ - u₂|`. -/
def IsLipschitzSU (a b : ℝ) {K : ℕ} (g : (Fin K → ℝ) → ℝ → ℝ → (Fin K → ℝ)) (c : ℝ)
    (S : Set (Fin K → ℝ)) (U : Set ℝ) : Prop :=
  (∀ s₁ ∈ S, ∀ s₂ ∈ S, ∀ r ∈ U, ∀ x ∈ Set.Icc a b,
      eucNorm (g s₁ r x - g s₂ r x) ≤ c * eucNorm (s₁ - s₂)) ∧
    (∀ s ∈ S, ∀ r₁ ∈ U, ∀ r₂ ∈ U, ∀ x ∈ Set.Icc a b,
      eucNorm (g s r₁ x - g s r₂ x) ≤ c * |r₁ - r₂|)

end DeepONetUniversal


