-- Prove2me | Definitions.Def_GMCPBandit_Regret_Model
-- name    : GMCPBandit_Regret_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:31:58.795981+00:00
-- url     : https://prove2.me/theorems/51811a9b-9399-4e7d-be29-a95349b297f7
-- title:
--   pp. 6–9 — the GLM reward family, the covariate bandit primitives and Assumptions A.1–A.5
-- statement:
--   This definition file fixes the model of §3 of Wang, Wei and Yao. Covariates are vectors $x\in\mathbb R^d$, decisions are $k\in\mathcal K=\{1,\dots,K\}$, and times are $t=1,2,\dots$
--
--   **Norms and supports.** $\|v\|_1=\sum_j|v_j|$, $\|v\|_2=(\sum_j v_j^2)^{1/2}$, $\mathcal S(v)=\{j:v_j\neq0\}$, and $u_I$ is $u$ with the entries outside $I$ set to $0$.
--
--   **Generalized linear reward family.** A base measure $\nu$ on $\mathbb R$ concentrated on $[-R_{\max},R_{\max}]$ and a jointly measurable density $g(r\mid\eta)$ with respect to $\nu$, positive for $r\in[-R_{\max},R_{\max}]$, integrable and normalized, $\int g(r\mid\eta)\,d\nu(r)=1$, for every linear predictor $\eta$. The reward of decision $k$ at covariate $x$ has law $g(\cdot\mid x^\top\beta_k)\,\nu$. Write
--   $$f(r\mid\eta)=-\log g(r\mid\eta),\qquad \mu(\eta)=\int r\,g(r\mid\eta)\,d\nu(r),$$
--   so that $\mathbb E[R_k\mid x,\beta]=\mu(x^\top\beta)$.
--
--   **Regions and expected Hessian.** $U_k=\{x\in\mathcal X:\mu(x^\top\beta_k)>\max_{j\neq k}\mu(x^\top\beta_j)+h\}$, and for $\xi\in\mathbb R^d$ the expected Hessian of the log-likelihood over samples with $x\in U_k$,
--   $$\mathbb E[\nabla^2\mathcal L(\xi)]_{ij}=\frac{1}{\mathcal P_x(U_k)}\int_{U_k}\Big(\int f''(r\mid x^\top\xi)\,g(r\mid x^\top\beta_k)\,d\nu(r)\Big)x_ix_j\,d\mathcal P_x(x).$$
--
--   **Assumptions** (pp. 8–9).
--   1. **A.1** (parameter set): $x_{\max},s,R_{\max},\beta_{\min},b>0$ with $\|x\|_\infty\le x_{\max}$ for $x\in\mathcal X$, $|\mathcal S_k|\le s$, $\beta_{\min}\le|\beta_{k,j}|$ for $j\in\mathcal S_k$, and $\|\beta_k\|_1\le b$.
--   2. **A.2** (margin): $C>0$ with $\mathbb P\big(0<|\mu(x^\top\beta_i)-\mu(x^\top\beta_j)|\le\gamma\big)\le CR_{\max}\gamma$ for all $i\neq j$ and $\gamma>0$, $x\sim\mathcal P_x$.
--   3. **A.3** (arm optimality): a partition $\mathcal K=\mathcal K_o\cup\mathcal K_s$ and $h,p^*>0$ with $\mu(x^\top\beta_k)+h<\max_{j\ne k}\mu(x^\top\beta_j)$ for $k\in\mathcal K_s$ and $x\in\mathcal X$, and $\mathcal P_x(U_k)\ge p^*$ for $k\in\mathcal K_o$.
--   4. **A.4** (restricted eigenvalue): $\kappa>0$ such that for $k\in\mathcal K_o$, $\|\xi\|_1\le b$ and $\|u_{\mathcal S_k^c}\|_1\le3\|u_{\mathcal S_k}\|_1$: $\frac{\kappa}{s}\|u_{\mathcal S_k}\|_1^2\le u^\top\mathbb E[\nabla^2\mathcal L(\xi)]u$.
--   5. **A.5** (density): for $r\in[-R_{\max},R_{\max}]$, $\eta\mapsto f(r\mid\eta)$ is smooth and convex, and $|f'|\le\sigma$, $f''<\sigma_2$, $|f'''|\le\sigma_3$ for $|\eta|\le b\,x_{\max}$.
--
--   **Random primitives.** On a probability space: covariates $X_t\in\mathcal X$ with law $\mathcal P_x$, potential rewards $R_t(k)\in[-R_{\max},R_{\max}]$ with $(X_t,R_t(k))\sim\mathcal P_x(dx)\,g(r\mid x^\top\beta_k)\,\nu(dr)$, i.i.d. over $t$; exploration coins $V_t\sim\mathrm{Unif}[0,1]$ and uniform draws $A_t$ on $\mathcal K$, with $V_t$, $A_t$, $(X_t,R_t)$ independent and everything independent across times.
--
--   These are the standing hypotheses of every result of the paper.
--
--   **Formalization Note** Decisions are `Fin K` (the paper's $k$ is `k.val + 1`). A.5's derivatives are in the linear predictor $\eta$, required on the range $|\eta|\le bx_{\max}$ of $x^\top\beta$ for covariates and feasible parameters; smoothness is `ContDiff ℝ ∞` (not analytic). A.3's "every $x$" means every $x$ in the covariate domain $\mathcal X$. A.4 is required for $k\in\mathcal K_o$ only, where $\mathcal P_x(U_k)\ge p^*>0$; the conditional expectation divides by $\mathcal P_x(U_k)$. The dependence between rewards of different decisions at the same time is unconstrained. Exploration is modelled by exogenous coins: $\mathcal D_t=1$ iff $V_t\le\min\{1,t_0/t\}$.
-- source:
--   Wang, Wei and Yao, Online Learning and Decision-Making under Generalized Linear Model with High-Dimensional Data, arXiv:1812.02962v1, pp. 6–9, §3, Assumptions A.1–A.5

import Mathlib

open MeasureTheory ProbabilityTheory

namespace GMCPBandit.Regret

/-! Wang, Wei and Yao, *Online Learning and Decision-Making under Generalized Linear Model with
High-Dimensional Data*, arXiv:1812.02962v1, §3, pp. 6–9: the generalized linear reward model, the
random primitives of the covariate bandit, and Assumptions A.1–A.5.

Conventions. Covariates are vectors `x : Fin d → ℝ`; decisions (arms) are `Fin K`, the paper's
decision `k ∈ {1, …, K}` being `k.val + 1`. Times are `t = 1, 2, …`; values at `t = 0` are never
used. -/

/-- The `ℓ₁` norm `‖v‖₁ = ∑ⱼ |vⱼ|`. -/
def l1 {d : ℕ} (v : Fin d → ℝ) : ℝ := ∑ j, |v j|

/-- The Euclidean norm `‖v‖₂ = (∑ⱼ vⱼ²)^{1/2}`. -/
noncomputable def l2 {d : ℕ} (v : Fin d → ℝ) : ℝ := Real.sqrt (∑ j, v j ^ 2)

/-- The support `S(v) = {j : vⱼ ≠ 0}` (p. 7: `𝒮_k = {j : β^true_{k,j} ≠ 0}`). -/
noncomputable def supp {d : ℕ} (v : Fin d → ℝ) : Finset (Fin d) :=
  by classical exact Finset.univ.filter (fun j => v j ≠ 0)

/-- `u_I`: the vector `u` with the entries outside `I` set to zero. -/
noncomputable def restrictTo {d : ℕ} (I : Finset (Fin d)) (u : Fin d → ℝ) : Fin d → ℝ :=
  by classical exact fun j => if j ∈ I then u j else 0

/-- The negative log density `f(r | η) ≐ −log g(r | η)` (A.5, p. 9), as a function of the
reward `r` and the linear predictor `η = xᵀβ`. -/
noncomputable def negLogDens (g : ℝ → ℝ → ℝ) (r η : ℝ) : ℝ := -Real.log (g r η)

/-- The mean reward at linear predictor `η`: `μ(η) = ∫ r g(r | η) dν(r)`, so that
`𝔼[R_k | x, β] = μ(xᵀβ)` (p. 7: `𝔼[R_k | x, β] = ∫ r dG(r | xᵀβ)`). -/
noncomputable def meanFn (ν : Measure ℝ) (g : ℝ → ℝ → ℝ) (η : ℝ) : ℝ := ∫ r, r * g r η ∂ν

/-- The **generalized linear reward family** of §3 (p. 6–7): a base measure `ν` on `ℝ` concentrated on
`[−R_max, R_max]` (A.1's `|R_k| ≤ R_max`) and a jointly measurable density `g(r | η)` w.r.t. `ν`,
positive on `[−R_max, R_max]`, integrable and normalized for every linear predictor `η`. The reward of
decision `k` at covariate `x` has law `g(· | xᵀβ_k) · ν`. -/
structure IsGLMFamily (ν : Measure ℝ) (g : ℝ → ℝ → ℝ) (Rmax : ℝ) : Prop where
  Rmax_pos : 0 < Rmax
  concentrated : ν (Set.Icc (-Rmax) Rmax)ᶜ = 0
  measurable_g : Measurable (Function.uncurry g)
  pos : ∀ r ∈ Set.Icc (-Rmax) Rmax, ∀ η : ℝ, 0 < g r η
  integrable : ∀ η : ℝ, Integrable (fun r => g r η) ν
  normalized : ∀ η : ℝ, ∫ r, g r η ∂ν = 1

/-- `max_{j ≠ k} 𝔼[R_j | x, β_j] = max_{j ≠ k} μ(xᵀβ_j)`. For `K ≥ 2` the index set is finite and
nonempty, so the supremum is a maximum. -/
noncomputable def maxOther {d K : ℕ} (ν : Measure ℝ) (g : ℝ → ℝ → ℝ) (β : Fin K → Fin d → ℝ)
    (x : Fin d → ℝ) (k : Fin K) : ℝ :=
  ⨆ j : {j : Fin K // j ≠ k}, meanFn ν g (x ⬝ᵥ β j)

/-- The region `U_k ≐ {x ∈ 𝒳 : 𝔼[R_k | x, β_k] > max_{j≠k} 𝔼[R_j | x, β_j] + h}` of A.3 (p. 8). -/
def optRegion {d K : ℕ} (𝒳 : Set (Fin d → ℝ)) (ν : Measure ℝ) (g : ℝ → ℝ → ℝ)
    (β : Fin K → Fin d → ℝ) (h : ℝ) (k : Fin K) : Set (Fin d → ℝ) :=
  {x | x ∈ 𝒳 ∧ maxOther ν g β x k + h < meanFn ν g (x ⬝ᵥ β k)}

/-- The expected Hessian of A.4 (p. 9) for decision `k` at the point `ξ`:
`𝔼[∇²ℒ(ξ)] = 𝔼[f''(R | Xᵀξ) X Xᵀ | X ∈ U_k]`, where `X ∼ 𝒫_x` conditioned on `U_k` and
`R | X ∼ g(· | Xᵀβ_k) ν`; entry `(i, j)` is
`(1/𝒫_x(U_k)) ∫_{U_k} (∫ f''(r | xᵀξ) g(r | xᵀβ_k) dν(r)) xᵢ xⱼ d𝒫_x(x)`, with `f''` the second
derivative of `η ↦ f(r | η)`. -/
noncomputable def condHessian {d K : ℕ} (𝒳 : Set (Fin d → ℝ)) (PX : Measure (Fin d → ℝ))
    (ν : Measure ℝ) (g : ℝ → ℝ → ℝ) (β : Fin K → Fin d → ℝ) (h : ℝ) (k : Fin K)
    (ξ : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j =>
    (∫ x in optRegion 𝒳 ν g β h k,
        (∫ r, iteratedDeriv 2 (fun η => negLogDens g r η) (x ⬝ᵥ ξ) * g r (x ⬝ᵥ β k) ∂ν) *
          x i * x j ∂PX) /
      (PX (optRegion 𝒳 ν g β h k)).toReal

/-- **A.1** (Parameter set), p. 8: positive constants `x_max, s, R_max, β_min, b` with
`‖x‖_∞ ≤ x_max` on the covariate domain, `|𝒮_k| ≤ s`, `β_min ≤ |β_{k,j}|` for `j ∈ 𝒮_k`, and
`‖β_k‖₁ ≤ b`, for every decision `k`. (`|R_k| ≤ R_max` is carried by `IsGLMFamily` and by the
primitives; "all feasible β satisfies ‖β‖₁ ≤ b" by the feasible set of the estimator.) -/
def A1 {d K : ℕ} (𝒳 : Set (Fin d → ℝ)) (β : Fin K → Fin d → ℝ) (xmax s Rmax βmin b : ℝ) : Prop :=
  0 < xmax ∧ 0 < s ∧ 0 < Rmax ∧ 0 < βmin ∧ 0 < b ∧
    (∀ x ∈ 𝒳, ∀ j, |x j| ≤ xmax) ∧
    (∀ k, ((supp (β k)).card : ℝ) ≤ s) ∧
    (∀ k, ∀ j ∈ supp (β k), βmin ≤ |β k j|) ∧
    (∀ k, l1 (β k) ≤ b)

/-- **A.2** (Margin condition), p. 8: a constant `C > 0` with
`ℙ(0 < |𝔼[R_i | x, β_i] − 𝔼[R_j | x, β_j]| ≤ γ) ≤ C R_max γ` for all `i ≠ j` and all `γ > 0`,
`x ∼ 𝒫_x`. -/
def A2 {d K : ℕ} (PX : Measure (Fin d → ℝ)) (ν : Measure ℝ) (g : ℝ → ℝ → ℝ)
    (β : Fin K → Fin d → ℝ) (Rmax C : ℝ) : Prop :=
  0 < C ∧ ∀ i j : Fin K, i ≠ j → ∀ γ : ℝ, 0 < γ →
    PX {x | 0 < |meanFn ν g (x ⬝ᵥ β i) - meanFn ν g (x ⬝ᵥ β j)| ∧
        |meanFn ν g (x ⬝ᵥ β i) - meanFn ν g (x ⬝ᵥ β j)| ≤ γ} ≤ ENNReal.ofReal (C * Rmax * γ)

/-- **A.3** (Arm optimality), p. 8: a partition `𝒦 = 𝒦_o ∪ 𝒦_s` and constants `h > 0`, `p* > 0`
such that every `k ∈ 𝒦_s` has `𝔼[R_k | x] + h < max_{j≠k} 𝔼[R_j | x]` for every covariate `x ∈ 𝒳`,
and every `k ∈ 𝒦_o` has `ℙ(x ∈ U_k) ≥ p*`. -/
def A3 {d K : ℕ} (𝒳 : Set (Fin d → ℝ)) (PX : Measure (Fin d → ℝ)) (ν : Measure ℝ)
    (g : ℝ → ℝ → ℝ) (β : Fin K → Fin d → ℝ) (Ko Ks : Finset (Fin K)) (h pstar : ℝ) : Prop :=
  0 < h ∧ 0 < pstar ∧ Disjoint Ko Ks ∧ Ko ∪ Ks = Finset.univ ∧
    (∀ k ∈ Ks, ∀ x ∈ 𝒳, meanFn ν g (x ⬝ᵥ β k) + h < maxOther ν g β x k) ∧
    ∀ k ∈ Ko, ENNReal.ofReal pstar ≤ PX (optRegion 𝒳 ν g β h k)

/-- **A.4** (Restricted eigenvalue condition), p. 9: `κ > 0` such that for every `k ∈ 𝒦_o`, every
feasible `ξ` (`‖ξ‖₁ ≤ b`) and every `u` with `‖u_{𝒮_kᶜ}‖₁ ≤ 3‖u_{𝒮_k}‖₁`,
`(κ/s) ‖u_{𝒮_k}‖₁² ≤ uᵀ 𝔼[∇²ℒ(ξ)] u`, the expectation being over i.i.d. samples with `x ∈ U_k`. -/
def A4 {d K : ℕ} (𝒳 : Set (Fin d → ℝ)) (PX : Measure (Fin d → ℝ)) (ν : Measure ℝ)
    (g : ℝ → ℝ → ℝ) (β : Fin K → Fin d → ℝ) (Ko : Finset (Fin K)) (h s b κ : ℝ) : Prop :=
  0 < κ ∧ ∀ k ∈ Ko, ∀ ξ : Fin d → ℝ, l1 ξ ≤ b → ∀ u : Fin d → ℝ,
    l1 (restrictTo (supp (β k))ᶜ u) ≤ 3 * l1 (restrictTo (supp (β k)) u) →
      κ / s * l1 (restrictTo (supp (β k)) u) ^ 2 ≤
        u ⬝ᵥ (condHessian 𝒳 PX ν g β h k ξ).mulVec u

/-- **A.5** (Density function), p. 9: for every reward `r ∈ [−R_max, R_max]`, `η ↦ f(r | η)` is
smooth (`C^∞`) and convex, and there are `σ, σ₂, σ₃ > 0` with `|f'(r | η)| ≤ σ`, `f''(r | η) < σ₂`
and `|f'''(r | η)| ≤ σ₃` for every linear predictor `|η| ≤ b x_max` (the range of `xᵀβ` over
covariates and feasible parameters). Derivatives are in `η`. -/
def A5 (g : ℝ → ℝ → ℝ) (Rmax b xmax σ σ2 σ3 : ℝ) : Prop :=
  0 < σ ∧ 0 < σ2 ∧ 0 < σ3 ∧ ∀ r ∈ Set.Icc (-Rmax) Rmax,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun η => negLogDens g r η) ∧
    ConvexOn ℝ Set.univ (fun η => negLogDens g r η) ∧
    ∀ η : ℝ, |η| ≤ b * xmax →
      |deriv (fun η => negLogDens g r η) η| ≤ σ ∧
      iteratedDeriv 2 (fun η => negLogDens g r η) η < σ2 ∧
      |iteratedDeriv 3 (fun η => negLogDens g r η) η| ≤ σ3

/-- The **exploration coins** of the ε-decay random sampling method (p. 13), on a probability space
`(Ω, P)`: `V_t ∼ Unif[0, 1]` (the coin `𝒟_t = 𝟙{V_t ≤ min{1, t₀/t}}`) and `A_t` uniform on the
`K` decisions (the uniformly random decision), with `V_t` and `A_t` independent and the pairs
`(V_t, A_t)`, `t ≥ 1`, independent across times. -/
structure IsExplorationCoins {Ω : Type*} [MeasurableSpace Ω] {K : ℕ} (P : Measure Ω)
    (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K) : Prop where
  measurable_V : ∀ t, 1 ≤ t → Measurable (V t)
  measurable_A : ∀ t, 1 ≤ t → Measurable (A t)
  law_V : ∀ t, 1 ≤ t → P.map (V t) = volume.restrict (Set.Icc (0 : ℝ) 1)
  law_A : ∀ t, 1 ≤ t → ∀ k : Fin K, P {ω | A t ω = k} = (K : ENNReal)⁻¹
  indep_V_A : ∀ t, 1 ≤ t → IndepFun (V t) (A t) P
  iIndep_time : iIndepFun (fun t : ℕ => fun ω => (V (t + 1) ω, A (t + 1) ω)) P

/-- The **random primitives** of the bandit (§3, pp. 6–7), on a probability space `(Ω, P)`:
covariates `X_t ∈ 𝒳` and potential rewards `R_t(k)` of every decision `k`, together with the
exploration coins `(V_t, A_t)`. For `t ≥ 1`:
* `(X_t, R_t)` are identically distributed, `X_t ∼ 𝒫_x`, every reward lies in `[−R_max, R_max]`,
  and for each decision `k` the law of `(X_t, R_t(k))` is `𝒫_x(dx) g(r | xᵀβ_k) ν(dr)`;
* the tuples `(X_t, R_t, V_t, A_t)` are independent across `t`, and within a time `(X_t, R_t)` is
  independent of `(V_t, A_t)`.
The dependence between the rewards of different decisions at the same time is left free. -/
structure IsPrimitives {Ω : Type*} [MeasurableSpace Ω] {d K : ℕ} (P : Measure Ω)
    (𝒳 : Set (Fin d → ℝ)) (PX : Measure (Fin d → ℝ)) (ν : Measure ℝ) (g : ℝ → ℝ → ℝ)
    (β : Fin K → Fin d → ℝ) (Rmax : ℝ) (X : ℕ → Ω → Fin d → ℝ) (R : ℕ → Ω → Fin K → ℝ)
    (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K) : Prop where
  measurableSet_domain : MeasurableSet 𝒳
  measurable_X : ∀ t, 1 ≤ t → Measurable (X t)
  measurable_R : ∀ t, 1 ≤ t → Measurable (R t)
  mem_domain : ∀ t, 1 ≤ t → ∀ ω, X t ω ∈ 𝒳
  reward_bounded : ∀ t, 1 ≤ t → ∀ ω k, |R t ω k| ≤ Rmax
  law_X : ∀ t, 1 ≤ t → P.map (X t) = PX
  law_XR : ∀ t, 1 ≤ t → ∀ k : Fin K, ∀ S : Set (Fin d → ℝ), ∀ B : Set ℝ,
    MeasurableSet S → MeasurableSet B →
      P {ω | X t ω ∈ S ∧ R t ω k ∈ B} =
        ∫⁻ x in S, ∫⁻ r in B, ENNReal.ofReal (g r (x ⬝ᵥ β k)) ∂ν ∂PX
  identDistrib_XR : ∀ t, 1 ≤ t →
    IdentDistrib (fun ω => (X t ω, R t ω)) (fun ω => (X 1 ω, R 1 ω)) P P
  coins : IsExplorationCoins P V A
  indep_XR_VA : ∀ t, 1 ≤ t → IndepFun (fun ω => (X t ω, R t ω)) (fun ω => (V t ω, A t ω)) P
  iIndep_time : iIndepFun (fun t : ℕ => fun ω => (X (t + 1) ω, R (t + 1) ω, V (t + 1) ω, A (t + 1) ω)) P

end GMCPBandit.Regret


