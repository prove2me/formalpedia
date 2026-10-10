-- Prove2me | Definitions.Def_RiskSensMFG_Existence_NonhomMDP
-- name    : RiskSensMFG_Existence_NonhomMDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:25.209885+00:00
-- url     : https://prove2.me/theorems/f44de256-b5f0-4cfa-b890-c8c04b4948fc
-- title:
--   §4.1, pp. 11–13 — the risk-sensitive nonhomogeneous MDP of a fixed flow: $J^n_k$, $J_k$, their optimal values, the operator $T_k$ (4) and $\nu^\pi_k$
-- statement:
--   Fix a measure flow $\mu=(\mu_t)_{t\ge0}$ and write $p_t(\cdot|x,a)=p(\cdot|x,a,\mu_t)$ and $c_t(x,a)=c(x,a,\mu_t)$. This defines a nonhomogeneous Markov decision process.
--
--   **Chain started at time $k$.** For a Markov policy $\pi$, a time $k$ and a state $x$, consider the chain with $x(k)=x$, $a(t)\sim\pi_t(\cdot|x(t))$ and $x(t+1)\sim p_t(\cdot|x(t),a(t))$ for $t\ge k$, and write $E^\pi[\,\cdot\,|\,x(k)=x]$ for expectation under it.
--
--   **Value functions.** For $\gamma>0$ and $n\ge k\ge0$,
--   $$J^n_k(\pi,x,\gamma)=E^\pi\Big[e^{\gamma\sum_{t=k}^{n}\beta^{t-k}c_t(x(t),a(t))}\,\Big|\,x(k)=x\Big],\qquad J^n_k(x,\gamma)=\inf_\pi J^n_k(\pi,x,\gamma),$$
--   $$J_k(\pi,x,\gamma)=E^\pi\Big[e^{\gamma\sum_{t=k}^{\infty}\beta^{t-k}c_t(x(t),a(t))}\,\Big|\,x(k)=x\Big],\qquad J_k(x,\gamma)=\inf_\pi J_k(\pi,x,\gamma),$$
--   the infima being over Markov policies.
--
--   **Dynamic programming operator** (4). For $u:\mathsf X\to\mathbb R$,
--   $$[T_ku](x)=\inf_{a\in\mathsf A}\Big[e^{\lambda\beta^kc_k(x,a)}\int_{\mathsf X}u(y)\,p_k(dy\,|\,x,a)\Big].$$
--
--   **State–action marginals.** For a Markov policy $\pi$, $\nu^\pi_k=\mathcal L(x(k),a(k))$ is the law of the time-$k$ state–action pair under $P^\pi$ (initial law $\mu_0$, flow $\mu$).
--
--   These are the objects of Lemmas 1–3 and Theorem 2, and, with the flow of state marginals of a state–action flow $\nu$, of the value functions $J^\nu_{*,t}$ of §4.2.
--
--   **Formalization Note** As the paper states on p. 11, in §4.1 “policy” means Markov policy, and the infima are over Markov policies. The conditional expectation “given $x(k)=x$” is realized by starting the chain at time $k$ in state $x$ (Ionescu–Tulcea from $\delta_x\otimes\pi_k(\cdot|x)$, with the time-shifted kernels), so it is defined for every $x$, not only almost everywhere. The finite sum is over $t\in\{k,\dots,n\}$ (empty when $n<k$; every statement assumes $n\ge k$). The infima are real infima of quantities $\ge0$ over a nonempty set whenever $\mathsf A\neq\emptyset$, which every statement assumes.
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, §4.1, pp. 11–13, definitions of p_t, c_t, J^n_k, J_k (p. 11), operator (4) (p. 12), ν^π_k (Theorem 2, p. 13)

import Mathlib
import Definitions.Def_RiskSensMFG_Existence_Model

open MeasureTheory ProbabilityTheory Finset

namespace RiskSensMFG.Existence

variable {X A : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
  [MeasurableSpace A]

/-- For a fixed flow `μ`, the law on `(X × A)^∞` of the nonhomogeneous chain started at time `k`
in state `x` under the Markov policy `π` (§4.1, p. 11): coordinate `j` is `(x(k+j), a(k+j))`,
`x(k) = x`, `a(k+j) ∼ π_{k+j}(· | x(k+j))`, `x(k+j+1) ∼ p_{k+j}(· | x(k+j), a(k+j))` with
`p_t(· | x, a) = p(· | x, a, μ_t)`. -/
noncomputable def chainFrom (M : Model X A) (μ : ℕ → PM X) (π : MarkovPolicy X A) (k : ℕ)
    (x : X) : Measure (ℕ → X × A) :=
  @Kernel.trajMeasure (fun _ : ℕ => X × A) (fun _ => inferInstance)
    (Measure.dirac x ⊗ₘ π.π k)
    (fun j =>
      (M.p.comap (fun h : (Π _ : Iic j, X × A) =>
          ((h ⟨j, mem_Iic.2 le_rfl⟩).1, (h ⟨j, mem_Iic.2 le_rfl⟩).2, μ (k + j))) (by fun_prop)) ⊗ₖ
        (π.π (k + j + 1)).comap Prod.snd measurable_snd)
    (fun _ => by infer_instance)

/-- `J^n_k(π, x, γ) = E^π[exp(γ ∑_{t=k}^n β^{t-k} c_t(x(t), a(t))) | x(k) = x]` (p. 11), with
`c_t(x, a) = c(x, a, μ_t)`. -/
noncomputable def Jfin (M : Model X A) (μ : ℕ → PM X) (π : MarkovPolicy X A) (k n : ℕ) (x : X)
    (γ : ℝ) : ℝ :=
  ∫ ω, Real.exp (γ * ∑ t ∈ Icc k n,
      M.β ^ (t - k) * M.c ((ω (t - k)).1, (ω (t - k)).2, μ t)) ∂(chainFrom M μ π k x)

/-- `J_k(π, x, γ) = E^π[exp(γ ∑_{t=k}^∞ β^{t-k} c_t(x(t), a(t))) | x(k) = x]` (p. 11). -/
noncomputable def Jinf (M : Model X A) (μ : ℕ → PM X) (π : MarkovPolicy X A) (k : ℕ) (x : X)
    (γ : ℝ) : ℝ :=
  ∫ ω, Real.exp (γ * ∑' j, M.β ^ j * M.c ((ω j).1, (ω j).2, μ (k + j))) ∂(chainFrom M μ π k x)

/-- The finite-horizon optimal value `J^n_k(x, γ) = inf_π J^n_k(π, x, γ)`, the infimum over Markov
policies (p. 11). -/
noncomputable def JfinOpt (M : Model X A) (μ : ℕ → PM X) (k n : ℕ) (x : X) (γ : ℝ) : ℝ :=
  ⨅ π : MarkovPolicy X A, Jfin M μ π k n x γ

/-- The infinite-horizon optimal value `J_k(x, γ) = inf_π J_k(π, x, γ)`, the infimum over Markov
policies (p. 11). -/
noncomputable def JinfOpt (M : Model X A) (μ : ℕ → PM X) (k : ℕ) (x : X) (γ : ℝ) : ℝ :=
  ⨅ π : MarkovPolicy X A, Jinf M μ π k x γ

/-- The operator (4): `[T_k u](x) = inf_{a ∈ A} [exp(λ β^k c_k(x, a)) ∫ u(y) p_k(dy | x, a)]`. -/
noncomputable def T (M : Model X A) (μ : ℕ → PM X) (k : ℕ) (u : X → ℝ) (x : X) : ℝ :=
  ⨅ a : A, Real.exp (M.lam * M.β ^ k * M.c (x, a, μ k)) * ∫ y, u y ∂(M.p (x, a, μ k))

/-- `ν^π_k = L(x(k), a(k))` under the Markov policy `π`, the flow `μ` and the initial law `μ₀`
(Theorem 2, p. 13). -/
noncomputable def stateActionLaw (M : Model X A) (μ : ℕ → PM X) (π : MarkovPolicy X A) (k : ℕ) :
    Measure (X × A) :=
  (law M μ π.toPolicy).map (fun ω => ω k)

end RiskSensMFG.Existence


