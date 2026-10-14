-- Prove2me | Definitions.Def_GMCPBandit_Regret_Algorithm
-- name    : GMCPBandit_Regret_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:52.396929+00:00
-- url     : https://prove2.me/theorems/91768d68-646f-4fa5-8069-e1d8606ebfbd
-- title:
--   pp. 11–14 — 2-step weighted Lasso, ε-decay sampling, the G-MCP-Bandit algorithm and its cumulative regret
-- statement:
--   This definition file fixes the G-MCP-Bandit algorithm of §4 and its regret.
--
--   **Weighted Lasso** (Eq. (3), p. 11). On samples $(x_j,r_j)_{j=1}^n$ and nonnegative weights $w\in\mathbb R^d$, the objective is
--   $$\frac1n\sum_{j=1}^n f(r_j\mid x_j^\top\beta)+\sum_{i=1}^d w_i|\beta_i|,$$
--   minimized over the feasible set $B_b=\{\beta:\|\beta\|_1\le b\}$. A *selection rule* returns, for every $n\ge1$, every data set with rewards in $[-R_{\max},R_{\max}]$ and every $w\ge0$, a minimizer over $B_b$, measurably in the data and the weights.
--
--   **MCP and 2sWL** (pp. 11–12). $P'_{\lambda,a}(x)=\max(0,\lambda-x/a)$ for $x\ge0$. The 2sWL estimate with inputs $a,\lambda$: Step 1, $\beta_1=\beta^W(X,r,\lambda)$ with all weights $\lambda$; Step 2, $w_j=P'_{a,\lambda}(|\beta_{1,j}|)$ if $\beta_{1,j}\ne0$ and $w_j=\lambda$ otherwise, and $\hat\beta_{2sWL}=\beta^W(X,r,w)$. On an empty data set the estimate is $0$.
--
--   **ε-decay sampling** (p. 13). At time $t$, a random sample is drawn ($\mathcal D_t=1$) with probability $\min\{1,t_0/t\}$, and then a decision is chosen uniformly from $\mathcal K$. $\mathcal R_k(t)$ is the set of times $s\le t$ with $\mathcal D_s=1$ and decision $k$ drawn; $n_k=|\mathcal R_k(T)|$.
--
--   **G-MCP-Bandit** (box, p. 14), with inputs $t_0,h,\lambda_{1,0},\lambda_{2,0},a$ and
--   $$\lambda_1(t)=\lambda_{1,0}\sqrt{1+\frac{\log d}{\log(t+1)}},\qquad\lambda_2(t)=\lambda_{2,0}\sqrt{\frac{\log(t+1)+\log d}{t+1}}.$$
--   At $t=1,2,\dots$: observe $x_t$; if $\mathcal D_t=1$ play the uniformly drawn decision. Otherwise, with $\beta^{random}_k(t-1)$ the 2sWL estimate on $\mathcal R_k(t-1)$ with $\lambda_1(t-1)$ and $\beta^{whole}_k(t-1)$ the 2sWL estimate on $\mathcal W_k(t-1)=\{s\le t-1:\pi_s=k\}$ with $\lambda_2(t-1)$, form
--   $$\Pi_t=\Big\{i:\mu(x_t^\top\beta^{random}_i(t-1))\ge\max_j\mu(x_t^\top\beta^{random}_j(t-1))-\tfrac h2\Big\}$$
--   and play $\pi_t\in\arg\max_{k\in\Pi_t}\mu(x_t^\top\beta^{whole}_k(t-1))$ (the single element if $\Pi_t$ is a singleton).
--
--   **Regret** (p. 7).
--   $$R^C(T)=\sum_{t=1}^T\mathbb E\Big[\max_k\mu(x_t^\top\beta_k)-\mu(x_t^\top\beta_{\pi_t})\Big].$$
--
--   These objects are the subject of Propositions 2, 4, 6 and Theorem 1.
--
--   **Formalization Note** The algorithm is run round by round on each sample path; each round sees only the covariates, the rewards of the decisions actually played, the past decisions, and the coin and draw of the current and past rounds. Ties in the arg max are broken by an arbitrary tie-breaking rule, measurable in the scores. The regret is written with the conditional means $\mu(x^\top\beta)$; it equals the paper's $\mathbb E[R^{\pi^*_t}_t-R^{\pi_t}_t]$ by the tower property, since $\pi_t$ does not depend on the time-$t$ rewards. Rows of a sample set are taken in increasing time order.
-- source:
--   Wang, Wei and Yao, Online Learning and Decision-Making under Generalized Linear Model with High-Dimensional Data, arXiv:1812.02962v1, pp. 7, 11–14, Eq. (3), (4), §4.2 2sWL Procedure, §4.3 ε-decay Random Sampling Method, §4.4 G-MCP-Bandit Algorithm

import Mathlib
import Definitions.Def_GMCPBandit_Regret_Model

open MeasureTheory ProbabilityTheory

namespace GMCPBandit.Regret

/-! Wang, Wei and Yao, arXiv:1812.02962v1, §4, pp. 11–14: the weighted Lasso (3), the MCP
derivative, the 2-step weighted Lasso (2sWL, p. 12), the ε-decay random sampling method (p. 13),
the G-MCP-Bandit algorithm (box, p. 14) and the cumulative regret `R^C(T)` (p. 7). -/

/-- The feasible set `B_b = {β : ‖β‖₁ ≤ b}` (A.1: "all feasible β satisfies ‖β‖₁ ≤ b"). -/
def feasibleBall (d : ℕ) (b : ℝ) : Set (Fin d → ℝ) := {β | l1 β ≤ b}

/-- The weighted Lasso objective of Eq. (3), p. 11, on `n` samples `D j = (x_j, r_j)`:
`(1/n) ∑_j f(r_j | x_jᵀβ) + ∑_i w_i |β_i|`, with `f = −log g`. -/
noncomputable def wlObjective {d : ℕ} (g : ℝ → ℝ → ℝ) {n : ℕ} (D : Fin n → (Fin d → ℝ) × ℝ)
    (w : Fin d → ℝ) (β' : Fin d → ℝ) : ℝ :=
  (∑ j, negLogDens g (D j).2 ((D j).1 ⬝ᵥ β')) / n + ∑ i, w i * |β' i|

/-- A weighted-Lasso selection rule: given `n` samples and a weight vector, it returns a vector. -/
abbrev WLSelector (d : ℕ) := (n : ℕ) → (Fin n → (Fin d → ℝ) × ℝ) → (Fin d → ℝ) → (Fin d → ℝ)

/-- The selection rule returns a weighted Lasso estimate `β^W(X, r, w)` of Eq. (3) over the feasible
set `B_b`: for every `n ≥ 1`, every data set whose rewards lie in `[−R_max, R_max]` and every
nonnegative weight vector `w`, its output lies in `B_b` and minimizes the objective (3) over `B_b`
(minimizers need not be unique). It is measurable in the data and the weights. -/
def IsWLSelector {d : ℕ} (g : ℝ → ℝ → ℝ) (Rmax b : ℝ) (sel : WLSelector d) : Prop :=
  (∀ (n : ℕ), 1 ≤ n → ∀ (D : Fin n → (Fin d → ℝ) × ℝ), (∀ j, (D j).2 ∈ Set.Icc (-Rmax) Rmax) →
    ∀ (w : Fin d → ℝ), (∀ i, 0 ≤ w i) →
      sel n D w ∈ feasibleBall d b ∧
        ∀ β' ∈ feasibleBall d b, wlObjective g D w (sel n D w) ≤ wlObjective g D w β') ∧
  ∀ n : ℕ, Measurable (fun p : (Fin n → (Fin d → ℝ) × ℝ) × (Fin d → ℝ) => sel n p.1 p.2)

/-- The derivative of the MCP penalty `P_{λ,a}(x) = ∫_0^{|x|} max(0, λ − |t|/a) dt` (p. 11) at
`x ≥ 0`: `P'_{λ,a}(x) = max(0, λ − x/a)`. -/
noncomputable def mcpDeriv (lam a x : ℝ) : ℝ := max 0 (lam - x / a)

/-- The **2-step weighted Lasso** (2sWL) procedure of p. 12 with inputs `a` and `λ`:
Step 1, `β₁ = β^W(X, r, λ)` (all weights `λ`); Step 2, `w_j = P'_{a,λ}(|β_{1,j}|)` if `β_{1,j} ≠ 0`
and `w_j = λ` otherwise, and `β̂_2sWL = β^W(X, r, w)`. -/
noncomputable def twoStepEst {d : ℕ} (sel : WLSelector d) (lam a : ℝ) (n : ℕ)
    (D : Fin n → (Fin d → ℝ) × ℝ) : Fin d → ℝ :=
  let β1 := sel n D (fun _ => lam)
  sel n D (fun j => if β1 j ≠ 0 then mcpDeriv lam a |β1 j| else lam)

/-- The 2sWL estimate on the samples `(x_s, y_s)` at the times `s ∈ S`, rows in increasing time
order; `0` when `S = ∅` (the algorithm's initialization `β(0) = 0`). -/
noncomputable def estOn {d : ℕ} (sel : WLSelector d) (lam a : ℝ) (S : Finset ℕ)
    (x : ℕ → Fin d → ℝ) (y : ℕ → ℝ) : Fin d → ℝ :=
  if S = ∅ then 0 else
    twoStepEst sel lam a S.card
      (fun i => (x (S.orderEmbOfFin rfl i), y (S.orderEmbOfFin rfl i)))

/-- The input parameters `t₀, h, λ_{1,0}, λ_{2,0}, a` of the G-MCP-Bandit algorithm (box, p. 14). -/
structure AlgParams where
  t0 : ℝ
  h : ℝ
  lam10 : ℝ
  lam20 : ℝ
  a : ℝ

/-- `λ₁(t) = λ_{1,0} √(1 + log d / log(t+1))` (box, p. 14), natural logarithms. -/
noncomputable def lam1 (lam10 : ℝ) (d t : ℕ) : ℝ :=
  lam10 * Real.sqrt (1 + Real.log d / Real.log ((t : ℝ) + 1))

/-- `λ₂(t) = λ_{2,0} √((log(t+1) + log d)/(t+1))` (box, p. 14), natural logarithms. -/
noncomputable def lam2 (lam20 : ℝ) (d t : ℕ) : ℝ :=
  lam20 * Real.sqrt ((Real.log ((t : ℝ) + 1) + Real.log d) / ((t : ℝ) + 1))

/-- The ε-decay coin (p. 13): a random sample is drawn at time `t`, `𝒟_t = 1`, iff the uniform
`v_t ∈ [0, 1]` satisfies `v_t ≤ min{1, t₀/t}` (probability `min{1, t₀/t}`). -/
def explore (t0 : ℝ) (v : ℕ → ℝ) (t : ℕ) : Prop := v t ≤ min 1 (t0 / t)

/-- The random-sample set `ℛ_k(t) = {s ∈ [1, t] : 𝒟_s = 1, π_s = k}`: the times up to `t` at which a
random sample was drawn and the uniformly random decision `u_s` was `k`. Its size is the random
sample size `n_k` of Proposition 2. -/
noncomputable def randomSet {K : ℕ} (t0 : ℝ) (v : ℕ → ℝ) (u : ℕ → Fin K) (k : Fin K) (t : ℕ) :
    Finset ℕ :=
  by classical exact (Finset.Icc 1 t).filter (fun s => explore t0 v s ∧ u s = k)

/-- The random samples of decision `k` up to time `t` whose covariate lies in `U`:
`𝒜 = {s ∈ ℛ_k(t) : x_s ∈ U}` (Lemma EC.8, p. ec16, with `U = U_k`). -/
noncomputable def randomSamplesIn {d K : ℕ} (t0 : ℝ) (v : ℕ → ℝ) (u : ℕ → Fin K)
    (x : ℕ → Fin d → ℝ) (U : Set (Fin d → ℝ)) (k : Fin K) (t : ℕ) : Finset ℕ :=
  by classical exact (randomSet t0 v u k t).filter (fun s => x s ∈ U)

/-- The whole-sample set `𝒲_k(t) = {s ∈ [1, t] : π_s = k}` of a sequence of decisions. -/
noncomputable def wholeSet {K : ℕ} (arm : ℕ → Fin K) (k : Fin K) (t : ℕ) : Finset ℕ :=
  by classical exact (Finset.Icc 1 t).filter (fun s => arm s = k)

/-- A tie-breaking rule for `arg max_{k ∈ Π} s_k`: given scores `s` and a set of decisions `Π`. -/
abbrev ArgmaxRule (K : ℕ) := (Fin K → ℝ) → Finset (Fin K) → Fin K

/-- The rule returns, for every nonempty `Π`, an element of `Π` maximizing the score over `Π`, and is
measurable in the scores. (On a singleton `Π_t` it returns the single element, as the box does.) -/
def IsArgmaxRule {K : ℕ} (tb : ArgmaxRule K) : Prop :=
  (∀ (s : Fin K → ℝ) (S : Finset (Fin K)), S.Nonempty → tb s S ∈ S ∧ ∀ j ∈ S, s j ≤ s (tb s S)) ∧
    ∀ S : Finset (Fin K), Measurable (fun s : Fin K → ℝ => tb s S)

/-- One round `t ≥ 1` of the **G-MCP-Bandit** algorithm (box, p. 14). It reads the covariates
`x_s` (`s ≤ t`), the observed rewards `y_s` (`s < t`), the decisions `past s` played before `t`, the
coin values `v_t` and the uniform draws `u_s` (`s ≤ t`).
* If `𝒟_t = 1`, the uniformly random decision `u_t` is played.
* Otherwise, with `β^random_k(t−1) = 2sWL(ℛ_k(t−1), λ₁(t−1))` and
  `β^whole_k(t−1) = 2sWL(𝒲_k(t−1), λ₂(t−1))`,
  `Π_t = {i : μ(x_tᵀβ^random_i(t−1)) ≥ max_j μ(x_tᵀβ^random_j(t−1)) − h/2}`, and the decision played
  is `arg max_{k ∈ Π_t} μ(x_tᵀβ^whole_k(t−1))`. -/
noncomputable def banditStep {d K : ℕ} (ν : Measure ℝ) (g : ℝ → ℝ → ℝ) (sel : WLSelector d)
    (tb : ArgmaxRule K) (θ : AlgParams) (t : ℕ) (x : ℕ → Fin d → ℝ) (y : ℕ → ℝ) (v : ℕ → ℝ)
    (u : ℕ → Fin K) (past : ℕ → Fin K) : Fin K := by
  classical
  exact
    if explore θ.t0 v t then u t
    else
      let βr : Fin K → Fin d → ℝ := fun k =>
        estOn sel (lam1 θ.lam10 d (t - 1)) θ.a (randomSet θ.t0 v u k (t - 1)) x y
      let βw : Fin K → Fin d → ℝ := fun k =>
        estOn sel (lam2 θ.lam20 d (t - 1)) θ.a (wholeSet past k (t - 1)) x y
      let shortlist : Finset (Fin K) := Finset.univ.filter (fun i =>
        (⨆ j, meanFn ν g (x t ⬝ᵥ βr j)) - θ.h / 2 ≤ meanFn ν g (x t ⬝ᵥ βr i))
      tb (fun k => meanFn ν g (x t ⬝ᵥ βw k)) shortlist

/-- The decisions played by the G-MCP-Bandit in rounds `1, …, t`, computed round by round: `r s k`
is the reward decision `k` would yield at time `s`, and round `t+1` is given only the rewards
`r s (π_s)` of the decisions actually played. Entry `s` is meaningful for `1 ≤ s ≤ t`. -/
noncomputable def armHistory {d K : ℕ} [NeZero K] (ν : Measure ℝ) (g : ℝ → ℝ → ℝ)
    (sel : WLSelector d) (tb : ArgmaxRule K) (θ : AlgParams) (x : ℕ → Fin d → ℝ)
    (r : ℕ → Fin K → ℝ) (v : ℕ → ℝ) (u : ℕ → Fin K) : ℕ → ℕ → Fin K
  | 0 => fun _ => 0
  | t + 1 =>
    Function.update (armHistory ν g sel tb θ x r v u t) (t + 1)
      (banditStep ν g sel tb θ (t + 1) x
        (fun s => r s (armHistory ν g sel tb θ x r v u t s)) v u
        (armHistory ν g sel tb θ x r v u t))

/-- The decision `π_t` played at time `t ≥ 1` on the sample path `ω`, with covariates `X_t(ω)`,
potential rewards `R_t(ω)`, coins `V_t(ω)` and uniform draws `A_t(ω)`. -/
noncomputable def arm {Ω : Type*} {d K : ℕ} [NeZero K] (ν : Measure ℝ) (g : ℝ → ℝ → ℝ)
    (sel : WLSelector d) (tb : ArgmaxRule K) (θ : AlgParams) (X : ℕ → Ω → Fin d → ℝ)
    (R : ℕ → Ω → Fin K → ℝ) (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K) (ω : Ω) (t : ℕ) : Fin K :=
  armHistory ν g sel tb θ (fun s => X s ω) (fun s => R s ω) (fun s => V s ω) (fun s => A s ω) t t

/-- The random-sample estimator `β^random_k(t) = 2sWL(ℛ_k(t), λ₁(t))` on the sample path `ω`, for the
algorithm inputs `t₀`, `λ_{1,0}`, `a`. On `ℛ_k(t)` the decision played is `k`, so its rewards are
`R_s(k)`. It depends only on the exploration coins, the draws, the covariates and the rewards of
decision `k`, not on the exploitation decisions. -/
noncomputable def betaRandom {Ω : Type*} {d K : ℕ} (sel : WLSelector d) (t0 lam10 a : ℝ)
    (X : ℕ → Ω → Fin d → ℝ) (R : ℕ → Ω → Fin K → ℝ) (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K)
    (k : Fin K) (t : ℕ) (ω : Ω) : Fin d → ℝ :=
  estOn sel (lam1 lam10 d t) a (randomSet t0 (fun s => V s ω) (fun s => A s ω) k t)
    (fun s => X s ω) (fun s => R s ω k)

/-- The whole-sample estimator `β^whole_k(t) = 2sWL(𝒲_k(t), λ₂(t))` on the sample path `ω`, where
`𝒲_k(t)` is the set of times `s ≤ t` at which the algorithm played `k`. -/
noncomputable def betaWhole {Ω : Type*} {d K : ℕ} [NeZero K] (ν : Measure ℝ) (g : ℝ → ℝ → ℝ)
    (sel : WLSelector d) (tb : ArgmaxRule K) (θ : AlgParams) (X : ℕ → Ω → Fin d → ℝ)
    (R : ℕ → Ω → Fin K → ℝ) (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K) (k : Fin K) (t : ℕ) (ω : Ω) :
    Fin d → ℝ :=
  estOn sel (lam2 θ.lam20 d t) θ.a (wholeSet (arm ν g sel tb θ X R V A ω) k t)
    (fun s => X s ω) (fun s => R s ω k)

/-- The cumulative regret `R^C(T) = ∑_{t=1}^T 𝔼[max_k μ(X_tᵀβ_k) − μ(X_tᵀβ_{π_t})]` (p. 7), the
expected reward of the oracle decision minus that of the decision played. -/
noncomputable def regret {Ω : Type*} [MeasurableSpace Ω] {d K : ℕ} [NeZero K] (P : Measure Ω)
    (ν : Measure ℝ) (g : ℝ → ℝ → ℝ) (β : Fin K → Fin d → ℝ) (sel : WLSelector d)
    (tb : ArgmaxRule K) (θ : AlgParams) (X : ℕ → Ω → Fin d → ℝ) (R : ℕ → Ω → Fin K → ℝ)
    (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, ∫ ω, ((⨆ k, meanFn ν g (X t ω ⬝ᵥ β k)) -
    meanFn ν g (X t ω ⬝ᵥ β (arm ν g sel tb θ X R V A ω t))) ∂P

end GMCPBandit.Regret


