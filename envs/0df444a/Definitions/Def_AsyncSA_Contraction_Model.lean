-- Prove2me | Definitions.Def_AsyncSA_Contraction_Model
-- name    : AsyncSA_Contraction_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:31.561229+00:00
-- url     : https://prove2.me/theorems/71671a5e-fd5a-41ab-b5d1-8fd2d8bca199
-- title:
--   Asynchronous stochastic approximation model and Assumptions 1–3, 5, 6
-- statement:
--   Fix a positive number $n$ of coordinates and a probability space $(\Omega,\mathcal F,\mathsf P)$. An **asynchronous stochastic approximation algorithm** consists of a map $F:\mathbb R^n\to\mathbb R^n$, iterates $x(t)$, step sizes $\alpha_i(t)\in[0,1]$, noise $w_i(t)$, and observation times $0\le\tau^i_j(t)\le t$. Its update is
--
--   $$x_i(t+1)=x_i(t)+\alpha_i(t)\bigl(F_i(x^i(t))-x_i(t)+w_i(t)\bigr),\qquad x^i_j(t)=x_j(\tau^i_j(t)).$$
--
--   The file defines the running maximum $M(t)=\max_{s\le t,j}|x_j(s)|$, the weighted maximum norm $\|z\|_v=\max_i|z_i|/v_i$, and the zero-start noise-tail recursion. It records Assumption 1 (all observation times tend to infinity almost surely), Assumption 2 (adapted choices, conditional mean-zero noise, and a conditional second-moment bound $A+BM(t)^2$), Assumption 3 (divergent step-size sums and a deterministic bound on the squared sums), Assumption 5 (contraction toward $x^*$ in $\|\cdot\|_v$), and Assumption 6 (weighted linear growth of $F$).
--
--   These interfaces support the paper's boundedness and convergence theorems and can be reused for other coordinatewise stochastic iterations.
--
--   **Formalization Note** Coordinates use `Fin n`, starting at zero rather than one. Idle rounds have $\alpha_i(t)=0$; their observation times need not equal $t$ because they do not affect the update. Adaptedness of $x(t)$ is stated explicitly in theorems. Conditional moments use measurable-set integrals, with the conditional second-moment upper bound required nonnegative almost surely. Series conditions use finite partial sums.
-- source:
--   Tsitsiklis, Asynchronous Stochastic Approximation and Q-Learning, Machine Learning 16 (1994), pp. 187–189, §2, equations (1)–(9), Assumptions 1–3, 5–6

import Mathlib

namespace AsyncSA.Contraction

open MeasureTheory Filter Topology

variable {Ω : Type*}

/-- The generalized conditional mean-zero statement, tested on integrable restrictions. -/
def CondMeanZero (m₀ m : MeasurableSpace Ω)
    (P : @Measure Ω m₀) (f : Ω → ℝ) : Prop :=
  ∀ S, MeasurableSet[m] S → ∫⁻ ω in S, ‖f ω‖ₑ ∂P < ⊤ → ∫ ω in S, f ω ∂P = 0

/-- The conditional second-moment inequality, tested on every measurable set. -/
def CondSqLe (m₀ m : MeasurableSpace Ω)
    (P : @Measure Ω m₀) (f g : Ω → ℝ) : Prop :=
  (∀ᵐ ω ∂P, 0 ≤ g ω) ∧
    ∀ S, MeasurableSet[m] S →
      ∫⁻ ω in S, ENNReal.ofReal (f ω ^ 2) ∂P ≤
        ∫⁻ ω in S, ENNReal.ofReal (g ω) ∂P

/-- The weighted maximum norm of (6). -/
noncomputable def wNorm {n : ℕ} (v x : Fin n → ℝ) : ℝ :=
  ⨆ i, |x i| / v i

/-- The unified asynchronous recursion (1)–(3). -/
structure Algorithm (n : ℕ) (Ω : Type*) where
  n_pos : 0 < n
  F : (Fin n → ℝ) → Fin n → ℝ
  x : ℕ → Ω → Fin n → ℝ
  α : Fin n → ℕ → Ω → ℝ
  w : Fin n → ℕ → Ω → ℝ
  τ : Fin n → Fin n → ℕ → Ω → ℕ
  α_mem : ∀ i t ω, α i t ω ∈ Set.Icc (0 : ℝ) 1
  τ_le : ∀ i j t ω, τ i j t ω ≤ t
  update : ∀ i t ω, x (t + 1) ω i =
    x t ω i + α i t ω *
      (F (fun j => x (τ i j t ω) ω j) i - x t ω i + w i t ω)

namespace Algorithm

variable {n : ℕ} (alg : Algorithm n Ω)

/-- The possibly outdated vector xⁱ(t) of (3). -/
def xi (i : Fin n) (t : ℕ) (ω : Ω) : Fin n → ℝ :=
  fun j => alg.x (alg.τ i j t ω) ω j

/-- The running maximum M(t) of (12). -/
noncomputable def runMax (t : ℕ) (ω : Ω) : ℝ :=
  ⨆ s : Fin (t + 1), ⨆ j : Fin n, |alg.x s ω j|

variable [m₀ : MeasurableSpace Ω]

/-- Assumption 1: every old component value is eventually discarded. -/
def Assumption1 (P : Measure Ω) : Prop :=
  ∀ i j, ∀ᵐ ω ∂P, Tendsto (fun t => alg.τ i j t ω) atTop atTop

/-- Assumption 2: adapted choices and martingale-difference noise with a conditional bound. -/
structure Assumption2 (P : Measure Ω) (𝓕 : Filtration ℕ m₀) : Prop where
  x0_meas : ∀ j, Measurable[𝓕 0] (fun ω => alg.x 0 ω j)
  w_meas : ∀ i t, Measurable[𝓕 (t + 1)] (alg.w i t)
  α_meas : ∀ i t, Measurable[𝓕 t] (alg.α i t)
  τ_meas : ∀ i j t, Measurable[𝓕 t] (alg.τ i j t)
  mean_zero : ∀ i t, CondMeanZero m₀ (𝓕 t) P (alg.w i t)
  var_bound : ∃ cA cB : ℝ, ∀ i t,
    CondSqLe m₀ (𝓕 t) P (alg.w i t)
      (fun ω => cA + cB * alg.runMax t ω ^ 2)

/-- Explicit adaptedness of the iterate sequence. -/
def Adapted (𝓕 : Filtration ℕ m₀) : Prop :=
  ∀ t j, Measurable[𝓕 t] (fun ω => alg.x t ω j)

/-- Assumption 3, using partial sums so the divergent series is meaningful. -/
structure Assumption3 (P : Measure Ω) : Prop where
  sum_inf : ∀ i, ∀ᵐ ω ∂P,
    Tendsto (fun T => ∑ t ∈ Finset.range T, alg.α i t ω) atTop atTop
  sum_sq : ∃ C : ℝ, ∀ i, ∀ᵐ ω ∂P,
    ∀ T, ∑ t ∈ Finset.range T, alg.α i t ω ^ 2 ≤ C

end Algorithm

variable {n : ℕ}

/-- Assumption 5, with its witnesses made explicit. -/
def Assumption5 (F : (Fin n → ℝ) → Fin n → ℝ)
    (xstar v : Fin n → ℝ) (β : ℝ) : Prop :=
  (∀ i, 0 < v i) ∧ 0 ≤ β ∧ β < 1 ∧
    ∀ x, wNorm v (F x - xstar) ≤ β * wNorm v (x - xstar)

/-- Assumption 6: weighted linear growth with a strict contraction factor. -/
def Assumption6 (F : (Fin n → ℝ) → Fin n → ℝ) : Prop :=
  ∃ (v : Fin n → ℝ) (β D : ℝ),
    (∀ i, 0 < v i) ∧ 0 ≤ β ∧ β < 1 ∧
      ∀ x, wNorm v (F x) ≤ β * wNorm v x + D

/-- The zero-start tail recursion W(t;t₀) of (20) and (23). -/
def tailW (α w : ℕ → ℝ) (t₀ : ℕ) : ℕ → ℝ
  | 0 => 0
  | t + 1 =>
    if t₀ ≤ t then (1 - α t) * tailW α w t₀ t + α t * w t else 0

end AsyncSA.Contraction


