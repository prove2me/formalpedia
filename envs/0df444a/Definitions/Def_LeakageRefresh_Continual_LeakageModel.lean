-- Prove2me | Definitions.Def_LeakageRefresh_Continual_LeakageModel
-- name    : LeakageRefresh_Continual_LeakageModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:09:03.006363+00:00
-- url     : https://prove2.me/theorems/882f0135-13c3-4ee0-9aac-7c122585727e
-- title:
--   The continual-leakage model: answers in $\{0,1\}^\lambda\times\{0,1\}^\lambda$, adaptive strategies, the real execution, the transcript law $P_s^T$, statistical distance and the tape-included view
-- statement:
--   Fix $n\ge 2$, a number of refreshes $T\ge0$ and a leakage budget $\lambda\ge0$. The **answer alphabet** is $\mathcal Z=\{0,1\}^\lambda\times\{0,1\}^\lambda$, of size $K=2^{2\lambda}$. A **pair of leakage functions** is $(\mathrm{Leak}^L,\mathrm{Leak}^R)$ with
--   $$\mathrm{Leak}^L:U_L\times\mathrm{InvMatr}^n_2\to\{0,1\}^\lambda,\qquad \mathrm{Leak}^R:U_R\times\mathrm{InvMatr}^n_2\to\{0,1\}^\lambda ,$$
--   and the **answer** of a refresh of the old state $(L,R)$ by $M$ is $Z=(\mathrm{Leak}^L(L,M),\mathrm{Leak}^R(R,M))\in\mathcal Z$. A **deterministic strategy** assigns a pair of leakage functions $(\mathrm{Leak}^L_{i,h},\mathrm{Leak}^R_{i,h})$ to every round $i\in\{1,\dots,T\}$ and every formal history $h\in\mathcal Z^{i-1}$, including histories that never occur.
--
--   The **real execution** for the secret $s$: sample $X_0=(L_0,R_0)\leftarrow\mu_s$ and $M_1,\dots,M_T$ independent and uniform in $\mathrm{InvMatr}^n_2$; in round $i$ the leakage functions are chosen from the real history $H_{i-1}=(Z_1,\dots,Z_{i-1})$, the answer is $Z_i=(\mathrm{Leak}^L_{i,H_{i-1}}(L_{i-1},M_i),\mathrm{Leak}^R_{i,H_{i-1}}(R_{i-1},M_i))$, and the state becomes $(L_{i-1}M_i,\ M_i^{-1}R_{i-1})$. $P_s^T$ is the law of the complete transcript $H_T\in\mathcal Z^T$. The **statistical distance** of two distributions on a finite set $V$ is
--   $$\delta(P,Q)=\tfrac12\sum_{v\in V}|P(v)-Q(v)| .$$
--   A **randomized adversary** is a probability space $(\Theta,\rho)$ with a measurable map $\theta\mapsto\sigma_\theta$ to deterministic strategies; its **view** for the secret $s$ is the joint law of $(\theta,H_T)$ when $\theta\leftarrow\rho$ and $H_T\sim P_s^T[\sigma_\theta]$, and two views are compared by the total variation $\sup_A|V_0(A)-V_1(A)|$ over measurable sets $A$ (the published definition `FoundationsRL_DECLower_tvDist`, used by Theorem 4.1).
--
--   **Formalization Note.** `Answer lam` is `(Fin lam → Bool) × (Fin lam → Bool)`; `LeakPair n lam` is the pair of functions `UL n → InvMatr n → (Fin lam → Bool)` and `UR n → InvMatr n → (Fin lam → Bool)`. `Strategy n T lam` gives, for each `i : Fin T` (the paper's round $i+1$) and each history `Fin i → Answer lam`, a `LeakPair`. `runPrefix`/`transcript` compute the execution for an initial state and a tuple of matrices, choosing each round's leakage functions from the real earlier answers. `transcriptLaw σ s h` $=\sum_{x_0}\mu_s(x_0)\cdot\#\{(M_1,\dots,M_T):\text{transcript}=h\}/|\mathrm{InvMatr}^n_2|^T$. Strategies carry the discrete σ-algebra; `transcriptKernel` is $\sigma\mapsto P_s^T[\sigma]$ as a kernel, and `viewLaw ρ σ hσ s` is the composition-product `ρ ⊗ₘ (kernel ∘ σ)`, the law of $(\theta,H_T)$. The total variation is not defined here: Theorem 4.1 uses the published `FoundationsRL.DECLower.tvDist` (`⨆` over measurable sets of $|P(A)-Q(A)|$, real-valued), which for the probability measures `viewLaw` produces is a supremum of a nonempty set bounded by $1$.
-- source:
--   Dziembowski, Faust, Leakage-Resilient Computation via Matrix Refreshing, arXiv:2611.04876 (sha256 fdbb2454…), p. 16, Definition 2.2; p. 17, Definition 2.4; pp. 24–27, Definitions 3.1–3.3 and §3.4; p. 27, §4.1; p. 79, App. A (Statistical distance)

import Mathlib
import Definitions.Def_LeakageRefresh_Continual_Encoding

/-!
# The continual-leakage model of the matrix refresh and the transcript laws

Dziembowski, Faust, *Leakage-Resilient Computation via Matrix Refreshing*, arXiv:2611.04876
(sha256 fdbb2454…), Definitions 2.2 and 2.4 (pp. 16–17), §3: Definitions 3.1–3.3 and §3.4
(pp. 24–27), §4.1 (p. 27), App. A "Statistical distance" (p. 79).

* `Answer lam = {0,1}^λ × {0,1}^λ` is the answer alphabet `Z` (`K = |Z| = 2^{2λ}`); `lam` is `λ`.
* `LeakPair n lam` is a pair of leakage functions `Leak^L : U_L × InvMatr → {0,1}^λ` (left) and
  `Leak^R : U_R × InvMatr → {0,1}^λ` (right); `answer lp x M` is the complete answer
  `(Leak^L(L, M), Leak^R(R, M))` of a refresh of the old state `x = (L, R)` by `M`.
* `Strategy n T lam`: a deterministic adaptive strategy. Round `i : Fin T` is the paper's round
  `i + 1`; its formal incoming history is a tuple `Fin i → Answer lam` (the paper's `Z^{i}`
  for round `i + 1`); the strategy is defined on every formal history.
* `runPrefix`, `transcript`: the real execution of Definition 2.4 for an initial state and
  `T` matrices; each round's leakage functions are chosen from the real history of earlier
  answers, evaluated at the old shares and the round's matrix, and the state is refreshed.
* `transcriptLaw σ s h = P_sᵀ(h)`: the probability of the complete history `h` when
  `(L₀, R₀) ←$ µₛ` and `M₁, …, M_T ←$ InvMatr` are independent and uniform.
* `statDist P Q = ½ ∑ |P − Q|` (Definition 2.2).
* Randomized adversaries (§3.4): a probability space `(Θ, ρ)` and a measurable map
  `σ : Θ → Strategy` (the strategy type carries the discrete σ-algebra). `viewLaw ρ σ hσ s` is
  the joint law of `(θ, H_T)` on `Θ × Zᵀ`. Its total variation `sup_A |V₀(A) − V₁(A)|` over
  measurable sets is the published definition `FoundationsRL_DECLower_tvDist`, imported by the
  theorem that uses it.
-/

namespace LeakageRefresh.Continual

open MeasureTheory ProbabilityTheory

/-- The answer alphabet `Z = {0,1}^λ × {0,1}^λ` (Definition 3.2). -/
abbrev Answer (lam : ℕ) := (Fin lam → Bool) × (Fin lam → Bool)

/-- A pair of leakage functions of one refresh (Definition 3.1): the left one reads the old
left share and the refresh matrix, the right one the old right share and the matrix. -/
abbrev LeakPair (n lam : ℕ) :=
  (UL n → InvMatr n → (Fin lam → Bool)) × (UR n → InvMatr n → (Fin lam → Bool))

/-- The complete answer `Z = (Leak^L(L, M), Leak^R(R, M))` of a refresh of the old state
`x = (L, R)` by the matrix `M` (Definition 3.2). -/
def answer {n lam : ℕ} (lp : LeakPair n lam) (x : State n) (M : InvMatr n) : Answer lam :=
  (lp.1 x.1 M, lp.2 x.2 M)

/-- A deterministic adaptive leakage strategy for `T` refreshes (Definition 3.3): for every
round `i : Fin T` (the paper's round `i + 1`) and every formal incoming history `h ∈ Z^{i}`,
a pair of leakage functions. -/
def Strategy (n T lam : ℕ) : Type :=
  (i : Fin T) → (Fin i → Answer lam) → LeakPair n lam

instance (n T lam : ℕ) : Finite (Strategy n T lam) := by
  unfold Strategy
  have h1 : ∀ i : Fin T, Finite (Fin i → Answer lam) := fun _ => Pi.finite
  have h2 : Finite (LeakPair n lam) := inferInstance
  have h3 : ∀ i : Fin T, Finite ((Fin i → Answer lam) → LeakPair n lam) := fun _ => Pi.finite
  exact Pi.finite

/-- Strategies carry the discrete σ-algebra. -/
instance (n T lam : ℕ) : MeasurableSpace (Strategy n T lam) := ⊤

instance (n T lam : ℕ) : DiscreteMeasurableSpace (Strategy n T lam) :=
  ⟨fun _ => trivial⟩

/-- The real execution (Definition 2.4 with the answers of Definitions 3.1–3.2) for `k ≤ T`
rounds: the state after `k` refreshes and the history `H_k = (Z₁, …, Z_k)`. -/
def runPrefix {n T lam : ℕ} (σ : Strategy n T lam) (x0 : State n) (Ms : Fin T → InvMatr n) :
    (k : ℕ) → k ≤ T → State n × (Fin k → Answer lam)
  | 0, _ => (x0, Fin.elim0)
  | k + 1, hk =>
    let p := runPrefix σ x0 Ms k (Nat.le_of_succ_le hk)
    let i : Fin T := ⟨k, hk⟩
    let z : Answer lam := answer (σ i p.2) p.1 (Ms i)
    (refreshState (Ms i) p.1, Fin.snoc (α := fun _ => Answer lam) p.2 z)

/-- The complete transcript `H_T = (Z₁, …, Z_T)` of the execution with initial state `x0` and
refresh matrices `Ms`. -/
def transcript {n T lam : ℕ} (σ : Strategy n T lam) (x0 : State n) (Ms : Fin T → InvMatr n) :
    Fin T → Answer lam :=
  (runPrefix σ x0 Ms T le_rfl).2

/-- The transcript distribution `P_sᵀ` (§4.1): the probability of the complete history `h` when
`X₀ = (L₀, R₀) ←$ µₛ` and the matrices `M₁, …, M_T ←$ InvMatrⁿ₂` are independent and uniform. -/
noncomputable def transcriptLaw {n T lam : ℕ} (σ : Strategy n T lam) (s : ZMod 2)
    (h : Fin T → Answer lam) : ℝ :=
  ∑ x0 : State n, mu n s x0 *
    (((Finset.univ.filter (fun Ms : Fin T → InvMatr n => transcript σ x0 Ms = h)).card : ℝ) /
      (Fintype.card (Fin T → InvMatr n) : ℝ))

/-- Statistical distance `δ(P, Q) = ½ ‖P − Q‖₁ = ½ ∑_v |P(v) − Q(v)|` (Definition 2.2). -/
noncomputable def statDist {V : Type*} [Fintype V] (P Q : V → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ v, |P v - Q v|

/-- `P_sᵀ` as a measure on `Zᵀ` (a finite sum of point masses). -/
noncomputable def transcriptMeasure {n T lam : ℕ} (σ : Strategy n T lam) (s : ZMod 2) :
    Measure (Fin T → Answer lam) :=
  ∑ h : Fin T → Answer lam, ENNReal.ofReal (transcriptLaw σ s h) • Measure.dirac h

/-- The kernel `σ ↦ P_sᵀ[σ]` from deterministic strategies to transcripts. -/
noncomputable def transcriptKernel (n T lam : ℕ) (s : ZMod 2) :
    Kernel (Strategy n T lam) (Fin T → Answer lam) :=
  Kernel.ofFunOfCountable (fun σ => transcriptMeasure σ s)

/-- The view of a randomized adversary with its tape (§3.4, App. A p. 79): the tape
`θ ←$ ρ` selects the deterministic strategy `σ θ`; the view is the joint law of `(θ, H_T)`. -/
noncomputable def viewLaw {n T lam : ℕ} {Θ : Type*} [MeasurableSpace Θ] (ρ : Measure Θ)
    (σ : Θ → Strategy n T lam) (hσ : Measurable σ) (s : ZMod 2) :
    Measure (Θ × (Fin T → Answer lam)) :=
  ρ ⊗ₘ (Kernel.comap (transcriptKernel n T lam s) σ hσ)

end LeakageRefresh.Continual


