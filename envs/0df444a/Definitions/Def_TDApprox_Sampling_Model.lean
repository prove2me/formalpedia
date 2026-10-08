-- Prove2me | Definitions.Def_TDApprox_Sampling_Model
-- name    : TDApprox_Sampling_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:21.87129+00:00
-- url     : https://prove2.me/theorems/b007cb86-ef29-4b1a-ab87-02786ce103ae
-- title:
--   The Markov model, q-sampled TD(0), and Assumptions 1, 2, and 4
-- statement:
--   Let $S$ be a finite or countable state space, $P$ a Markov transition kernel, $g(i,j)$ the cost of moving from $i$ to $j$, and $0<\alpha<1$ the discount factor. The path law from $i$ starts at $i$ and follows $P$. Its cost-to-go is the expected discounted sum of transition costs. For an invariant distribution $\pi$, the space $L_2(S,D)$ consists of functions with summable $\pi(i)J(i)^2$, and $\Pi$ is the weighted projection onto the span of the basis functions $\phi_k$. The operator $T^{(0)}$ takes the expected one-step cost plus $\alpha$ times the next-state value.
--
--   For independently sampled state–successor pairs $(I_t,J_t)$ with joint law $q(i)P(i,\{j\})$, the sampled iteration is
--
--   $$r_{t+1}=r_t+\gamma_t\phi(I_t)\bigl(g(I_t,J_t)+\alpha\phi(J_t)^\mathsf{T}r_t-\phi(I_t)^\mathsf{T}r_t\bigr).$$
--
--   Assumptions 1 and 2 express the paper's invariant-law, finite-moment, and independent-basis conditions. Assumption 4 requires nonnegative, nonincreasing step sizes with divergent sum and summable squares. The file also defines the one-feature construction used in Theorem 3 and the coefficients of its mean recurrence.
--
--   **Formalization Note** The state space is a countable discrete measurable type. The path law is built with Ionescu–Tulcea. Expectations and infinite sums have explicit integrability or summability guards in theorem statements. The projection uses the inverse Gram matrix under Assumptions 1 and 2. Only $T^{(0)}$ is needed in this mission.
-- source:
--   Tsitsiklis & Van Roy, LIDS-P-2322 (1996), §2 p. 4, §3 Eq. (1) p. 6, §4 Assumptions 1, 2, 4 pp. 9–11, §9 pp. 24–25; https://dspace.mit.edu/entities/publication/ab395d25-a6d3-407a-9589-60eaac58fd05

import Mathlib
import Definitions.Def_TDApprox_Conv_Model

namespace TDApprox.Sampling

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

variable {S : Type*} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

noncomputable def pathLaw (P : Kernel S S) [IsMarkovKernel P] (i : S) :
    Measure (ℕ → S) :=
  Kernel.trajMeasure (Measure.dirac i)
    (fun n => P.comap (fun x : (k : Finset.Iic n) → S => x ⟨n, Finset.mem_Iic.mpr (le_refl n)⟩) (by fun_prop))

noncomputable def gram (π : Measure S) {K : ℕ} (φ : S → Fin K → ℝ) :
    Matrix (Fin K) (Fin K) ℝ :=
  fun k l => ∑' i, (π {i}).toReal * φ i k * φ i l

noncomputable def featureMoment (π : Measure S) {K : ℕ}
    (φ : S → Fin K → ℝ) (J : S → ℝ) : Fin K → ℝ :=
  fun k => ∑' i, (π {i}).toReal * φ i k * J i

noncomputable def proj (π : Measure S) {K : ℕ}
    (φ : S → Fin K → ℝ) (J : S → ℝ) : S → ℝ :=
  fun i => dotProduct (φ i) (Matrix.mulVec (gram π φ)⁻¹ (featureMoment π φ J))

noncomputable def T0 (P : Kernel S S) [IsMarkovKernel P]
    (g : S → S → ℝ) (α : ℝ) (J : S → ℝ) (i : S) : ℝ :=
  ∫ ω, (g (ω 0) (ω 1) + α * J (ω 1)) ∂(pathLaw P i)

structure Assumption1 (P : Kernel S S) [IsMarkovKernel P]
    (π : Measure S) [IsProbabilityMeasure π] (g : S → S → ℝ) (α : ℝ) : Prop where
  invariant : P.Invariant π
  unique_invariant : ∀ ν : Measure S, [IsProbabilityMeasure ν] → P.Invariant ν → ν = π
  positive : ∀ i, 0 < π {i}
  cost_square_integrable : Integrable (fun x : S × S => g x.1 x.2 ^ 2) (π ⊗ₘ P)
  cost_to_go_integrable : ∀ i,
    (∫⁻ ω, ∑' t : ℕ, ENNReal.ofReal (α ^ t * |g (ω t) (ω (t + 1))|) ∂(pathLaw P i)) < ⊤

structure Assumption2 (π : Measure S) {K : ℕ} (φ : S → Fin K → ℝ) : Prop where
  independent : LinearIndependent ℝ (fun k : Fin K => fun i : S => φ i k)
  square_integrable : ∀ k : Fin K, Integrable (fun i => φ i k ^ 2) π

def IsQSample {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : S → ℝ) (P : Kernel S S) (I J : ℕ → Ω → S) : Prop :=
  (∀ t, Measurable (I t) ∧ Measurable (J t)) ∧
  iIndepFun (fun t ω => (I t ω, J t ω)) μ ∧
  ∀ t i j, μ {ω | I t ω = i ∧ J t ω = j} = ENNReal.ofReal (q i) * P i {j}

def qIter {Ω : Type*} {K : ℕ} (α : ℝ) (γ : ℕ → ℝ)
    (g : S → S → ℝ) (φ : S → Fin K → ℝ) (r₀ : Fin K → ℝ)
    (I J : ℕ → Ω → S) : ℕ → Ω → Fin K → ℝ
  | 0, _ => r₀
  | t + 1, ω =>
    qIter α γ g φ r₀ I J t ω +
      (γ t * (g (I t ω) (J t ω) +
        α * (φ (J t ω) ⬝ᵥ qIter α γ g φ r₀ I J t ω) -
        (φ (I t ω) ⬝ᵥ qIter α γ g φ r₀ I J t ω))) • φ (I t ω)

noncomputable def qBias (q : S → ℝ) (P : Kernel S S)
    (g : S → S → ℝ) {K : ℕ} (φ : S → Fin K → ℝ) : Fin K → ℝ :=
  fun k => ∑' i, q i * φ i k * TDApprox.Conv.gbar P g i

noncomputable def qDrift (q : S → ℝ) (P : Kernel S S)
    (α : ℝ) {K : ℕ} (φ : S → Fin K → ℝ) : Matrix (Fin K) (Fin K) ℝ :=
  fun k l => ∑' i, q i * φ i k * (α * (∫ j, φ j l ∂(P i)) - φ i l)

noncomputable def rowKernel (p : Measure S) : Kernel S S := Kernel.const S p

instance rowKernel.instIsMarkovKernel (p : Measure S) [IsProbabilityMeasure p] :
    IsMarkovKernel (rowKernel p) := by
  unfold rowKernel
  infer_instance

noncomputable def sampleFeature (s₁ s₂ : S) : S → Fin 1 → ℝ :=
  by classical exact fun s _ => if s = s₁ then 1 else if s = s₂ then 2 else 0

end TDApprox.Sampling


