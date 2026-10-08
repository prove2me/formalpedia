-- Prove2me | Definitions.Def_ArapostathisAC_RossReduction_CMP
-- name    : ArapostathisAC_RossReduction_CMP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T14:52:46.513301+00:00
-- url     : https://prove2.me/theorems/858e239d-0f31-495d-bc2a-f1992d2b26d3
-- title:
--   Countable-state controlled Markov processes, admissible policies, and cost criteria
-- statement:
--   The state space is $S=\{0,1,2,\ldots\}$. At state $i$, the controller chooses an action from a nonempty compact set $U(i)$ in a metric action space. A measurable nonnegative one-stage cost $c(i,a)$ and a stochastic transition law $P(j\mid i,a)$ specify the process. For each fixed $i,j$, the functions $a\mapsto c(i,a)$ and $a\mapsto P(j\mid i,a)$ are continuous on $U(i)$.
--
--   An admissible policy may randomize its action using the full observed history; a stationary deterministic policy chooses one admissible action $f(i)$ in each state. The induced path law defines the expected $N$-stage cost $J_N(i,\pi)$ and discounted cost $J_\beta(i,\pi)$. The average cost is the limiting upper value of $J_N(i,\pi)/N$, and the optimal discounted and average values take the infimum over all admissible policies.
--
--   The average cost optimality equation requires $\rho+h(i)$ to equal an attained minimum of $c(i,a)+\sum_jP(j\mid i,a)h(j)$, with the real series summable. A transformed model has the same admissible actions and costs and transition probabilities $(P(j\mid i,a)-\alpha\mathbf 1_{\{j=0\}})/(1-\alpha)$ on admissible pairs.
--
--   **Formalization Note** Expected nonnegative costs and their infima are extended nonnegative real values. The path law is the Ionescu–Tulcea measure for history-dependent randomized policies. The transformed model is constrained by its full transition formula, so the reduction cannot use an unrelated second process.
-- source:
--   Arapostathis et al., Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), pp. 284–288, 299, 304, §2.1–§2.4, (5.1), proof of Theorem 5.6; https://doi.org/10.1137/0331018

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ArapostathisAC.RossReduction

/-- The countable-state controlled Markov process of §5, with the standing
compactness, continuity, measurability, and nonnegative-cost assumptions. -/
structure CMP (A : Type*) [MetricSpace A] [MeasurableSpace A] [BorelSpace A] where
  U : ℕ → Set A
  U_nonempty : ∀ i, (U i).Nonempty
  U_compact : ∀ i, IsCompact (U i)
  c : ℕ → A → ℝ
  c_meas : Measurable (fun p : ℕ × A => c p.1 p.2)
  c_nonneg : ∀ i, ∀ a ∈ U i, 0 ≤ c i a
  P : Kernel (ℕ × A) ℕ
  [isMarkov : IsMarkovKernel P]
  c_cont : ∀ i, ContinuousOn (c i) (U i)
  P_cont : ∀ i j, ContinuousOn (fun a => (P (i, a) {j}).toReal) (U i)

attribute [instance] CMP.isMarkov

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

/-- The transition probability `P(j | i,a)`. -/
noncomputable def prob (M : CMP A) (i : ℕ) (a : A) (j : ℕ) : ℝ :=
  (M.P (i, a) {j}).toReal

/-- A randomized, history-dependent admissible policy. -/
structure Policy (M : CMP A) where
  rule : (t : ℕ) → Kernel ((Fin t → ℕ × A) × ℕ) A
  [isMarkov : ∀ t, IsMarkovKernel (rule t)]
  adm : ∀ t hist, rule t hist (M.U hist.2)ᶜ = 0

attribute [instance] Policy.isMarkov

/-- A stationary deterministic admissible policy. -/
def StationaryPolicy (M : CMP A) := {f : ℕ → A // ∀ i, f i ∈ M.U i}

/-- View a stationary policy as a general admissible policy. -/
noncomputable def StationaryPolicy.toPolicy {M : CMP A} (f : StationaryPolicy M) : Policy M where
  rule _ := Kernel.deterministic (fun h => f.1 h.2)
    ((measurable_of_countable f.1).comp measurable_snd)
  adm := by
    intro t hist
    simp [Kernel.deterministic_apply, f.2 hist.2]

omit [MetricSpace A] [BorelSpace A] in
private lemma measurable_histFin (t : ℕ) : Measurable (ArapostathisAC.VanishingDiscount.histFin (A := A) t) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

/-- The controlled transition from one state-action pair to the next. -/
noncomputable def stepKernel (M : CMP A) (π : Policy M) (t : ℕ) :
    Kernel (Π _ : Finset.Iic t, ℕ × A) (ℕ × A) :=
  (M.P.comap (ArapostathisAC.VanishingDiscount.lastPair t) (measurable_pi_apply _)) ⊗ₖ
    ((π.rule (t + 1)).comap (fun p => (ArapostathisAC.VanishingDiscount.histFin t p.1, p.2))
      (((measurable_histFin t).comp measurable_fst).prodMk measurable_snd))

instance (M : CMP A) (π : Policy M) (t : ℕ) : IsMarkovKernel (stepKernel M π t) := by
  have h1 : IsMarkovKernel (M.P.comap (ArapostathisAC.VanishingDiscount.lastPair (A := A) t) (measurable_pi_apply _)) :=
    Kernel.IsMarkovKernel.comap _ _
  have h2 : IsMarkovKernel ((π.rule (t + 1)).comap (fun p :
      (Π _ : Finset.Iic t, ℕ × A) × ℕ => (ArapostathisAC.VanishingDiscount.histFin t p.1, p.2))
      (((measurable_histFin t).comp measurable_fst).prodMk measurable_snd)) :=
    Kernel.IsMarkovKernel.comap _ _
  exact Kernel.IsMarkovKernel.compProd _ _

/-- Initial state `i`, followed by the action drawn from `π₀`. -/
noncomputable def initMeasure {M : CMP A} (π : Policy M) (i : ℕ) : Measure (ℕ × A) :=
  ((π.rule 0) (fun j => j.elim0, i)).map (fun a => (i, a))

/-- The strategic path measure under an admissible policy. -/
noncomputable def pathMeasure (M : CMP A) (π : Policy M) (i : ℕ) :
    Measure (ℕ → ℕ × A) :=
  Kernel.trajMeasure (X := fun _ => ℕ × A) (initMeasure π i) (stepKernel M π)

/-- Expected cumulative nonnegative cost over `N` stages. -/
noncomputable def costN (M : CMP A) (π : Policy M) (N i : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, (∑ t ∈ Finset.range N, ENNReal.ofReal (M.c (ω t).1 (ω t).2))
    ∂(pathMeasure M π i)

/-- Expected infinite-horizon discounted nonnegative cost. -/
noncomputable def discCost (M : CMP A) (π : Policy M) (β : ℝ) (i : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, (∑' t : ℕ, ENNReal.ofReal (β ^ t * M.c (ω t).1 (ω t).2))
    ∂(pathMeasure M π i)

/-- Limiting upper average expected cost. -/
noncomputable def avgCost (M : CMP A) (π : Policy M) (i : ℕ) : ℝ≥0∞ :=
  limsup (fun N : ℕ => (N : ℝ≥0∞)⁻¹ * costN M π N i) atTop

/-- Discounted value over all history-dependent randomized policies. -/
noncomputable def discValue (M : CMP A) (β : ℝ) (i : ℕ) : ℝ≥0∞ :=
  ⨅ π : Policy M, discCost M π β i

/-- Optimal average cost over all history-dependent randomized policies. -/
noncomputable def optAvg (M : CMP A) (i : ℕ) : ℝ≥0∞ :=
  ⨅ π : Policy M, avgCost M π i

/-- The average cost optimality equation, including attained minima and
summability of the real expectations. -/
def ACOE (M : CMP A) (ρ : ℝ) (h : ℕ → ℝ) : Prop :=
  ∀ i, (∀ a ∈ M.U i, Summable (fun j => prob M i a j * h j)) ∧
    (∃ a ∈ M.U i, ρ + h i = M.c i a + ∑' j, prob M i a j * h j) ∧
    (∀ a ∈ M.U i, ρ + h i ≤ M.c i a + ∑' j, prob M i a j * h j)

/-- `M'` is the transformed process of the proof of Theorem 5.6.
The equations are required only for admissible state-action pairs. -/
def ModifiedLaw (M M' : CMP A) (α : ℝ) : Prop :=
  M'.U = M.U ∧
  (∀ i a, a ∈ M.U i → M'.c i a = M.c i a) ∧
  ∀ i a, a ∈ M.U i → ∀ j,
    prob M' i a j = (prob M i a j - if j = 0 then α else 0) / (1 - α)

/-- A stationary policy attains the discounted value in every state. -/
def DiscountOptimal (M : CMP A) (β : ℝ) (f : StationaryPolicy M) : Prop :=
  ∀ i, discCost M f.toPolicy β i = discValue M β i

/-- A statewise action map is admissible and discount optimal. This form
allows the same map to be used for the original and transformed processes. -/
def DiscountOptimalFor (M : CMP A) (β : ℝ) (f : ℕ → A) : Prop :=
  ∃ hf : ∀ i, f i ∈ M.U i, DiscountOptimal M β ⟨f, hf⟩

/-- A statewise action map is admissible and average-cost optimal. -/
def AverageOptimalFor (M : CMP A) (f : ℕ → A) : Prop :=
  ∃ hf : ∀ i, f i ∈ M.U i,
    ∀ i, avgCost M (StationaryPolicy.toPolicy ⟨f, hf⟩) i = optAvg M i

end ArapostathisAC.RossReduction


