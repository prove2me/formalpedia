-- Prove2me | Definitions.Def_LearnVsOpt_Supplement_Play
-- name    : LearnVsOpt_Supplement_Play
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:20:25.403228+00:00
-- url     : https://prove2.me/theorems/b25cddf3-1cf5-4c3a-a47a-ba91a3d092ab
-- title:
--   The law of play of Algorithm 1 with an arbitrary forecaster against an adaptive optimizer
-- statement:
--   The probability law of $t$ rounds of **Algorithm 1 (Forecast-Based Best-Response)** with an arbitrary forecaster against an arbitrary adaptive optimizer.
--
--   A round's record is $(i_t,f^{(t)},j_t)$. Given the history $h$ of the previous rounds, round $t$ is **active** when the historical spending $\sum_{r<t}C_L[i_r,j_r]$ is at most $t\rho_L-1$. Then:
--
--   1. the optimizer draws $i_t\sim\sigma_t(h)$, where $\sigma_t$ is any Markov kernel from histories to $[n_O]$;
--   2. independently given $h$, in an active round the forecaster draws $f^{(t)}\sim F_t(h)$, where $F_t$ is any Markov kernel from histories to forecasts, and the learner samples $j_t\sim\eta(f^{(t)})$, where $\eta$ is the sampler of $y(f)$; in a non-active round the learner plays the null action $j_0$, and the record holds the placeholder forecast $0$.
--
--   The law of $t+1$ rounds is the law of $t$ rounds composed with this round kernel, with the new record appended. Read from a history are: the entries $M[i_t,j_t]$; the realized vectors $uc_t=(U_L[i_t,:],C_L[i_t,:])$; the forecast distribution of round $t$; whether round $t$ is active; and the Lagrangian-calibration error
--   $$L_t=\sum_{t'\le t,\ t'\in\mathcal T}\mathbb E_{f\sim F_{t'}}\big[\delta^L(f,k_{t'})\big].$$
--
--   This is the probability space of Theorem 5.2.
--
--   **Formalization Note** Kernels make every step measurable, so the law is a probability measure; the verification file proves this. The optimizer's and the forecaster's draws in a round are independent given the past (the moves are simultaneous).
-- source:
--   Fikioris, Sivan & Tardos, Learning vs. Optimizing Players in Budgeted Games, arXiv:2611.05580, Algorithm 1 p.7; L_t p.12; Theorem 5.2 p.14

import Mathlib
import Definitions.Def_LearnVsOpt_Supplement_Forecaster

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace LearnVsOpt.Supplement

variable {nO nL : ℕ}

/-- The record of one round of Algorithm 1 (Fikioris, Sivan & Tardos, arXiv:2611.05580, p.7): the
optimizer's action `i_t`, the forecast `f^(t)` (the placeholder `0` in a non-active round) and the
learner's action `j_t`. -/
abbrev Rec (nO nL : ℕ) : Type := Fin nO × Forecast × Fin nL

/-- A history of `t` rounds; round `r + 1` is at position `r`. -/
abbrev Hist (nO nL t : ℕ) : Type := Fin t → Rec nO nL

/-- The learner's historical spending `Σ_r C_L[i_r, j_r]` over a history. -/
def spent (G : Game nO nL) {t : ℕ} (h : Hist nO nL t) : ℝ :=
  ∑ r, G.CL (h r).1 (h r).2.2

/-- The histories of `t` rounds after which round `t + 1` is **active** (Algorithm 1, p.7): the round
is non-active when the historical spending exceeds `(t + 1)ρ_L − 1`. -/
def activeSet (G : Game nO nL) (ρL : ℝ) (t : ℕ) : Set (Hist nO nL t) :=
  {h | spent G h ≤ ((t : ℝ) + 1) * ρL - 1}

/-- The active set is measurable (structural lemma, needed to branch a kernel on it). -/
theorem measurableSet_activeSet (G : Game nO nL) (ρL : ℝ) (t : ℕ) :
    MeasurableSet (activeSet G ρL t) := by
  refine measurableSet_le ?_ measurable_const
  refine Finset.measurable_sum _ fun r _ => ?_
  have h1 : Measurable fun h : Hist nO nL t => ((h r).1, (h r).2.2) :=
    ((measurable_fst.comp (measurable_pi_apply r)).prodMk
      (measurable_snd.comp (measurable_snd.comp (measurable_pi_apply r))))
  exact (measurable_of_countable (fun p : Fin nO × Fin nL => G.CL p.1 p.2)).comp h1

open Classical in
/-- **One round of Algorithm 1 with an arbitrary forecaster** (p.7), as a kernel from the history of
the first `t` rounds to the record of round `t + 1`. The optimizer draws `i ∼ σ(h)`; independently, if
the round is active the forecaster draws `f ∼ F(h)` and the learner samples `j ∼ η(f)` (that is,
`j ∼ y(f)`), and otherwise the learner plays the null action `j₀`.

**Formalization Note.** The optimizer's and the learner's draws are independent given the history (the
moves are simultaneous, p.3); the optimizer does not see the current `f^(t)` or `j_t`. -/
noncomputable def roundKernel (G : Game nO nL) (ρL : ℝ) (j₀ : Fin nL) (t : ℕ)
    (σ : Kernel (Hist nO nL t) (Fin nO)) (F : Kernel (Hist nO nL t) Forecast)
    (η : Kernel Forecast (Fin nL)) : Kernel (Hist nO nL t) (Rec nO nL) :=
  σ ×ₖ Kernel.piecewise (measurableSet_activeSet G ρL t)
    (F ⊗ₖ Kernel.prodMkLeft (Hist nO nL t) η)
    (Kernel.const (Hist nO nL t) (Measure.dirac ((0 : Forecast), j₀)))

/-- **The law of play** of the first `t` rounds of Algorithm 1 with forecaster `F`, response sampler
`η` and adaptive optimizer `σ` (p.7; Theorem 5.2, p.14): built round by round, appending each new
record to the history. -/
noncomputable def playLaw (G : Game nO nL) (ρL : ℝ) (j₀ : Fin nL)
    (σ : (t : ℕ) → Kernel (Hist nO nL t) (Fin nO)) (F : (t : ℕ) → Kernel (Hist nO nL t) Forecast)
    (η : Kernel Forecast (Fin nL)) : (t : ℕ) → Measure (Hist nO nL t)
  | 0 => Measure.dirac (fun r => r.elim0)
  | t + 1 => ((playLaw G ρL j₀ σ F η t) ⊗ₘ roundKernel G ρL j₀ t (σ t) (F t) η).map
      (fun p => Fin.snoc (α := fun _ => Rec nO nL) p.1 p.2)

/-- The prefix of the first `n ≤ T` rounds of a history of `T` rounds. -/
def prefixH {T : ℕ} (h : Hist nO nL T) (n : ℕ) (hn : n ≤ T) : Hist nO nL n :=
  fun r => h (Fin.castLE hn r)

/-- Round `t ∈ [T]` of the history `h` is active. -/
def IsActiveRound (G : Game nO nL) (ρL : ℝ) {T : ℕ} (h : Hist nO nL T) (t : ℕ) : Prop :=
  ∃ ht : 1 ≤ t ∧ t ≤ T, prefixH h (t - 1) (by omega) ∈ activeSet G ρL (t - 1)

/-- The entry `M[i_t, j_t]` of round `t ∈ [T]` (`0` outside `[T]`). -/
def entry {T : ℕ} (h : Hist nO nL T) (M : Matrix (Fin nO) (Fin nL) ℝ) (t : ℕ) : ℝ :=
  if ht : 1 ≤ t ∧ t ≤ T then M (h ⟨t - 1, by omega⟩).1 (h ⟨t - 1, by omega⟩).2.2 else 0

/-- The realized utility-cost vector `uc_t = (U_L[i_t, :], C_L[i_t, :])` of round `t ∈ [T]`. -/
def roundUC (G : Game nO nL) {T : ℕ} (h : Hist nO nL T) (t : ℕ) : UC nL :=
  if ht : 1 ≤ t ∧ t ≤ T then (G.UL (h ⟨t - 1, by omega⟩).1, G.CL (h ⟨t - 1, by omega⟩).1) else 0

/-- The forecast distribution `F_t` the forecaster used in round `t ∈ [T]`, as a function of the
history before round `t`. -/
noncomputable def roundF (F : (t : ℕ) → Kernel (Hist nO nL t) Forecast) {T : ℕ}
    (h : Hist nO nL T) (t : ℕ) : Measure Forecast :=
  if ht : 1 ≤ t ∧ t ≤ T then F (t - 1) (prefixH h (t - 1) (by omega)) else 0

open Classical in
/-- **The Lagrangian-calibration error** `L_t = Σ_{t' ≤ t, t' ∈ 𝒯} E_{f∼F_{t'}}[δ^L(f, k_{t'})]`
(p.12, after (10)), along the history `h`; only its components `L^u, L^c, L^{uy}, L^{cy}` are read
(through `JointVec.normL`). -/
noncomputable def Lvec (G : Game nO nL) (ρL : ℝ) (sel : Selector nL) (D : List (UC nL))
    (F : (t : ℕ) → Kernel (Hist nO nL t) Forecast) {T : ℕ} (h : Hist nO nL T) (t : ℕ) :
    JointVec nL :=
  sumJ ((Finset.Icc 1 t).filter (IsActiveRound G ρL h))
    fun t' => expDelta ρL sel D (roundF F h t') (roundUC G h t')

end LearnVsOpt.Supplement


