-- Prove2me | Definitions.Def_MaxPressure_FluidStab_Supplement_Residuals
-- name    : MaxPressure_FluidStab_Supplement_Residuals
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:06:53.147029+00:00
-- url     : https://prove2.me/theorems/94e9453d-6088-42c8-9d49-62b68efcc3b5
-- title:
--   Assumption 3, p. 208; Lemma 6, p. 215 — real power laws and actual residual clocks
-- statement:
--   For each activity $j$, Assumption 3 chooses deterministic constants $\varepsilon_j>0$ and $m'_j>0$ before the almost-sure quantifier, with
--
--   $$\lim_{n\to\infty}\frac1n\sum_{\ell=1}^n \eta_j(\ell)^{1+\varepsilon_j}=m'_j.$$
--
--   The exponent is real and may depend on the activity. The separate processing law is (3), without any routing or probability hypothesis.
--
--   A residual clock records cumulative activity processing time $T(t)$, with $0\le T(t)\le t$, and either the index of the actual held episode or an idle marker. For a held episode $n$, its consumed effort lies between the preceding and current partial sums. Its actual residual is
--
--   $$\widehat\eta(t)=\sum_{\ell=1}^{n}\eta(\ell)-T(t),$$
--
--   and the idle residual is zero. This is the unfinished requirement at activity time $T(t)$, rather than a replacement by a whole next service duration. A history-clock extractor records the actual open episode of a physical history. Initial residuals are covered by the delayed primitive convention in the histories module.
--
--   This interface supports the deterministic residual limit of Lemma 6 and the moment assumption of Theorem 9. No positive busy fraction, independence, uniform exponent or almost-sure restriction is imposed on the deterministic lemma.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), Assumption 3, p. 208; Lemma 6, p. 215 — real power laws and actual residual clocks

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Supplement_Histories

namespace MaxPressure.FluidStab.Supplement

open MeasureTheory Filter Topology

variable {I J K : ℕ}

/-- The sample-path first-moment law (3) alone; no routing or probability premise. -/
def ProcessingLaw {Ω : Type*} (N : FluidStab.Network I J K)
    (P : Throughput.Primitives I J Ω) (ω : Ω) : Prop :=
  ∀ j, Tendsto (fun n : ℕ =>
    BellWilliams2001.ThresholdPolicy.partialSum (fun l => P.eta j l ω) n / n)
    atTop (𝓝 (N.m j))

/-- The activity-dependent real exponents in (29). -/
def PowerLaw {Ω : Type*} (P : Throughput.Primitives I J Ω) (ω : Ω)
    (ε m' : Fin J → ℝ) : Prop :=
  (∀ j, 0 < ε j ∧ 0 < m' j) ∧
  ∀ j, Tendsto (fun n : ℕ =>
    (∑ l ∈ Finset.Icc 1 n, (P.eta j l ω) ^ (1 + ε j)) / n)
    atTop (𝓝 (m' j))

/-- Assumption 3: constants are chosen before the almost-sure quantifier. -/
def Assumption3 {Ω : Type*} [MeasurableSpace Ω]
    (P : Throughput.Primitives I J Ω) (Pr : Measure Ω) : Prop :=
  ∃ ε m' : Fin J → ℝ, (∀ j, 0 < ε j ∧ 0 < m' j) ∧
    ∀ᵐ ω ∂Pr, PowerLaw P ω ε m'

/-- A processing clock and the actual currently held episode. `none` means idle.
The completion opportunity is extended-valued until explicitly known finite;
no conversion of infinity to a natural number is hidden here. -/
structure ResidualClock where
  effort : ℝ → ℝ
  current : ℝ → Option ℕ

/-- Physical progress constraints sufficient to define the residual. This allows
zero busy fractions, frozen jobs, and arbitrary nondecreasing processing clocks. -/
def ResidualClock.Legal (η : ℕ → ℝ) (c : ResidualClock) : Prop :=
  (∀ n, 1 ≤ n → 0 ≤ η n) ∧ c.effort 0 = 0 ∧
  MonotoneOn c.effort (Set.Ici 0) ∧
  (∀ t, 0 ≤ t → 0 ≤ c.effort t ∧ c.effort t ≤ t) ∧
  ∀ t n, 0 ≤ t → c.current t = some n → 1 ≤ n ∧
    BellWilliams2001.ThresholdPolicy.partialSum η (n - 1) ≤ c.effort t ∧
    c.effort t ≤ BellWilliams2001.ThresholdPolicy.partialSum η n

/-- The actual unfinished requirement at activity time T(t), zero when idle.
At an exact completion boundary either adjacent episode gives residual zero or
the requirement of the newly started job, according to the physical history. -/
noncomputable def residual (η : ℕ → ℝ) (c : ResidualClock) (t : ℝ) : ℝ :=
  match c.current t with
  | none => 0
  | some n => BellWilliams2001.ThresholdPolicy.partialSum η n - c.effort t

/-- Extract the actual open job index from a physical history. Uniqueness follows
from positive residual and ordered episodes; zero-duration jobs hold no time. -/
noncomputable def historyClock (h : History I J) (j : Fin J) : ResidualClock where
  effort t := h.T t j
  current t := by
    classical
    exact if hex : ∃ n : ℕ, 1 ≤ n ∧ h.start j n ≤ (t : WithTop ℝ) ∧
      (t : WithTop ℝ) < h.finish j n then some hex.choose else none

end MaxPressure.FluidStab.Supplement


