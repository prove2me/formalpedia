-- Prove2me | Definitions.Def_ChenOutlierPricing_General_Exploration
-- name    : ChenOutlierPricing_General_Exploration
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T06:42:30.974468+00:00
-- url     : https://prove2.me/theorems/d315b85e-102f-4aea-92b1-c5dbd4f8d35e
-- title:
--   Algorithm 4: partial exploration and both price estimates
-- statement:
--   Defines the endpoint-inclusive equally spaced grid, independent uniform arm draws, accumulators of actual censored sales, and the two grid optimizers. The demand estimate is exactly $N_3\widehat d(i)/T_0$, $T_0=\lceil\sqrt T\rceil$, retaining the printed denominator. Both optimizers use the lowest index in a tie. A supplied policy fills periods outside the selected subset using a disjoint private tape, so it cannot reveal future exploration draws. Outputs and contamination counts are computed from the actual trajectory. The module also defines $H_Z$ and both exact bounds in Lemma 5, including $\sqrt2\,N_3$ in the denominator and the full logarithm $\log(2N_3T^2)$. At N=0 or N=1 the grid/output defaults to the lower endpoint, an explicit total completion for Algorithm 5; the literal Lemma 5 formulas are stated only where their grid and sample denominators are defined.
-- source:
--   Chen and Wang, DOI 10.1287/opre.2022.2280, §6.1, supplied source.pdf pp. 30–31, Algorithm 4 and Lemma 5

import Definitions.Def_ChenOutlierPricing_General_Model

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ChenOutlierPricing.General

noncomputable def initialBlock (T : ℕ) : ℕ := ⌈Real.sqrt T⌉₊

/-- Endpoint-inclusive grid. A zero/singleton grid is completed at the lower endpoint. -/
noncomputable def gridPrice (B : PriceBand) (N i : ℕ) : ℝ :=
  if N ≤ 1 then B.lo else B.lo + (B.hi - B.lo) * i / (N - 1 : ℕ)

noncomputable def drawIndex (N : ℕ) (u : ℝ) : ℕ := min (N-1) ⌊N * u⌋₊

/-- Lowest-index tie breaking; an empty grid returns the lower endpoint. -/
noncomputable def leastMin (N : ℕ) (f : ℕ → ℝ) : ℕ :=
  ((List.range N).foldl (fun best i =>
    match best with
    | none => some i
    | some j => if f i < f j then some i else some j) none).getD 0

noncomputable def accumulator (B : PriceBand) (N i : ℕ) (h : History) : ℝ :=
  (h.map (fun o => if o.1 = gridPrice B N i then o.2 else 0)).sum

/-- Algorithm 4, step 9, retaining its printed T₀ denominator. -/
noncomputable def estimateDemand (B : PriceBand) (T N : ℕ) (h : History) (i : ℕ) : ℝ :=
  N * accumulator B N i h / initialBlock T

noncomputable def estimates (B : PriceBand) (T N : ℕ) (x₀ : ℝ) (h : History) : ℝ × ℝ :=
  let d := estimateDemand B T N h
  (gridPrice B N (leastMin N (fun i => |d i - x₀|)),
    gridPrice B N (leastMin N (fun i => -(gridPrice B N i * d i))))

/-- The outside policy has its own tape and cannot inspect future exploration draws. -/
noncomputable def partialPolicy (B : PriceBand) (S : Finset ℕ) (N : ℕ)
    (otherwise : Policy) : Policy := fun T x u h =>
  if h.length ∈ S then gridPrice B N (drawIndex N (u (3*h.length+1)))
  else otherwise T x (fun k => u (3*k+2)) h

/-- Select actual observations at the chosen selling periods. -/
def selectHistory (S : Finset ℕ) (h : History) : History :=
  (h.zipIdx.filter (fun oi => oi.2 ∈ S)).map Prod.fst

noncomputable def explorationOutput {Ξ : Type} (m : Model) (e : Environment Ξ) (otherwise : Policy)
    (T N : ℕ) (S : Finset ℕ) (u : Tape) (v : Ξ) : ℝ × ℝ :=
  estimates m.band T N m.x₀ (selectHistory S
    (observed (trajectory m (partialPolicy m.band S N otherwise) e T (m.x₀*T) u v T)))

noncomputable def corruptCount {Ξ : Type} (m : Model) (π : Policy) (e : Environment Ξ)
    (T : ℕ) (S : Finset ℕ) (u : Tape) (v : Ξ) : ℝ :=
  ∑ n ∈ S, if (roundAt m π e T (m.x₀*T) u v n).outlier then (1 : ℝ) else 0

noncomputable def errorRadius (T N K : ℕ) (Z : ℝ) : ℝ :=
  min 1 Z + Real.sqrt (N * Real.log (2*N*(T : ℝ)^2) / K) +
    2*N*Real.log (2*N*(T : ℝ)^2) / K

noncomputable def clearanceErrorBound (m : Model) (T N K : ℕ) (Z : ℝ) : ℝ :=
  m.LdUpper * (m.LpUpper*(m.band.hi-m.band.lo)/N + 2*errorRadius T N K Z)

noncomputable def optimumErrorBound (m : Model) (T N K : ℕ) (Z : ℝ) : ℝ :=
  2*m.LdUpper/m.sigmaSq *
    (Real.sqrt m.MSq*m.LpUpper*(m.band.hi-m.band.lo)/(Real.sqrt 2*N) +
      Real.sqrt (2*m.band.hi*errorRadius T N K Z))

end ChenOutlierPricing.General


