-- Prove2me | Definitions.Def_ChenOutlierPricing_General_MetaPolicy
-- name    : ChenOutlierPricing_General_MetaPolicy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T06:43:33.673906+00:00
-- url     : https://prove2.me/theorems/18a064e9-3b59-41af-9e40-97499d011626
-- title:
--   Algorithm 5: randomized epochs and shared physical inventory
-- statement:
--   Defines epoch lengths $2^\zeta T_0$, horizon-truncated epoch sets, private Bernoulli exploration assignments of probability $1/\sqrt{T(\zeta)}$, and $N_3=\lceil\sqrt{|G|}\rceil$. The whole private schedule is sampled in advance, as step 5 permits, so its cardinality is available for the grid; no schedule is given directly to the adversary. The previous epoch's actual exploration observations supply the next two estimates. Their ordering selects the source branch, with midpoint lower-price input for $\pi^o$. Each subroutine gets its nominal epoch horizon, nominal allocation $x_0T(\zeta)$, a fresh independent tape, and only its exploitation history. The nominal allocation is checked between selling periods; once exhausted, subsequent exploitation periods offer the upper price. A sale is censored by physical stock as in equation (2); the footnote is read as a rule for subsequent prices rather than an additional within-period censor. Global physical inventory is never replenished; all sales are censored by the common actual stock. The first estimates are the two endpoints, and no correctness of a branch is assumed. Empty/singleton exploration uses the declared Algorithm 4 completion. A zero horizon is given a total unused value; all targets use positive horizons.
-- source:
--   Chen and Wang, DOI 10.1287/opre.2022.2280, §6.2, supplied source.pdf pp. 31–32, Algorithm 5 and its footnote

import Definitions.Def_ChenOutlierPricing_General_Exploration

open scoped BigOperators

namespace ChenOutlierPricing.General

/-- Epoch z=0 is the paper's ζ=1. -/
noncomputable def epochLength (T z : ℕ) : ℕ := 2^(z+1) * initialBlock T
noncomputable def epochStart (T z : ℕ) : ℕ := 2 * initialBlock T * (2^z-1)
noncomputable def epochPeriods (T z : ℕ) : Finset ℕ :=
  Finset.Ico (epochStart T z) (min T (epochStart T z + epochLength T z))

noncomputable def epochAt (T t : ℕ) : ℕ :=
  ((List.range (t+2)).find? (fun z => t < epochStart T z + epochLength T z)).getD 0

/-- Bernoulli flags are sampled on private tape coordinates. The epoch's grid
uses the cardinality of the complete privately selected, horizon-truncated set. -/
noncomputable def explorationSet (T z : ℕ) (u : Tape) : Finset ℕ :=
  (epochPeriods T z).filter (fun t => u (3*t) < 1 / Real.sqrt (epochLength T z))

noncomputable def epochGrid (T z : ℕ) (u : Tape) : ℕ :=
  ⌈Real.sqrt (explorationSet T z u).card⌉₊

def epochTape (z : ℕ) (u : Tape) : Tape := fun k => u (3*Nat.pair z k+2)

/-- Algorithm 5 as an operational policy. It computes estimates only from the
previous epoch, uses actual censored observations, and never resets physical stock. -/
noncomputable def metaPolicy (B : PriceBand) (πo : ℝ → Policy) (πc : Policy) : Policy :=
  fun T x u h =>
    let x₀ := x / T
    let t := h.length
    let z := epochAt T t
    let G := explorationSet T z u
    let N := epochGrid T z u
    let prev := if z = 0 then (B.lo, B.hi) else
      estimates B T (epochGrid T (z-1) u) x₀
        (selectHistory (explorationSet T (z-1) u) h)
    let exploitation := selectHistory (epochPeriods T z \ G) h
    let allocation := x₀ * epochLength T z
    if x ≤ (h.map Prod.snd).sum then B.hi
    else if t ∈ G then gridPrice B N (drawIndex N (u (3*t+1)))
    else if allocation ≤ (exploitation.map Prod.snd).sum then B.hi
    else if prev.1 < prev.2 then
      πo ((prev.1+prev.2)/2) (epochLength T z) allocation (epochTape z u) exploitation
    else πc (epochLength T z) allocation (epochTape z u) exploitation

end ChenOutlierPricing.General


