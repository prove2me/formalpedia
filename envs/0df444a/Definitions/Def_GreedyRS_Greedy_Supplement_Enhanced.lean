-- Prove2me | Definitions.Def_GreedyRS_Greedy_Supplement_Enhanced
-- name    : GreedyRS_Greedy_Supplement_Enhanced
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:29:51.642445+00:00
-- url     : https://prove2.me/theorems/d4d22b90-6e1e-414b-a8ae-8dca91424368
-- title:
--   Procedure 3 — seeded rank groups, fresh observations and EFG+ selection
-- statement:
--   This file adds the enhanced explore-first greedy procedure (EFG+, Procedure 3) to the published normal observation and greedy-selection model. For a deterministic observation array $x_{ij}$, its first $n_{\rm sd}$ entries in each row determine the descending seed order, with smaller alternative indices first on ties. Seed rank is the number of alternatives preceding that row in this order.
--
--   Put $\Delta=2^G-1$. In one-based ranks, group 1 is $1,\ldots,\lfloor k/\Delta\rfloor$; group $r=2,\ldots,G-1$ is $\lfloor k2^{r-2}/\Delta\rfloor+1,\ldots,\lfloor k2^{r-1}/\Delta\rfloor$; group $G$ contains the remaining ranks. Each member of group $r$ receives
--   $$n^r=\left\lfloor\frac{n_0\Delta}{G2^{r-1}}\right\rfloor$$
--   fresh exploration observations. The budget parameter $n_0$ is real; the sample counts are integers. The fresh array is $x^{\rm fresh}_{ij}=x_{i,n_{\rm sd}+j}$ in zero-based observation indices.
--
--   Starting from those unequal fresh counts, each greedy step samples the current leader, using the published running average and smallest-index tie rule. For total integer budget $B$, including seeding, the number of greedy steps is $B-n_{\rm sd}k-\sum_{i<k}n^{r(i)}$, truncated at zero. The selected alternative is the final leader, and
--   $$\mathrm{PCS}^{+}=P\{\text{EFG+ selects alternative }0\}.$$
--
--   This supplies only the additional procedure-specific definitions; the published normal model, running means, crossing expectations, and tail-survival predicate are reused.
--
--   **Formalization Note** Seed observations never appear in later averages. $G\ge2$, $n_0\ge G$ and positive integer $n_{\rm sd}$ are the theorem's domain. The selection map returns 0 for $k<\Delta$, outside the source procedure's finite-problem domain; this affects only finitely many $k$ for fixed $G$. Other malformed arguments are totalized by natural division, floors and truncated subtraction, with no assertion about their statistical behavior.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, pp. 26–27, §5.6; Procedure 3, p. ec10 (PDF 49); post-seeding independence, p. 27

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

set_option autoImplicit false

namespace GreedyRS.Greedy.Supplement

/-- The post-seeding observations, independent of the seed prefix in the normal model (p. 27). -/
def freshTail (nsd : ℕ) (x : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun i j => x i (nsd + j)

/-- Δ = 2^G - 1 in Procedure 3. -/
def groupDenom (G : ℕ) : ℕ := 2 ^ G - 1

open Classical in
/-- Zero-based rank by decreasing seed mean, with smaller alternative indices first on ties. -/
noncomputable def seedRank (k nsd : ℕ) (x : ℕ → ℕ → ℝ) (i : ℕ) : ℕ :=
  ((Finset.range k).filter fun j =>
    runMean x i nsd < runMean x j nsd ∨
      (runMean x j nsd = runMean x i nsd ∧ j < i)).card

/-- Number of ranks through group r, for 1 ≤ r < G. The final group ends at k. -/
def groupCutoff (k G r : ℕ) : ℕ :=
  if r < G then k * 2 ^ (r - 1) / groupDenom G else k

open Classical in
/-- One-based group: cross each cutoff that is at most the zero-based rank.
Thus group 1 ends at floor(k/Δ), groups 2..G-1 have the printed dyadic endpoints,
and group G contains all remaining ranks. -/
noncomputable def seedGroup (k nsd G : ℕ) (x : ℕ → ℕ → ℝ) (i : ℕ) : ℕ :=
  1 + ((Finset.Icc 1 (G - 1)).filter fun r =>
    groupCutoff k G r ≤ seedRank k nsd x i).card

/-- n^r = floor(n0 Δ / (G 2^(r-1))); n0 is a real per-alternative budget. -/
noncomputable def groupLevel (n0 : ℝ) (G r : ℕ) : ℕ :=
  ⌊n0 * (groupDenom G : ℝ) / ((G : ℝ) * (2 : ℝ) ^ (r - 1))⌋₊

/-- Fresh exploration counts, assigned using only the seed prefix. -/
noncomputable def initialSizes (k nsd G : ℕ) (n0 : ℝ) (x : ℕ → ℕ → ℝ) : ℕ → ℕ :=
  fun i => groupLevel n0 G (seedGroup k nsd G x i)

/-- Fresh counts after m single-observation greedy steps, starting from the unequal exploration counts. -/
noncomputable def plusSizes (k nsd G : ℕ) (n0 : ℝ) (x : ℕ → ℕ → ℝ) : ℕ → (ℕ → ℕ)
  | 0 => initialSizes k nsd G n0 x
  | m + 1 =>
    let s := plusSizes k nsd G n0 x m
    let i := leader k (freshTail nsd x) s
    Function.update s i (s i + 1)

/-- Procedure 3 with total budget B including nsd*k seeding observations.
All main-phase averages use freshTail, and unused exploration budget goes to the greedy loop.
Return 0 for k < Δ, outside the procedure's stated domain (irrelevant to k → ∞). -/
noncomputable def plusSelect (k nsd G : ℕ) (n0 : ℝ) (B : ℕ) (x : ℕ → ℕ → ℝ) : ℕ :=
  if groupDenom G ≤ k then
    let initialCost := ∑ i ∈ Finset.range k, initialSizes k nsd G n0 x i
    leader k (freshTail nsd x) (plusSizes k nsd G n0 x (B - nsd * k - initialCost))
  else 0

/-- The unconditional probability of selecting alternative 0, including all seed orderings. -/
noncomputable def plusPCS {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → ℕ → Ω → ℝ) (k nsd G : ℕ) (n0 : ℝ) (B : ℕ) : ℝ≥0∞ :=
  P {ω | plusSelect k nsd G n0 B (fun i j => X i j ω) = 0}

end GreedyRS.Greedy.Supplement


