-- Prove2me | Definitions.Def_ChenGallegoPricing_ABE_Algorithm
-- name    : ChenGallegoPricing_ABE_Algorithm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:33:05.095019+00:00
-- url     : https://prove2.me/theorems/b0a19afd-7249-4c4a-8771-387725fdeaf0
-- title:
--   Operational ABE policy with every measurable split-price completion
-- statement:
--   The ABE state consists of a finite active partition and, for every cell, its visit count, interval endpoints, per-price counts and averages. Initially only the root is active, its interval is $[0,1]$, and all counters and averages are zero. Histories record covariates, charged prices and realized revenues. Replaying their prefixes reconstructs the state without access to the unknown demand or the true optimizer.
--
--   Use the exact tuning of §3.4:
--   $$K=\left\lfloor\frac{\log T}{(d+4)\log2}\right\rfloor,\quad \Delta_k=2^{-k}\log T,\quad N_k=\lceil\log T\rceil,$$
--   $$n_k=\max\left\{0,\left\lceil\frac{2^{4k+15}}{M_2^2\log^3T}\bigl(\log T+\log\log T-(d+2)k\log2\bigr)\right\rceil\right\}.$$
--   On arrival in an active level-$k$ cell, increment its visit count. If $k<K$ and the new count is strictly less than $n_k$, charge grid index $(N(B)-1)\bmod N_k$, with spacing $(u-l)/(N_k-1)$. Update that index's average to $(N_j\bar Y_j+Z)/(N_j+1)$ and increment its sample count. If $k<K$ and the new count is at least $n_k$, choose any maximizing stored average, split once, and initialize each child with zero statistics and interval $[\max(0,p^*-\Delta_{k+1}/2),\min(1,p^*+\Delta_{k+1}/2)]$. Other active cells are unchanged. Terminal cells repeatedly charge their interval midpoint and do not update empirical statistics.
--
--   Admissibility requires measurable tie and omitted-price choices, and a measurable resulting policy on each finite history space. Tie choices must maximize the stored averages at each splitting state. All such choices are allowed; there is no concentration or regret condition. At $n_k=0$ the first visit splits with no exploration samples; if $n_k\ge1$, only $n_k-1$ visits precede the split. The denominator $N_k-1$ is nonzero whenever the grid is active for a positive-dimensional admissible horizon.
--
--   Differences from the source:
--   - reading: Algorithm 1 lines 15–22 assign no price on a splitting round → every measurable history/current-covariate-based price in [0,1] is allowed there, its usual feedback is observed but discarded from bin statistics, and exactly one split consumes the round; reason: retain every completion of the printed transition relation rather than selecting a favorable omitted action
--   - encoding: grids and thresholds are displayed even for terminal bins → only active exploration or splitting branches evaluate them; terminal bins charge their midpoint, including T=1 and T=2; reason: inactive singular metadata have no effect on any action or observation
--   - encoding: dyadic bins store grid spacing and empirical statistics → cells have level/integer-coordinate addresses, spacing is computed from endpoints, and histories are replayed to reconstruct the state; clipping to [0,1] only totalizes off-domain metadata; reason: reachable valid states have a unique active cell, in-range grid prices and the same counters, means and decisions
--   - reading: the ceiling glyph in §3.4 and the conflicting verbal ceiling description in the p. 26 notation table → the conventional ceiling, the smallest integer not less than its argument; reason: the formula glyph is unambiguous and the table’s smallest integer not exceeding x does not exist; insight I5 records the typo
-- source:
--   Chen and Gallego, Nonparametric Pricing Analytics with Customer Covariates, arXiv:1805.01136v3 (16 February 2020), https://arxiv.org/abs/1805.01136v3; Algorithm 1 and §3.4, printed/PDF pp. 14–16

import Mathlib
import Definitions.Def_ChenGallegoPricing_ABE_Geometry

open MeasureTheory

namespace ChenGallegoPricing.ABE

abbrev Observation (d : ℕ) := Ctx d × Price × ℝ
abbrev History (d : ℕ) := List (Observation d)
abbrev Policy (d : ℕ) := History d → Ctx d → Price
abbrev TieRule (d : ℕ) := History d → Ctx d → ℕ

noncomputable def maxLevel (d T : ℕ) : ℕ :=
  ⌊Real.log T / (((d : ℝ) + 4) * Real.log 2)⌋₊
noncomputable def width (T k : ℕ) : ℝ := (2 : ℝ) ^ (-(k : ℤ)) * Real.log T
noncomputable def gridCount (T : ℕ) : ℕ := ⌈Real.log T⌉₊
noncomputable def threshold (d T : ℕ) (M₂ : ℝ) (k : ℕ) : ℕ :=
  (max (0 : ℤ) ⌈(2 : ℝ) ^ (4 * k + 15) / (M₂ ^ 2 * (Real.log T) ^ 3) *
    (Real.log T + Real.log (Real.log T) - ((d : ℝ) + 2) * k * Real.log 2)⌉).toNat

structure BinData where
  visits : ℕ
  lower : ℝ
  upper : ℝ
  count : ℕ → ℕ
  average : ℕ → ℝ

structure State (d : ℕ) where
  active : Finset (Cell d)
  data : Cell d → BinData

noncomputable def initial (d : ℕ) : State d :=
  ⟨{root d}, fun _ => ⟨0, 0, 1, fun _ => 0, fun _ => 0⟩⟩

/-- Only active exploration branches evaluate a grid spacing. -/
noncomputable def gridPrice (T : ℕ) (b : BinData) (j : ℕ) : ℝ :=
  b.lower + j * ((b.upper - b.lower) / ((gridCount T : ℝ) - 1))

noncomputable def locate {d : ℕ} (s : State d) (x : Ctx d) : Cell d := by
  classical
  exact if h : ∃ b ∈ s.active, x ∈ cellSet b then h.choose else root d

/-- The fallback merely totalizes invalid histories/selections; it is the identity on [0,1]. -/
noncomputable def asPrice (r : ℝ) : Price :=
  ⟨max 0 (min 1 r), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

noncomputable def quote {d : ℕ} (T : ℕ) (M₂ : ℝ) (completion : Policy d)
    (h : History d) (x : Ctx d) (s : State d) : Price :=
  let b := locate s x
  let a := s.data b
  if b.1 < maxLevel d T then
    if a.visits + 1 < threshold d T M₂ b.1 then
      asPrice (gridPrice T a (a.visits % gridCount T))
    else completion h x
  else asPrice ((a.lower + a.upper) / 2)

/-- One printed iteration. A split consumes a round and discards its feedback. -/
noncomputable def update {d : ℕ} (T : ℕ) (M₂ : ℝ) (tie : TieRule d)
    (h : History d) (x : Ctx d) (z : ℝ) (s : State d) : State d := by
  classical
  let b := locate s x
  let a := s.data b
  let bumped := { a with visits := a.visits + 1 }
  exact if b.1 < maxLevel d T then
    if a.visits + 1 < threshold d T M₂ b.1 then
      let j := a.visits % gridCount T
      let a' := { bumped with
        count := Function.update a.count j (a.count j + 1)
        average := Function.update a.average j
          (((a.count j : ℝ) * a.average j + z) / ((a.count j : ℝ) + 1)) }
      { s with data := Function.update s.data b a' }
    else
      let center := gridPrice T a (tie h x)
      let fresh : BinData := ⟨0, max 0 (center - width T (b.1 + 1) / 2),
        min 1 (center + width T (b.1 + 1) / 2), fun _ => 0, fun _ => 0⟩
      ⟨(s.active.erase b) ∪ children b,
        fun c => if c ∈ children b then fresh else if c = b then bumped else s.data c⟩
  else { s with data := Function.update s.data b bumped }

/-- Replay the supplied history. The current recorded price does not select the grid index.
Full observation triples, including prices, are retained in the prefixes supplied to `tie`.
Thus tie rules can depend on any previously observed price. -/
noncomputable def stateAfter {d : ℕ} (T : ℕ) (M₂ : ℝ) (tie : TieRule d)
    (h : History d) : State d :=
  (h.foldl (fun acc o =>
    (update T M₂ tie acc.2 o.1 o.2.2 acc.1, acc.2 ++ [(o.1, o.2.1, o.2.2)]))
    (initial d, ([] : History d))).1

/-- Both choices see full observed histories: `tie` during replay and `completion` at quote time. -/
noncomputable def abePolicy {d : ℕ} (T : ℕ) (M₂ : ℝ)
    (tie : TieRule d) (completion : Policy d) : Policy d :=
  fun h x => quote T M₂ completion h x (stateAfter T M₂ tie h)

/-- Every measurable tie choice and every measurable completion of the omitted price. -/
def IsAdmissibleABE {d : ℕ} (T : ℕ) (M₂ : ℝ)
    (tie : TieRule d) (completion : Policy d) : Prop :=
  (∀ n, Measurable (fun hx : (Fin n → Observation d) × Ctx d =>
    tie (List.ofFn hx.1) hx.2)) ∧
  (∀ n, Measurable (fun hx : (Fin n → Observation d) × Ctx d =>
    completion (List.ofFn hx.1) hx.2)) ∧
  (∀ n, Measurable (fun hx : (Fin n → Observation d) × Ctx d =>
    abePolicy T M₂ tie completion (List.ofFn hx.1) hx.2)) ∧
  ∀ h x,
    let s := stateAfter T M₂ tie h
    let b := locate s x
    let a := s.data b
    b.1 < maxLevel d T → threshold d T M₂ b.1 ≤ a.visits + 1 →
    tie h x < gridCount T ∧ ∀ j < gridCount T, a.average j ≤ a.average (tie h x)

end ChenGallegoPricing.ABE


