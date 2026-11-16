-- Prove2me | Definitions.Def_BatchedFacilityLocation_Nonuniform_Supplement_LowerBound
-- name    : BatchedFacilityLocation_Nonuniform_Supplement_LowerBound
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T15:43:23.762873+00:00
-- url     : https://prove2.me/theorems/2109a2d9-d4bc-4207-9372-1bd38da7e380
-- title:
--   Deterministic online algorithms with fully revealed batches and their cost (unit opening costs)
-- statement:
--   This file fixes the class of online algorithms for the lower bound of §5.
--
--   All opening costs are one and facilities may be opened at any point of a known finite metric $S$. Batches arrive one at a time and each is revealed in full. A deterministic online algorithm is a rule $A$ that, given the batches revealed so far $L_1,\dots,L_k$ (each a list of client sites, $L_k$ the current one), returns the set $A(L_1,\dots,L_k)$ of facilities it opens while serving the current batch. Openings are irrevocable, so after batch $k$ the open set is
--
--   $$
--   O_k=\bigcup_{i\le k}A(L_1,\dots,L_i).
--   $$
--
--   On the arrival sequence $L_1,\dots,L_B$ its cost is
--
--   $$
--   \mathrm{cost}(A,L)=|O_B|+\sum_{k=1}^{B}\sum_{x\in L_k}d(x,O_k),
--   $$
--
--   with $d(x,\emptyset)=\infty$: every client of batch $k$ is connected to a facility open by the end of its own batch. Any online algorithm that serves each batch before the next arrives, opening the facilities $O_k$, pays at least this, so a lower bound on it holds for every such algorithm, including those that use the whole revealed batch.
--
--   **Formalization Note** A randomized algorithm is, in the theorem, a family $A_\omega$ of such rules indexed by a probability space.
-- source:
--   Fabrizio Grandoni, Stefano Leonardi, Matteo Russo, Metric Facility Location under Batched Random Order, STOC 2027 submission #212 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/212.pdf (source.pdf sha256 2e976c4133df9baa0c32b4cd22b6e370c2c4611dfe4d4dec02ceb01bd7a0dc94), §5 p. 24–25 (unit opening costs, known tree, batches revealed in full), §2 p. 7 (each batch must be served before the next arrives), §1.2 p. 7 (lower bounds allow every use of the fully revealed batch)

import Mathlib
import Definitions.Def_BatchedFacilityLocation_Nonuniform_Batched

open MeasureTheory
open scoped ENNReal

namespace BatchedFacilityLocation.Nonuniform.Supplement

noncomputable section

open Classical

/-! # Online algorithms for the lower bound (§5, p. 24–25)

All opening costs are one and facilities may be opened at any point of the known finite metric
`S`. Each arriving batch is revealed in full. A deterministic online algorithm is a rule
`A : List (List S) → Finset S`: given the batches revealed so far (in arrival order, each a list
of client sites, the last one being the current batch), `A` returns the facilities it opens while
serving the current batch. Decisions are irrevocable, and every client of a batch must be served
before the next batch arrives. -/

variable {S : Type*} [Fintype S] [MetricSpace S]

/-- `O_k`: the facilities open by the end of batch `k` (0-indexed), i.e. `⋃_{i ≤ k} A(L_1, …, L_{i+1})`. -/
def openBy (A : List (List S) → Finset S) (L : List (List S)) (k : ℕ) : Finset S :=
  (Finset.range (k + 1)).biUnion (fun i => A (L.take (i + 1)))

/-- Cost of the deterministic online algorithm `A` on the arrival sequence `L` with unit opening
costs: the number of facilities it opens, plus, for every client `x` of batch `k`, the distance
`d(x, O_k)` to the facilities open by the end of its own batch (`∞` if none is open). This is the
least cost of any irrevocable algorithm with these openings, so a lower bound on it is a lower
bound on every algorithm that sees each batch in full. -/
def detCost (A : List (List S) → Finset S) (L : List (List S)) : ℝ≥0∞ :=
  (((Finset.range L.length).biUnion (fun i => A (L.take (i + 1)))).card : ℝ≥0∞) +
    ∑ k : Fin L.length, ((L.get k).map (fun x => dset x (openBy A L k))).sum

end

end BatchedFacilityLocation.Nonuniform.Supplement


