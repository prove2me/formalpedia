-- Prove2me | Definitions.Def_OverlapRouting_costAO
-- name    : OverlapRouting_costAO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:34:54.657823+00:00
-- url     : https://prove2.me/theorems/90838bd0-b27f-4299-8b51-615ded42ecd9
-- title:
--   Algorithm 1 (recourse under adjacent overlapping) and the daily AO travel cost
-- statement:
--   There are $M$ vehicles and $N=N'M$ customers, labelled along a tour. Vehicle $j$ ($1\le j\le M$) has the **primary route** $\mathcal N_j=[(j-1)N'+1,\dots,jN']$ and, under **adjacent overlapping**, the **extended route** $\mathcal E_j=\mathcal N_j\cup\mathcal N_{j+1}$ for $j<M$, $\mathcal E_M=\mathcal N_M$. Each vehicle has capacity $Q$.
--
--   For a demand vector $d$, write $\bar d_j=\sum_{i\in\mathcal N_j}d_i$. Algorithm 1 sets $e_0=0$ and, for $j=1,\dots,M$,
--   $$w_j=(\bar d_j-e_{j-1})^+,\qquad r_j=\lceil w_j/Q\rceil,\qquad e_j=Qr_j-w_j,\qquad e'_j=\min\{e_j,\bar d_{j+1}\}\ (j<M),\quad e'_M=0 .$$
--   Vehicle $j$ delivers all demand of $\mathcal N_j$ that vehicle $j-1$ did not deliver, then the first $e'_j$ units of the demand of $\mathcal N_{j+1}$ in label order. It leaves the depot $x_0$ full, visits its customers in label order (skipping customers with nothing to deliver), returns to the depot to refill exactly when it has run out, and resumes where it stopped. So its $k$-th trip carries its units $(k-1)Q+1,\dots,kQ$.
--
--   The **daily AO cost** is the total length of the trips of the $M$ vehicles.
--
--   **Formalization Note** Labels are 0-based ($0,\dots,N'M-1$), vehicles 1-based. Instead of the variables $s_j$ and $d'_{s_j}$ of Algorithm 1, the amount vehicle $j$ delivers to label $i\in\mathcal N_{j+1}$ is $\min\big(d_i,(e'_j-\sum_{k\in\mathcal N_{j+1},k<i}d_k)^+\big)$, which is the same split. The trips are `List.toChunks Q` of the vehicle's unit list.
-- source:
--   Ledvina, Qin, Simchi-Levi & Wei, A New Approach for Vehicle Routing with Stochastic Demand: Combining Route Assignment with Process Flexibility, SSRN 3656374 (PDF of 2022-03-11), https://ssrn.com/abstract=3656374, §3, pp.9–11 (primary and extended routes, the three rules of p.10, Algorithm 1, p.11); display (3), p.14; classical recourse, pp.6–7

import Mathlib
import Definitions.Def_OverlapRouting_vrpOpt

namespace OverlapRouting

/-! Algorithm 1, "Recourse Under Adjacent Overlapping" (Ledvina, Qin, Simchi-Levi & Wei, SSRN
3656374 (2022), §3, pp.9–11, and display (3), p.14).

**Formalization Note.** Customers carry 0-based labels `0, …, N′M − 1` (the paper's customer `i`
is label `i − 1`); vehicles carry the paper's 1-based indices `j = 1, …, M`. Demands are a function
`dem : ℕ → ℕ` on labels; only labels `< N′M` are read. -/

/-- The primary route `𝒩ⱼ = [(j − 1)N′ + 1, …, jN′]` (p.9) as 0-based labels
`(j − 1)N′ ≤ i < jN′`. -/
def primaryRoute (N' j : ℕ) : Finset ℕ := Finset.Ico ((j - 1) * N') (j * N')

/-- `d̄ⱼ = ∑_{i ∈ 𝒩ⱼ} dᵢ`, the total demand of the primary route of vehicle `j` (p.14). -/
def groupDemand (N' : ℕ) (dem : ℕ → ℕ) (j : ℕ) : ℕ := ∑ i ∈ primaryRoute N' j, dem i

/-- The excess capacity `eⱼ` of display (3), p.14: `e₀ = 0`, `wⱼ = (d̄ⱼ − eⱼ₋₁)⁺`,
`rⱼ = ⌈wⱼ/Q⌉`, `eⱼ = Q rⱼ − wⱼ`.

**Formalization Note.** Natural-number subtraction is `(·)⁺`, and `w ⌈/⌉ Q = ⌈w/Q⌉` for `Q ≥ 1`. -/
def excess (N' Q : ℕ) (dem : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 =>
    Q * ((groupDemand N' dem (j + 1) - excess N' Q dem j) ⌈/⌉ Q)
      - (groupDemand N' dem (j + 1) - excess N' Q dem j)

/-- The workload `wⱼ = (d̄ⱼ − eⱼ₋₁)⁺` of vehicle `j` (Algorithm 1, lines 1 and 4; display (3)). -/
def workload (N' Q : ℕ) (dem : ℕ → ℕ) (j : ℕ) : ℕ :=
  groupDemand N' dem j - excess N' Q dem (j - 1)

/-- `rⱼ = ⌈wⱼ/Q⌉` of display (3), p.14. -/
def trips (N' Q : ℕ) (dem : ℕ → ℕ) (j : ℕ) : ℕ := workload N' Q dem j ⌈/⌉ Q

/-- `e′ⱼ = min{eⱼ, ∑_{i ∈ 𝒩ⱼ₊₁} dᵢ}` for `j < M` (Algorithm 1, lines 1 and 4), and `e′_M = 0`
since `ℰ_M = 𝒩_M` (p.10). -/
def usedExcess (N' Q M : ℕ) (dem : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j < M then min (excess N' Q dem j) (groupDemand N' dem (j + 1)) else 0

/-- The amount of the demand of label `i ∈ 𝒩ⱼ₊₁` delivered by vehicle `j`: vehicle `j` serves
the first `e′ⱼ` units of the demand of `𝒩ⱼ₊₁` in label order, i.e.
`min(dᵢ, (e′ⱼ − ∑_{k ∈ 𝒩ⱼ₊₁, k < i} d_k)⁺)`; `0` for labels outside `𝒩ⱼ₊₁`.

**Formalization Note.** This prefix-sum form replaces the variables `s_{j+1}` and `d′_{s_{j+1}}` of
Algorithm 1 (lines 2, 5, 9, 11): `s_{j+1}` is the first label of `𝒩ⱼ₊₁` at which vehicle `j` stops
short of the full demand, and vehicle `j + 1` serves the rest there. -/
def overlapAmount (N' Q M : ℕ) (dem : ℕ → ℕ) (j i : ℕ) : ℕ :=
  if i ∈ primaryRoute N' (j + 1) then
    min (dem i) (usedExcess N' Q M dem j - ∑ k ∈ Finset.Ico (j * N') i, dem k)
  else 0

/-- The amount vehicle `j` delivers to label `i` under Algorithm 1: on its primary route `𝒩ⱼ`, all
demand not already served by vehicle `j − 1`; on the additional segment `𝒩ⱼ₊₁` of its extended
route `ℰⱼ`, the amount `overlapAmount` (p.10, rules 2 and 3; Algorithm 1, line 13); `0`
elsewhere. -/
def served (N' Q M : ℕ) (dem : ℕ → ℕ) (j i : ℕ) : ℕ :=
  if i ∈ primaryRoute N' j then dem i - overlapAmount N' Q M dem (j - 1) i
  else overlapAmount N' Q M dem j i

/-- The units vehicle `j` delivers, in the order it delivers them: its served labels in increasing
label order (the order of `ℰⱼ`), each label repeated once per unit delivered there. Labels with
nothing to deliver are skipped (Algorithm 1, line 13). -/
def unitLabels (N' Q M : ℕ) (dem : ℕ → ℕ) (j : ℕ) : List ℕ :=
  (List.range (N' * M)).flatMap fun i => List.replicate (served N' Q M dem j i) i

/-- The trips of vehicle `j`: it leaves the depot full (`Q` units), delivers its units in order,
and returns to the depot to refill exactly when it has run out, then resumes at the point of the
stock-out (p.10, rule 1; the classical recourse, pp.6–7). So its `k`-th trip carries units
`(k − 1)Q + 1, …, kQ` of `unitLabels`.

**Formalization Note.** `List.toChunks Q` splits the unit list into consecutive blocks of `Q`
(the last one possibly shorter). A vehicle with no units makes no trip ("If `wⱼ = 0`, vehicle `j`
is not sent out"). -/
def vehicleTrips (N' Q M : ℕ) (dem : ℕ → ℕ) (j : ℕ) : List (List ℕ) :=
  (unitLabels N' Q M dem j).toChunks Q

/-- Travel distance of vehicle `j` on one day: each trip goes from the depot `x₀` through the
locations `pt i` of its units in order and back to `x₀`. Consecutive units at the same customer
add no distance, and the vehicle drives straight between consecutive served customers. -/
noncomputable def vehicleCost (N' Q M : ℕ) (x₀ : Point) (pt : ℕ → Point) (dem : ℕ → ℕ)
    (j : ℕ) : ℝ :=
  ((vehicleTrips N' Q M dem j).map fun t => walkLength (x₀ :: t.map pt ++ [x₀])).sum

/-- Total travel distance of the `M` vehicles under the adjacent overlapping strategy and
Algorithm 1 on one day, for labelled locations `pt` and labelled demands `dem`. -/
noncomputable def costAO (N' Q M : ℕ) (x₀ : Point) (pt : ℕ → Point) (dem : ℕ → ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 M, vehicleCost N' Q M x₀ pt dem j

end OverlapRouting


