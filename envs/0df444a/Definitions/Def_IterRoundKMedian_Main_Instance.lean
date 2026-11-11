-- Prove2me | Definitions.Def_IterRoundKMedian_Main_Instance
-- name    : IterRoundKMedian_Main_Instance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:25:32.325143+00:00
-- url     : https://prove2.me/theorems/c03fe371-6320-4687-bcea-7f6bc3617a64
-- title:
--   Metric k-median instances over the rationals, their bit encoding, cost and OPT
-- statement:
--   A **metric k-median instance** $I$ consists of $n$ points $\{0,\dots,n-1\}$, a distance $d$ on them with rational values that is a metric (nonnegative, $d(i,j)=0$ exactly when $i=j$, symmetric, triangle inequality), a set $C$ of **clients** and a nonempty set $F$ of **facilities** (arbitrary subsets of the points, possibly overlapping), and an integer budget $k\ge 1$. No relation between $k$ and $|F|$ is assumed.
--
--   For a nonempty set $S$ of points, $d(j,S)=\min_{i\in S} d(j,i)$, and the **cost** of $S$ is
--   $$\mathrm{cost}(S)=\sum_{j\in C} d(j,S).$$
--   The **optimum** is $\mathrm{OPT}(I)=\min\{\mathrm{cost}(S) : S\subseteq F,\ S\ne\emptyset,\ |S|\le k\}$; the feasible family is nonempty because $F\neq\emptyset$ and $k\ge1$.
--
--   The **encoding** $\mathrm{enc}(I)$ is the bit string listing $n$, $k$, the client and facility masks, and the distance matrix row by row, each natural number and rational in the self-delimiting binary codes `encodeNat`, `encodeRat` of the published `KMedianThreshold` definition.
--
--   **Formalization Note.** Points are `Fin n`; `distance : Fin n → Fin n → ℚ`; `distToSet` returns $0$ on the empty set, a value never used (feasible outputs are nonempty). The structure mirrors `OAI.MetricKMedian.Instance` without its field `k ≤ facilities.card` and with `facilities.Nonempty`.
-- source:
--   Byrka, Guo, Hu, Li, Shin, Vajanopath, Wan, Wang, Iterative Randomized Rounding for k-Median in General and Euclidean Metrics, STOC 2027 submission (manuscript sha256 02f6267b…), p. 3, §1 (problem definition)

import Mathlib
import Definitions.Def_KMedianThreshold

namespace IterRoundKMedian.Main

/-- A metric k-median instance: `n` points `Fin n` with a rational metric `distance`
(nonnegative, zero exactly on the diagonal, symmetric, triangle inequality), a set of
clients and a nonempty set of facilities (both arbitrary subsets of the points, possibly
overlapping), and a budget `k ≥ 1`. There is no condition `k ≤ |facilities|`. -/
structure Instance where
  n : ℕ
  distance : Fin n → Fin n → ℚ
  clients : Finset (Fin n)
  facilities : Finset (Fin n)
  k : ℕ
  distance_nonneg : ∀ i j, 0 ≤ distance i j
  distance_eq_zero : ∀ i j, distance i j = 0 ↔ i = j
  distance_symm : ∀ i j, distance i j = distance j i
  distance_triangle : ∀ i j h, distance i h ≤ distance i j + distance j h
  k_pos : 1 ≤ k
  facilities_nonempty : facilities.Nonempty

/-- Bit encoding of an instance: `n`, `k`, the client and facility masks, and the
`n × n` distance matrix row by row, every rational in the self-delimiting binary code
`OAI.MetricKMedian.encodeRat`. -/
def encodeInstance (I : Instance) : List Bool :=
  OAI.MetricKMedian.encodeNat I.n ++ OAI.MetricKMedian.encodeNat I.k ++
    List.ofFn (fun i : Fin I.n => decide (i ∈ I.clients)) ++
    List.ofFn (fun i : Fin I.n => decide (i ∈ I.facilities)) ++
    (List.ofFn (fun i : Fin I.n =>
      (List.ofFn (fun j : Fin I.n => OAI.MetricKMedian.encodeRat (I.distance i j))).flatten)).flatten

/-- `d(j, S) = min_{i ∈ S} d(j, i)` for a nonempty set `S` (value `0` on the empty set,
which is never used: feasible outputs are nonempty). -/
noncomputable def distToSet (I : Instance) (j : Fin I.n) (S : Finset (Fin I.n)) : ℝ :=
  if h : S.Nonempty then
    (S.image (fun i => (I.distance j i : ℝ))).min' (h.image _)
  else 0

/-- `cost(S) = Σ_{j ∈ C} d(j, S)`. -/
noncomputable def cost (I : Instance) (S : Finset (Fin I.n)) : ℝ :=
  ∑ j ∈ I.clients, distToSet I j S

/-- Feasible solutions: nonempty sets of at most `k` facilities. -/
def feasibleSets (I : Instance) : Finset (Finset (Fin I.n)) :=
  I.facilities.powerset.filter (fun S => S.Nonempty ∧ S.card ≤ I.k)

/-- `OPT`: the minimum cost over nonempty facility sets of size at most `k`. The set of
feasible solutions is nonempty for every instance (`F ≠ ∅`, `k ≥ 1`), so the fallback
value `0` is never taken. -/
noncomputable def optimum (I : Instance) : ℝ :=
  if h : (feasibleSets I).Nonempty then
    ((feasibleSets I).image (cost I)).min' (h.image _)
  else 0

end IterRoundKMedian.Main


