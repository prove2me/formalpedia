-- Prove2me | Definitions.Def_DetANN_HPIMThreshold
-- name    : DetANN_HPIMThreshold
-- status  : Definition
-- author  : @milia
-- created : 2026-11-16T05:51:12.915793+00:00
-- url     : https://prove2.me/theorems/d1f9cdf2-8c81-4942-ac99-ea92a36d3e06
-- title:
--   The threshold graph of a point set and its median threshold
-- statement:
--   Let $P_1,\dots,P_n\in\mathbb R^m$ and $d\in\mathbb R$. The **threshold graph** at $d$ joins $a\ne b$ when $\|P_a-P_b\|\le d$.
--
--   1. `thrReach P d i j`: $j$ is reachable from $i$ in the threshold graph at $d$.
--   2. The **median threshold** is the least pairwise distance $d$ at which some component has at least $\lfloor n/2\rfloor+1$ points ($0$ if there is none).
--   3. $i$ is a **representative** at $d$ if it is the least index of its component.
--
--   In the tree of Har-Peled, Indyk and Motwani (2012, §2), the median threshold is $2r_{\mathrm{med}}$. There it is approximated by random sampling; here it is defined exactly, and any minimum spanning tree computes it deterministically.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). The search tree follows Har-Peled, Indyk, Motwani, Approximate nearest neighbor: towards removing the curse of dimensionality, Theory of Computing 8 (2012), §2, made deterministic and floor-free.

import Mathlib

/-!
# The threshold graph of a point set and its median threshold

For points `P : Fin n → ℝ^m` and `d ∈ ℝ`, the threshold graph joins `a ≠ b` when `‖P a − P b‖ ≤ d`.
* `thrReach P d i j`: `j` is reachable from `i` in the threshold graph.
* `medThreshold P`: the least pairwise distance `d` at which some component has at least
  `⌊n/2⌋ + 1` points (`0` if there is none). This is the exact `2 r_med` of the HPIM tree, computed
  without randomness (any minimum spanning tree gives it).
* `IsRep P d i`: `i` is the least index of its component (its representative).
-/

namespace DetANN.HPIM

variable {m : ℕ}

/-- Reachability in the threshold graph `{a ~ b : dist ≤ d}`. -/
def thrReach {n : ℕ} (pts : Fin n → EuclideanSpace ℝ (Fin m)) (d : ℝ) (i j : Fin n) : Prop :=
  (SimpleGraph.fromRel fun a b => dist (pts a) (pts b) ≤ d).Reachable i j

/-- The edge threshold `2 r_med`: the least pairwise distance `d` at which the threshold graph has a
component with `≥ ⌊n/2⌋ + 1` points (`0` if none). -/
noncomputable def medThreshold {n : ℕ} (pts : Fin n → EuclideanSpace ℝ (Fin m)) : ℝ := by
  classical
  let cand := ((Finset.univ ×ˢ Finset.univ).image fun ij : Fin n × Fin n => dist (pts ij.1) (pts ij.2)).filter
    fun d => ∃ i, n / 2 + 1 ≤ (Finset.univ.filter (thrReach pts d i)).card
  exact if h : cand.Nonempty then cand.min' h else 0

/-- The representative of a component of the threshold graph: its least index. -/
def IsRep {n : ℕ} (P : Fin n → EuclideanSpace ℝ (Fin m)) (d : ℝ) (i : Fin n) : Prop :=
  ∀ j, thrReach P d j i → i ≤ j

end DetANN.HPIM


