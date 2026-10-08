-- Prove2me | Definitions.Def_VRPTWColGen92_Bound_WindowReduction
-- name    : VRPTWColGen92_Bound_WindowReduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:24:13.440003+00:00
-- url     : https://prove2.me/theorems/982396a1-8a91-42c2-b9a5-c2b651e310fa
-- title:
--   Sec. 6.1, p. 349 — the four time window reduction conditions
-- statement:
--   This module defines the four time window reduction conditions of Sec. 6.1 of Desrochers, Desrosiers and Solomon (1992), as operations on an instance of the mission's network.
--
--   Applying a condition at a node $k$ replaces one end of the window $[a_k, b_k]$ and leaves all other data unchanged:
--   1. minimal arrival time from predecessors: $a_k \leftarrow \max\{a_k, \min\{b_k, \min_{(i,k)\in A}(a_i + t_{ik})\}\}$;
--   2. minimal arrival time to successors: $a_k \leftarrow \max\{a_k, \min\{b_k, \min_{(k,j)\in A}(a_j - t_{kj})\}\}$;
--   3. maximal departure time from predecessors: $b_k \leftarrow \min\{b_k, \max\{a_k, \max_{(i,k)\in A}(b_i + t_{ik})\}\}$;
--   4. maximal departure time to successors: $b_k \leftarrow \min\{b_k, \max\{a_k, \max_{(k,j)\in A}(b_j - t_{kj})\}\}$.
--
--   An empty inner minimum is $+\infty$ and an empty inner maximum is $-\infty$, so a node without predecessors (successors) gets $\min\{b_k, +\infty\} = b_k$ or $\max\{a_k, -\infty\} = a_k$ inside the outer bracket. A finite sequence of (condition, node) pairs is applied in order, each to the windows produced by the previous ones, as the page's "applied sequentially at each node … examined cyclically" does.
--
--   **Formalization Note.** The inner minimum and maximum are folded with $b_k$ and $a_k$ as the starting values, which implements the empty-set convention without extended reals. The page prints condition 2 with "$\min\{k_k$", a misprint for $\min\{b_k$; the definition uses $b_k$.
-- source:
--   Desrochers, Desrosiers & Solomon, A new optimization algorithm for the vehicle routing problem with time windows, Oper. Res. 40 (1992), p. 349, Sec. 6.1, conditions 1–4

import Mathlib
import Definitions.Def_VRPTWColGen92_Bound_Network

namespace VRPTWColGen92.Bound

variable {n : ℕ}

open Classical in
/-- `min{b_k, min_{(i,k) ∈ A} (a_i + t_ik)}`; an empty inner minimum is `+∞`, so the value is `b_k`. -/
noncomputable def predEarliest (I : Instance n) (k : Fin (n + 1)) : ℝ :=
  (Finset.univ.filter (fun i => I.arc i k)).fold min (I.b k) (fun i => I.a i + I.t i k)

open Classical in
/-- `min{b_k, min_{(k,j) ∈ A} (a_j − t_kj)}`; an empty inner minimum is `+∞`, so the value is `b_k`. -/
noncomputable def succEarliest (I : Instance n) (k : Fin (n + 1)) : ℝ :=
  (Finset.univ.filter (fun j => I.arc k j)).fold min (I.b k) (fun j => I.a j - I.t k j)

open Classical in
/-- `max{a_k, max_{(i,k) ∈ A} (b_i + t_ik)}`; an empty inner maximum is `−∞`, so the value is `a_k`. -/
noncomputable def predLatest (I : Instance n) (k : Fin (n + 1)) : ℝ :=
  (Finset.univ.filter (fun i => I.arc i k)).fold max (I.a k) (fun i => I.b i + I.t i k)

open Classical in
/-- `max{a_k, max_{(k,j) ∈ A} (b_j − t_kj)}`; an empty inner maximum is `−∞`, so the value is `a_k`. -/
noncomputable def succLatest (I : Instance n) (k : Fin (n + 1)) : ℝ :=
  (Finset.univ.filter (fun j => I.arc k j)).fold max (I.a k) (fun j => I.b j - I.t k j)

/-- The four time window reduction conditions of Sec. 6.1 (p. 349). -/
inductive Rule
  | minArrivalFromPred
  | minArrivalToSucc
  | maxDepartureFromPred
  | maxDepartureToSucc

/-- Apply one condition at node `k`: only the window of `k` changes.
1. `a_k := max{a_k, min{b_k, min_{(i,k)∈A}(a_i + t_ik)}}`;
2. `a_k := max{a_k, min{b_k, min_{(k,j)∈A}(a_j − t_kj)}}`;
3. `b_k := min{b_k, max{a_k, max_{(i,k)∈A}(b_i + t_ik)}}`;
4. `b_k := min{b_k, max{a_k, max_{(k,j)∈A}(b_j − t_kj)}}`. -/
noncomputable def reduce (I : Instance n) (ρ : Rule) (k : Fin (n + 1)) : Instance n :=
  match ρ with
  | .minArrivalFromPred => { I with a := Function.update I.a k (max (I.a k) (predEarliest I k)) }
  | .minArrivalToSucc => { I with a := Function.update I.a k (max (I.a k) (succEarliest I k)) }
  | .maxDepartureFromPred => { I with b := Function.update I.b k (min (I.b k) (predLatest I k)) }
  | .maxDepartureToSucc => { I with b := Function.update I.b k (min (I.b k) (succLatest I k)) }

/-- Apply a finite sequence of conditions, in order, each to the windows produced by the previous ones. -/
noncomputable def reduceSeq (I : Instance n) : List (Rule × Fin (n + 1)) → Instance n
  | [] => I
  | s :: rest => reduceSeq (reduce I s.1 s.2) rest

end VRPTWColGen92.Bound


