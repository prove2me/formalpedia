-- Prove2me | Definitions.Def_MethodFulfillment_Instance
-- name    : MethodFulfillment_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:08.453234+00:00
-- url     : https://prove2.me/theorems/20728e08-91d7-4168-b3e1-7193e4529cec
-- title:
--   Data of an online multi-item fulfillment problem
-- statement:
--   An **online multi-item fulfillment problem** over a horizon of $T$ periods consists of
--
--   1. a finite set $I$ of items, a finite set $K$ of (real) facilities and a finite set $Q$ of order types;
--   2. for each order type $q$, the set of items it requests (each exactly once);
--   3. for each order type $q$, its set $M(q)$ of **fulfillment methods**; a method $m$ is the set of item–facility pairs $(i,k)$ it uses, so $(i,k)\in m$ means that item $i$ is shipped from facility $k$;
--   4. a cost $c_m$ for each method $m$ of $q$, and a constant $\kappa$ bounding the ratio between the cost of not fulfilling an order and the cost of any method;
--   5. arrival probabilities $p_t(q)$, the probability that an order of type $q$ arrives in period $t$;
--   6. the inventories $S_{ik}\in\mathbb N$ of item $i$ at facility $k$, never replenished.
--
--   These are the data of the model of Section 2. The hypotheses the paper places on them are collected in the definition `Valid`.
--
--   **Formalization Note** The paper adds a dummy facility $0$ with infinite inventory, and "fulfilling an item from the dummy facility" means discarding it. Here the dummy facility is implicit: a method lists only its pairs with real facilities, and an item of $q$ with no pair in the method is discarded. The discard method $m'(q)$ is the empty set. Methods and costs are indexed by their order type, so the same set of pairs may be a method of several order types. Time is 0-based: Lean period $t$ is the paper's period $t+1$.
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), §2, pp.7–9

import Mathlib

namespace MethodFulfillment

/-- The data of an online multi-item fulfillment problem (Amil, Makhdoumi & Wei, *Multi-Item Order
Fulfillment Revisited: LP Formulation and Prophet Inequality*, manuscript, PDF sha256 197c13b9…,
§2, pp.7–9): items `I`, real facilities `K`, order types `Q`, a horizon of `T` periods, the item
set of each order type, its fulfillment methods with their costs, the cost-ratio bound `κ`, the
arrival probabilities `p t q` and the inventories `S i k`.

**Formalization Note.**
* A method of order type `q` **is** its set of (item, real facility) pairs, a `Finset (I × K)`.
  The dummy facility 0 of p.9 is implicit: an item of `q` with no pair in the method is served
  from the dummy facility (discarded). The discard method `m′(q)` is therefore `∅`.
* Methods are indexed by their order type (`methods q`, cost `c q m`), so the same pair set may be
  a method of several order types without being identified ("each method m … fulfill[s] a unique
  order type", p.8).
* Time is `Fin T`, 0-based: Lean time `t` is the paper's period `t + 1`.
* Inventories are natural numbers (units). The hypotheses the paper places on these data are
  collected in `MethodFulfillment.Valid`. -/
structure Instance (I K Q : Type) (T : ℕ) where
  /-- The items requested by an order of type `q` (each exactly once, p.8). -/
  items : Q → Finset I
  /-- The fulfillment methods `M(q)` of order type `q`, each given by its (item, facility) pairs. -/
  methods : Q → Finset (Finset (I × K))
  /-- `c q m` is the cost `c_m` of fulfilling an order of type `q` with method `m`. -/
  c : Q → Finset (I × K) → ℝ
  /-- The bound `κ` on the ratio `c_{m′(q)} / c_m` (p.9). -/
  κ : ℝ
  /-- `p t q` is the arrival probability `p_{t+1}(q)` of order type `q` at Lean time `t`. -/
  p : Fin T → Q → ℝ
  /-- `S i k` is the initial inventory `S_{ik}` of item `i` at facility `k`. -/
  S : I → K → ℕ

end MethodFulfillment


