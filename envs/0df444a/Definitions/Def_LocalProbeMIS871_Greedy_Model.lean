-- Prove2me | Definitions.Def_LocalProbeMIS871_Greedy_Model
-- name    : LocalProbeMIS871_Greedy_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T01:51:37.129891+00:00
-- url     : https://prove2.me/theorems/17271731-227e-4f8b-8a31-5fe99dd4f2d1
-- title:
--   §2 — Uniform ranks, the cached greedy run and adjacency-list probe cost
-- statement:
--   Let $G$ be a finite simple undirected graph on $n$ labeled vertices. Each adjacency list is an arbitrary ordering of exactly its vertex's neighbors, fixed independently of the ranks. Assign real ranks $r(u)$ and order vertices by the lexicographic key $(r(u),u)$, breaking ties by labels. A fresh recursive call reads the degree and full list, scans lower-key neighbors in increasing key order, stops at the first accepted neighbor, and caches its answer. Each top-level query starts with an empty cache. Let $R_G(v,r)$ be the fresh vertices in its actual trace, $U_G(v,r)=|R_G(v,r)|$, and let $p(u)$ be the first fresh caller when one exists. Its probe cost is
--
--   $$Q_G(v,r)=\sum_{u\in R_G(v,r)}(1+\deg_G(u)).$$
--
--   Write $\mu_n$ for the product of Lebesgue probability laws on $(0,1)$, and $\mu_{n,v}$ for its pushforward obtained by setting the root's rank to $1$. The latter is used only for the intermediate lemmas. Good ranks have root rank $1$, distinct coordinates, and all other coordinates in $(0,1)$.
--
--   These definitions connect the reused generic recursion to this source's charged oracle operations. An exponential-moment bound means a measurable nonnegative Lebesgue expectation, so divergence cannot be hidden by a default Bochner integral.
--
--   **Formalization Note** Labels use `Fin n` (add one for the source labels). The run consumes the sorted complete neighborhood, so its result and charged cost do not depend on the supplied list order. `ExpBound` asserts almost-everywhere measurability of its real exponent and bounds the lower integral of its exponential. The overwriting map is a measurable coordinate update, not an arbitrary pushforward map.
-- source:
--   Peter Kiss, Yuichi Yoshida, The Local Probe Complexity of Maximal Independent Set, STOC 2027 submission #871 (October 2026), pp. 10–11, PDF pp. 12–13, §2; Eqs.(4)–(5) and §3.1 on p. 11, PDF p. 13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/871.pdf

import Mathlib
import Definitions.Def_RGMISFast_run

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false

namespace LocalProbeMIS871.Greedy

/-- §2 (printed pp.10–11): arbitrary list orders, each listing exactly the neighbors. -/
structure AdjacencyLists {n : ℕ} (G : SimpleGraph (Fin n)) where
  lists : Fin n → List (Fin n)
  perm : ∀ u, (lists u).Perm (G.neighborFinset u).toList

/-- Labels are zero based; adding one recovers the paper's [n]. -/
def key {n : ℕ} (r : Fin n → ℝ) (u : Fin n) : ℝ ×ₗ Fin n := toLex (r u, u)

/-- Fresh-cache early-stopping execution. Complete lists are read before sorting by key. -/
def execution {n : ℕ} (G : SimpleGraph (Fin n)) (r : Fin n → ℝ) (v : Fin n) :=
  RGMISFast.run G (key r) v

/-- Fresh trace vertices, including the initial root. -/
def R {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (r : Fin n → ℝ) : Finset (Fin n) :=
  (((execution G r v).2.trace.filter (fun e => e.fresh)).map (fun e => e.callee)).toFinset

def U {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (r : Fin n → ℝ) : ℕ := (R G v r).card

/-- Eq.(5): degree probe plus complete list for each fresh vertex. Sorting erases list order. -/
def Q {n : ℕ} (G : SimpleGraph (Fin n)) (_lists : AdjacencyLists G)
    (v : Fin n) (r : Fin n → ℝ) : ℕ :=
  ∑ u ∈ R G v r, (1 + G.degree u)

/-- First fresh caller, read from the actual trace; none for the root or an unevaluated vertex. -/
def parent {n : ℕ} (G : SimpleGraph (Fin n)) (v u : Fin n) (r : Fin n → ℝ) : Option (Fin n) :=
  ((execution G r v).2.trace.find? (fun e => e.fresh && decide (e.callee = u))).bind (fun e => e.caller)

/-- Original shared independent uniform ranks in (0,1), including the empty product. -/
def rankLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => volume.restrict (Set.Ioo (0 : ℝ) 1))

def forceRoot {n : ℕ} (v : Fin n) (r : Fin n → ℝ) : Fin n → ℝ := Function.update r v 1

/-- Only the intermediate lemmas use this pushforward law. -/
def forcedLaw {n : ℕ} (v : Fin n) : Measure (Fin n → ℝ) :=
  Measure.map (forceRoot v) (rankLaw n)

/-- The probability-one distinct-rank domain of the forced-root model. -/
def GoodRanks {n : ℕ} (v : Fin n) (r : Fin n → ℝ) : Prop :=
  r v = 1 ∧ (∀ u, u ≠ v → 0 < r u ∧ r u < 1) ∧ Function.Injective r

/-- A genuine nonnegative Lebesgue exponential moment, with measurability asserted. -/
def ExpBound {n : ℕ} (μ : Measure (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) (b : ℝ) : Prop :=
  AEMeasurable f μ ∧ (∫⁻ r, ENNReal.ofReal (Real.exp (f r)) ∂μ) ≤ ENNReal.ofReal b

end LocalProbeMIS871.Greedy


