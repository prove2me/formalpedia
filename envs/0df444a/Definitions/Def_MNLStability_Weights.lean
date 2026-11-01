-- Prove2me | Definitions.Def_MNLStability_Weights
-- name    : MNLStability_Weights
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:18.373603+00:00
-- url     : https://prove2.me/theorems/73a65b23-628e-4c7a-87d3-f3527dd27909
-- title:
--   MNL preference weights $(w_0,w_1,\dots,w_n)$, $w_{\max}$, $w_{\min}$ and $\Delta$
-- statement:
--   The **preference weights** of an instance with $n$ products are the weight $w_0$ of the no-purchase option and the weight $w_i$ of each product $i\in[n]$. A customer facing the set $S$ of products in stock buys $i\in S$ with probability $w_i/(w_0+w(S))$, where $w(S)=\sum_{j\in S}w_j$, and leaves with probability $w_0/(w_0+w(S))$.
--
--   The definition also fixes the derived quantities used throughout the paper:
--
--   1. $w(S)=\sum_{j\in S}w_j$;
--   2. $w_{\max}=\max_i w_i$ and $w_{\min}=\min_i w_i$;
--   3. $\Delta=w_{\max}/w_{\min}$, the ratio of the extreme product weights;
--   4. a weight vector is **uniform on** a set $I$ of products when all products of $I$ have the same weight.
--
--   Weights are a separate object because the paper changes them: Theorem 2 scales one product's weight, §3.1 rounds all of them, and the proof of Lemma 5 scales the no-purchase weight.
--
--   **Formalization Note** Products are indexed by `Fin n` (0-based). Positivity of the weights is the predicate `Weights.Pos`. $w_{\max}$ and $w_{\min}$ are computed by folding over the products; for $n\ge1$ and positive weights they are the maximum and the minimum.
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), §1.1, pp.3–4 (weights, w(S)); p.5 (w_max, w_min, Δ); §4.1, p.18 (uniform weights)

import Mathlib

namespace MNLStability

/-- The MNL preference weights of an instance with `n` products (Aouad & Segev, SSRN:3498325,
§1.1, pp.3–4): the weight `w0` of the no-purchase option and the weight `w i` of product `i`.

**Formalization Note.** Products are `Fin n` (0-based). The weights are kept apart from prices,
capacity and the law of `M`, because §2.1, §3.1 and the proof of Lemma 5 (p.17) change them. -/
structure Weights (n : ℕ) where
  /-- The weight `w₀` of the no-purchase option. -/
  w0 : ℝ
  /-- The weight `wᵢ` of product `i`. -/
  w : Fin n → ℝ

namespace Weights

variable {n : ℕ}

/-- Preference weights are positive: `0 < w₀` and `0 < wᵢ` for every product (§1.1, p.3). -/
def Pos (wts : Weights n) : Prop := 0 < wts.w0 ∧ ∀ i, 0 < wts.w i

/-- `w(S) = Σ_{j ∈ S} w_j`, the total weight of a set of products (p.4). -/
noncomputable def wsum (wts : Weights n) (S : Finset (Fin n)) : ℝ := ∑ j ∈ S, wts.w j

/-- `w_max = max_i w_i` (p.5); `0` when `n = 0`, a case every statement excludes. -/
noncomputable def wmax (wts : Weights n) : ℝ := ((List.finRange n).map wts.w).foldr max 0

/-- `w_min = min_i w_i` (p.5). For `n ≥ 1` and positive weights this is the minimum weight. -/
noncomputable def wmin (wts : Weights n) : ℝ := ((List.finRange n).map wts.w).foldr min wts.wmax

/-- `Δ = w_max / w_min`, the ratio of the extreme product weights (p.5). -/
noncomputable def Delta (wts : Weights n) : ℝ := wts.wmax / wts.wmin

/-- A weight vector is uniform on a set of products `I` when all products of `I` have the same
weight ("a set of products with uniform preference weights", §4.1, p.18). -/
def UniformOn (wts : Weights n) (I : Finset (Fin n)) : Prop := ∀ i ∈ I, ∀ j ∈ I, wts.w i = wts.w j

end Weights

end MNLStability


