-- Prove2me | Definitions.Def_PConeEB_SatisfiesG1
-- name    : PConeEB_SatisfiesG1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:32:10.058992+00:00
-- url     : https://prove2.me/theorems/bde09fc8-d149-44a0-a9b6-fed370c90b2f
-- title:
--   The asymptotic optimality criterion (G1)
-- statement:
--   Let $\mathfrak g:\mathbb R_+\to\mathbb R_+$ be nondecreasing with $\mathfrak g(0)=0$, $K$ a closed convex cone, and $z\in K^*$ with $\mathcal F=\{z\}^\perp\cap K$ a proper face. The criterion (G1) holds if there are $\bar v\in\mathcal F\setminus\{0\}$ and a continuous function $w:(0,1]\to\{z\}^\perp\cap\operatorname{span}K\setminus\mathcal F$ with
--   $$
--   \lim_{\epsilon\downarrow0}w_\epsilon=\bar v\qquad\text{and}\qquad\limsup_{\epsilon\downarrow0}\frac{\mathfrak g(\operatorname{dist}(w_\epsilon,K))}{\operatorname{dist}(w_\epsilon,\mathcal F)}=:L_{\mathfrak g}<\infty .
--   $$
--
--   The criterion says that a curve approaching the face witnesses that $\mathfrak g$ cannot be improved near $\bar v$.
--
--   **Formalization Note** The predicate carries the witnesses $\bar v$, $w$, $L_{\mathfrak g}$ as parameters. The curve is a total function with its conditions on $(0,1]$, and the limit superior is taken in $[0,\infty]$ and equals the real number $L_{\mathfrak g}\ge0$. The standing assumptions on $\mathfrak g$, $K$, $z$ are hypotheses of the statements that use the predicate.
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, Definition 3.1, (G1), p.11

import Mathlib
import Definitions.Def_PConeEB_hyperplane

namespace PConeEB

/-- Definition 3.1 (the asymptotic optimality criterion (G1)), with its witnesses: `v ∈ F \ {0}`,
a continuous `w : (0, 1] → {z}^⊥ ∩ span K \ F` with `w_ε → v` as `ε ↓ 0`, and
`L_g = limsup_{ε ↓ 0} g(dist(w_ε, K)) / dist(w_ε, F) < ∞`, where `F = K ∩ {z}^⊥`.
Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, Definition 3.1, (G1), p.11.

**Formalization Note.** `w` is a total function constrained on `Set.Ioc 0 1`. The limsup is taken in
`ENNReal`, which has no boundedness side conditions, and equals the real number `Lg ≥ 0`; this is
the finiteness of the paper's `L_g`. The denominator is positive on `(0, 1]`, since `w ε ∉ F` and
`F` is closed and nonempty. The standing assumptions on `g`, `K`, `z`, `F` of Definition 3.1 are
hypotheses of the statements that use the predicate. -/
structure SatisfiesG1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (z : E) (g : ℝ → ℝ) (v : E) (w : ℝ → E) (Lg : ℝ) : Prop where
  v_mem : v ∈ K ∩ hyperplane z
  v_ne : v ≠ 0
  cont : ContinuousOn w (Set.Ioc 0 1)
  mem_hyperplane : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, w ε ∈ hyperplane z
  mem_span : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, w ε ∈ Submodule.span ℝ K
  not_mem : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, w ε ∉ K ∩ hyperplane z
  tendsto : Filter.Tendsto w (nhdsWithin 0 (Set.Ioi 0)) (nhds v)
  Lg_nonneg : 0 ≤ Lg
  limsup_eq : Filter.limsup
    (fun ε => ENNReal.ofReal
      (g (Metric.infDist (w ε) K) / Metric.infDist (w ε) (K ∩ hyperplane z)))
    (nhdsWithin 0 (Set.Ioi 0)) = ENNReal.ofReal Lg

end PConeEB


