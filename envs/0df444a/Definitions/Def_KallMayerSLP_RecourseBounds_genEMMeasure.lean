-- Prove2me | Definitions.Def_KallMayerSLP_RecourseBounds_genEMMeasure
-- name    : KallMayerSLP_RecourseBounds_genEMMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:52.812001+00:00
-- url     : https://prove2.me/theorems/a043c854-aae5-481a-9180-7a63477741f9
-- title:
--   Generalized E–M distribution $\mathbb Q$ as a measure on $\mathbb R^r$
-- statement:
--   The generalized Edmundson–Madansky distribution $\mathbb Q$ of (2.30), viewed as a discrete measure on $\mathbb R^r$:
--   $$
--   \mathbb Q=\sum_{\nu=1}^{2^r}\mathbb Q(v^\nu)\,\delta_{v^\nu},
--   $$
--   with mass $\mathbb Q(v^\nu)$ at each vertex $v^\nu$ of the box $\Xi$. In this form it is a candidate for the moment problem (2.35), whose feasible points are probability measures on $\Xi$.
--
--   **Formalization Note** The weights enter through `ENNReal.ofReal`; they are nonnegative whenever the underlying distribution is carried by the box, so nothing is lost there.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, (2.30)–(2.35), pp.216–219 (PDF 225–228)

import Mathlib
import Definitions.Def_KallMayerSLP_RecourseBounds_genEMWeight

open MeasureTheory

namespace KallMayerSLP.RecourseBounds

/-- **The generalized Edmundson–Madansky distribution `Q` as a measure on `ℝ^r`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, (2.30)–(2.35), printed pp.216–219
(PDF 225–228): "the probability measure `Q` defined on the vertices `v^ν` of `Ξ`", the discrete
measure with mass `Q(v^ν)` at the vertex `v^ν`; it is the candidate solution of the moment problem
(2.35).

**Formalization Note.** `Σ_v ofReal(Q(v)) • δ_{v}` with the vertex `NumStochOpt.Bounds.boxVertex a b v`;
the weights `Q(v)` are nonnegative whenever `μ` is carried by the box, so `ENNReal.ofReal` loses
nothing there. -/
noncomputable def genEMMeasure {r : ℕ} (μ : Measure (Fin r → ℝ)) (a b : Fin r → ℝ) :
    Measure (Fin r → ℝ) :=
  ∑ v : Fin r → Bool,
    ENNReal.ofReal (genEMWeight μ a b v) • Measure.dirac (NumStochOpt.Bounds.boxVertex a b v)

end KallMayerSLP.RecourseBounds


