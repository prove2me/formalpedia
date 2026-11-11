-- Prove2me | Definitions.Def_NodeStableProj_Main_SizeEstimate
-- name    : NodeStableProj_Main_SizeEstimate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:57:04.052197+00:00
-- url     : https://prove2.me/theorems/28ed5338-c13b-4bd1-a051-d103df41975a
-- title:
--   The truncated discrete Laplace size estimate of Appendix C
-- statement:
--   For $\varepsilon_s>0$ and $\delta_s\in(0,1)$ let
--   $$B=\Big\lceil\frac1{\varepsilon_s}\log\frac4{\delta_s}\Big\rceil .$$
--   $Z$ is the **discrete Laplace law with parameter $\varepsilon_s$ conditioned on $|Z|\le B$**: $\Pr[Z=z]\propto e^{-\varepsilon_s|z|}$ for integers $z\in[-B,B]$. For a graph with $s$ vertices the unclamped size estimate is $s+B+Z$, and the released estimate is $\hat n=\max\{1,s+B+Z\}$.
--
--   **Formalization Note.** $\log$ is natural; the law of $Z$ is a finite sum of Dirac masses on $\mathbb Z$ with the discrete σ-algebra.
-- source:
--   Aden-Ali, Sealfon, Smith, Steinke, Ullman, Node Differential Privacy via Node-Stable Graph Projections, STOC 2027 submission (manuscript sha256 42f18565…), p. 33, Appendix C

import Mathlib

open MeasureTheory

namespace NodeStableProj.Main

/-!
# The private size estimate of Appendix C

Aden-Ali, Sealfon, Smith, Steinke, Ullman, *Node Differential Privacy via Node-Stable Graph
Projections*, STOC 2027 submission (manuscript sha256 42f18565…), p. 33 (PDF 35), Appendix C.

**Formalization Note.** `log` in `B = ⌈(1/ε_s) log(4/δ_s)⌉` is the natural logarithm. `ℤ` carries
its discrete σ-algebra.
-/

/-- `B = ⌈(1/ε_s) log(4/δ_s)⌉`. -/
noncomputable def sizeB (εs δs : ℝ) : ℕ := ⌈(1 / εs) * Real.log (4 / δs)⌉₊

/-- The discrete Laplace law with parameter `ε_s` conditioned on `|Z| ≤ B`:
`Pr[Z = z] ∝ e^{−ε_s |z|}` for integers `z ∈ [−B, B]`. -/
noncomputable def truncDiscreteLaplace (εs : ℝ) (B : ℕ) : Measure ℤ :=
  ∑ z ∈ Finset.Icc (-(B : ℤ)) B,
    ENNReal.ofReal (Real.exp (-εs * |(z : ℝ)|) /
      ∑ w ∈ Finset.Icc (-(B : ℤ)) B, Real.exp (-εs * |(w : ℝ)|)) • Measure.dirac z

/-- The law of the unclamped estimate `s + B + Z` for a graph with `s` vertices. -/
noncomputable def sizeEstimateLaw (εs δs : ℝ) (s : ℕ) : Measure ℤ :=
  (truncDiscreteLaplace εs (sizeB εs δs)).map fun z => (s : ℤ) + sizeB εs δs + z

end NodeStableProj.Main


