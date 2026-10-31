-- Prove2me | Definitions.Def_RBMSensitivity_Data_M
-- name    : RBMSensitivity_Data_M
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:34:21.198832+00:00
-- url     : https://prove2.me/theorems/c7d8859c-8875-411d-bd3e-0533a47befaa
-- title:
--   The function $M^\alpha$
-- statement:
--   For $\alpha\in U$ and $x\in G$, let $f^{\alpha,x}(t):=x+b(\alpha)t$, and let $(h^{\alpha,x},g^{\alpha,x})$ be the solution to the SP for $f^{\alpha,x}$. Then
--   $$M^\alpha(x):=\inf\{t\ge 0:h^{\alpha,x}(t)=0\}.$$
--
--   This is the time at which the deterministic fluid path reaches the origin. It is the Lyapunov function of Atar, Budhiraja and Dupuis for the RBM.
--
--   **Formalization Note** The value lies in $[0,\infty]$. It is finite under Assumption 3.4, by Lemma 7.1.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §7.1, (7.1), p.27

import Mathlib
import Definitions.Def_RBMSensitivity_Data_IsSPSolution
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- `M^α(x) := inf{t ≥ 0 : h^{α,x}(t) = 0}` of (7.1): arXiv:1907.00472v2, p.27, where `(h^{α,x}, g^{α,x})`
is the solution to the SP for `f^{α,x}(t) := x + b(α)t`.

**Formalization Note.** Values are in `ℝ≥0∞`, with the convention `inf ∅ = ∞` of p.4. The solution is
unique under the standing assumptions, so quantifying over solutions is the same as using the
solution. Under Assumption 3.4 the value is finite (Lemma 7.1). -/
noncomputable def Data.M {J : ℕ} (D : Data J) (α : ℝ) (x : E J) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : ∃ h g, D.IsSPSolution α (fun s => x + (s : ℝ) • D.b α) h g ∧ h t = 0),
    (t : ℝ≥0∞)

end RBMSensitivity


