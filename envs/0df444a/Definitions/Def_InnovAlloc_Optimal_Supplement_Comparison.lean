-- Prove2me | Definitions.Def_InnovAlloc_Optimal_Supplement_Comparison
-- name    : InnovAlloc_Optimal_Supplement_Comparison
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:48:51.740674+00:00
-- url     : https://prove2.me/theorems/b28ba9c9-2226-49a9-875d-2ee4085400de
-- title:
--   Proof of Theorem 2, p. 41 — attained optimized values and their difference
-- statement:
--   For capacity $B>1$, the candidate optimized monopoly value is $M(B)=(1-1/\sqrt B)^2$. Define $D(\alpha,B)=0$ for $B\le2$ and otherwise evaluate the equal-investment objective at the chosen maximizing share $\gamma_d(\alpha,B)$. The optimized difference is $\Delta(\alpha,B)=D(\alpha,B)-M(B)$. With $z=\gamma B$, the transformed objective on $2<z<B$ is
--
--   $$F(\alpha,B,z)=\frac{B-z}{Bz}\left(\alpha z+\sqrt z\sqrt{8-8\alpha+\alpha^2z}-4\right).$$
--
--   Proposition 5 asserts actual maximizer attainment, membership in $2<\gamma_d B<B$, equality of $D$ with $F$ there, and domination of every admissible $z$. Theorem 2 also asserts maximizing-share membership whenever it uses the nonzero branch. Thus no empty or unbounded real supremum defines these values. All switching comparisons concern the optimized objectives, rather than the fixed-share thresholds of Theorem 1.
-- source:
--   Gao, Fan, Huang & Chen, “Resource Allocation Among Competing Innovators”, SSRN preprint 3658157 (February 2021), p. 41, proof of Theorem 2, definitions preceding (21)

import Mathlib
import Definitions.Def_InnovAlloc_Optimal_Supplement_MonoSharing
import Definitions.Def_InnovAlloc_Optimal_Supplement_DuoSharing

namespace InnovAlloc.Optimal.Supplement

noncomputable section

/-- The attained equal-investment value; it is zero for B ≤ 2.
For B > 2 the theorems assert IsDuoShare at gammaD, excluding the fallback branch. -/
def duoValue (α B : ℝ) : ℝ :=
  if B ≤ 2 then 0 else profitDuo α (gammaD α B) B

/-- The reparametrized objective on 2 < z < B in the proof of Theorem 2 (p. 41). -/
def duoZProfit (α B z : ℝ) : ℝ :=
  (B - z) / (B * z) *
    (α * z + Real.sqrt z * Real.sqrt (8 - 8 * α + α ^ 2 * z) - 4)

/-- The optimized difference Δ of the proof of Theorem 2, for B > 1. -/
def delta (α B : ℝ) : ℝ := duoValue α B - monoValue B

end
end InnovAlloc.Optimal.Supplement


