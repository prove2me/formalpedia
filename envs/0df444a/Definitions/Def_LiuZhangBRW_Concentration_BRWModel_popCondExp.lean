-- Prove2me | Definitions.Def_LiuZhangBRW_Concentration_BRWModel_popCondExp
-- name    : LiuZhangBRW_Concentration_BRWModel_popCondExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:18.21643+00:00
-- url     : https://prove2.me/theorems/795758fc-b9b5-4654-88d3-ebb3091202a3
-- title:
--   BRW conditional expectation $\mathbb E^{(M)}_i$ of (6.6)
-- statement:
--   For $i\le M$ the BRW conditional expectation (6.6) of a function $f$ of the lineage is
--   $$
--   \mathbb E^{(M)}_i[f]=\frac{\int f\,a_{i+1}a_{i+2}\cdots a_M\,P(dX_{i+1}\cdots dX_M\mid u_i)}{\int a_{i+1}a_{i+2}\cdots a_M\,P(dX_{i+1}\cdots dX_M\mid u_i)},\qquad a_j=a_j(u_{j-1}):
--   $$
--   the history $X_1,\dots,X_i$ is frozen and the future increments are integrated against the random-walk law of the future given that history, weighted by the future birth rates. The future law depends on the history only through $u_i$.
--
--   **Formalization Note** The future law is `Kernel.traj B.stepKernel i` applied to the history; it integrates every coordinate after $i$, including those after $M$, on which the weight does not depend. Integrals are Bochner integrals and the ratio is a real division, hence $0$ where the denominator vanishes, a null set for $P^{(M)}$.
-- source:
--   Liu, Zhang, Concentration Inequalities for Branching Random Walks with Applications to Phase Transitions in CSPs, arXiv:1601.04794 (artifact sha256 7499631b9d550f66e791c0b3df0879f26102f111fee3052e363ebbff0c72bdcb; no version stamp), (6.6), p. 22; (6.7), (6.8) and the definition of P_i^(M), p. 23

import Mathlib
import Definitions.Def_LiuZhangBRW_Concentration_BRWModel

open MeasureTheory ProbabilityTheory

namespace LiuZhangBRW.Concentration

namespace BRWModel

/-- The future population weight `a_{i+1}(u_i) ⋯ a_M(u_{M−1}) = ∏_{j=i+1}^M a_j(u_{j−1})` (Liu,
Zhang, *Concentration Inequalities for Branching Random Walks with Applications to Phase
Transitions in CSPs*, arXiv:1601.04794, artifact sha256 7499631b…bdcb, (6.6) p. 22 and the
definition of `P_i^(M)`, p. 23). -/
noncomputable def weightAfter (B : BRWModel) (i M : ℕ) (ω : ℕ → ℝ) : ℝ :=
  ∏ j ∈ Finset.Ioc i M, B.rate j (B.pos (j - 1) ω)

/-- The BRW conditional expectation `E_i^(M)` of (6.6) (Liu, Zhang, arXiv:1601.04794, artifact
sha256 7499631b…bdcb, (6.6), p. 22):
`E_i^(M)[·] = ∫(·) a_{i+1} ⋯ a_M P(dX_{i+1} ⋯ dX_M | u_i) / ∫ a_{i+1} ⋯ a_M P(dX_{i+1} ⋯ dX_M | u_i)`.
At a path `ω`, the history `(ω_0, …, ω_i)` is frozen and the future coordinates are integrated
against the random-walk law of the future given that history (`Kernel.traj B.stepKernel i`),
which depends on the history only through `u_i`.

**Formalization Note** The ratio is a real division, so it is `0` where the denominator
vanishes; that set is null under the population measure. Integrals are Bochner integrals.
The future law integrates every coordinate after `i`, including those after `M`, on which the
weight does not depend. -/
noncomputable def popCondExp (B : BRWModel) (M i : ℕ) (f : (ℕ → ℝ) → ℝ) (ω : ℕ → ℝ) : ℝ :=
  (∫ ω', f ω' * B.weightAfter i M ω'
      ∂(Kernel.traj (X := fun _ => ℝ) B.stepKernel i (Preorder.frestrictLe i ω))) /
    (∫ ω', B.weightAfter i M ω'
      ∂(Kernel.traj (X := fun _ => ℝ) B.stepKernel i (Preorder.frestrictLe i ω)))

end BRWModel

end LiuZhangBRW.Concentration


