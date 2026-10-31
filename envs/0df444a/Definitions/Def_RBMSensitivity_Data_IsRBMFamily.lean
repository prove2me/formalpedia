-- Prove2me | Definitions.Def_RBMSensitivity_Data_IsRBMFamily
-- name    : RBMSensitivity_Data_IsRBMFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:34:17.402909+00:00
-- url     : https://prove2.me/theorems/7d7dcfad-d250-4643-8e32-7d9428540dfa
-- title:
--   The family $\{Z^{\alpha,x}\}$ of RBMs
-- statement:
--   Under Assumptions 2.4 and 2.5, for $\alpha\in U$ and $x\in G$, $Z^{\alpha,x}$ denotes the pathwise unique RBM associated with $\alpha$ starting at $x$. This predicate says that a family $(\alpha,x)\mapsto Z^{\alpha,x}$ consists of such processes, all with the same driving Brownian motion.
--
--   The transition functions of the RBM and of the joint process are defined through this family.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §2.1, p.7

import Mathlib
import Definitions.Def_RBMSensitivity_Data_IsRBM
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- A family `Z α x` of RBMs, one for each `α ∈ U` and `x ∈ G`, each started at `x`, all driven by
`W`: the family `Z^{α,x}` of arXiv:1907.00472v2, §2.1, p.7.

**Formalization Note.** Theorem 2.8 shows such a family exists, and that it is unique up to
indistinguishability, so the choice of family does not matter. -/
def Data.IsRBMFamily {J : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} (D : Data J)
    (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (W : ℝ≥0 → Ω → E J)
    (Z : ℝ → E J → ℝ≥0 → Ω → E J) : Prop :=
  ∀ α ∈ D.U, ∀ x ∈ D.G, D.IsRBM 𝓕 P W α (Z α x) ∧ ∀ᵐ ω ∂P, Z α x 0 ω = x

end RBMSensitivity


