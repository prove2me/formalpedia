-- Prove2me | Definitions.Def_IrrevAccess_Supplement_Cunion
-- name    : IrrevAccess_Supplement_Cunion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:57:23.251311+00:00
-- url     : https://prove2.me/theorems/7049cda5-e4d4-491c-8119-68cc08578f78
-- title:
--   Common root allocation $C_\cup(b)$, program (5)
-- statement:
--   Let $\Lambda_j(b)=\{b':f_j(b')\ne f_j(b)\}$ and $\Lambda_\cup(b)=\bigcup_j\Lambda_j(b)$. The **common root allocation** is
--   $$
--   C_\cup(b)=\min_{z\ge0}\Big\{\sum_{e\in D}z_e:\ \sum_{e\in D}z_e\,d_e(b,b')\ge1\ \text{for every }b'\in\Lambda_\cup(b)\Big\}\in[0,\infty],
--   $$
--   with value $0$ for an empty constraint family and $+\infty$ when infeasible. It is the first-order panel cost of preparing every task's answer before the task is known.
-- source:
--   Chen–Fang, The Price of Irreversible Experiment Access, STOC 2027 submission (manuscript, sha256 ba610425…9726), §4.1, p.11 (PDF 13), program (5)

import Mathlib
import Definitions.Def_IrrevAccess_Supplement_coverValue
import Definitions.Def_IrrevAccess_Supplement_divD

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace IrrevAccess.Supplement

/-- **Common root allocation `C_∪(b)`, program (5).** Chen–Fang, *The Price of Irreversible Experiment Access*, STOC 2027 submission (manuscript, sha256 ba610425…9726), §4.1, p.11 (PDF 13):
"Λ_j(b) = {b′ : f_j(b′) ≠ f_j(b)}, Λ_∪(b) = ⋃_{j=1}^k Λ_j(b). For a fixed b, define
C_∪(b) = min_{z≥0} { Σ_{e∈D} z_e : Σ_{e∈D} z_e d_e(b, b′) ≥ 1 for every b′ ∈ Λ_∪(b) } (5)."

**Formalization Note** Valued in `[0, ∞]` through `coverValue` (empty family `0`, infeasible
`+∞`). -/
noncomputable def Cunion {k : ℕ} {B D Y : Type} [Fintype D] (μ : B → D → ℝ) (f : Fin k → B → Y)
    (b : B) : ℝ≥0∞ :=
  coverValue {b' : B | ∃ j, f j b' ≠ f j b} (fun b' e => divD μ e b b')

end IrrevAccess.Supplement


