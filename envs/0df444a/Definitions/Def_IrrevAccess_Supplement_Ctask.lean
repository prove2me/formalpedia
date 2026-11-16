-- Prove2me | Definitions.Def_IrrevAccess_Supplement_Ctask
-- name    : IrrevAccess_Supplement_Ctask
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:57:51.223938+00:00
-- url     : https://prove2.me/theorems/e07713c0-b356-440e-9f1d-97a0385f1486
-- title:
--   Single-task allocation $C_j(b)$, program (6)
-- statement:
--   For a task $j$ and a latent parameter $b$,
--   $$
--   C_j(b)=\min_{z\ge0}\Big\{\sum_{e\in D}z_e:\ \sum_{e\in D}z_e\,d_e(b,b')\ge1\ \text{for every }b'\in\Lambda_j(b)\Big\}\in[0,\infty],
--   $$
--   where $\Lambda_j(b)=\{b':f_j(b')\ne f_j(b)\}$; empty family $0$, infeasible $+\infty$.
-- source:
--   Chen–Fang, The Price of Irreversible Experiment Access, STOC 2027 submission (manuscript, sha256 ba610425…9726), §4.1, p.11 (PDF 13), program (6)

import Mathlib
import Definitions.Def_IrrevAccess_Supplement_coverValue
import Definitions.Def_IrrevAccess_Supplement_divD

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace IrrevAccess.Supplement

/-- **Single-task allocation `C_j(b)`, program (6).** Chen–Fang, *The Price of Irreversible Experiment Access*, STOC 2027 submission (manuscript, sha256 ba610425…9726), §4.1, p.11 (PDF 13):
"C_j(b) = min_{z≥0} { Σ_{e∈D} z_e : Σ_{e∈D} z_e d_e(b, b′) ≥ 1 for every b′ ∈ Λ_j(b) } (6)", with
Λ_j(b) = {b′ : f_j(b′) ≠ f_j(b)}.

**Formalization Note** Valued in `[0, ∞]` through `coverValue`. -/
noncomputable def Ctask {k : ℕ} {B D Y : Type} [Fintype D] (μ : B → D → ℝ) (f : Fin k → B → Y)
    (j : Fin k) (b : B) : ℝ≥0∞ :=
  coverValue {b' : B | f j b' ≠ f j b} (fun b' e => divD μ e b b')

end IrrevAccess.Supplement


