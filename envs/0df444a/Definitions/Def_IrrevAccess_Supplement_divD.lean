-- Prove2me | Definitions.Def_IrrevAccess_Supplement_divD
-- name    : IrrevAccess_Supplement_divD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:56:54.477718+00:00
-- url     : https://prove2.me/theorems/9f47da2d-cb33-4318-8fde-43f82f54260d
-- title:
--   Per-observation divergence $d_e(b,b')$
-- statement:
--   For latent parameters $b,b'$ and a diagnostic $e$,
--   $$
--   d_e(b,b')=\frac{(\mu_{b,e}-\mu_{b',e})^2}{2},
--   $$
--   the Kullback–Leibler divergence between $N(\mu_{b,e},1)$ and $N(\mu_{b',e},1)$.
-- source:
--   Chen–Fang, The Price of Irreversible Experiment Access, STOC 2027 submission (manuscript, sha256 ba610425…9726), §4.1, p.11 (PDF 13)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace IrrevAccess.Supplement

/-- **Per-observation divergence `d_e(b, b')`.** Chen–Fang, *The Price of Irreversible Experiment Access*, STOC 2027 submission (manuscript, sha256 ba610425…9726), §4.1, p.11 (PDF 13): "For b, b′ ∈ B, write
d_e(b, b′) = (µ_{b,e} − µ_{b′,e})² / 2". -/
noncomputable def divD {B D : Type} (μ : B → D → ℝ) (e : D) (b b' : B) : ℝ :=
  (μ b e - μ b' e) ^ 2 / 2

end IrrevAccess.Supplement


