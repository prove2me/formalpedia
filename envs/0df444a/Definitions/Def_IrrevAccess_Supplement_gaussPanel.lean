-- Prove2me | Definitions.Def_IrrevAccess_Supplement_gaussPanel
-- name    : IrrevAccess_Supplement_gaussPanel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:56:21.253633+00:00
-- url     : https://prove2.me/theorems/079dcc40-7e7f-4a09-90a0-4c9cef6c3af6
-- title:
--   Gaussian panel laws $P_{b,e}=N(\mu_{b,e},1)$
-- statement:
--   Given a real mean table $\mu:B\times D\to\mathbb R$, the **Gaussian panel** assigns to latent parameter $b$ and diagnostic $e$ the law
--   $$
--   P_{b,e}=N(\mu_{b,e},1)\quad\text{on }\mathbb R .
--   $$
--   These are the panel laws of the two-stage Gaussian model of §4.1; they depend on $b$ and not on the task $j$.
-- source:
--   Chen–Fang, The Price of Irreversible Experiment Access, STOC 2027 submission (manuscript, sha256 ba610425…9726), §4.1 "A two-stage model", p.10 (PDF 12)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace IrrevAccess.Supplement

/-- **Gaussian panel laws `P_{b,e} = N(µ_{b,e}, 1)`.** Chen–Fang, *The Price of Irreversible Experiment Access*, STOC 2027 submission (manuscript, sha256 ba610425…9726), §4.1 "A two-stage model", p.10
(PDF 12): "At the initial state r, a finite collection D of diagnostics returns independent samples
Y_e ∼ N(µ_{b,e}, 1), e ∈ D. These laws depend on b and not on j."

`gaussPanel µ b e` is the unit-variance Gaussian law with mean `µ b e` on `ℝ`; the observation
space of every diagnostic is `ℝ`. -/
noncomputable def gaussPanel {B D : Type} (μ : B → D → ℝ) : B → (e : D) → Measure ((fun _ : D => ℝ) e) :=
  fun b e => gaussianReal (μ b e) 1

end IrrevAccess.Supplement


