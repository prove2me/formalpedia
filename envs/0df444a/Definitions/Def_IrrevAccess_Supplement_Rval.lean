-- Prove2me | Definitions.Def_IrrevAccess_Supplement_Rval
-- name    : IrrevAccess_Supplement_Rval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:58:53.980571+00:00
-- url     : https://prove2.me/theorems/845a1764-5204-45f5-8312-4948eb56d548
-- title:
--   Joint retained value $R(j,b)$, program (12), with spacing $s$
-- statement:
--   For a spacing $s$, a task $j$ and a parameter $b$,
--   $$
--   R_s(j,b)=\min_{z_0,z_e\ge0}\Big\{z_0+\sum_e z_e:\ z_0\,\frac{s^2(j-j')^2}{2}+\sum_e z_e\,d_e(b,b')\ge1\ \ \forall (j',b')\text{ with } f_{j'}(b')\ne f_j(b)\Big\}\in[0,\infty].
--   $$
--   The alternatives may change both the task and the latent parameter. The case $s=1$ is the paper's $R(j,b)$.
--
--   **Formalization Note** The weight vector is indexed by "index or diagnostic" (`Option D`).
-- source:
--   Chen–Fang, The Price of Irreversible Experiment Access, STOC 2027 submission (manuscript, sha256 ba610425…9726), §4.4, p.14 (PDF 16), program (12); §4.5, p.18 (PDF 20)

import Mathlib
import Definitions.Def_IrrevAccess_Supplement_coverValue
import Definitions.Def_IrrevAccess_Supplement_divD

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace IrrevAccess.Supplement

/-- **Joint retained value `R(j, b)`, program (12), with index spacing `s`.** Chen–Fang, *The Price of Irreversible Experiment Access*, STOC 2027 submission (manuscript, sha256 ba610425…9726), §4.4, p.14
(PDF 16): "R(j, b) = min_{z₀, z_e ≥ 0} { z₀ + Σ_e z_e : z₀ (j − j′)²/2 + Σ_e z_e d_e(b, b′) ≥ 1
∀ (j′, b′) with f_{j′}(b′) ≠ f_j(b) } (12)", and §4.5, p.18 (PDF 20): "we write R_s(j, b) for the
resulting joint value" of `I_s`, where `(j − j′)²` becomes `s²(j − j′)²`.

The weight vector is indexed by `Option D`: `none` is the index weight `z₀`, `some e` the weight of
diagnostic `e`. `Rval 1` is the paper's `R(j, b)`.

**Formalization Note** Valued in `[0, ∞]` through `coverValue`. -/
noncomputable def Rval {k : ℕ} {B D Y : Type} [Fintype D] (s : ℝ) (μ : B → D → ℝ) (f : Fin k → B → Y)
    (j : Fin k) (b : B) : ℝ≥0∞ :=
  coverValue (ι := Option D) {p : Fin k × B | f p.1 p.2 ≠ f j b}
    (fun p o => o.elim (s ^ 2 * (((j : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ)) ^ 2 / 2) (fun e => divD μ e b p.2))

end IrrevAccess.Supplement


