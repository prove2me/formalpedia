-- Prove2me | Definitions.Def_IrrevAccess_Supplement_Jval
-- name    : IrrevAccess_Supplement_Jval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:58:25.499188+00:00
-- url     : https://prove2.me/theorems/5d6e645a-654d-44d2-a15e-29dee64530ab
-- title:
--   Index-answer value $J_b(j)$, program (11), with spacing $s$
-- statement:
--   For a spacing $s$, a task $j$ and a parameter $b$,
--   $$
--   J^{(s)}_b(j)=\min_{z_0\ge0}\Big\{z_0:\ z_0\,\frac{s^2(j-j')^2}{2}\ge1\ \text{whenever } f_{j'}(b)\ne f_j(b)\Big\}\in[0,\infty].
--   $$
--   It is $0$ when no task $j'$ answers differently at $b$. The case $s=1$ is the paper's $J_b(j)$; general $s$ is the index value of the instance $I_s$ (§4.5).
-- source:
--   Chen–Fang, The Price of Irreversible Experiment Access, STOC 2027 submission (manuscript, sha256 ba610425…9726), §4.4, p.14 (PDF 16), program (11); §4.5, p.18 (PDF 20)

import Mathlib
import Definitions.Def_IrrevAccess_Supplement_coverValue

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace IrrevAccess.Supplement

/-- **Index-answer value `J_b(j)`, program (11), with index spacing `s`.** Chen–Fang, *The Price of Irreversible Experiment Access*, STOC 2027 submission (manuscript, sha256 ba610425…9726), §4.4, p.14
(PDF 16): "J_b(j) = min_{z₀≥0} { z₀ : z₀ (j − j′)²/2 ≥ 1 if f_{j′}(b) ≠ f_j(b) } (11). This value is
zero when the constraint set is empty", and §4.5, p.18 (PDF 20): for the instance `I_s` "(j − j′)²
is replaced by s²(j − j′)² in (11) and (12)".

`Jval s f j b` is program (11) of `I_s`; `Jval 1` is the paper's `J_b(j)`.

**Formalization Note** The program depends on tasks only through differences `j − j′`, so the
shift of tasks to `Fin k` changes nothing. Valued in `[0, ∞]` through `coverValue`. -/
noncomputable def Jval {k : ℕ} {B Y : Type} (s : ℝ) (f : Fin k → B → Y) (j : Fin k) (b : B) : ℝ≥0∞ :=
  coverValue (ι := Unit) {j' : Fin k | f j' b ≠ f j b}
    (fun j' _ => s ^ 2 * (((j : ℕ) : ℝ) - ((j' : ℕ) : ℝ)) ^ 2 / 2)

end IrrevAccess.Supplement


