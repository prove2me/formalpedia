-- Prove2me | Definitions.Def_AdaptiveRefresh_Main_MatrixProcess
-- name    : AdaptiveRefresh_Main_MatrixProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:01:22.454607+00:00
-- url     : https://prove2.me/theorems/9f40015a-95fe-4c9f-b4bf-9813141b70d4
-- title:
--   Contractive matrix recursions and conditional expectations
-- statement:
--   For real $d\times d$ matrix-valued processes $P_i,Z_i$, define
--
--   $$E_0=0,\qquad E_i=P_iE_{i-1}P_i^\top+Z_i\quad(i\ge1).$$
--
--   The same recursion with innovations $W_i$ gives $V_i$. Conditional expectation is taken entry by entry under an actual probability measure and sub-sigma-algebra. No norm, centering, predictability, symmetry or variance guarantee is built into these definitions. At a zero denominator in the Freedman exponential, the exponential factor is one for threshold zero and zero for a positive threshold. This is the trivial or limiting bound, respectively.
--
--   The interface supports all finite-dimensional contractions rather than a diagonal special case.
-- source:
--   Maximilian Probst Gutenberg, Yu-Cheng Yeh, Gernot Zöcklein, STOC 2027 submission #894 (October 2026), Lemma 4.4, printed pp. 9–10 (PDF pp. 10–11). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/894.pdf

import Mathlib
import Definitions.Def_AdaptiveRefresh_Main_Graph

set_option autoImplicit false
open MeasureTheory ProbabilityTheory

namespace AdaptiveRefresh.Main

/-- The two matrix recursions start at zero; the first innovation is indexed 1. -/
noncomputable def matrixProcess {Ω : Type*} {d : ℕ}
    (P Z : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) :
    ℕ → Ω → Matrix (Fin d) (Fin d) ℝ
  | 0 => fun _ => 0
  | i + 1 => fun ω => P (i + 1) ω * matrixProcess P Z i ω *
      (P (i + 1) ω).transpose + Z (i + 1) ω

/-- Entrywise conditional expectation; integrability appears in the theorem's hypotheses. -/
noncomputable def conditionalMatrix {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) (F : MeasurableSpace Ω)
    (Z : Ω → Matrix (Fin d) (Fin d) ℝ) (ω : Ω) : Matrix (Fin d) (Fin d) ℝ :=
  fun u v => μ[fun ξ => Z ξ u v | F] ω

/-- At zero denominator: τ=0 gives the trivial exponential factor 1, while a positive
threshold and zero variance/increment scale give limiting factor 0. -/
noncomputable def freedmanFactor (R variance τ : ℝ) : ℝ :=
  if 2 * variance + (2 / 3 : ℝ) * R * τ = 0 then
    if τ = 0 then 1 else 0
  else Real.exp (-(τ ^ 2) / (2 * variance + (2 / 3 : ℝ) * R * τ))

end AdaptiveRefresh.Main


