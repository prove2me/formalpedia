-- Prove2me | Definitions.Def_QAlgorithms_Defs_TaylorSegmentChannels
-- name    : QAlgorithms_Defs_TaylorSegmentChannels
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:27:03.518068+00:00
-- url     : https://prove2.me/theorems/6e466a97-f3ac-438a-8ca9-79efa88758c1
-- title:
--   TaylorSegmentChannels
-- statement:
--   TaylorSegmentChannels
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\TaylorSegmentChannels.lean

import Definitions.Def_QAlgorithms_Defs_PositiveLCU
import Definitions.Def_QAlgorithms_Defs_TaylorLCUWords
import Definitions.Def_QAlgorithms_Defs_Measurement
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.TaylorSimulation

/-- QAlgorithms.TaylorSimulation.amplifiedUnitary: arxiv-1412.4687v1 PDF p.2, arxiv-1412.4687v1 PDF p.3. Source domains are explicit below. -/
def amplifiedUnitary {J I : Type*} [Fintype J] [Fintype I] [DecidableEq J] [DecidableEq I]
    (zero : J) (W : Matrix.unitaryGroup (J × I) ℂ) : Matrix (J × I) (J × I) ℂ :=
  let R := 1-(2 : ℂ) • Matrix.kronecker (pureDensity (ket zero)) (1 : Matrix I I ℂ)
  show Matrix (J × I) (J × I) ℂ from -((W : Matrix _ _ ℂ)*R*star (W : Matrix _ _ ℂ)*R*(W : Matrix _ _ ℂ))

/-- QAlgorithms.TaylorSimulation.segmentChannel: arxiv-1412.4687v1 PDF p.3. Source domains are explicit below. -/
def segmentChannel {J I : Type*} [Fintype J] [Fintype I] [DecidableEq J] [DecidableEq I]
    (zero : J) (W : Matrix.unitaryGroup (J × I) ℂ) : Superop I I :=
  fun rho => traceLeft (conjSuperop (amplifiedUnitary zero W)
    (Matrix.kronecker (pureDensity (ket zero)) rho))

example {J I : Type*} [Fintype J] [Fintype I] [DecidableEq J] [DecidableEq I]
    (zero : J) (W : Matrix.unitaryGroup (J × I) ℂ) : segmentChannel zero W 0 = 0 := by
  ext i j
  simp [segmentChannel, conjSuperop, traceLeft]

end QAlgorithms.TaylorSimulation


