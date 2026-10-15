-- Prove2me | Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
-- name    : OAI_PiExponent_LogarithmicJetIdeals_PlainJet
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-15T05:44:52.961656+00:00
-- url     : https://prove2.me/theorems/4da0a68a-454b-476b-a228-f0c326cb62c8
-- title:
--   Affine formal jet at a center
-- statement:
--   `plainJet c` is the affine formal expansion sending the polynomial variable at index 0 to `1 + X 0`, and each remaining variable to its center coordinate plus the corresponding formal variable.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

namespace OAI.PiExponent.LogarithmicJetIdeals

noncomputable def plainJet {m : Nat} (c : Fin m -> Complex) :
    AlgHom Complex (MvPolynomial (Fin (m + 1)) Complex)
      (MvPowerSeries (Fin (m + 1)) Complex) :=
  MvPolynomial.aeval (Fin.cases (1 + MvPowerSeries.X 0)
    (fun i => MvPowerSeries.C (c i) + MvPowerSeries.X i.succ))

end OAI.PiExponent.LogarithmicJetIdeals


