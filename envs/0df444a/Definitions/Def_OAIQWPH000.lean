-- Prove2me | Definitions.Def_OAIQWPH000
-- name    : OAIQWPH000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T16:03:09.152992+00:00
-- url     : https://prove2.me/theorems/3e48ce65-6016-4e71-8f00-7bee5f58ab6e
-- title:
--   OpenAI pinched Kähler split: the Cauchy jet constant (definitions bundle 1 of 2)
-- statement:
--   A one-definition bundle of the split of OpenAI's proof of the negatively pinched Kähler threefold without bounded holomorphic coordinates (`OAI.PinchedHartogs.main_theorem`). It holds OpenAI's `OAI.PinchedHartogs.BaseConstruction.cauchyJetConstant` from `BaseCauchyJets.lean` of `lean/OAI/Geometry/Kahler` (OpenAI, *A negatively pinched Kähler threefold without bounded holomorphic coordinates*, OpenAI Math Release, September 25, 2026, result family 359, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a: the constant $C_0 = 1$, $C_{n+1} = 4\cdot 2^n\,C_n$ of the Cauchy estimates.
--
--   It is kept apart so that the published statement `OAI.PinchedHartogs.BaseConstruction.analytic_jet_bound` (Cauchy estimates for all derivatives of a bounded holomorphic map between complex normed spaces) imports only Mathlib and this bundle. It imports only Mathlib.
--
--   Modules: `BaseCauchyJets.lean`.
-- source:
--   OpenAI, A negatively pinched Kähler threefold without bounded holomorphic coordinates, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 359; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-negatively-pinched-Kahler-threefold-without-bounded-holomorphic-coordinates-September-25-2026/paper.pdf; Apache License 2.0); definition carved from lean/OAI/Geometry/Kahler/BaseCauchyJets.lean at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQW_PinchedHartogs.BaseCauchyJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler8342_1 uKahler8342_2 uKahler8392_1 uKahler8392_2

open scoped ContDiff
open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open Set Filter Topology MeasureTheory
open scoped ContDiff ComplexOrder
noncomputable section

open Set Filter Topology
namespace PinchedHartogs.BaseConstruction

def cauchyJetConstant : ℕ → ℝ
  | 0 => 1
  | n+1 => 4*2^n*cauchyJetConstant n

end PinchedHartogs.BaseConstruction

end

end OAI
end


