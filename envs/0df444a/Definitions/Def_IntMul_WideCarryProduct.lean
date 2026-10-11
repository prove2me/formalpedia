-- Prove2me | Definitions.Def_IntMul_WideCarryProduct
-- name    : IntMul_WideCarryProduct
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T15:25:18.323637+00:00
-- url     : https://prove2.me/theorems/4b979466-ea96-4257-ab4c-e8277b546070
-- title:
--   Actual prepared convolution product recovery at arbitrary sufficient coefficient precision
-- statement:
--   Prepared convolution coefficients occupy the real source tape as fixed-width binary words of a declared precision N. The same physical carry and canonical output machine processes them with an N-bit initial zero carry, rather than requiring the precision to equal the minimal analytic coefficient width. All coefficient generation and source loading remain explicit caller obligations. Correctness, zero final carry, retained complete terminal frame and actual transition bound for any sufficient N are separate theorem obligations. This allows a simple precision such as three times a logarithmic block width.
-- source:
--   Physical convolution product recovery extended to any sufficient declared coefficient precision. Written by Codex.

import Definitions.Def_IntMul_CarryProduct
namespace IntMul.WideCarryProduct

noncomputable def coefficientWords (N B : ℕ) (x y : List Bool) : List (List Bool) :=
  (CarryNormalization.coefficients B x y).map (bin N)
noncomputable abbrev machine : MultitapeTM := CarryOutput.machine
/-- Actual prepared coefficient words have the declared precision N=val(l)+1,
which may exceed the minimal coefficient precision. Generation is separate. -/
noncomputable def initialFrame (pre x y z l : List Bool) : machine.Cfg :=
  CarryOutput.initialFrame pre (coefficientWords (val l+1) (CarryStep.blockSize z) x y) []
    (bin (val l+1) 0) z l
noncomputable def finalFrame (pre x y z l : List Bool) : machine.Cfg :=
  CarryOutput.finalFrame pre (coefficientWords (val l+1) (CarryStep.blockSize z) x y) []
    (bin (val l+1) 0) z l
end IntMul.WideCarryProduct


