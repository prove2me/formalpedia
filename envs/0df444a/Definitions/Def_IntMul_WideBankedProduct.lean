-- Prove2me | Definitions.Def_IntMul_WideBankedProduct
-- name    : IntMul_WideBankedProduct
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T16:22:10.919889+00:00
-- url     : https://prove2.me/theorems/be0e15a1-afc6-4131-ac8a-7340df6bebe1
-- title:
--   Actual writable-bank exact-width product at arbitrary sufficient coefficient precision
-- statement:
--   The fixed eighteen-tape prepared-state banked caller executes the complete native product-normalization pipeline at any sufficient coefficient precision. Prepared coefficients occupy writable work bank 2, while the true global input and its head are retained. The exact terminal native banks and actual bit-by-bit return to global product output are specified. Initialization, coefficient generation, loading, local markers and parameter placement remain explicit incoming obligations.
-- source:
--   Physical banked exact-width product normalization at arbitrary sufficient coefficient precision. Written by Codex.

import Definitions.Def_IntMul_WideNormalizedProduct
import Definitions.Def_IntMul_PreparedBankedCall

namespace IntMul.WideBankedProduct

noncomputable abbrev child : MultitapeTM := WideNormalizedProduct.machine
noncomputable abbrev machine : MultitapeTM := PreparedBankedCall.machine child

/-- Prepared convolution coefficients occupy physical work bank 2, while
physical tape 0 retains the original caller input. All native local markers,
descriptors, carry and cursor positions remain explicit incoming obligations. -/
noncomputable def initialFrame (base : machine.Cfg) (nativeBase : child.Cfg)
    (pre x y z l d : List Bool) : machine.Cfg :=
  PreparedBankedCall.runningFrame child base
    (WideNormalizedProduct.initialFrame nativeBase pre x y z l d)

/-- Exact returned global product plus the complete terminal native frame in
writable work banks. The original caller input and every bank prefix remain. -/
noncomputable def finalFrame (base : machine.Cfg) (nativeBase : child.Cfg)
    (pre x y z l d : List Bool) : machine.Cfg :=
  PreparedBankedCall.finalFrame child base
    (WideNormalizedProduct.finalFrame nativeBase pre x y z l d)
    (bin (FixedOutputWidth.width d) (val x*val y))

end IntMul.WideBankedProduct


