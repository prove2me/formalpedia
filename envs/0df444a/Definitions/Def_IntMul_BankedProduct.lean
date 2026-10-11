-- Prove2me | Definitions.Def_IntMul_BankedProduct
-- name    : IntMul_BankedProduct
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T14:11:27.01899+00:00
-- url     : https://prove2.me/theorems/77f02a40-bd86-48ca-9272-5198ff3868e5
-- title:
--   Actual prepared convolution product execution on writable banks and global output return
-- statement:
--   A fixed eighteen-tape banked machine executes the complete sixteen-tape coefficient product normalization pipeline on writable work banks. The prepared coefficients occupy physical work bank 2 while the original true caller input remains read-only. Descriptor preparation and exact-width product normalization execute physically, and the child output is then rewound and copied to global output. The exact incoming coefficient, carry, descriptor, local-marker and cursor frame is an explicit caller obligation. Correctness, exact terminal product frame, retained input and prefixes, and the complete charged clock are separate theorem obligations.
-- source:
--   Original composition of complete physical product normalization with arbitrary-prepared-state banked execution and global output return. Written by Codex.

import Definitions.Def_IntMul_NormalizedProduct
import Definitions.Def_IntMul_PreparedBankedCall

namespace IntMul.BankedProduct

noncomputable abbrev child : MultitapeTM := NormalizedProduct.machine
noncomputable abbrev machine : MultitapeTM := PreparedBankedCall.machine child

/-- Prepared convolution coefficients occupy physical work bank 2, while
physical tape 0 retains the original caller input. All native local markers,
descriptors, carry and cursor positions remain explicit incoming obligations. -/
noncomputable def initialFrame (base : machine.Cfg) (nativeBase : child.Cfg)
    (pre x y z l d : List Bool) : machine.Cfg :=
  PreparedBankedCall.runningFrame child base
    (NormalizedProduct.initialFrame nativeBase pre x y z l d)

/-- Exact returned global product plus the complete terminal native frame in
writable work banks. The original caller input and every bank prefix remain. -/
noncomputable def finalFrame (base : machine.Cfg) (nativeBase : child.Cfg)
    (pre x y z l d : List Bool) : machine.Cfg :=
  PreparedBankedCall.finalFrame child base
    (NormalizedProduct.finalFrame nativeBase pre x y z l d)
    (bin (FixedOutputWidth.width d) (val x*val y))

end IntMul.BankedProduct


