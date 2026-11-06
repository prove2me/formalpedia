-- Prove2me | Definitions.Def_ConstrSOSP_RunOut
-- name    : ConstrSOSP_RunOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:00:29.578337+00:00
-- url     : https://prove2.me/theorems/8efe313c-0629-446e-9856-5d7ee9e4dafe
-- title:
--   Clocked run of a machine code
-- statement:
--   A machine code **outputs** $u$ on input $w$ within the clock $T\cdot(|w|+1)^K$ if it is the code of a machine that, started on $w$, halts within $T\cdot(|w|+1)^K$ steps with $u$ written on its tape. The paper notes that "a running time upper bound on a given Turing machine can be enforced syntactically by stopping the computation"; here the bound is part of the semantics.
--
--   **Formalization Note** $T$ is written in unary in the instance and the exponent $K$ is fixed by the problem, so a reduction cannot hide exponential work in the clock. A run that does not halt within the bound, or ends with an unreadable tape, has no output.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §4.1, p.17

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ConstrSOSP_MCode_toTM
import Definitions.Def_ConstrSOSP_MCode_inSym
import Definitions.Def_ConstrSOSP_MCode_decodeOut
import Definitions.Def_ConstrSOSP_encMCode

namespace ConstrSOSP

/-- **Clocked run of a machine code** (arXiv:2604.02285, 2 Nov 2026, §4.1, p.17: "C_f runs in time
upper bounded by some polynomial in b … a running time upper bound on a given Turing machine can be
enforced syntactically by stopping the computation and outputting a fixed output whenever the
computation exceeds the bound").

`RunOut K T code w out` holds iff `code` is the binary code `encMCode M` of a machine `M`, and `M`,
started on the bit string `w`, halts within `T · (|w| + 1)^K` steps with the bit string `out` on
its tape (read from the head rightwards, trailing blanks removed).

**Formalization Note** The time bound is `T · (|w| + 1)^K` with `T` written in unary in the
instance and the exponent `K` a parameter of the problem, not of the instance; a run that does not
halt within the bound, or ends with an unreadable tape, has no output. -/
def RunOut (K T : ℕ) (code w out : List Bool) : Prop :=
  ∃ M : MCode, code = encMCode M ∧
    M.toTM.HaltsWithin (T * (w.length + 1) ^ K) (w.map M.inSym) ∧
    M.decodeOut (M.toTM.output (M.toTM.run (T * (w.length + 1) ^ K)
      (M.toTM.init (w.map M.inSym)))) = some out

end ConstrSOSP


