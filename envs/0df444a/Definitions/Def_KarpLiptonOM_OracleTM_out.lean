-- Prove2me | Definitions.Def_KarpLiptonOM_OracleTM_out
-- name    : KarpLiptonOM_OracleTM_out
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:44:28.134874+00:00
-- url     : https://prove2.me/theorems/756c315f-8fca-4a14-a220-23f6145c5e25
-- title:
--   Output $M^O(w)$ of an oracle transducer
-- statement:
--   For an oracle machine $M$ running in time $|w|^k + k$, the **output** $M^O(w)$ is the binary string on its work tape (read from the head position) when it halts, i.e. after $|w|^k + k$ steps with oracle $O$. Generators and the machines of $\mathrm{FP}^\Pi$ are transducers in this sense.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.2, p.21 (FP^Π) and §A.2.4, p.23 (generators)

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_run
import Definitions.Def_KarpLiptonOM_OracleTM_init
import Definitions.Def_KarpLiptonOM_Tape_bits

namespace KarpLiptonOM

/-- The output `M^O(w)` of an oracle transducer with time exponent `k`: the string on the work tape
(read from the head, `Tape.bits`) after `|w|^k + k` steps (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.2, p.21, Definition A.2.1,
`FP^Π`; §A.2.4, p.23, generators).

**Formalization Note** For a machine with `IsPolyTime M k` the machine has halted by then, so this
is its output on halting. -/
noncomputable def OracleTM.out (M : OracleTM) (O : Set (List Bool)) (k : ℕ)
    (w : List (Option Bool)) : List Bool :=
  (M.run O (w.length ^ k + k) (M.init w)).work.bits M.ι

end KarpLiptonOM


