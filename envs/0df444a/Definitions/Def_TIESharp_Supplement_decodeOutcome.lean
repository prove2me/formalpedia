-- Prove2me | Definitions.Def_TIESharp_Supplement_decodeOutcome
-- name    : TIESharp_Supplement_decodeOutcome
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:55:38.152984+00:00
-- url     : https://prove2.me/theorems/fef12504-62fe-4ff4-a19f-362dfaaa386c
-- title:
--   Decoding an output string as an outcome $(A,\pi)$
-- statement:
--   For fixed numbers of machines $n$ and jobs $m$, a bit string $s$ **decodes** to the outcome $(A,\pi)$ — an assignment $A:[m]\to[n]$ and rational payments $\pi\in\mathbb Q^n$ — when $s$ is the binary code of $(A,\pi)$; a string that is the code of no outcome decodes to nothing. Since the outcome code is injective, the decoded outcome is unique. The realized assignment and payments of a run of the mechanism are read from its output in this way.
--
--   **Formalization Note** The outcome is selected with `Classical.choose`, as the published `BlottoFPTAS.Main.BitRAM.decodeAlloc` does; the result is an `Option`. A verification file checks that decoding the code of $(A,\pi)$ returns $(A,\pi)$ and that the empty string decodes to nothing when $n\ge1$.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134, Theorem 1.3, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_TIESharp_Supplement_outputCode

set_option autoImplicit false

namespace TIESharp

namespace Supplement

open Classical in
/-- **Decoding a run's output** as an outcome (Li, *Sharp Bounds for Truthful-in-Expectation
Scheduling*, arXiv:2611.05134, Theorem 1.3, p.2): `some (A, π)` if the bit string is
`outputCode A π` for an assignment `A : Fin m → Fin n` and payments `π : Fin n → ℚ`, and `none` if
it is the code of no outcome.

**Formalization Note.** The pair is picked with `Classical.choose`, as the published
`BlottoFPTAS.Main.BitRAM.decodeAlloc` does; `outputCode` is injective for fixed `n, m`, so the
decoded outcome is the unique one. -/
noncomputable def decodeOutcome (n m : ℕ) (bits : List Bool) :
    Option ((Fin m → Fin n) × (Fin n → ℚ)) :=
  if h : ∃ o : (Fin m → Fin n) × (Fin n → ℚ), outputCode o.1 o.2 = bits then
    some (Classical.choose h)
  else none

end Supplement

end TIESharp


