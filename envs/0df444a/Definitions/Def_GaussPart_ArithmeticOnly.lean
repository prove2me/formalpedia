-- Prove2me | Definitions.Def_GaussPart_ArithmeticOnly
-- name    : GaussPart_ArithmeticOnly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:36.872857+00:00
-- url     : https://prove2.me/theorems/a880e056-2076-47c3-9c16-f2763ac6757b
-- title:
--   Arithmetic-only programs of the sampling real RAM
-- statement:
--   A program of the sampling real RAM (`GaussMixHH_Machine`) is **arithmetic-only** if each of its instructions is a core real-RAM instruction (exact $+,-,\times,\div$, rational literals, comparisons, loads, stores and pointer moves), a pointer-to-real cast, $\mathrm{sample}$ or $\mathrm{halt}$. It thus excludes $\sqrt{\cdot}$, $\exp$, $\cos$, $\sin$ and coin flips. A run of such a program never reads the coin tape; it is run on the constant tape `noCoins`.
--
--   The paper measures running time in "arithmetic operations" (end of the proof of Proposition 3.3, p.35) and names no other machine; this predicate is that list.
--
--   **Formalization Note** The predicate restricts only the program chosen under "there is an algorithm", never the input. It is the stronger reading: any additional unit-cost primitive would make the theorems weaker. The proofs in the paper use exact singular subspaces, unit vectors and the Gaussian distribution function, so a program meeting the theorems must use approximations within the slack of the analysis.
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), proof of Proposition 3.3, p.35 (PDF p.37); Theorem 3.1, p.14

import Mathlib
import Definitions.Def_GaussMixHH_Machine

namespace GaussPart

/-- Only the arithmetic part of the published `GaussMixHH` sampling RAM: every instruction of the
program is a real-RAM core instruction (exact `+ − × ÷`, rational literals by `GaussMixHH.Admissible`,
load, store, pointer moves, comparison jumps), a pointer-to-real cast, `sample` or `halt`. So no
`√`, `exp`, `cos`, `sin` and no `coin`.

arXiv:2611.05264 (sha256 7e0ca6d4…) measures running time in "arithmetic operations" (proof of
Proposition 3.3, p.35, PDF p.37) and gives no other machine.

**Formalization Note.** This restricts the program chosen under `∃`, never the input. It is the
literal list, and the non-weaker reading: a further unit-cost primitive would make the theorems
weaker. The proof on the page uses exact singular subspaces, unit vectors and `Φ`; a program meeting
these theorems must use approximate subroutines inside the slack of the proof. -/
def ArithmeticOnly (P : GaussMixHH.Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core _ | .pointerReal _ _ | .sample _ | .halt => True
    | _ => False

/-- The coin tape of a run of an `ArithmeticOnly` program. Such a program has no `coin`
instruction, so the tape is never read; the algorithm is deterministic given its samples. -/
def noCoins : ℕ → Bool := fun _ => false

end GaussPart


