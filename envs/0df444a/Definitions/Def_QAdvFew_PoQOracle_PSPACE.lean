-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_PSPACE
-- name    : QAdvFew_PoQOracle_PSPACE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:43.963708+00:00
-- url     : https://prove2.me/theorems/552f9b07-a23f-446c-bcef-9731e6ee028d
-- title:
--   $\mathsf{PSPACE}^O$
-- statement:
--   A language $L$ is in $\mathsf{PSPACE}^O$ if a deterministic oracle Turing machine $M^O$ halts on every input, uses polynomial space including its query tape, and satisfies $M^O(x)=L(x)$ for every $x$.
--
--   Counting the query tape is essential: otherwise exponentially long queries would change the class. The running time is not bounded.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Definition 3.5, p. 13 (PDF p. 15)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OTM

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

open Classical in
/-- The class `PSPACE^O` (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity
Implications*, arXiv:2611.05303v1, Definition 3.5, p. 13 (PDF p. 15)): `L ∈ PSPACE^O` if some
deterministic oracle Turing machine `M^O` halts on every input, uses polynomial space including its
query tape, and satisfies `M^O(x) = L(x)` for every `x`.

**Formalization Note** For every `x` there is a step count `T` at which `M^O(x)` has halted with the
right answer, and the cells visited on the work tape and on the query tape up to `T` number at most
`p(|x|)`. The running time is not bounded. -/
def PSPACE (O : Oracle) : Set (Set Str) :=
  {L | ∃ (M : OTM) (p : Polynomial ℕ), ∀ x : Str, ∃ T : ℕ,
    M.result O x T = some (decide (x ∈ L)) ∧ M.space O x T ≤ p.eval x.length}

end QAdvFew.PoQOracle


