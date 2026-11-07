-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_P
-- name    : QAdvFew_PoQOracle_P
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:48.40501+00:00
-- url     : https://prove2.me/theorems/2800ea8b-7f6f-4796-8f44-7d4eac2c0193
-- title:
--   $\mathsf P^O$
-- statement:
--   A language $L$ is in $\mathsf P^O$ if there are a deterministic oracle Turing machine $M$ and a polynomial $p$ such that, for every $x\in\{0,1\}^*$, the machine $M^O(x)$ halts within $p(|x|)$ steps and accepts exactly when $x\in L$.
--
--   **Formalization Note** The time bound is with respect to the given oracle $O$, as "$M^O$" says.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Definition 3.1, p. 12 (PDF p. 14)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OTM

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

open Classical in
/-- The class `P^O` (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity
Implications*, arXiv:2611.05303v1, Definition 3.1, p. 12 (PDF p. 14)): `L ∈ P^O` if some
deterministic oracle Turing machine `M` and some polynomial `p` are such that, for every
`x ∈ {0,1}*`, `M^O(x)` halts within `p(|x|)` steps and accepts exactly when `x ∈ L`.

**Formalization Note** The time bound is with respect to the given oracle `O` ("`M^O`"). A
language is a set of bit strings. -/
def P (O : Oracle) : Set (Set Str) :=
  {L | ∃ (M : OTM) (p : Polynomial ℕ), ∀ x : Str,
    M.result O x (p.eval x.length) = some (decide (x ∈ L))}

end QAdvFew.PoQOracle


