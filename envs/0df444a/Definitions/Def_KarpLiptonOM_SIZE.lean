-- Prove2me | Definitions.Def_KarpLiptonOM_SIZE
-- name    : KarpLiptonOM_SIZE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:41:27.932011+00:00
-- url     : https://prove2.me/theorems/01446739-09e7-4ecf-b291-0b819df46f7b
-- title:
--   $\mathrm{SIZE}[n^k]$: circuits of size $O(n^k)$
-- statement:
--   For $k \in \mathbb N$, $\mathrm{SIZE}[n^k]$ is the class of languages $L$ for which there is a constant $c$ such that for every $n$ some circuit with $n$ inputs and at most $c\,n^k + c$ gates computes $L$ on $\{0,1\}^n$.
--
--   **Formalization Note** The paper uses $\mathrm{SIZE}[n^k]$ only in statements "for every $k$", where size $O(n^k)$ and size $n^k$ give the same statement.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), (F2), p.23 (standard class)

import Mathlib
import Definitions.Def_KarpLiptonOM_Circuit_eval

namespace KarpLiptonOM

/-- `SIZE[n^k]`: languages computed on every `{0,1}ⁿ` by a circuit with `n` inputs and at most
`c·n^k + c` gates, for a constant `c` (standard; Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), (F2), p.23, "`OL₂^P ⊄ SIZE[n^k]` for every `k`").

**Formalization Note** The constant `c` makes this the class of size `O(n^k)`; for the statement
"for every `k`" this is the same as size `n^k`. -/
def SIZE (k : ℕ) : Set (Set (List Bool)) :=
  {L | ∃ c : ℕ, ∀ n : ℕ, ∃ C : Circuit n, C.gates.length ≤ c * n ^ k + c ∧
    ∀ x : List Bool, x.length = n → (C.eval x = true ↔ x ∈ L)}

end KarpLiptonOM


