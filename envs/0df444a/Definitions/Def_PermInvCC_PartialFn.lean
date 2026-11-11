-- Prove2me | Definitions.Def_PermInvCC_PartialFn
-- name    : PermInvCC_PartialFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:22:57.747564+00:00
-- url     : https://prove2.me/theorems/b3eda303-a7ae-42e8-9052-874bc2fdffc1
-- title:
--   Partial functions $f:[q]^n\times[q]^n\to\{-1,+1,*\}$
-- statement:
--   Alice holds a string $x\in[q]^n$ and Bob a string $y\in[q]^n$. A **partial function** assigns to each input pair a value in $\{-1,+1,*\}$, where $*$ means *undefined*:
--   $$f:[q]^n\times[q]^n\to\{-1,+1,*\}.$$
--   The pairs with $f(x,y)\ne *$ are the **promised** inputs.
--
--   This is the class of problems whose communication complexity the paper studies.
--
--   **Formalization Note** $[q]$ and $[n]$ are `Fin q` and `Fin n`; the value $*$ is `none`, $+1$ is `some true` and $-1$ is `some false`.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), §1.1, p.1 and Definition 2.2, p.9

import Mathlib

namespace PermInvCC

/-- A **partial function** `f : [q]ⁿ × [q]ⁿ → {−1, +1, ∗}` (Y. Huang and Z. Ye, *Quantum Advantage
of Permutation-Invariant Functions in Communication Complexity*, arXiv:2609.40116, held version
sha256 fe1797dd…, §1.1, p.1, and Definition 2.2, p.9). Alice holds `x : [q]ⁿ`, Bob holds `y : [q]ⁿ`.

**Formalization Note.** `[q]` is `Fin q` and `[n]` is `Fin n`. The value `none` is the undefined
value `∗`; `some true` is `+1` and `some false` is `−1`. A pair `(x, y)` is *promised* when
`f x y ≠ none`. -/
abbrev PartialFn (n q : ℕ) : Type := (Fin n → Fin q) → (Fin n → Fin q) → Option Bool

end PermInvCC


