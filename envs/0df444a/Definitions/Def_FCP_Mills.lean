-- Prove2me | Definitions.Def_FCP_Mills
-- name    : FCP_Mills
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T19:05:09.708752+00:00
-- url     : https://prove2.me/theorems/9b2627ac-7df1-42f0-84b0-ce521a10eadd
-- title:
--   Mills' property and Mills' constant
-- statement:
--   A real number $A$ has **Mills' property** if $\lfloor A^{3^n} \rfloor$ is prime for every integer $n \ge 1$. Mills' constant is the least $A > 1$ with this property; $\mathrm{IsMinMills}(A)$ says exactly that $A$ is a least element of $\{x : x > 1 \text{ and } x \text{ has Mills' property}\}$, i.e. it belongs to the set and is a lower bound for it.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/Mills.lean); W. H. Mills, A prime-representing function, Bull. AMS 53 (1947), 604

import Mathlib

namespace FCP.Mills

/-- `IsMills A` says that `⌊A ^ (3 ^ n)⌋` is a prime number for every positive integer `n`,
where `⌊·⌋` is the floor into `ℕ`. -/
def IsMills (A : ℝ) : Prop := ∀ n : ℕ, 0 < n → Nat.Prime ⌊A ^ (3 ^ n)⌋₊

/-- `IsMinMills A` says that `A` is the least real number greater than `1` satisfying
`IsMills`; such an `A` is Mills' constant. -/
def IsMinMills (A : ℝ) : Prop := IsLeast {x : ℝ | 1 < x ∧ IsMills x} A

end FCP.Mills


