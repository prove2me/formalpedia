-- Prove2me | Definitions.Def_ApproxDegComp_Supplement_orFn
-- name    : ApproxDegComp_Supplement_orFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:57:39.71766+00:00
-- url     : https://prove2.me/theorems/66ab52db-ebe2-4b54-be21-1d9e840cef55
-- title:
--   The OR function $\mathrm{OR}_m:\{0,1\}^m\to\{0,1\}$
-- statement:
--   For $m\ge 0$, the **OR function** $\mathrm{OR}_m:\{0,1\}^m\to\{0,1\}$ is
--
--   $$\mathrm{OR}_m(x)=1\iff x_j=1\text{ for some }j\in[m].$$
--
--   It is the inner function of Theorems 15, 32 and 33, where it is block-composed with an arbitrary outer function $f$.
--
--   **Formalization Note** $\{0,1\}^m$ is `Fin m → Bool` with true read as $1$. For $m=0$ there is no coordinate, so $\mathrm{OR}_0$ is the constant $0$.
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), §3.1, p.17; Theorems 15 (p.18), 32 (p.34), 33 (p.37)

import Mathlib

namespace ApproxDegComp

namespace Supplement

/-- **The OR function** `OR_m : {0,1}^m → {0,1}` (§3.1, p.17).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), §3.1, p.17
("Arbitrary Function composed with OR Function"), used in Theorems 15, 32 and 33:
`OR_m(x) = 1` iff some bit `x_j` equals `1`.

**Formalization Note** `{0,1}^m` is `Fin m → Bool` with `true ↦ 1`. For `m = 0` there is no
bit, so `OR_0` is the constant `0` (`false`). -/
def orFn (m : ℕ) : (Fin m → Bool) → Bool :=
  fun x => decide (∃ j, x j = true)

end Supplement

end ApproxDegComp


