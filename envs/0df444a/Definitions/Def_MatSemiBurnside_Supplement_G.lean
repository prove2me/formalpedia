-- Prove2me | Definitions.Def_MatSemiBurnside_Supplement_G
-- name    : MatSemiBurnside_Supplement_G
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:43:37.940204+00:00
-- url     : https://prove2.me/theorems/6b94c269-efa0-4d3d-9be0-0b8980d84590
-- title:
--   The bound $G_d(N)=(N+1)(H+1)^d-1$
-- statement:
--   For positive integers $N,d$ put
--   $$D=\binom{d}{\lfloor d/2\rfloor},\qquad H=\binom{N+D^2+1}{D^2},\qquad G_d(N)=(N+1)(H+1)^d-1 .$$
--
--   $G_d(N)$ is the diameter bound of Theorem 2: it is doubly exponential only in $d$ and does not depend on the number of generators.
--
--   **Formalization Note** Computed exactly in $\mathbb N$ with `Nat.choose`; $\lfloor d/2\rfloor$ is `d / 2`. The final subtraction never truncates since $(N+1)(H+1)^d\ge1$. The asymptotic estimate printed next to the definition is a remark and is not part of it.
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), eq. (2), p.10 (also p.4)

import Mathlib
set_option autoImplicit false

namespace MatSemiBurnside.Supplement

/-- **The bound G_d(N).** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), eq. (2), p.10 (also p.4): "For positive integers N, d, define
G_d(N) := (N + 1)(H + 1)^d − 1 where H := binom(N + D² + 1, D²) and D := binom(d, ⌊d/2⌋)."

**Formalization Note.** Computed exactly in ℕ: `D = Nat.choose d (d / 2)` (`d / 2` is ⌊d/2⌋),
`H = Nat.choose (N + D^2 + 1) (D^2)`. The truncated subtraction `- 1` is the true subtraction, since
(N + 1)(H + 1)^d ≥ 1. The asymptotic estimate min{2^{O(d²N)}, (N+1)^{2^{O(d)}}} printed beside (2) is a remark,
not part of the definition. -/
def G (d N : ℕ) : ℕ :=
  (N + 1) * (Nat.choose (N + (Nat.choose d (d / 2)) ^ 2 + 1) ((Nat.choose d (d / 2)) ^ 2) + 1) ^ d - 1

end MatSemiBurnside.Supplement


