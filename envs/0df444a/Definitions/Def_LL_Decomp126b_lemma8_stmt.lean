-- Prove2me | Definitions.Def_LL_Decomp126b_lemma8_stmt
-- name    : LL_Decomp126b_lemma8_stmt
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T15:51:44.095009+00:00
-- url     : https://prove2.me/theorems/9cc89b7f-a221-4a6b-9da6-de3238474a64
-- title:
--   Statement of the cubic Pocklington criterion
-- statement:
--   The proposition asserting: for all natural numbers $N,R,F,s,r$ with $N\ge2$, $F\ge2$, $F$ even, $\gcd(R,F)=1$, $N$ odd, $N=RF+1$, $R=2Fs+r$, $r<2F$ and $N<2F^3$, if there exists $a\in\mathbb Z$ with $N\mid a^{N-1}-1$ (stated as $a^{N-1}\equiv1\pmod N$) and $\gcd(a^{(N-1)/p}-1,N)=1$ for every prime $p\mid F$, then $N$ is prime if and only if $s=0$ or $r^2-8s$ is not the square of an integer. Here $(N-1)/p$ is natural-number division and $a^{N-1}$, $a^{(N-1)/p}$ are integer powers.

import Mathlib

namespace LL_Decomp126b

def lemma8_stmt : Prop := ∀ N R F s r : ℕ,
    2 ≤ N → 2 ≤ F → Even F → Nat.Coprime R F → Odd N →
    N = R * F + 1 → R = 2 * F * s + r → r < 2 * F → N < 2 * F ^ 3 →
    (∃ a : ℤ, Int.ModEq (N : ℤ) (a ^ (N - 1)) 1 ∧
      ∀ p : ℕ, p.Prime → p ∣ F → Int.gcd (a ^ ((N - 1) / p) - 1) N = 1) →
    (N.Prime ↔ s = 0 ∨ ¬ IsSquare ((r : ℤ) ^ 2 - 8 * s))

end LL_Decomp126b


