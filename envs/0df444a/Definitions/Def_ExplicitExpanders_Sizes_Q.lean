-- Prove2me | Definitions.Def_ExplicitExpanders_Sizes_Q
-- name    : ExplicitExpanders_Sizes_Q
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T06:12:46.131084+00:00
-- url     : https://prove2.me/theorems/b0f8b280-42f6-42a1-b960-047360d2a70d
-- title:
--   The LPS vertex count $Q(q_1,q_2,s,t)$ (Section 2.3)
-- statement:
--   For natural numbers $q_1, q_2, s, t$ define
--
--   $$
--   Q(q_1,q_2,s,t)=q_1^{3(s-1)}\,q_2^{3(t-1)}\cdot\frac{q_1(q_1-1)(q_1+1)}{2}\cdot\frac{q_2(q_2-1)(q_2+1)}{2}.
--   $$
--
--   In Alon's construction $p$ is prime with $p\equiv1\pmod4$, the distinct primes $q_1,q_2$ each satisfy $q_i\equiv1\pmod{4p}$, and $s,t\ge1$. Under those conditions, $Q(q_1,q_2,s,t)$ is the number of vertices of the Lubotzky–Phillips–Sarnak quaternion graph $H(p,q_1^s q_2^t)$. The paper derives this count from Hensel's lemma and the Chinese remainder theorem; here $Q$ is simply the explicit arithmetic expression above, which Lemma 2.2 applies to arbitrary distinct primes.
--
--   Both fractions are integers: $q(q-1)(q+1)$ is a product of three consecutive integers, hence even.
--
--   The set $\{Q(q_1,q_2,s,t): s,t\ge 1\}$ is the set of vertex counts available from this family of LPS graphs, and the question of how densely it covers the integers is what Lemma 2.2 answers.
--
--   **Formalization Note** $Q$ is $\mathbb N$-valued, with natural-number subtraction and division. The division by $2$ is exact, as explained above, so casting to $\mathbb R$ after the division gives the real value of the paper's formula. The subtractions $s-1$, $t-1$, $q_i-1$ are the true differences whenever $s,t\ge1$ and $q_i\ge1$; every statement of the mission assumes $s,t\ge1$ and $q_1,q_2$ prime. For $s=0$ the expression would silently equal its value at $s=1$, so it must not be used there.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, p. 6, Section 2.3 (display defining Q(q1, q2, s, t))

import Mathlib

namespace ExplicitExpanders.Sizes

/-- The vertex count of the LPS graph `H(p, q₁ˢ q₂ᵗ)` as an explicit expression (Alon, *Explicit
expanders of every degree and size*, arXiv:2003.11673v1, §2.3, p. 6):
`Q(q₁, q₂, s, t) = q₁^{3(s−1)} q₂^{3(t−1)} · q₁(q₁−1)(q₁+1)/2 · q₂(q₂−1)(q₂+1)/2`.
It is used only for `s, t ≥ 1` (so `s - 1`, `t - 1` are the true differences) and primes `q₁, q₂`
(so `qᵢ - 1` is the true difference). Each division by `2` is exact, because `q(q−1)(q+1)` is a
product of three consecutive integers and hence even. -/
def Q (q₁ q₂ s t : ℕ) : ℕ :=
  q₁ ^ (3 * (s - 1)) * q₂ ^ (3 * (t - 1)) * (q₁ * (q₁ - 1) * (q₁ + 1) / 2) *
    (q₂ * (q₂ - 1) * (q₂ + 1) / 2)

end ExplicitExpanders.Sizes


