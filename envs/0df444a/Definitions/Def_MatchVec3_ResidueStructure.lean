-- Prove2me | Definitions.Def_MatchVec3_ResidueStructure
-- name    : MatchVec3_ResidueStructure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:40:50.499805+00:00
-- url     : https://prove2.me/theorems/3ce4965c-2ec4-4e8d-94d4-74a7b8c742aa
-- title:
--   The two-residue structure on $m=p^aq^b$
-- statement:
--   Residues $\alpha,\beta\in\mathbb Z_m$ have the **two-residue structure** if $m=p^aq^b$ for primes $p<q$ and integers $a,b\ge1$, and
--
--   $$\alpha\equiv0\pmod{p^aq^{b-1}},\quad \alpha\not\equiv0\pmod{q^b},\qquad \beta\equiv0\pmod{p^{a-1}q^b},\quad \beta\not\equiv0\pmod{p^a}.$$
--
--   This is the conclusion of the minimal-modulus reduction in its non-prime-power case and the standing assumption of §5. Modulo $p^a$ the residue $\alpha$ vanishes and $\beta$ does not; modulo $q^b$ the roles are exchanged.
--
--   **Formalization Note** Each modulus above divides $m$, so the congruences do not depend on the representative; they are divisibilities of the canonical representative `ZMod.val`. The number $m$ is a separate index with the equation $m=p^aq^b$ as a field, so no cast between `ZMod m` and `ZMod (p ^ a * q ^ b)` occurs.
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), Lemma 2.3, p.9, and preamble of §5, p.13

import Mathlib

namespace MatchVec3

/-- **The two-residue structure** (Aggarwal, Obremski, STOC 2027 submission (manuscript sha256
44199413…), Lemma 2.3, p.9, and the preamble of §5, p.13): `m = p^a q^b` for primes `p < q` and
positive integers `a, b`, and the residues `α, β` modulo `m` satisfy
`α ≡ 0 (mod p^a q^(b-1))`, `α ≢ 0 (mod q^b)`, `β ≡ 0 (mod p^(a-1) q^b)`, `β ≢ 0 (mod p^a)`.

**Formalization Note** Each modulus here divides `m`, so a congruence of a residue modulo it does not
depend on the representative; it is written as a divisibility of the canonical representative
`ZMod.val`. The subtractions `a - 1`, `b - 1` are on `ℕ` and safe since `1 ≤ a`, `1 ≤ b` are fields.
`m` stays a separate index, with `m = p ^ a * q ^ b` as a field, so that theorems need no cast between
`ZMod m` and `ZMod (p ^ a * q ^ b)`. -/
structure ResidueStructure (m p q a b : ℕ) (α β : ZMod m) : Prop where
  p_prime : p.Prime
  q_prime : q.Prime
  p_lt_q : p < q
  a_pos : 1 ≤ a
  b_pos : 1 ≤ b
  m_eq : m = p ^ a * q ^ b
  α_dvd : p ^ a * q ^ (b - 1) ∣ α.val
  α_not_dvd : ¬ q ^ b ∣ α.val
  β_dvd : p ^ (a - 1) * q ^ b ∣ β.val
  β_not_dvd : ¬ p ^ a ∣ β.val

end MatchVec3


