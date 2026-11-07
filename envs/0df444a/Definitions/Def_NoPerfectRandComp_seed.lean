-- Prove2me | Definitions.Def_NoPerfectRandComp_seed
-- name    : NoPerfectRandComp_seed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:43:21.574194+00:00
-- url     : https://prove2.me/theorems/bf138fa7-cd68-46f2-a6aa-fde44560607e
-- title:
--   The partial approximate-index seed $p_q$
-- statement:
--   Fix an address length $k$ and a radius $r$. The **seed** $p$ is the partial function on inputs $(a, (P_b, V_b)_{b\in\{0,1\}^k})$ whose value is $z \in \{0,1\}$ when
--   $$
--   P_b = \mathbf 1[d_H(a,b) \le r]\ \text{ for all } b, \qquad V_b = z \ \text{ whenever } d_H(a,b) \le r,
--   $$
--   where $d_H$ is the Hamming distance. Values $V_b$ outside the ball are unrestricted. Since the ball contains $a$, the two promised values are disjoint. At $k = k_q$, $r = r_q$ this is the seed $p_q$.
--
--   Weak independent evidence about the address lands in the ball, while ordinary queries reveal little about the table value; this is what makes the seed cheap for weak information and hard for exact queries.
--
--   **Formalization Note** The domain is the union over $z$ of the two promises, and the value is read at $V_a$, which equals the promised $z$ on the domain.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §4.1, p.12; §5.3, p.24

import Mathlib
import Definitions.Def_NoPerfectRandComp_PartialFn
import Definitions.Def_NoPerfectRandComp_SeedIdx

namespace NoPerfectRandComp

/-- The partial approximate-index seed `p_q` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §4.1, p.12), generic in the address
length `k` and radius `r`. Its value is `z` when `P_b = 1[d_H(a, b) ≤ r]` for all `b` and
`V_b = z` whenever `d_H(a, b) ≤ r`; value bits outside the ball are unrestricted.

**Formalization Note** The domain is the union over `z` of the two promises. The value is read
at `V_a`, which lies in the ball (`d_H(a, a) = 0 ≤ r`), so it equals the promised `z` on the
domain. At `k = k_q`, `r = r_q` this is `p_q`. -/
def seed (k r : ℕ) : PartialFn (SeedIdx k) where
  dom := {x | (∀ b : Fin k → Bool,
      x (Sum.inr (b, false)) = decide (hammingDist (fun i => x (Sum.inl i)) b ≤ r)) ∧
    ∃ z : Bool, ∀ b : Fin k → Bool,
      hammingDist (fun i => x (Sum.inl i)) b ≤ r → x (Sum.inr (b, true)) = z}
  val := fun x => x (Sum.inr (fun i => x (Sum.inl i), true))

end NoPerfectRandComp


