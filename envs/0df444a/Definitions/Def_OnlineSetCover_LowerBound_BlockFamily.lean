-- Prove2me | Definitions.Def_OnlineSetCover_LowerBound_BlockFamily
-- name    : OnlineSetCover_LowerBound_BlockFamily
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:47:06.397988+00:00
-- url     : https://prove2.me/theorems/64dc7a3d-92e1-4241-b98b-ba784e46f22c
-- title:
--   The block family $\{F_{R,I}\}$ of Section 4
-- statement:
--   Let $k, r$ be positive integers. The ground set consists of $k r^2$ pairwise disjoint **blocks** $X_1, \dots, X_{kr^2}$, each of $2^k$ elements, the elements of a block being identified with $\{0, \dots, 2^k - 1\}$. For a block $X_b$ and a bit location $1 \le t \le k$, $X_b(t)$ is the set of elements of $X_b$ whose $t$th bit is on.
--
--   For every $r$-element subset $R = \{b_1 < \dots < b_r\}$ of $\{1, \dots, kr^2\}$ and every sequence of bit locations $I = (i_1, \dots, i_r)$ with $1 \le i_t \le k$, define
--
--   $$F_{R,I} = \bigcup_{t=1}^{r} X_{b_t}(i_t).$$
--
--   Each $F_{R,I}$ meets exactly $r$ blocks, and contains half the elements of each. The **block family** $\mathcal F$ is the family of all sets $F_{R,I}$. It is the hard instance of Section 4: an adversary forces any deterministic online algorithm to take $kr$ of these sets while one of them covers every element presented.
--
--   **Formalization Note** The ground set is `Fin (k * r ^ 2) × Fin (2 ^ k)`: the pair $(b, j)$ is element $j$ of block $X_{b+1}$, and its bit $t+1$ is `Nat.testBit j t` (bits counted from the least significant one). The sequence $I$ is encoded as a function from all blocks to `Fin k`, of which only the values on $R$ are used; the family is the image of $(R, I) \mapsto F_{R,I}$, so it contains each set once. The paper places the blocks inside $\{1, \dots, n\}$ with $n \ge 2^k kr^2$; the elements outside the blocks lie in no set of this family and are omitted here (Proposition 4.2 reintroduces them).
-- source:
--   Alon, Awerbuch, Azar, Buchbinder, Naor, The Online Set Cover Problem, SIAM J. Comput. 39(2) (2009), pp. 368–369, Section 4 (definition of X_b(t), F_{R,I} and the family F)

import Mathlib

namespace OnlineSetCover.LowerBound

/-- The set `F_{R,I}` of §4 (Alon et al. 2009, p. 368) on the block ground set
`Fin B × Fin (2^k)`: the element `(b, j)` is element `j` of block `X_{b+1}`, and its bit number
`t + 1` is `Nat.testBit j t`. For a set `R` of block indices and a choice `I` of a bit location
`I b` for every block, `F_{R,I}` is the union over `b ∈ R` of `X_b(I b)`, the elements of block
`b` whose bit `I b` is on. Only the values of `I` on `R` matter. -/
def blockSet {k B : ℕ} (R : Finset (Fin B)) (I : Fin B → Fin k) : Finset (Fin B × Fin (2 ^ k)) :=
  Finset.univ.filter (fun p => p.1 ∈ R ∧ p.2.val.testBit (I p.1).val)

/-- The family `𝓕` of §4 (p. 368–369): all sets `F_{R,I}` with `R` an `r`-element subset of the
`k r²` blocks and `I` a choice of one of the `k` bit locations in each block of `R`. The ground
set is the `k r²` disjoint blocks of `2^k` elements each, `Fin (k * r ^ 2) × Fin (2 ^ k)`. -/
def blockFamily (k r : ℕ) : Finset (Finset (Fin (k * r ^ 2) × Fin (2 ^ k))) :=
  ((Finset.univ.powersetCard r) ×ˢ (Finset.univ : Finset (Fin (k * r ^ 2) → Fin k))).image
    (fun RI => blockSet RI.1 RI.2)

end OnlineSetCover.LowerBound


