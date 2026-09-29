-- Prove2me | Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
-- name    : BraidsLinksMCG_ArtinBraidGroup
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-13T18:52:46.34006+00:00
-- url     : https://prove2.me/theorems/e767e05b-9946-4c2c-a259-005f59d01f52
-- title:
--   The abstract braid group $B_n$ by generators and relations
-- statement:
--   The abstract braid group of Artin, presented by generators and defining relations.
--
--   For $n \ge 0$, generators are indexed by $\mathrm{Fin}(n-1)$, using truncated subtraction, so
--   that there are $n-1$ generators when $n \ge 1$ and none when $n = 0$. The generator with index
--   $i$ corresponds to the book's $\sigma_{i+1}$, the elementary braid interchanging the $i$-th and
--   $(i+1)$-st strands.
--
--   The relation set consists of the two families of equations (1-1) and (1-2):
--
--   $$\sigma_i\sigma_j\sigma_i^{-1}\sigma_j^{-1} \quad (|i-j| \ge 2), \qquad
--     \sigma_i\sigma_{i+1}\sigma_i(\sigma_{i+1}\sigma_i\sigma_{i+1})^{-1},$$
--
--   viewed as elements of the free group on the generator index set, and
--   $B_n$ is the quotient of that free group by the normal closure of this set. Also provided are
--   the generator $\sigma_i$ of $B_n$ and the element $\sigma_1\sigma_2\cdots\sigma_{n-1}$, the
--   product of all generators in increasing order of index, which appears in the description of the
--   centre of $B_n$.
-- source:
--   Joan S. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82, Princeton University Press, 1974, Chapter 1, p. 11 (relations (1-1), (1-2)) and p. 18 (Theorem 1.8)

import Mathlib

/-!
# The Artin braid group, by generators and defining relations

This file sets up the abstract group `B_n` of Birman, *Braids, Links, and Mapping Class
Groups*, Chapter 1 (equations (1-1) and (1-2), p. 11 and p. 18): the group with generators
`σ₁, …, σ_{n-1}` and the braid relations.

Generators are indexed by `Fin (n - 1)`; the generator with index `i` corresponds to
`σ_{i+1}` in the book's 1-based notation.
-/

namespace BraidsLinksMCG

/-- Artin's defining relations for the braid group on `n` strands, as a set of words in the
free group on the generator set `Fin (n - 1)`:

* commuting relations (1-1): `σ_i σ_j σ_i⁻¹ σ_j⁻¹` whenever `|i - j| ≥ 2`;
* braid relations (1-2): `σ_i σ_j σ_i (σ_j σ_i σ_j)⁻¹` whenever `j = i + 1`. -/
def braidRels (n : ℕ) : Set (FreeGroup (Fin (n - 1))) :=
  {r | ∃ i j : Fin (n - 1), 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs ∧
        r = FreeGroup.of i * FreeGroup.of j * (FreeGroup.of i)⁻¹ * (FreeGroup.of j)⁻¹} ∪
  {r | ∃ i j : Fin (n - 1), (j : ℕ) = (i : ℕ) + 1 ∧
        r = FreeGroup.of i * FreeGroup.of j * FreeGroup.of i *
              (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹}

/-- The abstract braid group `B_n` on `n` strands: the group presented by the generators
`σ₁, …, σ_{n-1}` and the braid relations `braidRels n`. -/
def ArtinBraidGroup (n : ℕ) : Type := PresentedGroup (braidRels n)

instance (n : ℕ) : Group (ArtinBraidGroup n) :=
  inferInstanceAs (Group (PresentedGroup (braidRels n)))

/-- The generator `σ_{i+1}` of `ArtinBraidGroup n` (the index `i : Fin (n - 1)` is 0-based). -/
def sigma {n : ℕ} (i : Fin (n - 1)) : ArtinBraidGroup n :=
  PresentedGroup.of i

/-- The element `σ₁ σ₂ ⋯ σ_{n-1}` of `ArtinBraidGroup n`, with the factors multiplied in
increasing order of the index. -/
def sigmaProd (n : ℕ) : ArtinBraidGroup n :=
  (List.ofFn (fun i : Fin (n - 1) => sigma i)).prod

end BraidsLinksMCG


