-- Prove2me | Definitions.Def_BraidsLinksMCG_ArtinEndo
-- name    : BraidsLinksMCG_ArtinEndo
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-13T18:57:28.308044+00:00
-- url     : https://prove2.me/theorems/d8295a10-de91-451f-8af0-0b01a4fd1d5b
-- title:
--   Artin's automorphisms of the free group, equation (1-14)
-- statement:
--   Artin's action of the braid generators on a free group, equation (1-14).
--
--   Let $F_n$ be the free group on $x_1, \dots, x_n$. The braid generator $\sigma_i$ acts by
--   $$x_i \mapsto x_i x_{i+1} x_i^{-1}, \qquad x_{i+1} \mapsto x_i, \qquad
--     x_j \mapsto x_j \ \ (j \neq i, i+1).$$
--   The file defines, for each braid generator index, the corresponding endomorphism of the free
--   group obtained by extending this assignment multiplicatively, together with the word
--   $x_1x_2\cdots x_n$ that is left fixed by every braid automorphism (condition (1-23) of
--   Theorem 1.9). Free-group generators are indexed by $\mathrm{Fin}\,n$ and braid generators by
--   $\mathrm{Fin}(n-1)$, both $0$-based.
-- source:
--   Joan S. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82, Princeton University Press, 1974, Chapter 1, p. 25, Corollary 1.8.3, equation (1-14)

import Mathlib

/-!
# Artin's automorphisms of the free group

Birman, *Braids, Links, and Mapping Class Groups*, Chapter 1, equation (1-14), p. 25:
the braid generator `σ_{i+1}` acts on the free group `F_n = ⟨x_1, …, x_n⟩` by

* `x_i ↦ x_i x_{i+1} x_i⁻¹`,
* `x_{i+1} ↦ x_i`,
* `x_j ↦ x_j` for `j ≠ i, i+1`.

Generators of the free group are indexed by `Fin n` (index `j` stands for `x_{j+1}`), braid
generators by `Fin (n - 1)`.
-/

namespace BraidsLinksMCG

/-- The strand index `i` (as an index of a free generator) attached to the braid generator
`σ_{i+1}`. -/
def strandIdx {n : ℕ} (i : Fin (n - 1)) : Fin n :=
  ⟨(i : ℕ), by have := i.isLt; omega⟩

/-- The strand index `i + 1` attached to the braid generator `σ_{i+1}`. -/
def strandIdxSucc {n : ℕ} (i : Fin (n - 1)) : Fin n :=
  ⟨(i : ℕ) + 1, by have := i.isLt; omega⟩

/-- Artin's endomorphism (1-14) of the free group `F_n` attached to the braid generator
`σ_{i+1}`. -/
def artinEndo (n : ℕ) (i : Fin (n - 1)) : FreeGroup (Fin n) →* FreeGroup (Fin n) :=
  FreeGroup.lift fun j : Fin n =>
    if j = strandIdx i then
      FreeGroup.of (strandIdx i) * FreeGroup.of (strandIdxSucc i) *
        (FreeGroup.of (strandIdx i))⁻¹
    else if j = strandIdxSucc i then FreeGroup.of (strandIdx i)
    else FreeGroup.of j

/-- The word `x_1 x_2 ⋯ x_n` in the free group `F_n`, the factors taken in increasing order of
the index. -/
def freeWordProd (n : ℕ) : FreeGroup (Fin n) :=
  (List.ofFn fun j : Fin n => FreeGroup.of j).prod

end BraidsLinksMCG


