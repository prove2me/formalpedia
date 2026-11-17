-- Prove2me | Definitions.Def_ModLatSVP_Supplement_IsSemistable
-- name    : ModLatSVP_Supplement_IsSemistable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:17:47.037236+00:00
-- url     : https://prove2.me/theorems/7d63d9a4-e746-4c5d-99f7-669aa996a532
-- title:
--   Semistable lattices
-- statement:
--   Let $L=B_L\mathbb Z^D$ be a $D$-dimensional lattice with Gram matrix $G=B_L^{T}B_L$, and let $g=\det(L)^{1/D}$, where $\det(L)=\sqrt{\det G}$. The lattice is **semistable** if every nonzero sublattice $\Gamma\subseteq L$ of rank $k$ satisfies
--
--   $$\det(\Gamma)\ge g^{k}.$$
--
--   In coordinates: for every $k\ge1$ and every integer $D\times k$ matrix $U$ of rank $k$ (so that $\Gamma=B_LU\mathbb Z^k$),
--
--   $$\sqrt{\det(U^{T}GU)}\ \ge\ \big((\det G)^{1/(2D)}\big)^{k}.$$
--
--   Semistable lattices have covering radius at most a constant times $\sqrt D\,g$, which is what makes their closest vector problem solvable with $2^{O(D)}$ SVP-oracle calls (Theorem 5.2); every rank-one module lattice over a cyclotomic field is semistable.
--
--   **Formalization Note** Every nonzero sublattice of rank $k$ has a basis of $k$ vectors, so quantifying over integer matrices of full column rank covers all nonzero sublattices, primitive or not, as the paper's definition does.
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), §5.1, p.33 (PDF p.33), definition of semistability

import Mathlib

open Matrix

namespace ModLatSVP

namespace Supplement

/-- A semistable lattice. Kim, Lee, Son, *Exact SVP and CVP in Structured Lattices: Polynomial-Space
Algorithms and Reductions*, STOC 2027 submission (manuscript sha256 e7151fad…), §5.1, p.33 (PDF p.33):
"Let L be a D-dimensional Euclidean lattice and g = det(L)^{1/D}. The lattice L is semistable if every
nonzero Z-sublattice Γ ⊆ L of rank k satisfies det(Γ) ≥ g^k."

For the lattice `L = B_L ℤ^D` with Gram matrix `G = B_Lᵀ B_L`, `IsSemistable G` says: for every `k ≥ 1`
and every integer `D × k` matrix `U` of rank `k` (the coefficient basis of the rank-`k` sublattice
`Γ = B_L U ℤ^k`), `√det(Uᵀ G U) ≥ g^k`, where `g = det(L)^{1/D} = (det G)^{1/(2D)}`.

**Formalization Note.** Every nonzero sublattice of rank `k` has a basis of `k` vectors, i.e. is `B_L U ℤ^k`
for an integer `U` of rank `k`, and its determinant is `√det(Uᵀ G U)`, so this quantifies over all nonzero
sublattices, primitive or not, as the definition does. -/
def IsSemistable {D : ℕ} (G : Matrix (Fin D) (Fin D) ℝ) : Prop :=
  ∀ (k : ℕ) (U : Matrix (Fin D) (Fin k) ℤ), 1 ≤ k → (U.map (Int.cast : ℤ → ℚ)).rank = k →
    (G.det ^ ((1 : ℝ) / (2 * D))) ^ k ≤
      Real.sqrt ((U.map (Int.cast : ℤ → ℝ))ᵀ * G * U.map (Int.cast : ℤ → ℝ)).det

end Supplement

end ModLatSVP


