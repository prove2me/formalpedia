-- Prove2me | Definitions.Def_PrivLittlestone_RankedCandidateSystem
-- name    : PrivLittlestone_RankedCandidateSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:25:01.490965+00:00
-- url     : https://prove2.me/theorems/8167b2e2-6cd2-49ce-b091-d8495f56cb4f
-- title:
--   Ranked candidate system of height $D$ and branching $B$ (Definition 2.2)
-- statement:
--   Let $Z$ be a space of training records and $U$ a candidate universe, with a fixed loss $\ell_u(h) \in \{0,1\}$ for $u \in Z$, $h \in U$, and $\ell_S(h) = \sum_{u \in S} \ell_u(h)$ counting multiplicities. A **ranked candidate system** of height $D$ and branching parameter $B \ge 1$ consists of nonempty finite sets $C(S) \subseteq U$ for every finite record sequence $S$, a rank $\rho : U \to \{0, \dots, D\}$, and, for every ordered pair $(S, S')$ of insertion/deletion neighbors, a map $F_{S,S'} : C(S) \to C(S')$ satisfying:
--
--   1. **Rank.** Common candidates are fixed; every other candidate maps to a candidate of strictly larger rank.
--   2. **Fibers.** For every $h \in C(S')$ and integer $j \ge 1$, $\left|\{g : F_{S,S'}(g) = h,\ \rho(h) - \rho(g) = j\}\right| \le B^j$.
--   3. **Mapped loss sensitivity.** For every $g \in C(S)$, $|\ell_S(g) - \ell_{S'}(F_{S,S'}(g))| \le 1$.
--
--   The maps are used for analysis only. Ranked candidate systems are the interface between the structural sampler and the continual learner of the paper.
--
--   **Formalization Note** $F$ is a total function of $(S, S', g)$, constrained on neighbor pairs and on $g \in C(S)$; the loss is part of the structure. The fibre set counts $g \in C(S)$.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), §2.2, p.4, and Definition 2.2, p.5

import Mathlib
import Definitions.Def_PrivLittlestone_IsInsDelNeighbor

namespace PrivLittlestone

open Classical in
/-- A **ranked candidate system** of height `D` and branching parameter `B ≥ 1` (He–He, *Private
Online Learning of Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript
(sha256 21480556…c562), §2.2, p.4, and Definition 2.2, p.5). Records `u ∈ Z` carry a fixed loss
`ℓ_u(h) ∈ {0,1}` on candidates `h ∈ U`, and `ℓ_S(h) = ∑_{u ∈ S} ℓ_u(h)` counts multiplicities.
The system consists of nonempty finite candidate sets `C(S) ⊆ U` for every finite record
sequence `S`, a rank `ρ : U → {0, …, D}`, and for every ordered pair of insertion/deletion
neighbors `(S, S')` a map `F_{S,S'} : C(S) → C(S')` with
1. (Rank) common candidates are fixed, every other candidate maps to one of strictly larger rank;
2. (Fibers) `|{g : F_{S,S'}(g) = h, ρ(h) − ρ(g) = j}| ≤ B^j` for every `h ∈ C(S')`, `j ≥ 1`;
3. (Mapped loss sensitivity) `|ℓ_S(g) − ℓ_{S'}(F_{S,S'}(g))| ≤ 1` for every `g ∈ C(S)`.

**Formalization Note** `F` is a total function of `(S, S', g)`, constrained only on neighbor
pairs and on `g ∈ C(S)`. The fibre condition counts `g ∈ C(S)`; `ρ h − ρ g = j` with `j ≥ 1` in
`ℕ` holds exactly when the integer difference is `j`. `U` is an arbitrary type. -/
structure RankedCandidateSystem (Z U : Type*) (D : ℕ) (B : ℝ) where
  /-- `B ≥ 1` -/
  one_le_B : 1 ≤ B
  /-- the loss `ℓ_u(h)` of candidate `h` on record `u` -/
  loss : Z → U → ℕ
  loss_le_one : ∀ u h, loss u h ≤ 1
  /-- the candidate set `C(S)` -/
  C : List Z → Finset U
  C_nonempty : ∀ S, (C S).Nonempty
  /-- the rank `ρ` -/
  ρ : U → ℕ
  ρ_le : ∀ h, ρ h ≤ D
  /-- the neighbor maps `F_{S,S'}` -/
  F : List Z → List Z → U → U
  F_mem : ∀ S S', IsInsDelNeighbor S S' → ∀ g ∈ C S, F S S' g ∈ C S'
  F_common : ∀ S S', IsInsDelNeighbor S S' → ∀ g ∈ C S, g ∈ C S' → F S S' g = g
  F_rank : ∀ S S', IsInsDelNeighbor S S' → ∀ g ∈ C S, g ∉ C S' → ρ g < ρ (F S S' g)
  F_fiber : ∀ S S', IsInsDelNeighbor S S' → ∀ h ∈ C S', ∀ j : ℕ, 1 ≤ j →
    ((((C S).filter fun g => F S S' g = h ∧ ρ h - ρ g = j).card : ℕ) : ℝ) ≤ B ^ j
  F_loss : ∀ S S', IsInsDelNeighbor S S' → ∀ g ∈ C S,
    |(((S.map fun u => loss u g).sum : ℕ) : ℝ) - (((S'.map fun u => loss u (F S S' g)).sum : ℕ) : ℝ)|
      ≤ 1

end PrivLittlestone


