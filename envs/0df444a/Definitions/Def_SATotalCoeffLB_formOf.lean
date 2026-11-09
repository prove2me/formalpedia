-- Prove2me | Definitions.Def_SATotalCoeffLB_formOf
-- name    : SATotalCoeffLB_formOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:18:47.862213+00:00
-- url     : https://prove2.me/theorems/b7a2303b-dcdc-4be9-86d8-7e2e783a6566
-- title:
--   Quadratic form $a_z$ of an edge vector $z\in\mathbb F_2^E$
-- statement:
--   Let $E$ be a set of pairs on $[n]$. A vector $z \in \mathbb F_2^E$ defines the quadratic form
--
--   $$
--   a_z(\bar x) = \sum_{e = \{i,j\} \in E} z_e\, \bar x_i \bar x_j \in Q_n,
--   $$
--
--   whose coefficient on the pair $e$ is $z_e$ for $e \in E$ and $0$ otherwise. Its polar matrix is the adjacency matrix of the graph with edge set $\{e \in E : z_e = 1\}$. The map $z \mapsto a_z$ is linear and injective, and for a code $C \subseteq \mathbb F_2^E$ the paper sets $L = \{a_z : z \in C\}$.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), Section 9.1, p.51

import Mathlib
import Definitions.Def_SATotalCoeffLB_QForm

namespace SATotalCoeffLB

/-- **The quadratic form `a_z` of an edge labelling** `z ∈ F₂^E` (Section 9.1, p.51, of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178)):
`a_z(x̄) := ∑_{e = {i,j} ∈ E} z_e x̄_i x̄_j`, i.e. the coefficient of the pair `e` is `z_e` for
`e ∈ E` and `0` otherwise. For a code `C ⊆ F₂^E`, `L := {a_z : z ∈ C}`. -/
def formOf {n : ℕ} (E : Finset (Pair n)) (z : E → ZMod 2) : QForm n :=
  fun e => if h : e ∈ E then z ⟨e, h⟩ else 0

end SATotalCoeffLB


