-- Prove2me | Definitions.Def_BFFPyramidal_cosetPartition
-- name    : BFFPyramidal_cosetPartition
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-13T18:25:29.06498+00:00
-- url     : https://prove2.me/theorems/774cff8f-ece2-4e38-af7b-ef44a980ba3c
-- title:
--   Coset partitions and their modulus
-- statement:
--   A family of left cosets $a_iK_i$ of subgroups $K_i \le G$, indexed by $i$, is a **coset partition** of $G$ when every element of $G$ lies in exactly one of them; equivalently the cosets are pairwise disjoint and cover $G$. These are the objects of the Herzog-Schönheim conjecture and, for $G = \mathbb{Z}$, the exact covering systems of the integers.
--
--   Attached to a finite family $K_1,\dots,K_t$ of subgroups of a finite group $G$ is the **modulus**
--   $$ l \;=\; \frac{|G|}{\gcd\!\left(|K_1|,\dots,|K_t|\right)}, $$
--   the quantity in terms of which the multiplicity bound of Berger, Felzenbaum and Fraenkel is stated.
--
--   **Formalization note.** Membership in the coset $a_i K_i$ is expressed as $(a_i)^{-1}x \in K_i$, and the partition condition is a `∃!` over the index type, which encodes disjointness and covering at once. The family is an indexed family rather than a set of cosets, so repetitions among the $K_i$ remain visible; this matters because the conclusion of the main theorem counts indices, not distinct subgroups. The gcd is taken over `Finset.univ` of the index type `Fin t`, and the division is natural-number division (exact here, since the gcd divides $|G|$).
--
--   A further note on boundary behaviour: uniqueness is uniqueness of the *index* $i$, so a family that repeats a coset (equal $K_i$ and equal $a_i$ at two different indices) does **not** satisfy the predicate, which is the intended reading of "partition". The index type is unconstrained, so it may be infinite; if it is empty the predicate is false rather than vacuously true, since $G$ is nonempty. For $t = 0$ the modulus degenerates to $0$, the gcd over an empty family being $0$; all statements that use it assume $t > 1$.
-- source:
--   Berger--Felzenbaum--Fraenkel 1987, Remark on the multiplicity of a partition of a group into cosets, Fund. Math. 128 (1987) 139-144, https://doi.org/10.4064/fm-128-3-139-144, p. 140 (statement of the Herzog-Schönheim conjecture) and p. 139, eq. (4) (the quantity $l$)

import Mathlib

namespace BFFPyramidal

/-- A family of left cosets `a i • K i`, indexed by `i : ι`, **partitions** the group `G`:
every element of `G` lies in exactly one of them. -/
def IsCosetPartition {G : Type*} [Group G] {ι : Type*}
    (K : ι → Subgroup G) (a : ι → G) : Prop :=
  ∀ x : G, ∃! i : ι, (a i)⁻¹ * x ∈ K i

/-- The quantity `l = |G| / gcd (|K i| : i)` attached to a finite family of subgroups;
equation (4) of Berger–Felzenbaum–Fraenkel. -/
noncomputable def modulus {G : Type*} [Group G] [Finite G] {t : ℕ}
    (K : Fin t → Subgroup G) : ℕ :=
  Nat.card G / (Finset.univ.gcd fun i => Nat.card (K i))

end BFFPyramidal


