-- Prove2me | Definitions.Def_CGWH_SteenrodCompactlyGenerated
-- name    : CGWH_SteenrodCompactlyGenerated
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T15:22:05.936837+00:00
-- url     : https://prove2.me/theorems/85c4e4bf-4cce-4a05-b6e8-df1c14a9302d
-- title:
--   Steenrod compactly generated spaces (topology coherent with the compact Hausdorff subspaces)
-- statement:
--   Definition of a Steenrod compactly generated space: a topological space whose topology is determined by its compact Hausdorff subspaces.
--
--   Let $X$ be a topological space. A *compact Hausdorff subspace* of $X$ is a subset $K\subseteq X$ that is compact and that is a Hausdorff space for the subspace topology (no condition on $X$ itself, and $K$ is not required to be closed in $X$).
--
--   **Definition** (`CGWH.SteenrodCompactlyGeneratedSpace X`). The space $X$ is *Steenrod compactly generated* if for every subset $U\subseteq X$
--   $$U\text{ is open in }X\iff\text{for every compact Hausdorff subspace }K\subseteq X,\ \ U\cap K\text{ is open in }K .$$
--   The implication from left to right holds in every topological space, so the condition is that a subset whose trace on every compact Hausdorff subspace is (relatively) open is open.
--
--   This is one of three notions of compact generation that the paper compares in its Section E.2.4: *compactly generated* spaces (the notion used throughout the paper and in Mathlib's `CompactlyGeneratedSpace`: a subset is open as soon as its preimage under every continuous map from a compact Hausdorff space is open), *Kelley compactly generated* spaces (the same condition as above with all compact subspaces $K$, Mathlib's `CompactlyCoherentSpace`) and Steenrod compactly generated spaces. Every Steenrod compactly generated space is compactly generated and every compactly generated space is Kelley compactly generated; the three notions agree for Hausdorff spaces, and the Sierpiński space is compactly generated without being Steenrod compactly generated. The definition is the setting of Steenrod's convenient category of compactly generated Hausdorff spaces, to which the paper contrasts its category of compactly generated weakly Hausdorff spaces.
--
--   **Formalization Note.** The class `CGWH.SteenrodCompactlyGeneratedSpace X` (for `X : Type*` with a topology) has the single field `isOpen_of_forall_isOpen_preimage_val`: for every `U : Set X`, if for every `K : Set X` with `IsCompact K` and `T2Space K` (the subtype `K` with its subspace topology is Hausdorff) the set `Subtype.val ⁻¹' U : Set K` is open, then `U` is open. Only the non-trivial implication is recorded. The file imports Mathlib only.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 865, Definition E.2.4.1(2)

import Mathlib

/-!
# Steenrod compactly generated spaces

A topological space is *Steenrod compactly generated* if its topology is coherent with the family of
its compact Hausdorff subspaces. This is one of the three notions of "compactly generated space"
compared in the literature:

* Mathlib's `CompactlyGeneratedSpace X` : the topology of `X` is coinduced by all continuous maps
  from compact Hausdorff spaces to `X` (no separation axiom);
* Mathlib's `CompactlyCoherentSpace X` ("Kelley compactly generated") : a subset `U` of `X` is open
  as soon as `U ∩ K` is open in `K` for every compact subspace `K` of `X`;
* `CGWH.SteenrodCompactlyGeneratedSpace X` (this file) : a subset `U` of `X` is open as soon as
  `U ∩ K` is open in `K` for every compact *Hausdorff* subspace `K` of `X`.

Source: A. M. Masullo, *The Music of the Primes*, Definition E.2.4.1(2). The name refers to
N. E. Steenrod, *A convenient category of topological spaces*, which the paper cites for the
category of compactly generated Hausdorff spaces.
-/

namespace CGWH

/-- A topological space `X` is *Steenrod compactly generated* if a subset `U ⊆ X` is open as soon
as, for every compact Hausdorff subspace `K ⊆ X`, the trace `U ∩ K` is open in `K` (for the subspace
topology of `K`). The converse implication holds in every topological space, so this says that
`U` is open if and only if all these traces are open. -/
class SteenrodCompactlyGeneratedSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- A set whose trace on every compact Hausdorff subspace is open is open. -/
  isOpen_of_forall_isOpen_preimage_val : ∀ U : Set X,
    (∀ K : Set X, IsCompact K → T2Space K → IsOpen (Subtype.val ⁻¹' U : Set K)) → IsOpen U

end CGWH


