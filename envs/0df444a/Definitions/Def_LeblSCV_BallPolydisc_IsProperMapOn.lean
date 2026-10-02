-- Prove2me | Definitions.Def_LeblSCV_BallPolydisc_IsProperMapOn
-- name    : LeblSCV_BallPolydisc_IsProperMapOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:16:53.306297+00:00
-- url     : https://prove2.me/theorems/7c04d318-6f4f-474c-b2e5-fdaf95c4bffa
-- title:
--   Definition 1.4.3 — proper map $f : U \to V$
-- statement:
--   Let $X, Y$ be topological spaces and $U \subset X$, $V \subset Y$ with their subspace topologies. A map $f : U \to V$ is **proper** if it is continuous and, for every compact set $K \subset V$, the preimage
--   $$f^{-1}(K) = \{ x \in U : f(x) \in K \}$$
--   is compact.
--
--   Vaguely, a proper map is one that "takes the boundary to the boundary". A biholomorphism is proper, but so is, for instance, $z \mapsto z^2$ as a map $\mathbb{D} \to \mathbb{D}$; as a map $\mathbb{D} \to \mathbb{C}$ it is not proper, so the codomain matters.
--
--   **Formalization Note.** The map is an ambient function `f : X → Y`; the predicate says that `f` maps `U` into `V`, is continuous on `U`, and that `U ∩ f ⁻¹' K` is compact for every compact `K ⊆ V`. Compactness of a subset in the subspace topology of `U` (resp. `V`) is the same as compactness in `X` (resp. `Y`), so this is exactly the book's definition for the restricted map $U \to V$. It is *not* `IsProperMap` of the ambient function.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 33, Definition 1.4.3

import Mathlib

namespace LeblSCV.BallPolydisc

/-- Definition 1.4.3 (Lebl, p. 33), for a map `f : U → V` between subsets `U ⊆ X`, `V ⊆ Y` with
their subspace topologies: `f` maps `U` into `V`, is continuous on `U`, and the preimage in `U`
of every compact `K ⊆ V` is compact. (A subset of `V` is compact in the subspace topology of `V`
iff it is compact in `Y`, and likewise for `U`.) -/
def IsProperMapOn {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (U : Set X) (V : Set Y) : Prop :=
  Set.MapsTo f U V ∧ ContinuousOn f U ∧
    ∀ K : Set Y, K ⊆ V → IsCompact K → IsCompact (U ∩ f ⁻¹' K)

end LeblSCV.BallPolydisc


