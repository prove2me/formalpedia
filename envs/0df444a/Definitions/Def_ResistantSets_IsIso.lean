-- Prove2me | Definitions.Def_ResistantSets_IsIso
-- name    : ResistantSets_IsIso
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:26:10.556523+00:00
-- url     : https://prove2.me/theorems/7e6fa992-f3fe-48f7-b722-b745e8c4ffa9
-- title:
--   Isomorphism of subsets of the cube (twisting and relabeling)
-- statement:
--   Two sets $S\subseteq\{0,1\}^n$ and $T\subseteq\{0,1\}^m$ are **isomorphic**, $S\cong T$, if one is obtained from the other after twisting and relabeling some coordinates: there are a bijection $e:[n]\to[m]$ of coordinates and a point $t\in\{0,1\}^m$ with
--   $$
--   T=\{\,(x\circ e^{-1})\triangle t : x\in S\,\}.
--   $$
--
--   Resistance, polarity and half-density are invariant under isomorphism, and the main theorem classifies sets up to isomorphism.
--
--   **Formalization Note** The relabeling is a bijection, so isomorphic sets have the same dimension. Complementation is not an isomorphism.
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, p.4, §1.1 ("We say that two sets S, S′ are isomorphic … if one is obtained from the other after twisting and relabeling some coordinates")

import Mathlib
import Definitions.Def_ResistantSets_twist

namespace ResistantSets

/-- **Isomorphism** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), §1.1, p.4): "We say that two sets S, S′ are isomorphic, and denote it by
S ≅ S′, if one is obtained from the other after twisting and relabeling some coordinates."

`IsIso S T` holds when `T ⊆ {0,1}ᵐ` is obtained from `S ⊆ {0,1}ⁿ` by a relabeling of
coordinates `e : Fin n ≃ Fin m` followed by a twist by a point `t`:
`T = {(x ∘ e⁻¹) △ t : x ∈ S}`.

**Formalization Note** The relabeling is a bijection, so isomorphic sets have the same dimension
(`n = m`). The relation is symmetric because the inverse of a relabel-and-twist is again one.
Complementation is not an isomorphism. -/
def IsIso {n m : ℕ} (S : Finset (Fin n → Bool)) (T : Finset (Fin m → Bool)) : Prop :=
  ∃ (e : Fin n ≃ Fin m) (t : Fin m → Bool),
    T = S.image (fun x => vxor (fun j => x (e.symm j)) t)

end ResistantSets


