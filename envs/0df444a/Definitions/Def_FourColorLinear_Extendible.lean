-- Prove2me | Definitions.Def_FourColorLinear_Extendible
-- name    : FourColorLinear_Extendible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:55:57.335279+00:00
-- url     : https://prove2.me/theorems/357e219f-ba6c-4988-9d56-8f5270021a74
-- title:
--   $i$-extendible ring colorings, the reducibility level and D-reducibility
-- statement:
--   A coloring $\kappa$ of the ring of a configuration is **$0$-extendible** if it extends to a coloring of the free completion $\hat Z$. For $i>0$ it is **$i$-extendible** if it is $(i-1)$-extendible, or if for every plane graph $G'$ containing the ring as a facial closed walk and every proper coloring $\bar\psi$ of $G'$ extending $\kappa$, some Kempe change of $\bar\psi$ yields an $(i-1)$-extendible coloring on the ring.
--
--   The **level** of $\kappa$ is the least such $i$. A configuration is **$D_i$-reducible** if every coloring of its ring is $i$-extendible, and **D-reducible** if it is $D_i$-reducible for some $i$. These are the fine invariants behind the 25 rounds of Kempe changes: an improving change lowers the level of a ring.
--
--   **Formalization Note** The ring in $G'$ is a closed walk along one face of length $|R|$ of a connected plane graph, not required to be injective on vertices. p.4 says "facial cycle", while p.3 allows ring identifications and the proof of Lemma 4 applies the definition to $G-V(Z)$. The printed case is an injective walk. As the level is an infimum, comparisons are used only for D-reducible configurations.
-- source:
--   Inoue, Kawarabayashi, Miyashita, Mohar, Thomassen, Thorup, Four-Coloring Planar Graphs in Linear Time, arXiv:2610.39753 (held version, sha256 4dce39c5…), §1.1, p.4

import Mathlib
import Definitions.Def_FourColorLinear_Config

open PlanarQueue.Genus

namespace FourColorLinear

/-- A host of a ring of size `R` (arXiv:2610.39753, held version, sha256 4dce39c5…, p.4): "an
arbitrary plane graph containing the ring R as a facial cycle".

**Formalization Note** The ring is a closed walk along one face of length `R` of a connected plane
graph, which need not be injective on vertices. The printed case is an injective `walk`. p.3 allows
identifications ("this homomorphism may not be 1-1 on R(Z)"), and the proof of Lemma 4, p.7, applies
the definition to `G − V(Z)`, whose hole is such a walk. Connectivity loses nothing: other components
meet no Kempe chain of the ring. The orientation of the walk loses nothing either, since reflecting
the rotation of `G'` reverses it and leaves all Kempe chains as they are. -/
structure RingHost (R : ℕ) where
  /-- number of vertices -/
  m : ℕ
  /-- the graph `G'` -/
  G : SimpleGraph (Fin m)
  [dec : DecidableRel G.Adj]
  /-- its plane embedding -/
  S : EmbeddingScheme G
  plane : IsPlaneScheme S
  conn : G.Connected
  /-- the ring, as a facial walk -/
  walk : Fin R → G.Dart
  walk_next : ∀ i, faceNext S (walk i) = walk (finRotate R i)
  walk_inj : Function.Injective walk

attribute [instance] RingHost.dec

namespace Config

/-- `i`-extendibility of a ring coloring (p.4): "We say that a coloring ψ of R is 0-extendible …
to Z if it can be extended to a coloring of Ẑ. For each integer i > 0 we say that ψ is i-extendible
to Z if it is either (i − 1)-extendible or the following holds: If G′ is an arbitrary plane graph
containing the ring R as a facial cycle and ψ̄ is any 4-coloring of G′ extending ψ, then there is a
Kempe change of ψ̄ such that the resulting 4-coloring on R after making the Kempe change is an
(i − 1)-extendible 4-coloring of R." -/
def Extendible (C : Config) : ℕ → (Fin C.R → Fin 4) → Prop
  | 0, κ => ∃ χ : Fin C.N → Fin 4, ProperOn C.G Set.univ χ ∧ ∀ i, χ (C.ring i) = κ i
  | i + 1, κ =>
      Extendible C i κ ∨
        ∀ (H : RingHost C.R) (ψ : Fin H.m → Fin 4), ProperOn H.G Set.univ ψ →
          (∀ j, ψ (H.walk j).fst = κ j) →
            ∃ ψ', IsKempeChangeOn H.G Set.univ ψ ψ' ∧
              Extendible C i fun j => ψ' (H.walk j).fst

/-- The reducibility level (p.4), "the minimum i such that ψ is i-extendible".

**Formalization Note** `sInf ∅ = 0` in `ℕ`, so a comparison of levels is meaningful only for a
D-reducible configuration, which is a hypothesis wherever `Level` is compared. -/
noncomputable def Level (C : Config) (κ : Fin C.R → Fin 4) : ℕ := sInf {i | C.Extendible i κ}

/-- `D_i`-reducible (p.4): "every 4-coloring of its ring is i-extendible". -/
def DiReducible (C : Config) (i : ℕ) : Prop :=
  ∀ κ, C.IsRingColoring κ → C.Extendible i κ

/-- D-reducible (p.4): "D_i-reducible for some finite i". -/
def DReducible (C : Config) : Prop := ∃ i, C.DiReducible i

end Config

end FourColorLinear


