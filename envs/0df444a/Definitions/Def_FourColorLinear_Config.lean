-- Prove2me | Definitions.Def_FourColorLinear_Config
-- name    : FourColorLinear_Config
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:54:46.028235+00:00
-- url     : https://prove2.me/theorems/cf2d0132-1b59-412d-b21f-a26cb81f369d
-- title:
--   Configurations, carried as their free completions
-- statement:
--   A **configuration** $(Z,\delta)$ is a near-triangulation $Z$ with a degree function $\delta$, where $\delta(v)=d_Z(v)$ off the boundary, $\delta(v)>d_Z(v)$ on it, and $\delta(v)=d_Z(v)+2$ at a cut-vertex. Its **free completion** $\hat Z$ adds a cycle $R$, the **ring**, disjoint from $Z$, as the outer face of a near-triangulation that contains $(Z,\delta)$.
--
--   The free completion determines $(Z,\delta)$ and conversely, so this definition carries $\hat Z$ itself: a connected plane graph with a chordless facial cycle $R$ of length at least $3$, all other faces triangles, $Z=\hat Z-R$ connected and nonempty, every ring vertex adjacent to $Z$, and the cut-vertex clause. The degree $\delta$ is the degree in $\hat Z$.
--
--   A **coloring of the ring** is a proper coloring of the cycle $R$. Two configurations are identified under a rotation-preserving isomorphism of free completions that carries ring to ring.
-- source:
--   Inoue, Kawarabayashi, Miyashita, Mohar, Thomassen, Thorup, Four-Coloring Planar Graphs in Linear Time, arXiv:2610.39753 (held version, sha256 4dce39c5…), §1.1, p.3

import Mathlib
import Definitions.Def_FourColorLinear_FaceOf
import Definitions.Def_FourColorLinear_IsKempeChangeOn

open PlanarQueue.Genus

namespace FourColorLinear

/-- A configuration (arXiv:2610.39753, held version, sha256 4dce39c5…, p.3), carried as its free
completion: "the near-triangulation Ẑ obtained from Z by adding a cycle R = R(Z), disjoint from Z and
joining vertices on the outer face of Z to R in such a way that R becomes the outer face of the
near-triangulation Ẑ and such that Ẑ contains (Z, δ)."

**Formalization Note** p.3 determines `Ẑ` from `(Z, δ)` and conversely `Z := Ẑ − R`, `δ := d_Ẑ` on
`Z`, so this is the same object, with the ring as data. `ringDart` is the outer facial walk, of length
`R ≥ 3`, a chordless cycle; every other face is a triangle. The clause "δ(v) > d_Z(v) on the
boundary" follows: a boundary vertex with no ring neighbour would have all its corners on triangles
of `Z`. The cut-vertex clause of p.3 is `cut_vertex`. -/
structure Config where
  /-- number of vertices of the free completion -/
  N : ℕ
  /-- the free completion `Ẑ` -/
  G : SimpleGraph (Fin N)
  [dec : DecidableRel G.Adj]
  /-- its plane embedding -/
  S : EmbeddingScheme G
  plane : IsPlaneScheme S
  conn : G.Connected
  /-- the ring size `|R|` -/
  R : ℕ
  three_le_R : 3 ≤ R
  /-- the ring, as the outer facial walk -/
  ringDart : Fin R → G.Dart
  ring_next : ∀ i, faceNext S (ringDart i) = ringDart (finRotate R i)
  ring_inj : Function.Injective fun i => (ringDart i).fst
  ring_chordless : ∀ i j, G.Adj (ringDart i).fst (ringDart j).fst →
    j = finRotate R i ∨ i = finRotate R j
  /-- all other faces are triangles -/
  triangles : ∀ d, d ∉ Set.range ringDart → (faceNext S)^[3] d = d
  /-- `Z = Ẑ − R` is connected, in particular nonempty -/
  Z_conn : (G.induce {v | ∀ i, v ≠ (ringDart i).fst}).Connected
  /-- each ring vertex is joined to `Z` -/
  ring_adj : ∀ i, ∃ z, (∀ j, z ≠ (ringDart j).fst) ∧ G.Adj (ringDart i).fst z
  /-- p.3: "if v is a cut-vertex of Z, then δ(v) = d_Z(v) + 2" -/
  cut_vertex : ∀ v, (∀ j, v ≠ (ringDart j).fst) →
    ¬ (G.induce ({u | ∀ i, u ≠ (ringDart i).fst} \ {v})).Preconnected →
      ((G.neighborFinset v).filter fun u => ∃ j, u = (ringDart j).fst).card = 2

attribute [instance] Config.dec

namespace Config

/-- The ring vertex with index `i`. -/
def ring (C : Config) (i : Fin C.R) : Fin C.N := (C.ringDart i).fst

/-- The vertex set of `Z`. -/
def Z (C : Config) : Set (Fin C.N) := {v | ∀ i, v ≠ C.ring i}

/-- A coloring of the ring (p.4), a proper coloring of the cycle `R`. -/
def IsRingColoring (C : Config) (κ : Fin C.R → Fin 4) : Prop :=
  ∀ i, κ i ≠ κ (finRotate C.R i)

end Config

/-- Isomorphism of configurations: a rotation-preserving isomorphism of free completions carrying
ring to ring. Two members of the set of Theorem 3 of p.5 are distinct up to this relation. -/
def ConfigIso (C C' : Config) : Prop :=
  ∃ e : C.G ≃g C'.G,
    (∀ z, z ∈ C.Z ↔ e z ∈ C'.Z) ∧
      ∀ d : C.G.Dart, e.toHom.mapDart (C.S.rot d) = C'.S.rot (e.toHom.mapDart d)

end FourColorLinear


