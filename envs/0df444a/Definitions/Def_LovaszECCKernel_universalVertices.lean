-- Prove2me | Definitions.Def_LovaszECCKernel_universalVertices
-- name    : LovaszECCKernel_universalVertices
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:55:29.606257+00:00
-- url     : https://prove2.me/theorems/d2aad88b-a15d-4030-ab7f-2fa2cbd16cb1
-- title:
--   Universal vertices
-- statement:
--   A vertex $v$ of a graph $G$ is **universal** if it is adjacent to every other vertex. Lemma 8 assumes at most one universal vertex, and Reduction Rule 4 removes all but one.
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), Lemma 8, p.38, and Reduction Rule 4, p.41 (= PDF pp.38, 41)

import Mathlib

set_option autoImplicit false

namespace LovaszECCKernel

open Classical in
/-- The set of **universal vertices** of a graph (Fomin, Golovach, Khargeliia, Sagunov, Simonov, *Stability Meets
Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems*, STOC 2027
submission (manuscript sha256 a9d53ab8…), Lemma 8, p.38, and Reduction Rule 4, p.41 (= PDF pp.38, 41)): the vertices
adjacent to every other vertex.

**Formalization Note** `v` is universal iff `G.Adj v u` for every `u ≠ v`. -/
noncomputable def universalVertices {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter (fun v => ∀ u, u ≠ v → G.Adj v u)

end LovaszECCKernel


