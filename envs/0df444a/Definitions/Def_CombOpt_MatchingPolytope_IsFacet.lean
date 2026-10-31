-- Prove2me | Definitions.Def_CombOpt_MatchingPolytope_IsFacet
-- name    : CombOpt_MatchingPolytope_IsFacet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:08:10.371547+00:00
-- url     : https://prove2.me/theorems/9a6f0409-ceb0-4042-a955-58922e208f2c
-- title:
--   A facet: a maximal proper face
-- statement:
--   A **facet** of a polyhedron $P$ is a maximal proper face: a proper face $F$ of $P$ such that every proper face $G$ of $P$ with $F\subseteq G$ equals $F$.
--
--   Facets are the faces that every defining system of $P$ must represent (Corollary 6.19).
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.3, p. 212 (PDF p. 220)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_IsProperFace

namespace CombOpt.MatchingPolytope

/-- **A facet.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.3, p. 212 (PDF p. 220): "A maximal proper face of a polyhedron is called a facet."

`IsFacet P F` says that `F` is a proper face of `P` contained in no other proper face. -/
def IsFacet {ι : Type*} [Fintype ι] (P F : Set (ι → ℝ)) : Prop :=
  IsProperFace P F ∧ ∀ G : Set (ι → ℝ), IsProperFace P G → F ⊆ G → G = F

end CombOpt.MatchingPolytope


