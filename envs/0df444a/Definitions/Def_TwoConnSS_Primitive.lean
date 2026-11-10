-- Prove2me | Definitions.Def_TwoConnSS_Primitive
-- name    : TwoConnSS_Primitive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:44.459619+00:00
-- url     : https://prove2.me/theorems/e64702de-273e-4f9d-88e7-d275e704f5f5
-- title:
--   Primitive 4-cycle components
-- statement:
--   A 4-cycle component of a cover $S$ is **primitive** if it is an unchanged 4-cycle component of the initial cover $S_0$: the same four vertices with the same four edges. `Primitive S₀ S` says that every 4-cycle component of $S$ is primitive.
--
--   Both algorithms maintain this, so the exclusion of spanning 8-cycles achieved by the initial merging persists for every surviving 4-cycle.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), §8.1.1, p.35

import Mathlib
import Definitions.Def_TwoConnSS_blocks

namespace TwoConnSS

open Classical

variable {V : Type*} [Fintype V]

/-- **Every 4-cycle component of `S` is primitive.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), §8.1.1, p.35: "A 4-cycle component
is primitive if it is an unchanged 4-cycle component of the initial cover S0. Our exchanges maintain
that every 4-cycle component is primitive."

**Formalization Note.** "Unchanged" is read as: same vertex set and same four edges. -/
def Primitive (S₀ S : Finset (Sym2 V)) : Prop :=
  ∀ C, IsCycleComp S C 4 → IsCycleComp S₀ C 4 ∧ edgesIn S C = edgesIn S₀ C

end TwoConnSS


