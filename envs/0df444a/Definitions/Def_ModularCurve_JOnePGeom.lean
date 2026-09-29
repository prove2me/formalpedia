-- Prove2me | Definitions.Def_ModularCurve_JOnePGeom
-- name    : ModularCurve_JOnePGeom
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/dcb977ce-45db-5f11-b9b6-04099af58f48
-- title:
--   Abstract points-level Néron special fibre of J1​(p;M)
-- statement:
--   For a natural number $p$, the module introduces a single structure, [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](../def/ModularCurve_JOnePGeom.html#L9), living in `Type 1` because it quantifies over carrier types. An inhabitant of it is exactly the following data: a type `J0s` with an additive commutative group structure; an additive subgroup `torus` of `J0s`; two further types `JI` and `JE`, each with an additive commutative group structure; an additive group homomorphism `proj : J0s →+ JI × JE`; a proof that `proj` is surjective; and a proof that the kernel of `proj` is precisely the subgroup `torus`. The group structures on the three carriers are registered as instances, so the carriers may be used as abelian groups wherever an inhabitant of the structure is fixed. Mathematically, therefore, an element of this structure is nothing more and nothing less than a short exact sequence of abelian groups
--   $$0 \longrightarrow T \longrightarrow J \longrightarrow J_I \times J_E \longrightarrow 0,$$
--   with $T$ given as a subgroup of $J$ and the surjection and the identification of the kernel carried as fields rather than proved. The names record the intended reading: $J$ is the group of geometric points of the identity component of the special fibre at $p$ of the Néron model of the Jacobian of the relevant modular curve of level divisible by $p$, $T$ is its toric part, and $J_I$, $J_E$ are the Jacobians of the two Igusa components of the special fibre, `proj` being restriction (pull-back of line bundles) to those two components. The parameter $p$ records the prime at which the fibre is taken and indexes the structure; no modular curve, Néron model, Jacobian or scheme is constructed, and all of the geometry is abstracted into the above group-theoretic data, so downstream statements are conditional on being given such a package.
--
--   **Relation to Mathlib.** Mathlib has no notion of Néron models, special fibres of Jacobians, or Igusa curves; this structure is the project's own abstraction, and it is assembled purely from Mathlib's `AddCommGroup`, `AddSubgroup` and `AddMonoidHom` (kernel and surjectivity).
--
--   **Where it is used.** This package is the geometric input for the level-lowering step at $p$: statements about the component group and the toric part of the special fibre of $J_1(p;M)$, and the comparison of that fibre with the Igusa curves, are formulated relative to a given inhabitant of it, with the Hecke, diamond and inertia operators supplied by a companion operator-level structure defined over such an inhabitant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JOnePGeom.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace ModularCurve

namespace JOneP

structure NeronSpecialFibreGeom (p : ℕ) : Type 1 where

  J0s : Type
  [instJ0s : AddCommGroup J0s]

  torus : AddSubgroup J0s

  JI : Type
  [instJI : AddCommGroup JI]
  JE : Type
  [instJE : AddCommGroup JE]

  proj : J0s →+ JI × JE
  proj_surjective : Function.Surjective proj
  ker_proj : proj.ker = torus

attribute [instance] NeronSpecialFibreGeom.instJ0s NeronSpecialFibreGeom.instJI NeronSpecialFibreGeom.instJE

end JOneP

end ModularCurve


