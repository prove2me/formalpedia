-- Prove2me | Definitions.Def_TC433_LinearAlgebra_Matrix_GeneralLinearGroup_Symplectic_Generation_4f0d101b17
-- name    : TC433_LinearAlgebra_Matrix_GeneralLinearGroup_Symplectic_Generation_4f0d101b17
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:37:22.765396+00:00
-- url     : https://prove2.me/theorems/623fc82b-b0a9-4931-9c73-36c8915338c7
-- title:
--   TauCeti: LinearAlgebra / Matrix / GeneralLinearGroup / Symplectic / Generation
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Generation for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/Symplectic/Generation.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Definitions.Def_TC433_LinearAlgebra_Matrix_GeneralLinearGroup_Symplectic_ChevalleyRelations_985093fc45
import Definitions.Def_TC433_GroupTheory_Commutator_3a22f3596c

/-!
# Generating the difference-root subgroups of the symplectic group

For the standard type-`C_m` root system, the roots `eᵢ - eⱼ` form its type-`A_(m-1)`
subsystem, whose structure-constant-one Chevalley relation is

```text
⁅x_{eᵢ-eⱼ}(a), x_{eⱼ-eₖ}(b)⁆ = x_{eᵢ-eₖ}(ab)
```

This file uses it to show that a subgroup containing the difference-root elements at adjacent
indices, in both orientations, contains every difference-root element. This is the first generation
step for identifying the full-weight type-`C` Chevalley carrier with the standard symplectic group:
the numbered short simple roots are adjacent difference roots, while the remaining simple root is
long.

## Main results

* `TauCeti.GLSymplecticFin.differenceShortRootUnit_mem_of_adjacent`: adjacent difference-root
  subgroups generate all difference-root subgroups.

## References

* R. W. Carter, *Simple Groups of Lie Type* (1972), §5.2.
* R. Steinberg, *Lectures on Chevalley Groups* (1968), §§3--4.

This advances Layer 9, "The Chevalley--Demazure construction", of
`TauCetiRoadmap/ReductiveGroups/README.md`: it supplies the type-`A` subsystem generation needed
to identify the explicit full-weight type-`C` carrier on field-valued points.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

open Matrix
open scoped commutatorElement

namespace TauCeti.GLSymplecticFin

universe u

variable {R : Type u} [CommRing R] {m : ℕ} {i j : Fin m}

/-- If a subgroup of the standard symplectic group contains every adjacent difference-root
element in both orientations, then it contains every difference-root element. -/
theorem differenceShortRootUnit_mem_of_adjacent
    (H : Subgroup (GLSymplecticFin m R))
    (hadjacent : ∀ {i j : Fin m} (hij : i ≠ j) (c : R),
      i.val + 1 = j.val ∨ j.val + 1 = i.val → differenceShortRootUnit hij c ∈ H)
    {i j : Fin m} (hij : i ≠ j) (c : R) :
    differenceShortRootUnit hij c ∈ H := by
  exact Subgroup.mem_of_adjacent_of_commutator H
    (fun hij c => differenceShortRootUnit hij c)
    (fun hij hjk hik a => by
      simpa using
        commutatorElement_differenceShortRootUnit_differenceShortRootUnit hij hjk hik a 1)
    hadjacent hij c

end TauCeti.GLSymplecticFin


