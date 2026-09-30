-- Prove2me | Definitions.Def_TauCeti_FieldTheory_Galois_Abelian
-- name    : TauCeti_FieldTheory_Galois_Abelian
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:31:30.419122+00:00
-- url     : https://prove2.me/theorems/d455dd4e-5f7a-4ed4-8a5b-421fcabb9e37
-- title:
--   Commutativity of Galois groups
-- statement:
--   For a field extension $L/K$, a Galois group with commuting automorphisms carries a commutative group structure. This makes the abelian-group operations available for its characters and Artin map.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/FieldTheory/Galois/Abelian.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/FieldTheory/Galois/Abelian.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.FieldTheory.Galois.Abelian

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Commutativity of Galois groups

Mathlib carries abelianness of a Galois extension as the class `IsAbelianGalois`, and its
instance `IsAbelianGalois K K'` for an intermediate field `K'` says that every subextension of an
abelian extension is again abelian. A construction whose ambient group is the Galois group of a
*general* extension cannot ask for that class, since a bundled commutative structure on
`Gal(L/K)` would be an assumption about `L/K`; it carries commutativity as a hypothesis
`∀ σ τ : Gal(L/K), Commute σ τ` instead. This file reads Mathlib's instance in that unbundled
form. The same hypothesis supplies the scoped `IsMulCommutative` instance used by constructions
that need Mathlib's bundled commutativity API, and it passes to every field in a tower under `L`.

## Main results

* `TauCeti.isMulCommutative_galoisGroup_of_commute`
* `TauCeti.commute_of_tower`
-/

 section

namespace TauCeti

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]

omit [IsGalois K L] in
/-- An explicit proof that a Galois group is commutative supplies Mathlib's bundled
`IsMulCommutative` structure on that group. -/
theorem isMulCommutative_galoisGroup_of_commute
    (hab : ∀ σ τ : L ≃ₐ[K] L, Commute σ τ) : IsMulCommutative (L ≃ₐ[K] L) :=
  .of_comm fun σ τ ↦ (hab σ τ).eq



end TauCeti

end
end


