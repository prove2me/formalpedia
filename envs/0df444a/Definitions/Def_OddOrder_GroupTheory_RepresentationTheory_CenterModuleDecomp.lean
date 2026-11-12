-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CenterModuleDecomp
-- name    : OddOrder_GroupTheory_RepresentationTheory_CenterModuleDecomp
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:44:28.506466+00:00
-- url     : https://prove2.me/theorems/ce176dab-4420-4772-958f-b67567a05c96
-- title:
--   Isotypic decomposition of a representation via the central idempotents (Peterfalvi (9.1))
-- statement:
--   Given a splitting of $Z(k[U])$ with $(\mathrm{Fin}\,N\to k)$ over an algebraically closed field with $\mathrm{char}\nmid|U|$, the standard idempotents pull back to the primitive central idempotents. Their images under the algebra map of any representation $\rho$ are the isotypic projections of $W$, and they give an internal direct sum decomposition of $W$ (`isInternal_centerProj`), the input needed by the free-orbit count ($\dagger$).
--
--   The main declaration: `centerProj`.
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/CenterModuleDecomp.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CenterModuleDecomp.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_IdempotentDirectSum
import Mathlib.RepresentationTheory.Basic

namespace OddOrder.GroupTheory.CenterModuleDecomp

open Representation MonoidAlgebra

variable {k U : Type*} [Field k] [Group U] {N : ℕ}
  (φ : Subalgebra.center k (MonoidAlgebra k U) ≃ₐ[k] (Fin N → k))
  {W : Type*} [AddCommGroup W] [Module k W] (ρ : Representation k U W)

/-- The isotypic projection of `W` onto the `i`-th simple, `π i = asAlgebraHom ρ ε_i` where
`ε_i = φ.symm (Pi.single i 1)` is the `i`-th primitive central idempotent of `Z(k[U])`. -/
noncomputable def centerProj (i : Fin N) : Module.End k W :=
  asAlgebraHom ρ ((Subalgebra.center k (MonoidAlgebra k U)).val (φ.symm (Pi.single i 1)))

/-- The isotypic projections form a complete orthogonal family of idempotent endomorphisms: they are
the image of the standard idempotents `Pi.single i 1` under the algebra (hence ring) homomorphism
`asAlgebraHom ρ ∘ val ∘ φ.symm`. -/
theorem completeOrthogonalIdempotents_centerProj :
    CompleteOrthogonalIdempotents (centerProj φ ρ) := by
  let g : (Fin N → k) →ₐ[k] Module.End k W :=
    (asAlgebraHom ρ).comp ((Subalgebra.center k (MonoidAlgebra k U)).val.comp
      (φ.symm : (Fin N → k) →ₐ[k] Subalgebra.center k (MonoidAlgebra k U)))
  have h := (CompleteOrthogonalIdempotents.single (fun _ : Fin N => k)).map (f := g.toRingHom)
  exact h

/-- **I-2: isotypic decomposition.**  Any representation `ρ : Representation k U W` is the
internal direct sum of the isotypic components `range (centerProj φ ρ i)`. -/
theorem isInternal_centerProj :
    DirectSum.IsInternal (fun i : Fin N => LinearMap.range (centerProj φ ρ i)) :=
  IdempotentDirectSum.isInternal_range_of_completeOrthogonalIdempotents
    (completeOrthogonalIdempotents_centerProj φ ρ)

end OddOrder.GroupTheory.CenterModuleDecomp


