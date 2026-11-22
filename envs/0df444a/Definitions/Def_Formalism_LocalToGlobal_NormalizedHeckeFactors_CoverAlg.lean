-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg
-- name    : Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:50:04.450181+00:00
-- url     : https://prove2.me/theorems/4f5f3fea-1170-4f0f-9683-57983f68cd07
-- title:
--   Cover Alg
-- statement:
--   Definitions and structural lemmas for Cover Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.NCov
open Module Module.End
section Ops
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
end Ops
section Alg
variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
def W (T : Subalgebra O (End K V)) (χ : T → K) : Submodule K V :=
  ⨅ t : T, (t : End K V).maxGenEigenspace (χ t)
def pt {T : Subalgebra O (End K V)} (ψ : T →ₐ[O] O) : T → K := fun t => algebraMap O K (ψ t)
variable [IsLocalRing O]
def cls {T : Subalgebra O (End K V)} (ψ : T →ₐ[O] O) : Ideal T :=
  RingHom.ker ((IsLocalRing.residue O).comp ψ.toRingHom)
def part (T : Subalgebra O (End K V)) (𝔪 : Ideal T) : Submodule K V :=
  ⨆ (ψ : T →ₐ[O] O) (_ : cls ψ = 𝔪), W T (pt ψ)
def off (T : Subalgebra O (End K V)) (𝔪 : Ideal T) : Submodule K V :=
  ⨆ (ψ : T →ₐ[O] O) (_ : cls ψ ≠ 𝔪), W T (pt ψ)
variable {S : Set (End K V)}
end Alg
section Sat
open Polynomial
variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [IsLocalRing O]
  {S : Set (End K V)}
end Sat
end Formalism.L2.NCov


