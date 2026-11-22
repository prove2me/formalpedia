-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_ExistsStrictHenselianAbsolutelyClosedLocalRing
-- name    : Formalism_LocalToGlobal_IndefiniteReal_ExistsStrictHenselianAbsolutelyClosedLocalRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:58.618604+00:00
-- url     : https://prove2.me/theorems/ad966b09-6ba5-461f-bf19-ac244c9b2abf
-- title:
--   Exists Strict Henselian Absolutely Closed Local Ring
-- statement:
--   Definitions and structural lemmas for Exists Strict Henselian Absolutely Closed Local Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/ExistsStrictHenselianAbsolutelyClosedLocalRing.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Lemmata_RankOneOrbitForms_RankOneForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
namespace Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
namespace NormTraceLemmas
section Lin
variable {K : Type} [Field K] {G : Type} [Group G]
  {T : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
end Lin
section Char
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
  {T : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
variable [NumberField K]
end Char
section Alg
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
open Classical in

def epA (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) : MonoidAlgebra K G :=
  ((Nat.card H : ℕ) : K)⁻¹ •
    ∑ h : H, MonoidAlgebra.single (h : G) ((((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K))
def eA {T : Type} [AddCommGroup T] [Module K T] (τ : Representation K G T) : MonoidAlgebra K G :=
  (charOf τ 1 / (Fintype.card G : K)) • ∑ x : G, MonoidAlgebra.single x (charOf τ x⁻¹)
end Alg
end NormTraceLemmas
end Formalism.IndefR.LatticeTransfer


