-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_ToSigmaAddFstZeroFst
-- name    : ReciprocityTheory_DualLattices_ToSigmaAddFstZeroFst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:44.600554+00:00
-- url     : https://prove2.me/theorems/d817283f-f855-4354-aa65-a2499ad62e40
-- title:
--   To Sigma Add Fst Zero Fst
-- statement:
--   Definitions and structural lemmas for To Sigma Add Fst Zero Fst, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ToSigmaAddFstZeroFst.lean

import Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
namespace BX
def tot (B : BX R₀) {R : LAlg R₀} {x y : B.G R} (u : B.P R x y) : Σ x y : B.G R, B.P R x y :=
  ⟨x, y, u⟩
def tmap (B : BX R₀) {R S : LAlg R₀} (f : LHom R S) (t : Σ x y : B.G R, B.P R x y) :
    Σ x y : B.G S, B.P S x y :=
  ⟨B.map f t.1, B.map f t.2.1, B.pmap f t.2.2⟩
variable {B : BX R₀} {R S T : LAlg R₀}
end BX
end ReciprocityTheory.PGsh


