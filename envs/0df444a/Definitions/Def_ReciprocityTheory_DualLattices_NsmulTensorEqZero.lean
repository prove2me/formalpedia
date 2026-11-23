-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_NsmulTensorEqZero
-- name    : ReciprocityTheory_DualLattices_NsmulTensorEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:27.65781+00:00
-- url     : https://prove2.me/theorems/7f21786d-96d7-41cf-b52d-cadf3740875e
-- title:
--   Nsmul Tensor Eq Zero
-- statement:
--   Definitions and structural lemmas for Nsmul Tensor Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NsmulTensorEqZero.lean

import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
namespace ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
namespace BX
variable (B : BX R₀) {R : LAlg R₀} (Dp : DualPair R)
def HtC (N : ℕ) (y : B.G R) (x : B.G Dp.D) (E : (Dp.D : Type u)) : Prop :=
  ∃ v : B.P Dp.D x (B.map Dp.σ y), HEq (B.pmap Dp.π v) (B.zero1 y) ∧
    HEq (B.nsmul1 v N) (B.zero1 (B.map Dp.σ y)) ∧
    ∃ c : (Dp.D : Type u)ˣ, (c : (Dp.D : Type u)) = 1 - E ∧
      HEq (B.nsmul2 v N) (B.smul c (B.zero2 x))
end BX
end ReciprocityTheory.PGsh


