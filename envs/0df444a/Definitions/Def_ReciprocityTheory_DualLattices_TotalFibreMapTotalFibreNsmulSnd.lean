-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_TotalFibreMapTotalFibreNsmulSnd
-- name    : ReciprocityTheory_DualLattices_TotalFibreMapTotalFibreNsmulSnd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:22.178749+00:00
-- url     : https://prove2.me/theorems/f32c1b55-9b32-4c9a-ae7e-42ca8bdcee09
-- title:
--   Total Fibre Map Total Fibre Nsmul Snd
-- statement:
--   Definitions and structural lemmas for Total Fibre Map Total Fibre Nsmul Snd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TotalFibreMapTotalFibreNsmulSnd.lean

import Definitions.Def_ReciprocityTheory_DualLattices_NsmulTensorEqZero
import Definitions.Def_ReciprocityTheory_DualLattices_SmKerSurj
import Definitions.Def_ReciprocityTheory_DualLattices_TangentPairingStatement
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
variable (B : BX R₀)
abbrev Tot (R : LAlg R₀) : Type u := Σ x y : B.G R, B.P R x y
def Tmap {R S : LAlg R₀} (f : LHom R S) (t : B.Tot R) : B.Tot S :=
  ⟨B.map f t.1, B.map f t.2.1, B.pmap f t.2.2⟩
def Tsw {R : LAlg R₀} (t : B.Tot R) : B.Tot R := ⟨t.2.1, t.1, B.sw t.2.2⟩
def totalFibreNsmulSnd {R : LAlg R₀} (N : ℕ) (t : B.Tot R) : B.Tot R := ⟨t.1, N • t.2.1, B.nsmul2 t.2.2 N⟩
def Tsmul {R : LAlg R₀} (l : (R : Type u)ˣ) (t : B.Tot R) : B.Tot R :=
  ⟨t.1, t.2.1, B.smul l t.2.2⟩
section Fibre
variable {F R₁ R₂ R : LAlg R₀} {p₁ : LHom F R₁} {p₂ : LHom F R₂} {f₁ : LHom R₁ R}
  {f₂ : LHom R₂ R}
end Fibre
end BX
end ReciprocityTheory.PGsh


