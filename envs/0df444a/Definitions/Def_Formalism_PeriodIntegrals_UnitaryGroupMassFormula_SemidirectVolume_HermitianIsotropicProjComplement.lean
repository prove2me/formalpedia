-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:11:38.041804+00:00
-- url     : https://prove2.me/theorems/eab4e940-1eb9-4842-ad7c-1ee279614c9a
-- title:
--   Hermitian Isotropic Proj Complement
-- statement:
--   Definitions and structural lemmas for Hermitian Isotropic Proj Complement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/HermitianIsotropicProjComplement.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolSemiDirect.W.PG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
namespace Dat
def FixEZ (D : Dat A n r) (S : (n → A) →ₗ[A] (n → A)) : Prop := (∀ a, S (D.e a) = D.e a) ∧ S D.z = D.z
def Uni (D : Dat A n r) (S : (n → A) →ₗ[A] (n → A)) : Prop := ∀ x y, D.h (S x) (S y) = D.h x y
variable {D : Dat A n r}
end Dat
end PI.VolSemiDirect.W.PG


