-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:13:41.712848+00:00
-- url     : https://prove2.me/theorems/3e1f01e2-2821-46d9-b310-927415cc3f4e
-- title:
--   Hermitian Isotropic Proj Complement
-- statement:
--   Definitions and structural lemmas for Hermitian Isotropic Proj Complement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HermitianIsotropicProjComplement.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LevelKSplit.W.SemiG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
namespace Dat
def FixEZ (D : Dat A n r) (S : (n → A) →ₗ[A] (n → A)) : Prop := (∀ a, S (D.e a) = D.e a) ∧ S D.z = D.z
def Uni (D : Dat A n r) (S : (n → A) →ₗ[A] (n → A)) : Prop := ∀ x y, D.h (S x) (S y) = D.h x y
def MapX (D : Dat A n r) (S : (n → A) →ₗ[A] (n → A)) : Prop :=
  ∀ a, S (D.e a) ∈ Submodule.span A (Set.range D.e)
def MapW (D : Dat A n r) (S : (n → A) →ₗ[A] (n → A)) : Prop :=
  ∀ w, IsW D w → (∀ b, D.h (D.e b) (S w) = 0) ∧ D.h D.z (S w) = 0
variable {D : Dat A n r}
end Dat
end PI.LevelKSplit.W.SemiG


