-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_RhoSurj
-- name    : CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_RhoSurj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:08:32.393748+00:00
-- url     : https://prove2.me/theorems/17287900-0c64-426f-926c-7adf71c2fd9b
-- title:
--   Rho Surj
-- statement:
--   Definitions and structural lemmas for Rho Surj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/RhoSurj.lean

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.LKDens
open CompanionTheory.D.LK
open CompanionTheory.D.DSIC (KStab)
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
def rho (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (L : Submodule ℂ V) (hL : KStab ε E L) :
    FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] Module.End ℂ L :=
  FreeAlgebra.lift ℂ fun p => if h : ε p.1 = ε p.2 then (E p.1 p.2).restrict (hL p.1 p.2 h) else 0
def psi (ε : Fin n → Bool) : FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] FreeAlgebra ℂ (Fin n × Fin n) :=
  FreeAlgebra.lift ℂ fun p => if ε p.1 = ε p.2 then FreeAlgebra.ι ℂ p else 0
end GlobalTheory.CompanionTheory.LKDens


