-- Prove2me | Definitions.Def_MazurTransfer_ContinuousCoefficientExponentF19ModuleData
-- name    : MazurTransfer_ContinuousCoefficientExponentF19ModuleData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T01:39:33.181744+00:00
-- url     : https://prove2.me/theorems/7b69689c-69de-4dac-8cca-926c4eb58990
-- title:
--   Original ZMod exponent modules and F19 modules for representation-coefficient continuous H1
-- statement:
--   Retain the original module over ZMod n on the presented continuous H1 of any multiplicative coefficient group killed by n. For a representation on an F19 module, retain the original exponent-nineteen coefficient fact and global and subgroup continuous H1 modules over F19. The group G has its original topology, and subgroup topologies are inherited. All four original types and three nonproof module-constructor values are compared. The packaged exponent specialization is a checked computation fact with no extra owned theorem acceptance. Named downstream consumer: the actual norm-character continuous H1 linear maps and their restriction diagram. Finiteness and dimension bounds remain separate.
-- source:
--   Original MazurTheorem ContinuousCoefficientExponentAndContinuity.h1ZModModule, coefficient_exponent_nineteen, coefficientH1ZModModule and restrictedCoefficientH1ZModModule, Apache-2.0. Original declaration bodies retained, using the accepted general H1 exponent theorem.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: surjective actual intertwiners give continuous actions on
their discrete coefficient targets, and exponent-nineteen coefficients give
the canonical F19 structure on continuous H1. Named downstream consumer:
the actual norm quotient H1 maps and local Selmer restriction diagrams.
-/
import Definitions.Def_MazurTransfer_RepresentationDiscreteCoefficientsData
import Theorems.Thm_MazurTransfer_ContinuousCoefficientExponentAndContinuity_h1_killed
import Mathlib.Algebra.Module.ZMod

noncomputable section
namespace MazurTransfer.ContinuousCoefficientExponentAndContinuity
open RepresentationDiscreteCoefficients ContinuousFirstCohomologyPresentation

section Exponent
variable (G M : Type) [Group G] [CommGroup M] [MulDistribMulAction G M]
  [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M]

abbrev h1ZModModule (n : ℕ) (h : ∀ m : M, m ^ n = 1) : Module (ZMod n) (H1 G M) :=
  AddCommGroup.zmodModule (h1_killed G M n h)
end Exponent

section Coefficients
variable {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod 19) V]

theorem coefficient_exponent_nineteen (τ : Representation (ZMod 19) G V)
    (x : Coefficient τ) : x ^ 19 = 1 := by
  apply Coefficient.ext
  change (19 : ℕ) • x.val = 0
  rw [← Nat.cast_smul_eq_nsmul (R := ZMod 19)]
  change (19 : ZMod 19) • x.val = 0
  rw [show (19 : ZMod 19) = 0 by decide, zero_smul]

variable [TopologicalSpace G]

abbrev coefficientH1ZModModule (τ : Representation (ZMod 19) G V) :
    Module (ZMod 19) (H1 G (Coefficient τ)) :=
  h1ZModModule G (Coefficient τ) 19 (coefficient_exponent_nineteen τ)

abbrev restrictedCoefficientH1ZModModule (τ : Representation (ZMod 19) G V) (S : Subgroup G) :
    Module (ZMod 19) (H1 S (Coefficient τ)) :=
  h1ZModModule S (Coefficient τ) 19 (coefficient_exponent_nineteen τ)
end Coefficients

end MazurTransfer.ContinuousCoefficientExponentAndContinuity
#print axioms MazurTransfer.ContinuousCoefficientExponentAndContinuity.h1ZModModule
#print axioms MazurTransfer.ContinuousCoefficientExponentAndContinuity.coefficient_exponent_nineteen
#print axioms MazurTransfer.ContinuousCoefficientExponentAndContinuity.coefficientH1ZModModule
#print axioms MazurTransfer.ContinuousCoefficientExponentAndContinuity.restrictedCoefficientH1ZModModule


