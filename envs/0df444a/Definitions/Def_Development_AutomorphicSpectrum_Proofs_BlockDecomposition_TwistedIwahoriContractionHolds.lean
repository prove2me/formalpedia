-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistedIwahoriContractionHolds
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistedIwahoriContractionHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:28.913796+00:00
-- url     : https://prove2.me/theorems/49758bcd-ee66-4636-b5e7-bd4ec09edbc9
-- title:
--   Twisted Iwahori Contraction Holds
-- statement:
--   Definitions and structural lemmas for Twisted Iwahori Contraction Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistedIwahoriContractionHolds.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedExtensionIntegralBasis
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Tf.Loc Matrix ValuativeRel
namespace GlobalTheory.CompanionTheory.TwContraction
section Algebra
variable {F : Type*} [Field F] [ValuativeRel F] {n : ℕ}
def Dp (ρ : ValueGroupWithZero F) (j : ℕ) (M : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ i l, valuation F (M i l) ≤ ρ ^ j
end Algebra
section Step
variable {F : Type*} [Field F] [ValuativeRel F] {n : ℕ}
end Step
section Main
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
end Main
end GlobalTheory.CompanionTheory.TwContraction


