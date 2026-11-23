-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeCountRelativeErrorOfPsiRelativeError
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeCountRelativeErrorOfPsiRelativeError
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:20.729242+00:00
-- url     : https://prove2.me/theorems/d46c1229-4b7b-4779-adea-06d18a82b121
-- title:
--   Prime Count Relative Error Of Psi Relative Error
-- statement:
--   Definitions and structural lemmas for Prime Count Relative Error Of Psi Relative Error, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeCountRelativeErrorOfPsiRelativeError.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
namespace GlobalTheory.Lin.PsiToPi
open Formalism.HermitianLattices.GL2PrimeSums (Li Emain)
noncomputable def mainPsi (θ : ℤ) (β u : ℝ) : ℝ := u - θ * (u ^ β / β)
noncomputable def wt (P : ℕ → Prop) (n : ℕ) : ℝ := if n.Prime ∧ P n then Real.log n else 0
noncomputable def cnt (P : ℕ → Prop) (u : ℝ) : ℝ := (((Finset.Icc 1 ⌊u⌋₊).filter (fun p => p.Prime ∧ P p)).card : ℝ)
end GlobalTheory.Lin.PsiToPi
namespace GlobalTheory.Lin
open PsiToPi
end GlobalTheory.Lin


