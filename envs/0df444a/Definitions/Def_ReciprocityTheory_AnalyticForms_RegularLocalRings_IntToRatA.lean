-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:25:50.73704+00:00
-- url     : https://prove2.me/theorems/b3facc57-4f85-41b7-8ff8-db6a37884e83
-- title:
--   Int To Rat A
-- statement:
--   Definitions and structural lemmas for Int To Rat A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRatA.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R.IntegerToRational
open MvPolynomial
variable {σ : Type} [Fintype σ]
noncomputable def ChZero (q : Ideal (MvPolynomial σ ℤ)) : Prop := ∀ m : ℤ, (C m : MvPolynomial σ ℤ) ∈ q → m = 0
noncomputable abbrev intS (σ : Type) : Submonoid (MvPolynomial σ ℤ) := (nonZeroDivisors ℤ).map (C (σ := σ))
attribute [local instance] MvPolynomial.algebraMvPolynomial
end ReciprocityTheory.AnForm.R.IntegerToRational


