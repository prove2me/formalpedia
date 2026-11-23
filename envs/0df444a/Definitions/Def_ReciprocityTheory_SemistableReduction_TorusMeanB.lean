-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanB
-- name    : ReciprocityTheory_SemistableReduction_TorusMeanB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:59:19.917737+00:00
-- url     : https://prove2.me/theorems/9a641546-4292-4838-b751-6400494fe3c4
-- title:
--   Torus Mean B
-- statement:
--   Definitions and structural lemmas for Torus Mean B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanB.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Real Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev unitIntervalMeasure : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
instance isProbabilityMeasure_torusProb (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (torusProb ι) := by
  unfold torusProb; infer_instance
def tmUpd (i : ι) : (ι → ℝ) × ℝ → (ι → ℝ) := fun p => update p.1 i p.2
def tmSlice (i : ι) (x : ι → ℂ) (f : MvPolynomial ι ℂ) : Polynomial ℂ :=
  ∑ s ∈ f.support, Polynomial.monomial (s i)
    (MvPolynomial.eval x (MvPolynomial.monomial (s.erase i) (f.coeff s)))
end ReciprocityTheory.MultiplicativeHeights


