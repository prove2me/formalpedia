-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceIntegralBasis
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceIntegralBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:39.650652+00:00
-- url     : https://prove2.me/theorems/e060b695-42bd-47da-bf95-0d207e9d9eae
-- title:
--   Trace Integral Basis
-- statement:
--   Definitions and structural lemmas for Trace Integral Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TraceIntegralBasis.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis
open NumberField InfinitePlace Module Submodule
open scoped ComplexConjugate Classical
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
abbrev CP := {w : InfinitePlace E // IsComplex w}
abbrev VS := EuclideanSpace ℂ (CP E)
instance isEmpty_real : IsEmpty {w : InfinitePlace E // IsReal w} :=
  ⟨fun w => (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1)) w.2⟩
noncomputable def iota : E →+ VS E where
  toFun x := WithLp.toLp 2 (fun w : CP E => w.1.embedding x)
  map_zero' := by ext w; simp
  map_add' x y := by ext w; simp
variable {E}
variable (E)
noncomputable def toVS : mixedEmbedding.mixedSpace E ≃ₗ[ℝ] VS E :=
  LinearEquiv.ofLinearMap
    (f := (WithLp.linearEquiv 2 ℝ (CP E → ℂ)).symm.toLinearMap ∘ₗ LinearMap.snd ℝ _ _)
    (g := LinearMap.inr ℝ _ _ ∘ₗ (WithLp.linearEquiv 2 ℝ (CP E → ℂ)).toLinearMap)
    (by ext z w; simp)
    (by
      apply LinearMap.ext
      intro z
      refine Prod.ext (funext fun w => (IsEmpty.false w).elim) ?_
      simp)
noncomputable def bas : Basis (Free.ChooseBasisIndex ℤ (𝓞 E)) ℝ (VS E) :=
  (mixedEmbedding.latticeBasis E).map (toVS E)
variable {E}
end ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis


