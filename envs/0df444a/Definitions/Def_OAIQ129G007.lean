-- Prove2me | Definitions.Def_OAIQ129G007
-- name    : OAIQ129G007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T20:26:41.199866+00:00
-- url     : https://prove2.me/theorems/5eabc957-b557-41d0-84c9-4ac369efd0de
-- title:
--   Definitions bundle OAIQ129G007 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 103 declarations of OpenAI's Lean: 20 definitions, 1 inductive type or structure and 82 theorems. The definitions and types are `OAI.Generator.Tracial.PartialIsometry.rangeLink`, `OAI.Generator.Tracial.SpectralInterval`, `OAI.Generator.Tracial.SpectralInterval.approximant`, `OAI.Generator.Tracial.SpectralInterval.child`, `OAI.Generator.Tracial.SpectralInterval.high`, `OAI.Generator.Tracial.SpectralInterval.highProjection`, `OAI.Generator.Tracial.SpectralInterval.level`, `OAI.Generator.Tracial.SpectralInterval.low`, `OAI.Generator.Tracial.SpectralInterval.lowProjection`, `OAI.Generator.Tracial.SpectralInterval.midpoint`, `OAI.Generator.Tracial.SpectralInterval.partition`, `OAI.Generator.Tracial.cornerSpectralCut`, `OAI.Generator.Tracial.cornerSpectralPartition`, `OAI.Generator.Tracial.dimensionSpectralValue`, `OAI.Generator.Tracial.initialSpectralInterval`, `OAI.Generator.Tracial.intervalOrder`, `OAI.Generator.Tracial.intervalPreorder`, `OAI.Generator.Tracial.positiveSupport`, `OAI.Generator.Tracial.positiveSupportOrder`, `OAI.Generator.Tracial.traceFreeDyadicReference`, `OAI.Generator.Tracial.traceFreeDyadicSibling`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_Dimension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Dimension.lean), [`FactorGeneration_DyadicComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/DyadicComparison.lean), [`FactorGeneration_FiniteComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/FiniteComparison.lean), [`FactorGeneration_LocalizedStates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/LocalizedStates.lean), [`FactorGeneration_NormalDimension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/NormalDimension.lean), [`FactorGeneration_Pinching`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Pinching.lean), [`FactorGeneration_SpectralDimension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/SpectralDimension.lean), [`FactorGeneration_SpectralPinching`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/SpectralPinching.lean), [`FactorGeneration_SpectralStates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/SpectralStates.lean), [`FactorGeneration_Supports`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Supports.lean).
--
--   **Imports.** It imports the bundles `OAIQ129G003` and `OAIQ129G004` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ129G010`; the proof of `OAI.Generator.Tracial.representedCorner_irreducible_q129`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ129G003
import Definitions.Def_OAIQ129G004

section
-- module Solutions.OAIQ129_RG2.Compat
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Supports
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Kernel and range projections constructed in the actual von Neumann algebra.
Membership follows from commutant invariance, with no spectral theorem assumed. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Kernel projections fix the range of every operator they annihilate. -/
theorem kernelProjection_mul_of_mul_eq_zero (x y : M.toStarSubalgebra) (h : x*y=0) :
    (kernelProjection x).val*y=y := by
  apply Subtype.ext
  ext ξ
  apply kernelProjection_fixes
  exact congrArg (fun t : M.toStarSubalgebra => (t : H →L[ℂ] H) ξ) h

/-- For self-adjoint x, its range projection kills every y killed by x. -/
theorem rangeProjection_mul_eq_zero (x y : M.toStarSubalgebra) (hx : IsSelfAdjoint x)
    (h : x*y=0) : (rangeProjection x).val*y=0 := by
  change (1-(kernelProjection (star x)).val)*y=0
  rw [hx.star_eq,sub_mul,one_mul,kernelProjection_mul_of_mul_eq_zero x y h,sub_self]

end

/-! Spectral sign cuts from continuous positive parts and actual range projections.
These are constructed operators, not assumed Borel functional calculus data. -/
open scoped CStarAlgebra
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
attribute [local instance] OAI.Generator.Tracial.positiveSupportCStar
local instance positiveSupportOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance positiveSupportPreorder_rf87284_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance positiveSupportLE_rf87284_1 : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance positiveSupportStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

def positiveSupport (x : M.toStarSubalgebra) : AlgebraProjection M := rangeProjection x⁺

theorem positiveSupport_mul_pos (x : M.toStarSubalgebra) :
    (positiveSupport x).val*x⁺=x⁺ := rangeProjection_mul _

theorem positiveSupport_mul_neg (x : M.toStarSubalgebra) :
    (positiveSupport x).val*x⁻=0 :=
  rangeProjection_mul_eq_zero x⁺ x⁻ (CFC.posPart_nonneg x).isSelfAdjoint
    (CFC.posPart_mul_negPart x)

theorem positiveSupport_mul (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    (positiveSupport x).val*x=x⁺ := by
  calc (positiveSupport x).val*x = (positiveSupport x).val*(x⁺-x⁻) :=
         congrArg (fun z => (positiveSupport x).val*z) (CFC.posPart_sub_negPart x hx).symm
    _ = x⁺ := by rw [mul_sub,positiveSupport_mul_pos,positiveSupport_mul_neg,sub_zero]

theorem mul_positiveSupport (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    x*(positiveSupport x).val=x⁺ := by
  have h := congrArg star (positiveSupport_mul x hx)
  simpa only [star_mul,hx.star_eq,(positiveSupport x).property.isSelfAdjoint.star_eq,
    (CFC.posPart_nonneg x).isSelfAdjoint.star_eq] using h

theorem positiveSupport_commutes (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    Commute (positiveSupport x).val x := by
  show (positiveSupport x).val*x=x*(positiveSupport x).val
  rw [positiveSupport_mul x hx,mul_positiveSupport x hx]

theorem positiveSupport_compression (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    (positiveSupport x).val*x*(positiveSupport x).val=x⁺ := by
  rw [mul_assoc,mul_positiveSupport x hx,positiveSupport_mul_pos]

theorem positiveSupport_complement_mul (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    (1-(positiveSupport x).val)*x = -x⁻ := by
  rw [sub_mul,one_mul,positiveSupport_mul x hx]
  calc x-x⁺ = (x⁺-x⁻)-x⁺ := congrArg (fun z => z-x⁺) (CFC.posPart_sub_negPart x hx).symm
    _ = -x⁻ := by abel

theorem positiveSupport_complement_compression (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) :
    (1-(positiveSupport x).val)*x*(1-(positiveSupport x).val) = -x⁻ := by
  have hright : x⁻*(positiveSupport x).val=0 := by
    have h := congrArg star (positiveSupport_mul_neg x)
    simpa only [star_mul,(positiveSupport x).property.isSelfAdjoint.star_eq,
      (CFC.negPart_nonneg x).isSelfAdjoint.star_eq,star_zero] using h
  rw [positiveSupport_complement_mul x hx,mul_sub,mul_one,neg_mul,hright,neg_zero,sub_zero]

end

/-! A polar operator is constructed by extending the isometry on a range.
No polar-decomposition or projection-comparison hypothesis is used. -/

/-! Polar decomposition inside the given concrete von Neumann algebra. -/
open scoped CStarAlgebra

/-! Exact initial and final support projections of the constructed polar part. -/
open scoped CStarAlgebra
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_FiniteComparison
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! The closed span of algebra translates of a projection range gives its
central support. All operators act on the original Hilbert space; no trace,
cyclic vector, separability, finiteness, or comparison theorem is assumed. -/

/-! The original finiteness predicate excludes proper self-equivalence of a
projection. Projection comparison is connected to the unchanged IsII1Factor
predicate, with no representation, trace, or separability premise. -/

/-! Arbitrary-chain bounds with moving orthogonal initial and final supports, obtained from successive fixed-multiplier weak operator limits without a trace. -/

/-! Complete actual partial isometries to unitaries in a finite factor.
The construction uses projection comparison and finiteness, without a trace. -/
open scoped CStarAlgebra
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfactor hfinite in
theorem PartialIsometry.exists_unitary_extension (v : PartialIsometry M) :
    ∃ u : unitary M.toStarSubalgebra, (u : M.toStarSubalgebra)*v.support.val=v.val := by
  let p : AlgebraProjection M := ⟨1-v.support.val,v.support.property.one_sub⟩
  let q : AlgebraProjection M := ⟨1-v.target.val,v.target.property.one_sub⟩
  obtain ⟨w,hwp,hwq,hw⟩ := traceFree_exists_partialIsometry_comparison hfactor p q
  have hp : v.support.val*w.support.val=0 := by
    calc _ = v.support.val*(p.val*w.support.val) := by rw [hwp]
      _ = (v.support.val*p.val)*w.support.val := (mul_assoc _ _ _).symm
      _ = 0 := by
        change (v.support.val*(1-v.support.val))*w.support.val=0
        rw [v.support.property.mul_one_sub_self,zero_mul]
  have hq : v.target.val*w.target.val=0 := by
    calc _ = v.target.val*(q.val*w.target.val) := by rw [hwq]
      _ = (v.target.val*q.val)*w.target.val := (mul_assoc _ _ _).symm
      _ = 0 := by
        change (v.target.val*(1-v.target.val))*w.target.val=0
        rw [v.target.property.mul_one_sub_self,zero_mul]
  let a := v.patch w hp hq
  have hi : star a.val*a.val=1 := by
    rcases hw with hw | hw
    · rw [a.initial]
      change v.support.val+w.support.val=1
      rw [hw]
      change v.support.val+(1-v.support.val)=1
      abel
    · have hf : a.val*star a.val=1 := by
        change a.target.val=1
        rw [PartialIsometry.patch_target,hw]
        change v.target.val+(1-v.target.val)=1
        abel
      have h := hfinite (star a.val) (by simpa only [star_star] using hf)
      simpa only [star_star] using h
  exact ⟨⟨a.val,⟨hi,hfinite a.val hi⟩⟩,v.le_patch w hp hq⟩

attribute [local instance] OAI.Generator.Tracial.unitaryPolarCStar
attribute [local instance] OAI.Generator.Tracial.unitaryPolarOrder
attribute [local instance] OAI.Generator.Tracial.unitaryPolarStarOrder
include hfactor hfinite in
theorem exists_unitary_polar_decomposition (x : M.toStarSubalgebra) :
    ∃ u : unitary M.toStarSubalgebra, (u : M.toStarSubalgebra)*CFC.sqrt (star x*x)=x := by
  obtain ⟨v,hvx,hvi,_⟩ := exists_polar_decomposition x
  let a := CFC.sqrt (star x*x)
  let w : PartialIsometry M := ⟨rangeProjection a,v,hvi⟩
  obtain ⟨u,hu⟩ := w.exists_unitary_extension hfactor hfinite
  have ha : w.support.val*a=a := rangeProjection_mul a
  refine ⟨u,?_⟩
  calc (u : M.toStarSubalgebra)*a = (u : M.toStarSubalgebra)*(w.support.val*a) := by rw [ha]
    _ = w.val*a := by rw [← mul_assoc,hu]
    _ = x := hvx

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_DyadicComparison
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Halving every projection in a diffuse factor without a trace.
Maximality leaves no residual corner: a diffuse residual splits into two
nonzero orthogonal projections, and a polar link gives a strict extension. -/

/-! Finite partitions with explicit equivalence witnesses and compatible binary
refinement. The common initial projection is halved once and its two pieces
are transported to every old piece, so all new pieces remain equivalent. -/

/-! Actual sums of countable orthogonal partial isometries, including least
initial/final support identities. No trace or countable-cofinality premise. -/
namespace Tracial

/-! Projection equivalence and subequivalence are witnessed by actual partial
isometries in the original algebra. No dimension or trace oracle is used. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

/-- Link two ranges whose displayed partial isometries have the same source. -/
def rangeLink (v w : PartialIsometry M) (h : v.support=w.support) : PartialIsometry M :=
  w.compose v.adjoint (by rw [adjoint_target,h])

theorem rangeLink_target (v w : PartialIsometry M) (h : v.support=w.support) :
    (rangeLink v w h).target=w.target :=
  compose_target_of_eq w v.adjoint ((adjoint_target v).trans h)

end PartialIsometry

/-! Finiteness excludes an infinite family of nonzero equivalent orthogonal
projections. The shift and both of its least supports are constructed. -/

/-- The infinite shift omits the first range. Finiteness then forces that
range, and hence the common source projection, to be zero. -/
theorem traceFree_finite_orthogonal_copies_eq_zero
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (r : AlgebraProjection M) (a : ℕ → PartialIsometry M)
    (hs : ∀ i, (a i).support=r)
    (ho : ∀ i j, i≠j → (a i).target.val*(a j).target.val=0) : r.val=0 := by
  let w (i : ℕ) := PartialIsometry.rangeLink (a i) (a (i+1)) ((hs i).trans (hs (i+1)).symm)
  have hw₁ (i : ℕ) : (w i).support=(a i).target := rfl
  have hw₂ (i : ℕ) : (w i).target=(a (i+1)).target := PartialIsometry.rangeLink_target _ _ _
  obtain ⟨v,hv,hvp,hvq⟩ := PartialIsometry.traceFree_orthogonal_sum w
    (by intro i j h; rw [hw₁,hw₁]; exact ho i j h)
    (by intro i j h; rw [hw₂,hw₂]; exact ho (i+1) (j+1) (by omega))
  have hle : v.target ≤ v.support := by
    apply (hvq v.support).mpr
    intro i
    rw [hw₂,← hw₁ (i+1)]
    exact PartialIsometry.support_mono (hv (i+1))
  have he : v.target=v.support := v.target_eq_support_of_finite hfinite hle
  let c : AlgebraProjection M := ⟨1-(a 0).target.val,(a 0).target.property.one_sub⟩
  have hc : v.target ≤ c := by
    apply (hvq c).mpr
    intro i
    rw [hw₂]
    change (1-(a 0).target.val)*(a (i+1)).target.val=(a (i+1)).target.val
    rw [sub_mul,one_mul,ho 0 (i+1) (by omega),sub_zero]
  have h0 : (a 0).target ≤ c := by
    apply (PartialIsometry.support_mono (hv 0)).trans
    rw [← he]
    exact hc
  have hz : (a 0).target.val=0 := by
    change (1-(a 0).target.val)*(a 0).target.val=(a 0).target.val at h0
    rw [sub_mul,one_mul,(a 0).target.property.isIdempotentElem.eq,sub_self] at h0
    exact h0.symm
  have ha : (a 0).val=0 := by
    have h := (a 0).target_mul
    rw [hz,zero_mul] at h
    exact h.symm
  rw [← hs 0,← (a 0).initial,ha,star_zero,zero_mul]

/-- Subequivalence into every member of an orthogonal sequence is impossible
for a nonzero projection in a finite algebra. -/
theorem traceFree_finite_subequivalent_orthogonal_eq_zero
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (r : AlgebraProjection M) (q : ℕ → AlgebraProjection M)
    (ho : ∀ i j, i≠j → (q i).val*(q j).val=0)
    (h : ∀ i, r.Subequivalent (q i)) : r.val=0 := by
  choose a hs ht using h
  exact traceFree_finite_orthogonal_copies_eq_zero hfinite r a hs (by
    intro i j hij
    exact projection_orthogonal_of_le (ho i j hij) (ht i) (ht j))

/-! Finite comparison and cancellation with actual partial isometries.
No trace, dimension, or representation is assumed. -/
namespace AlgebraProjection

variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))

include hfinite hfactor in
/-- Comparison respects subtraction of equivalent pieces. -/
theorem remainder_subequivalent {p q P Q : AlgebraProjection M}
    (hp : p ≤ P) (hq : q ≤ Q) (he : p.Equivalent q) (h : P.Subequivalent Q) :
    (remainder p P hp).Subequivalent (remainder q Q hq) := by
  apply subequivalent_cancel hfinite hfactor
    (remainder_orthogonal p P hp) (remainder_orthogonal q Q hq) he
  simpa only [orthogonalSum_remainder] using h

end AlgebraProjection
end Tracial

/-! Actual finite sums of orthogonal partial isometries and finite subsets of
equivalent partitions. The finite subset is arbitrary, without an index order. -/
open scoped BigOperators
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

theorem subset_singleton [DecidableEq ι] (E : EquivalentPartition p ι) (i : ι) :
    E.subset {i}=(E.leg i).target := Subtype.ext (by simp only [subset_val,Finset.sum_singleton])

/-! Exact finite cardinal comparison of sums of equivalent nonzero projections.
Finiteness prevents a larger collection from embedding in a smaller one. -/

end EquivalentPartition
end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Dimension
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Archimedean comparison for the constructed dyadic reference projections.
Orthogonal sibling corners supply copies for the finite-algebra shift argument. -/
section
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

def traceFreeDyadicReference (p : AlgebraProjection M) (n : ℕ) : AlgebraProjection M :=
  ((traceFreeDyadicPartition hfactor hdiff p n).leg (dyadicFalseIndex n)).target

def traceFreeDyadicSibling (p : AlgebraProjection M) (n : ℕ) : AlgebraProjection M :=
  ((traceFreeDyadicPartition hfactor hdiff p (n+1)).leg (dyadicFalseIndex n,true)).target

theorem traceFreeDyadic_child_le (p : AlgebraProjection M) (n : ℕ)
    (i : DyadicIndex n) (b : Bool) :
    ((traceFreeDyadicPartition hfactor hdiff p (n+1)).leg (i,b)).target ≤
      ((traceFreeDyadicPartition hfactor hdiff p n).leg i).target :=
  PartialIsometry.compose_target_le _ _ (by
    rw [EquivalentPartition.initial]
    exact EquivalentPartition.bound _ b)

theorem traceFreeDyadicReference_antitone (p : AlgebraProjection M) :
    Antitone (traceFreeDyadicReference hfactor hdiff p) := by
  apply antitone_nat_of_succ_le
  intro n
  exact traceFreeDyadic_child_le hfactor hdiff p n (dyadicFalseIndex n) false

theorem traceFreeDyadicSibling_le (p : AlgebraProjection M) (n : ℕ) :
    traceFreeDyadicSibling hfactor hdiff p n ≤ traceFreeDyadicReference hfactor hdiff p n :=
  traceFreeDyadic_child_le hfactor hdiff p n (dyadicFalseIndex n) true

theorem traceFreeDyadicReference_sibling_orthogonal (p : AlgebraProjection M) (n : ℕ) :
    (traceFreeDyadicReference hfactor hdiff p (n+1)).val*
      (traceFreeDyadicSibling hfactor hdiff p n).val=0 := by
  apply EquivalentPartition.orthogonal
  exact fun h => Bool.false_ne_true (congrArg Prod.snd h)

theorem traceFreeDyadicSibling_orthogonal (p : AlgebraProjection M) (i j : ℕ) (hij : i≠j) :
    (traceFreeDyadicSibling hfactor hdiff p i).val*
      (traceFreeDyadicSibling hfactor hdiff p j).val=0 := by
  have hlt (i j : ℕ) (h : i<j) :
      (traceFreeDyadicSibling hfactor hdiff p i).val*
        (traceFreeDyadicSibling hfactor hdiff p j).val=0 := by
    apply projection_orthogonal_of_le
      (PartialIsometry.orthogonal_reverse _ _
        (traceFreeDyadicReference_sibling_orthogonal hfactor hdiff p i)) le_rfl
    exact (traceFreeDyadicSibling_le hfactor hdiff p j).trans
      (traceFreeDyadicReference_antitone hfactor hdiff p (by omega))
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j h
  · exact PartialIsometry.orthogonal_reverse _ _ (hlt j i h)

theorem traceFreeDyadicReference_equivalent_sibling (p : AlgebraProjection M) (n : ℕ) :
    (traceFreeDyadicReference hfactor hdiff p (n+1)).Equivalent
      (traceFreeDyadicSibling hfactor hdiff p n) := by
  let E := traceFreeDyadicPartition hfactor hdiff p (n+1)
  exact ⟨E.link (dyadicFalseIndex (n+1)) (dyadicFalseIndex n,true),
    E.link_support _ _,E.link_target _ _⟩

/-- A projection that embeds in every dyadic reference corner must be zero.
Finiteness is used through the constructed infinite shift, not through a trace. -/
theorem traceFree_dyadic_archimedean
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p r : AlgebraProjection M)
    (h : ∀ n, r.Subequivalent (traceFreeDyadicReference hfactor hdiff p n)) : r.val=0 := by
  apply traceFree_finite_subequivalent_orthogonal_eq_zero hfinite r
    (traceFreeDyadicSibling hfactor hdiff p)
    (traceFreeDyadicSibling_orthogonal hfactor hdiff p)
  intro n
  exact AlgebraProjection.subequivalent_trans (h (n+1))
    (traceFreeDyadicReference_equivalent_sibling hfactor hdiff p n).subequivalent

end Tracial

end

/-! Finite rounding by actual subset projections. A maximal fitting subset
leaves a remainder smaller in comparison than any unused equivalent piece. -/
namespace Tracial

section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-! The dyadic lower cut on projections below p and its normalized faithful monotone supremum, capped at one. -/

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

theorem traceFreeDyadicSup_equivalent (p : AlgebraProjection M) {q r : AlgebraProjection M}
    (h : q.Equivalent r) :
    traceFreeDyadicSup hfactor hdiff p q=traceFreeDyadicSup hfactor hdiff p r :=
  le_antisymm (traceFreeDyadicSup_mono hfactor hdiff p h.subequivalent)
    (traceFreeDyadicSup_mono hfactor hdiff p (AlgebraProjection.equivalent_symm h).subequivalent)

end

/-! Common refinements compare arbitrary dyadic levels. The supremum takes
the exact dyadic value on every reference subset projection, and finite
rounding bounds every projection with an explicit error at each level. -/

/-! Orthogonal lower approximants fit disjoint collections of the reference
pieces. Equivalent complements and finite cancellation enforce the capacity. -/

/-! Orthogonal additivity of the constructed dyadic dimension. Numerical
rounding errors tend to zero; every lower and upper bound uses actual
partial-isometry witnesses in the original finite diffuse factor. -/

end Tracial

/-! Classification of projection comparison by the constructed finite
dimension, and a wrapper for exactly the original IsII1Factor predicate.
No normality or trace-extension claim is made here. -/

/-! Bounds and concrete dyadic upper approximants for the constructed
projection dimension. These finite estimates do not assume continuity. -/
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

/-- A subset of the n-th reference partition with weight in [c,c+2^(-n)]. -/
theorem exists_dyadicWeight_upper (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) :
    ∃ s : Finset (DyadicIndex n), c ≤ dyadicWeight n s ∧ dyadicWeight n s ≤ c+1/2^n := by
  classical
  have hn : (0 : ℝ)<2^n := pow_pos (by norm_num) n
  have hk : Nat.ceil (c*2^n) ≤ Fintype.card (DyadicIndex n) := by
    rw [card_dyadicIndex,Nat.ceil_le]
    push_cast
    nlinarith
  obtain ⟨s,_,hs⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (DyadicIndex n))) (n := Nat.ceil (c*2^n))
    (by simpa only [Finset.card_univ] using hk)
  refine ⟨s,?_,?_⟩
  · change c ≤ (s.card : ℝ)/2^n
    rw [hs,le_div_iff₀ hn]
    exact Nat.le_ceil _
  · change (s.card : ℝ)/2^n ≤ c+1/2^n
    rw [hs,div_le_iff₀ hn]
    have h := (Nat.ceil_lt_add_one (mul_nonneg hc hn.le)).le
    calc (Nat.ceil (c*2^n) : ℝ) ≤ c*2^n+1 := h
         _ = (c+1/2^n)*2^n := by field_simp

include hfinite in
/-- Actual projection upper approximants for every real c in [0,1]. -/
theorem traceFreeDimension_exists_upper
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) :
    ∃ r : AlgebraProjection M, c ≤ traceFreeDimension hfactor hdiff r ∧
      traceFreeDimension hfactor hdiff r ≤ c+1/2^n := by
  obtain ⟨s,hs,ht⟩ := exists_dyadicWeight_upper c hc hc1 n
  refine ⟨(traceFreeDyadicPartition hfactor hdiff ⟨1,IsStarProjection.one _⟩ n).subset s,?_,?_⟩
  · simpa only [traceFreeDimension,traceFreeDyadicSup_subset hfactor hdiff hfinite
      ⟨1,IsStarProjection.one _⟩ hunit] using hs
  · simpa only [traceFreeDimension,traceFreeDyadicSup_subset hfactor hdiff hfinite
      ⟨1,IsStarProjection.one _⟩ hunit] using ht

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_NormalDimension
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Increasing projection suprema and compatible sequential comparison.
The witnesses live in the original algebra; no trace or dimension is used. -/
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace PartialIsometry

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfactor hfinite in
/-- Extend a given embedding to a larger source while keeping its target in r. -/
theorem exists_extension_of_subequivalent (v : PartialIsometry M)
    (p r : AlgebraProjection M) (hp : v.support ≤ p) (hr : v.target ≤ r)
    (hpr : p.Subequivalent r) :
    ∃ w : PartialIsometry M, v ≤ w ∧ w.support=p ∧ w.target ≤ r := by
  obtain ⟨u,hu,ht⟩ := AlgebraProjection.remainder_subequivalent hfinite hfactor hp hr
    (show v.support.Equivalent v.target from ⟨v,rfl,rfl⟩) hpr
  have hi : v.support.val*u.support.val=0 := by
    rw [hu]
    exact AlgebraProjection.remainder_orthogonal _ _ hp
  have ho : v.target.val*u.target.val=0 :=
    projection_orthogonal_of_le (AlgebraProjection.remainder_orthogonal _ _ hr) le_rfl ht
  refine ⟨v.patch u hi ho,v.le_patch u hi ho,?_,?_⟩
  · apply Subtype.ext
    change v.support.val+u.support.val=p.val
    rw [hu]
    change v.support.val+(p.val-v.support.val)=p.val
    abel
  · have he : (v.patch u hi ho).target=orthogonalSum v.target u.target ho :=
      Subtype.ext (v.patch_target u hi ho)
    rw [he]
    exact orthogonalSum_le ho hr (ht.trans (AlgebraProjection.remainder_le _ _ hr))

include hfactor hfinite in
/-- A sequence of comparable sources admits compatible actual embeddings. -/
theorem exists_monotone_embeddings (q : ℕ → AlgebraProjection M) (hq : Monotone q)
    (r : AlgebraProjection M) (hr : ∀ n, (q n).Subequivalent r) :
    ∃ a : ℕ → PartialIsometry M, Monotone a ∧
      (∀ n, (a n).support=q n) ∧ (∀ n, (a n).target ≤ r) := by
  classical
  obtain ⟨v,hv,ht⟩ := hr 0
  let step (n : ℕ) (w : {w : PartialIsometry M // w.support=q n ∧ w.target ≤ r}) :=
    exists_extension_of_subequivalent hfactor hfinite w.val (q (n+1)) r
      (by rw [w.property.1]; exact hq (Nat.le_succ n)) w.property.2 (hr (n+1))
  let a : (n : ℕ) → {w : PartialIsometry M // w.support=q n ∧ w.target ≤ r} :=
    Nat.rec ⟨v,hv,ht⟩ (fun n w => ⟨(step n w).choose,(step n w).choose_spec.2⟩)
  refine ⟨fun n => (a n).val,?_,fun n => (a n).property.1,fun n => (a n).property.2⟩
  apply monotone_nat_of_le_succ
  intro n
  exact (step n (a n)).choose_spec.1

end PartialIsometry
namespace AlgebraProjection

/-- Sequential increasing-union comparison, with a constructed compatible
partial-isometry limit. No dimension-continuity premise occurs. -/
theorem isLUB_subequivalent_of_sequence
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (q : ℕ → AlgebraProjection M) (hq : Monotone q)
    (p : AlgebraProjection M) (hp : IsLUB (Set.range q) p)
    (r : AlgebraProjection M) (hr : ∀ n, (q n).Subequivalent r) :
    p.Subequivalent r := by
  obtain ⟨a,ha,hs,ht⟩ := PartialIsometry.exists_monotone_embeddings hfactor hfinite q hq r hr
  obtain ⟨v,hv,hvs,hvt⟩ := PartialIsometry.traceFree_monotone_least_supports a ha
  refine ⟨v,le_antisymm (hvs p (fun n => by rw [hs]; exact hp.1 ⟨n,rfl⟩)) ?_,hvt r ht⟩
  apply hp.2
  rintro _ ⟨n,rfl⟩
  rw [← hs n]
  exact PartialIsometry.support_mono (hv n)

end AlgebraProjection
end

/-! Continuity of the constructed dimension on arbitrary increasing projection
nets. Compatible sequential embeddings are proved first; dimension approximation
then constructs a countable subfamily with the same projection supremum. -/

end Tracial

/-! Original-factor wrapper for normalized faithful order-continuous projection
dimension. This does not assert the existence of a linear trace functional. -/

/-! Exact prescribed dimensions are attained by actual subprojections.
Chain bounds use the proved arbitrary-net continuity of dimension. -/

/-! Actual vector functionals and their continuity on directed projection
suprema. No factor, trace, separability, or dimension hypothesis is used. -/
open Filter
open scoped Topology BigOperators
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace AlgebraProjection

theorem vectorValue_remainder (ξ : H) (p q : AlgebraProjection M) (h : p ≤ q) :
    vectorValue ξ (remainder p q h)=vectorValue ξ q-vectorValue ξ p := by
  change (inner ℂ ξ (q.val.val ξ-p.val.val ξ)).re=_
  rw [inner_sub_right,Complex.sub_re]
  rfl

theorem vectorValue_mono (ξ : H) : Monotone (vectorValue (M := M) ξ) := by
  intro p q hpq
  have h := vectorValue_nonneg ξ (remainder p q hpq)
  rw [vectorValue_remainder] at h
  linarith

/-- The vector functional preserves any directed projection supremum. -/
theorem vectorValue_isLUB_monotone
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (a : ι → AlgebraProjection M) (ha : Monotone a)
    (p : AlgebraProjection M) (hp : IsLUB (Set.range a) p) (ξ : H) :
    IsLUB (Set.range (fun i => vectorValue ξ (a i))) (vectorValue ξ p) := by
  obtain ⟨q,hq,ht⟩ := exists_isLUB_monotone_vector_limit a ha
  have he : q=p := le_antisymm (hq.2 hp.1) (hp.2 hq.1)
  subst q
  refine ⟨?_,?_⟩
  · rintro _ ⟨i,rfl⟩
    exact vectorValue_mono ξ (hp.1 ⟨i,rfl⟩)
  · intro r hr
    exact le_of_tendsto ((Complex.continuous_re.tendsto _).comp (ht ξ ξ))
      (Eventually.of_forall (fun i => hr ⟨i,rfl⟩))

theorem vectorValue_tendsto_monotone
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (a : ι → AlgebraProjection M) (ha : Monotone a)
    (p : AlgebraProjection M) (hp : IsLUB (Set.range a) p) (ξ : H) :
    Tendsto (fun i => vectorValue ξ (a i)) atTop (𝓝 (vectorValue ξ p)) :=
  tendsto_atTop_isLUB ((vectorValue_mono ξ).comp ha)
    (vectorValue_isLUB_monotone a ha p hp ξ)

end AlgebraProjection
end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Pinching
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite pinching in the actual ambient algebra. The squared L2 energy
is a sum of the energies of the mutually orthogonal compression blocks.
These identities do not postulate a local-quantizing partition. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-! Actual compression energies and the energy lost by finite pinching.
No existence statement about small-energy partitions is assumed here. -/

namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)

/-! Partition refinement decreases the actual compression energy. The final
selection theorem retains membership in the prescribed subalgebra. -/

theorem pinch_corner_compression (x : M.toStarSubalgebra) :
    Q.pinch (p.val*x*p.val) = Q.pinch x := by
  unfold pinch
  apply Finset.sum_congr rfl
  intro i _
  have hl : p.val*(Q.piece i).val = (Q.piece i).val := Q.piece_le i
  have hr := projection_mul_of_le (Q.piece_le i)
  simp only [← mul_assoc, hr]
  simp only [mul_assoc, hl]

end CornerPartition

end

/-! Actual finite refinement of a corner partition by partitions of its blocks.
The dependent family of block sizes is flattened without changing any piece.
No small-energy partition is an input to these constructions. -/

/-! Centered energy and the block scalar term that refinement preserves.
A blockwise descent applies to centered compressions, not to their full energy. -/

/-! Energy of compatible block refinements, including the scalar term.
The scalar term is necessary even when the original operator has trace zero. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_SpectralPinching
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual sign splitting inside a prescribed residual corner. -/
section
open scoped CStarAlgebra BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.cornerCutCStar
attribute [local instance] OAI.Generator.Tracial.cornerCutOrder
attribute [local instance] OAI.Generator.Tracial.cornerCutPreorder
attribute [local instance] OAI.Generator.Tracial.cornerCutLE
attribute [local instance] OAI.Generator.Tracial.cornerCutStarOrder
theorem positiveSupport_le_corner (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x)
    (p : AlgebraProjection M) (hp : x*p.val=x) : positiveSupport x ≤ p := by
  apply (rangeProjection_le_iff _ p).mpr
  have h := congrArg star (positivePart_right_support x hx p hp)
  simpa only [star_mul,p.property.isSelfAdjoint.star_eq,
    (CFC.posPart_nonneg x).isSelfAdjoint.star_eq] using h

def cornerSpectralCut (p : AlgebraProjection M) (x : M.toStarSubalgebra) (t : ℝ) :
    AlgebraProjection M := positiveSupport (cornerSpectralShift p x t)

theorem cornerSpectralCut_le (p : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) (t : ℝ) : cornerSpectralCut p x t ≤ p :=
  positiveSupport_le_corner _ (cornerSpectralShift_selfAdjoint p x hx t) p
    (cornerSpectralShift_support p x t)

/-- The finite corner partition constructed from the shifted positive part. -/
def cornerSpectralPartition (p : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) (t : ℝ) : CornerPartition p :=
  CornerPartition.binary p (cornerSpectralCut p x t) (cornerSpectralCut_le p x hx t)

/-- Its high block has the promised spectral lower bound. -/
theorem cornerSpectralCut_lower (p : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) (t : ℝ) :
    0 ≤ (cornerSpectralCut p x t).val*x*(cornerSpectralCut p x t).val -
      (t : ℂ) • (cornerSpectralCut p x t).val := by
  have hc := positiveSupport_compression (cornerSpectralShift p x t)
    (cornerSpectralShift_selfAdjoint p x hx t)
  have hqp := cornerSpectralCut_le p x hx t
  have hleft : p.val*(cornerSpectralCut p x t).val=(cornerSpectralCut p x t).val := hqp
  have he : (cornerSpectralCut p x t).val * cornerSpectralShift p x t *
      (cornerSpectralCut p x t).val =
      (cornerSpectralCut p x t).val*x*(cornerSpectralCut p x t).val -
        (t : ℂ) • (cornerSpectralCut p x t).val := by
    simp only [cornerSpectralShift,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
    simp only [← mul_assoc,projection_mul_of_le hqp]
    simp only [mul_assoc,hleft,(cornerSpectralCut p x t).property.isIdempotentElem.eq]
  rw [← he]
  exact hc.symm ▸ CFC.posPart_nonneg _

/-- The low block has the opposite shifted sign in the same corner. -/
theorem cornerSpectralCut_upper (p : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) (t : ℝ) :
    let r := p.val-(cornerSpectralCut p x t).val
    r*x*r-(t : ℂ) • r ≤ 0 := by
  let q := cornerSpectralCut p x t
  let r : AlgebraProjection M := ⟨p.val-q.val,q.property.sub_of_mul_eq_right p.property
    (cornerSpectralCut_le p x hx t)⟩
  have hrp : r ≤ p := by
    change p.val*(p.val-q.val)=p.val-q.val
    rw [mul_sub,p.property.isIdempotentElem.eq,cornerSpectralCut_le p x hx t]
  have hrleft : p.val*r.val=r.val := hrp
  have hs := cornerSpectralShift_support p x t
  have hsl : p.val*cornerSpectralShift p x t=cornerSpectralShift p x t := by
    have h := congrArg star hs
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq,
      (cornerSpectralShift_selfAdjoint p x hx t).star_eq] using h
  have hc : r.val*cornerSpectralShift p x t*r.val = -(cornerSpectralShift p x t)⁻ := by
    change (p.val-q.val)*cornerSpectralShift p x t*(p.val-q.val)=_
    have he : (p.val-q.val)*cornerSpectralShift p x t*(p.val-q.val) =
        (1-q.val)*cornerSpectralShift p x t*(1-q.val) := by
      simp only [sub_mul,mul_sub,one_mul,mul_one,hsl,hs,mul_assoc]
    rw [he]
    exact positiveSupport_complement_compression _ (cornerSpectralShift_selfAdjoint p x hx t)
  have he : r.val*cornerSpectralShift p x t*r.val=r.val*x*r.val-(t : ℂ) • r.val := by
    simp only [cornerSpectralShift,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
    simp only [← mul_assoc,projection_mul_of_le hrp]
    simp only [mul_assoc,hrleft,r.property.isIdempotentElem.eq]
  change r.val*x*r.val-(t : ℂ) • r.val ≤ 0
  rw [← he,hc]
  exact neg_nonpos.mpr (CFC.negPart_nonneg _)

end

/-! The constructed spectral splitting preserves the compressed operator.
This is distinct from using that splitting to reduce other operators' energy. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem cornerSpectralCut_commutes (p : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) (t : ℝ) :
    (cornerSpectralCut p x t).val*(p.val*x*p.val)=
      (p.val*x*p.val)*(cornerSpectralCut p x t).val := by
  let q := cornerSpectralCut p x t
  have h := (positiveSupport_commutes (cornerSpectralShift p x t)
    (cornerSpectralShift_selfAdjoint p x hx t)).eq
  change q.val*(p.val*x*p.val-(t : ℂ) • p.val) =
    (p.val*x*p.val-(t : ℂ) • p.val)*q.val at h
  have hqp := cornerSpectralCut_le p x hx t
  have hleft : p.val*q.val=q.val := hqp
  have hright : q.val*p.val=q.val := projection_mul_of_le hqp
  simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,
    hright,hleft] at h
  exact sub_left_inj.mp h

theorem cornerSpectralPartition_pinch (p : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) (t : ℝ) :
    (cornerSpectralPartition p x hx t).pinch x=p.val*x*p.val := by
  rw [← (cornerSpectralPartition p x hx t).pinch_corner_compression]
  apply CornerPartition.binary_pinch_of_commutes
  · simp only [← mul_assoc,p.property.isIdempotentElem.eq]
  · simp only [mul_assoc,p.property.isIdempotentElem.eq]
  · exact cornerSpectralCut_commutes p x hx t

end

/-! Interval bounds propagated through constructed spectral corner splits. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
attribute [local instance] OAI.Generator.Tracial.intervalCStar
local instance intervalOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance intervalPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.intervalLE
local instance intervalStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

theorem lower_bound_compress {p q : AlgebraProjection M} (hqp : q ≤ p)
    (x : M.toStarSubalgebra) (t : ℝ)
    (h : 0 ≤ p.val*x*p.val-(t : ℂ) • p.val) :
    0 ≤ q.val*x*q.val-(t : ℂ) • q.val := by
  have hh := star_left_conjugate_nonneg h q.val
  rw [q.property.isSelfAdjoint.star_eq,compress_scalar_shift hqp] at hh
  exact hh

theorem upper_bound_compress {p q : AlgebraProjection M} (hqp : q ≤ p)
    (x : M.toStarSubalgebra) (t : ℝ)
    (h : p.val*x*p.val-(t : ℂ) • p.val ≤ 0) :
    q.val*x*q.val-(t : ℂ) • q.val ≤ 0 := by
  have hh := star_left_conjugate_nonneg (neg_nonneg.mpr h) q.val
  rw [q.property.isSelfAdjoint.star_eq,mul_neg,neg_mul,compress_scalar_shift hqp] at hh
  exact neg_nonneg.mp hh

structure SpectralInterval (x : M.toStarSubalgebra) where
  proj : AlgebraProjection M
  lo : ℝ
  hi : ℝ
  lower : 0 ≤ proj.val*x*proj.val-(lo : ℂ) • proj.val
  upper : proj.val*x*proj.val-(hi : ℂ) • proj.val ≤ 0

namespace SpectralInterval
variable {x : M.toStarSubalgebra} (I : SpectralInterval x) (hx : IsSelfAdjoint x)

def midpoint : ℝ := (I.lo+I.hi)/2

def highProjection : AlgebraProjection M := cornerSpectralCut I.proj x I.midpoint

def lowProjection : AlgebraProjection M :=
  ⟨I.proj.val-(I.highProjection).val,
    (I.highProjection).property.sub_of_mul_eq_right I.proj.property
      (cornerSpectralCut_le I.proj x hx I.midpoint)⟩

theorem high_le (hx : IsSelfAdjoint x) : I.highProjection ≤ I.proj :=
  cornerSpectralCut_le I.proj x hx I.midpoint

theorem low_le : I.lowProjection hx ≤ I.proj := by
  change I.proj.val*(I.proj.val-(I.highProjection).val)=I.proj.val-I.highProjection.val
  rw [mul_sub,I.proj.property.isIdempotentElem.eq,I.high_le hx]

attribute [local instance] OAI.Generator.Tracial.intervalCStar
attribute [local instance] OAI.Generator.Tracial.intervalLE
def high : SpectralInterval x where
  proj := I.highProjection
  lo := I.midpoint
  hi := I.hi
  lower := cornerSpectralCut_lower I.proj x hx I.midpoint
  upper := upper_bound_compress (I.high_le hx) x I.hi I.upper

def low : SpectralInterval x where
  proj := I.lowProjection hx
  lo := I.lo
  hi := I.midpoint
  lower := lower_bound_compress (I.low_le hx) x I.lo I.lower
  upper := cornerSpectralCut_upper I.proj x hx I.midpoint

def child (b : Bool) : SpectralInterval x := if b then I.high hx else I.low hx

theorem child_le (b : Bool) : (I.child hx b).proj ≤ I.proj := by
  cases b
  · exact I.low_le hx
  · exact I.high_le hx

theorem child_width (b : Bool) :
    (I.child hx b).hi-(I.child hx b).lo=(I.hi-I.lo)/2 := by
  cases b <;> dsimp [child,high,low,midpoint] <;> ring

theorem child_total : (I.child hx false).proj.val+(I.child hx true).proj.val=I.proj.val := by
  change (I.proj.val-(I.highProjection).val)+(I.highProjection).val=I.proj.val
  exact sub_add_cancel _ _

theorem child_orthogonal (b c : Bool) (h : b ≠ c) :
    (I.child hx b).proj.val*(I.child hx c).proj.val=0 := by
  have hl : I.proj.val*(I.highProjection).val=(I.highProjection).val := I.high_le hx
  have hr := projection_mul_of_le (I.high_le hx)
  cases b <;> cases c
  · exact (h rfl).elim
  · change (I.proj.val-(I.highProjection).val)*(I.highProjection).val=0
    rw [sub_mul,hl,(I.highProjection).property.isIdempotentElem.eq,sub_self]
  · change (I.highProjection).val*(I.proj.val-(I.highProjection).val)=0
    rw [mul_sub,hr,(I.highProjection).property.isIdempotentElem.eq,sub_self]
  · exact (h rfl).elim

theorem child_compression_total :
    (I.child hx false).proj.val*x*(I.child hx false).proj.val+
    (I.child hx true).proj.val*x*(I.child hx true).proj.val=I.proj.val*x*I.proj.val := by
  have h := cornerSpectralPartition_pinch I.proj x hx I.midpoint
  rw [cornerSpectralPartition,CornerPartition.binary_pinch] at h
  exact (add_comm _ _).trans h

end SpectralInterval

end

/-! Finite dyadic trees of actual spectral interval cuts. -/
section
open scoped CStarAlgebra BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace SpectralInterval
variable {x : M.toStarSubalgebra} (I : SpectralInterval x) (hx : IsSelfAdjoint x)

def level (I : SpectralInterval x) (hx : IsSelfAdjoint x) : (n : ℕ) → DyadicIndex n → SpectralInterval x
  | 0,_ => I
  | n+1,i => (level I hx n i.1).child hx i.2

theorem level_le : ∀ n i, (I.level hx n i).proj ≤ I.proj
  | 0,_ => le_refl _
  | n+1,i => ((I.level hx n i.1).child_le hx i.2).trans (level_le n i.1)

theorem level_width : ∀ n i,
    (I.level hx n i).hi-(I.level hx n i).lo = (I.hi-I.lo)/(2:ℝ)^n
  | 0,_ => by simp [level]
  | n+1,i => by
    change ((I.level hx n i.1).child hx i.2).hi-
      ((I.level hx n i.1).child hx i.2).lo=_
    rw [child_width,level_width n i.1,pow_succ,div_div]

theorem level_total : ∀ n, (∑ i : DyadicIndex n, (I.level hx n i).proj.val)=I.proj.val
  | 0 => by
    change (∑ _ : Unit, I.proj.val)=I.proj.val
    simp
  | n+1 => by
    change (∑ i : DyadicIndex n × Bool, ((I.level hx n i.1).child hx i.2).proj.val)=_
    rw [Fintype.sum_prod_type]
    have he (i : DyadicIndex n) :
        (∑ b : Bool, ((I.level hx n i).child hx b).proj.val)=(I.level hx n i).proj.val := by
      rw [Fintype.sum_bool,add_comm,child_total]
    simp only [he]
    exact level_total n

theorem level_orthogonal : ∀ n (i j : DyadicIndex n), i ≠ j →
    (I.level hx n i).proj.val*(I.level hx n j).proj.val=0
  | 0,i,j,h => (h (@Subsingleton.elim Unit _ i j)).elim
  | n+1,⟨i,b⟩,⟨j,c⟩,h => by
    change ((I.level hx n i).child hx b).proj.val*((I.level hx n j).child hx c).proj.val=0
    by_cases hij : i=j
    · subst j
      exact (I.level hx n i).child_orthogonal hx b c (fun hbc => h (by cases hbc; rfl))
    · exact orthogonal_subprojections (level_orthogonal n i j hij)
        ((I.level hx n i).child_le hx b) ((I.level hx n j).child_le hx c)

theorem level_compression_total : ∀ n,
    (∑ i : DyadicIndex n, (I.level hx n i).proj.val*x*(I.level hx n i).proj.val) =
      I.proj.val*x*I.proj.val
  | 0 => by
    change (∑ _ : Unit, I.proj.val*x*I.proj.val)=I.proj.val*x*I.proj.val
    simp
  | n+1 => by
    change (∑ i : DyadicIndex n × Bool, ((I.level hx n i.1).child hx i.2).proj.val*x*
      ((I.level hx n i.1).child hx i.2).proj.val)=_
    rw [Fintype.sum_prod_type]
    have he (i : DyadicIndex n) :
        (∑ b : Bool, ((I.level hx n i).child hx b).proj.val*x*
          ((I.level hx n i).child hx b).proj.val)=
        (I.level hx n i).proj.val*x*(I.level hx n i).proj.val := by
      rw [Fintype.sum_bool,add_comm,child_compression_total]
    simp only [he]
    exact level_compression_total n

def partition (n : ℕ) : CornerPartition I.proj :=
  CornerPartition.ofFamily (fun i : DyadicIndex n => (I.level hx n i).proj)
    (I.level_orthogonal hx n) (I.level_total hx n)

theorem partition_pinch (n : ℕ) : (I.partition hx n).pinch x=I.proj.val*x*I.proj.val := by
  rw [partition,CornerPartition.ofFamily_pinch]
  exact I.level_compression_total hx n

end SpectralInterval

/-! Finite spectral approximations constructed by successive sign cuts.
The approximation bound is proved from the leaf intervals. -/

namespace SpectralInterval
variable {x : M.toStarSubalgebra} (I : SpectralInterval x) (hx : IsSelfAdjoint x)

attribute [local instance] OAI.Generator.Tracial.approximationCStar
attribute [local instance] OAI.Generator.Tracial.approximationOrder
attribute [local instance] OAI.Generator.Tracial.approximationPreorder
attribute [local instance] OAI.Generator.Tracial.approximationLE
attribute [local instance] OAI.Generator.Tracial.approximationStarOrder
theorem error_upper : I.proj.val*x*I.proj.val-(I.lo : ℂ) • I.proj.val ≤
    ((I.hi-I.lo : ℝ) : ℂ) • I.proj.val := by
  calc I.proj.val*x*I.proj.val-(I.lo : ℂ) • I.proj.val ≤
      (I.hi : ℂ) • I.proj.val-(I.lo : ℂ) • I.proj.val :=
        sub_le_sub_right (sub_nonpos.mp I.upper) _
    _ = _ := by rw [← sub_smul,Complex.ofReal_sub]

def approximant (n : ℕ) : M.toStarSubalgebra :=
  ∑ i : DyadicIndex n, ((I.level hx n i).lo : ℂ) • (I.level hx n i).proj.val

theorem approximant_error_sum (n : ℕ) :
    I.proj.val*x*I.proj.val-I.approximant hx n =
      ∑ i : DyadicIndex n, ((I.level hx n i).proj.val*x*(I.level hx n i).proj.val-
        ((I.level hx n i).lo : ℂ) • (I.level hx n i).proj.val) := by
  rw [Finset.sum_sub_distrib,I.level_compression_total hx]
  rfl

theorem approximant_error_nonneg (n : ℕ) :
    0 ≤ I.proj.val*x*I.proj.val-I.approximant hx n := by
  rw [I.approximant_error_sum hx]
  exact Finset.sum_nonneg (fun i _ => (I.level hx n i).lower)

theorem approximant_error_upper (n : ℕ) :
    I.proj.val*x*I.proj.val-I.approximant hx n ≤
      (((I.hi-I.lo)/(2:ℝ)^n : ℝ) : ℂ) • I.proj.val := by
  rw [I.approximant_error_sum hx]
  have he := Finset.sum_le_sum (s := (Finset.univ : Finset (DyadicIndex n)))
    (fun i _ => (I.level hx n i).error_upper)
  simp only [I.level_width hx] at he
  rw [← Finset.smul_sum,I.level_total hx] at he
  exact he

/-- Actual operator norm approximation, not an assumed energy budget. -/
theorem approximant_norm_error (n : ℕ) (hab : I.lo ≤ I.hi) :
    ‖I.proj.val*x*I.proj.val-I.approximant hx n‖ ≤ (I.hi-I.lo)/(2:ℝ)^n := by
  have hw : 0 ≤ (I.hi-I.lo)/(2:ℝ)^n := div_nonneg (sub_nonneg.mpr hab) (by positivity)
  calc ‖I.proj.val*x*I.proj.val-I.approximant hx n‖ ≤
      ‖(((I.hi-I.lo)/(2:ℝ)^n : ℝ) : ℂ) • I.proj.val‖ :=
        CStarAlgebra.norm_le_norm_of_le_of_nonneg (I.approximant_error_upper hx n)
          (I.approximant_error_nonneg hx n)
    _ = ((I.hi-I.lo)/(2:ℝ)^n)*‖I.proj.val‖ := by
      rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg hw]
    _ ≤ (I.hi-I.lo)/(2:ℝ)^n := by
      nlinarith only [mul_le_mul_of_nonneg_left I.proj.property.norm_le hw]

theorem exists_approximant (hab : I.lo ≤ I.hi) (ε : ℝ) (hε : 0 < ε) :
    ∃ n, ‖I.proj.val*x*I.proj.val-I.approximant hx n‖ < ε := by
  obtain ⟨n,hn⟩ := exists_nat_gt ((I.hi-I.lo)/ε)
  have hnp : (n : ℝ)<(2:ℝ)^n := by exact_mod_cast (show n < 2^n from Nat.lt_two_pow_self)
  have hbound : (I.hi-I.lo)/(2:ℝ)^n < ε := by
    rw [div_lt_iff₀ (by positivity : (0:ℝ)<2^n)]
    have hh := (div_lt_iff₀ hε).mp hn
    nlinarith [mul_lt_mul_of_pos_left hnp hε]
  exact ⟨n,(I.approximant_norm_error hx n hab).trans_lt hbound⟩

end SpectralInterval

attribute [local instance] OAI.Generator.Tracial.approximationCStar
attribute [local instance] OAI.Generator.Tracial.approximationOrder
attribute [local instance] OAI.Generator.Tracial.approximationPreorder
attribute [local instance] OAI.Generator.Tracial.approximationLE
attribute [local instance] OAI.Generator.Tracial.approximationStarOrder
/-- Start the construction with the actual operator norm bounds in any corner. -/
def initialSpectralInterval (p : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) : SpectralInterval x := by
  let oneP : AlgebraProjection M := ⟨1,IsStarProjection.one _⟩
  have hp : p ≤ oneP := one_mul _
  have hs (r : ℝ) : algebraMap ℝ M.toStarSubalgebra r=(r : ℂ) • (1 : M.toStarSubalgebra) := by
    rw [Algebra.algebraMap_eq_smul_one,Complex.coe_smul]
  refine ⟨p,-‖x‖,‖x‖,?_,?_⟩
  · apply lower_bound_compress hp x (-‖x‖)
    have h := hx.neg_algebraMap_norm_le_self
    rw [hs] at h
    change 0 ≤ 1*x*1-((-‖x‖ : ℝ) : ℂ) • (1 : M.toStarSubalgebra)
    simpa only [one_mul,mul_one,Complex.ofReal_neg,neg_smul] using sub_nonneg.mpr h
  · apply upper_bound_compress hp x ‖x‖
    have h := hx.le_algebraMap_norm_self
    rw [hs] at h
    change 1*x*1-(‖x‖ : ℂ) • (1 : M.toStarSubalgebra) ≤ 0
    simpa only [one_mul,mul_one] using sub_nonpos.mpr h

end

/-! Constructed cuts preserve commutation with other operators. -/
section
open scoped CStarAlgebra
open UltrapowerBridge ContinuousLinearMap LinearMap
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.spectralCommutationCStar
attribute [local instance] OAI.Generator.Tracial.spectralCommutationOrder
attribute [local instance] OAI.Generator.Tracial.spectralCommutationStarOrder
theorem positiveSupport_commutes_of_commutes (x y : M.toStarSubalgebra)
    (hxy : Commute x y) (hxys : Commute x (star y)) :
    Commute (positiveSupport x).val y := by
  have hpos := hxy.cfcₙ_real (fun t : ℝ => t⁺)
  have hposs := hxys.cfcₙ_real (fun t : ℝ => t⁺)
  change Commute x⁺ y at hpos
  change Commute x⁺ (star y) at hposs
  have hs : IsSelfAdjoint x⁺ := (CFC.posPart_nonneg x).isSelfAdjoint
  have hk := kernelProjection_commutes x⁺ y hpos hposs
  change Commute (1-(kernelProjection (star x⁺)).val) y
  rw [hs.star_eq]
  exact (Commute.one_left y).sub_left hk

end

/-! Spectral interval partitions in the commutant of a prescribed operator. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem positiveSupport_commutes_of_selfAdjoint {x y : M.toStarSubalgebra}
    (hx : IsSelfAdjoint x) (hxy : Commute x y) :
    Commute (positiveSupport x).val y :=
  positiveSupport_commutes_of_commutes x y hxy (selfAdjoint_commutes_star_right hx hxy)

theorem cornerSpectralCut_commutes_with (p : AlgebraProjection M) (x y : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) (hxy : Commute x y) (hp : Commute p.val y) (t : ℝ) :
    Commute (cornerSpectralCut p x t).val y := by
  apply positiveSupport_commutes_of_selfAdjoint (cornerSpectralShift_selfAdjoint p x hx t)
  have hscalar : Commute ((t : ℂ) • p.val) y := by
    show ((t : ℂ) • p.val)*y=y*((t : ℂ) • p.val)
    rw [smul_mul_assoc,mul_smul_comm,hp.eq]
  exact ((hp.mul_left hxy).mul_left hp).sub_left hscalar

namespace SpectralInterval
variable {x y : M.toStarSubalgebra} (I : SpectralInterval x) (hx : IsSelfAdjoint x)

theorem child_commutes (hxy : Commute x y) (hp : Commute I.proj.val y) (b : Bool) :
    Commute (I.child hx b).proj.val y := by
  have hq := cornerSpectralCut_commutes_with I.proj x y hx hxy hp I.midpoint
  cases b
  · exact hp.sub_left hq
  · exact hq

theorem level_commutes (hxy : Commute x y) (hp : Commute I.proj.val y) :
    ∀ n i, Commute (I.level hx n i).proj.val y
  | 0,_ => hp
  | n+1,i => (I.level hx n i.1).child_commutes hx hxy (level_commutes hxy hp n i.1) i.2

theorem partition_commutes (hxy : Commute x y) (hp : Commute I.proj.val y)
    (n : ℕ) (i : Fin (I.partition hx n).size) :
    Commute ((I.partition hx n).piece i).val y :=
  I.level_commutes hx hxy hp n _

end SpectralInterval

/-- One constructed partition preserves the whole displayed commutant,
not a separately selected partition for each test operator. -/
theorem exists_finite_spectral_approximation_preserving_commutant (p : AlgebraProjection M)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (ε : ℝ) (hε : 0 < ε) :
    ∃ (Q : CornerPartition p) (c : Fin Q.size → ℝ),
      Q.pinch x=p.val*x*p.val ∧
      (∀ y : M.toStarSubalgebra, Commute x y → Commute p.val y →
        ∀ i, Commute (Q.piece i).val y) ∧
      ‖p.val*x*p.val-∑ i, (c i : ℂ) • (Q.piece i).val‖ < ε := by
  let I := initialSpectralInterval p x hx
  have hI : I.lo ≤ I.hi := neg_le_self (norm_nonneg _)
  obtain ⟨n,hn⟩ := I.exists_approximant hx hI ε hε
  let e := (Fintype.equivFin (DyadicIndex n)).symm
  refine ⟨I.partition hx n,fun i => (I.level hx n (e i)).lo,I.partition_pinch hx n,
    fun y hxy hp => I.partition_commutes hx hxy hp n,?_⟩
  have he := Equiv.sum_comp e (fun i => ((I.level hx n i).lo : ℂ) • (I.level hx n i).proj.val)
  change ‖p.val*x*p.val-∑ i, ((I.level hx n (e i)).lo : ℂ) •
    (I.level hx n (e i)).proj.val‖ < ε
  rw [he]
  exact hn

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_SpectralDimension
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite spectral weights of the constructed projection dimension obey an
operator-norm bound. No linear trace on noncommuting elements is assumed. -/

/-! Construct the unique real spectral dimension value of each self-adjoint
operator by norm approximation. Global noncommuting additivity is not asserted. -/
section
open Filter
open scoped BigOperators Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
/-- Actual finite spectral approximants are Cauchy in their dimension values,
and their real limit controls every commuting spectral approximation. -/
theorem traceFreeDimension_exists_spectral_value
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    ∃ t : ℂ, t.im=0 ∧ IsDimensionSpectralValue hfactor hdiff x t := by
  classical
  have happrox (n : ℕ) :
      ∃ (Q : CornerPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M))
        (c : Fin Q.size → ℝ),
        (∀ y : M.toStarSubalgebra, Commute x y → ∀ i, Commute (Q.piece i).val y) ∧
        ‖x-∑ i, (c i : ℂ) • (Q.piece i).val‖ < 1/2^n := by
    obtain ⟨Q,c,_,hQ,herr⟩ := exists_finite_spectral_approximation_preserving_commutant
      ⟨1,IsStarProjection.one _⟩ x hx (1/2^n) (by positivity)
    exact ⟨Q,c,fun y hy => hQ y hy (Commute.one_left y),by simpa only [one_mul,mul_one] using herr⟩
  choose Q c hQ herr using happrox
  let f (n : ℕ) : ℂ := ∑ i, (c n i : ℂ)*(traceFreeDimension hfactor hdiff ((Q n).piece i) : ℂ)
  let a (n : ℕ) : M.toStarSubalgebra := ∑ i, (c n i : ℂ) • ((Q n).piece i).val
  have hbound (n : ℕ) (R : CornerPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M))
      (d : Fin R.size → ℂ) (hR : ∀ j, Commute (R.piece j).val x) :
      ‖f n-∑ j, d j*(traceFreeDimension hfactor hdiff (R.piece j) : ℂ)‖ ≤
        1/2^n+‖x-∑ j, d j • (R.piece j).val‖ := by
    have hc (i : Fin (Q n).size) (j : Fin R.size) :
        Commute ((Q n).piece i).val (R.piece j).val := hQ n _ (hR j).symm i
    have h := (Q n).dimension_weight_cross_norm_le hfactor hdiff hfinite R hc hunit
      (fun i => (c n i : ℂ)) d
    refine h.trans ?_
    have htri := dist_triangle (a n) x (∑ j, d j • (R.piece j).val)
    simp only [dist_eq_norm] at htri
    rw [norm_sub_rev (a n) x] at htri
    exact htri.trans (add_le_add (herr n).le le_rfl)
  have heps : Tendsto (fun n : ℕ => (1 : ℝ)/2^n) atTop (𝓝 0) := by
    simpa only [one_div_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)<1)
  have hf : CauchySeq f := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp (heps.eventually (gt_mem_nhds (half_pos hε)))
    refine ⟨N,?_⟩
    intro m hm n hn
    rw [dist_eq_norm]
    have h := hbound m (Q n) (fun i => (c n i : ℂ)) (hQ n x (Commute.refl x))
    have he := herr n
    have hm' := hN m hm
    have hn' := hN n hn
    change ‖f m-f n‖ ≤ _ at h
    linarith
  obtain ⟨t,ht⟩ := cauchySeq_tendsto_of_complete hf
  have him (n : ℕ) : (f n).im=0 := by simp [f]
  refine ⟨t,?_,?_⟩
  · have hi := Complex.continuous_im.tendsto t |>.comp ht
    exact tendsto_nhds_unique hi (by
      change Tendsto (fun n => (f n).im) atTop (𝓝 0)
      simpa only [him] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
  · intro R d hR
    apply le_of_tendsto_of_tendsto' ((ht.sub_const _).norm)
      (by simpa only [zero_add] using heps.add_const ‖x-∑ j, d j • (R.piece j).val‖)
    exact fun n => hbound n R d hR

/-- This is a constructed scalar value on self-adjoint operators; it is not
yet packaged as a linear functional. -/
def dimensionSpectralValue (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) : ℂ :=
  (traceFreeDimension_exists_spectral_value hfactor hdiff hfinite hunit x hx).choose

theorem dimensionSpectralValue_spec (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    (dimensionSpectralValue hfactor hdiff hfinite hunit x hx).im=0 ∧
      IsDimensionSpectralValue hfactor hdiff x
        (dimensionSpectralValue hfactor hdiff hfinite hunit x hx) :=
  (traceFreeDimension_exists_spectral_value hfactor hdiff hfinite hunit x hx).choose_spec

end

/-! The constructed spectral value is bounded and extends the actual
projection dimension. These laws do not assert noncommuting additivity. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem IsDimensionSpectralValue.on_projection (p : AlgebraProjection M) {t : ℂ}
    (ht : IsDimensionSpectralValue hfactor hdiff p.val t) :
    t=(traceFreeDimension hfactor hdiff p : ℂ) := by
  classical
  let r : AlgebraProjection M := ⟨1-p.val,p.property.one_sub⟩
  let a (b : Bool) : AlgebraProjection M := if b then r else p
  have hpr : p.val*r.val=0 := by
    change p.val*(1-p.val)=0
    rw [mul_sub,mul_one,p.property.isIdempotentElem.eq,sub_self]
  have ho (b c : Bool) (hbc : b≠c) : (a b).val*(a c).val=0 := by
    cases b <;> cases c
    · exact (hbc rfl).elim
    · exact hpr
    · exact PartialIsometry.orthogonal_reverse p r hpr
    · exact (hbc rfl).elim
  have ha : (∑ b : Bool, (a b).val)=(1 : M.toStarSubalgebra) := by
    change (∑ b : Bool, (if b then r else p).val)=1
    simp only [Fintype.sum_bool,ite_true, if_true,Bool.false_eq_true,ite_false, if_false]
    change (1-p.val)+p.val=1
    abel
  let Q : CornerPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) :=
    CornerPartition.ofFamily a ho ha
  let e : Fin Q.size ≃ Bool := (Fintype.equivFin Bool).symm
  let c (i : Fin Q.size) : ℂ := if e i then 0 else 1
  have hQ (i : Fin Q.size) : Commute (Q.piece i).val p.val := by
    change Commute (a (e i)).val p.val
    cases h : e i
    · exact Commute.refl p.val
    · exact (Commute.one_left p.val).sub_left (Commute.refl p.val)
  have hs : (∑ i, c i • (Q.piece i).val)=p.val := by
    change (∑ i, (if e i then (0 : ℂ) else 1) • (a (e i)).val)=p.val
    exact (Equiv.sum_comp e (fun b : Bool => (if b then (0 : ℂ) else 1) • (a b).val)).trans
      (by simp [a])
  have hw : (∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ))=
      (traceFreeDimension hfactor hdiff p : ℂ) := by
    change (∑ i, (if e i then (0 : ℂ) else 1)*
      (traceFreeDimension hfactor hdiff (a (e i)) : ℂ))=_
    exact (Equiv.sum_comp e (fun b : Bool => (if b then (0 : ℂ) else 1)*
      (traceFreeDimension hfactor hdiff (a b) : ℂ))).trans (by simp [a])
  have h := ht Q c hQ
  rw [hs,sub_self,norm_zero] at h
  exact (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))).trans hw

theorem dimensionSpectralValue_projection (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (p : AlgebraProjection M) :
    dimensionSpectralValue hfactor hdiff hfinite hunit p.val p.property.isSelfAdjoint=
      (traceFreeDimension hfactor hdiff p : ℂ) :=
  (dimensionSpectralValue_spec hfactor hdiff hfinite hunit p.val p.property.isSelfAdjoint).2.on_projection
    hfactor hdiff p

end

/-! Finite-family tests and real homogeneity for the constructed spectral value.
These statements do not assert additivity for noncommuting operators. -/
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem IsDimensionSpectralValue.family_bound {x : M.toStarSubalgebra} {t : ℂ}
    (ht : IsDimensionSpectralValue hfactor hdiff x t)
    {I : Type*} [Fintype I] (q : I → AlgebraProjection M)
    (ho : ∀ i j, i≠j → (q i).val*(q j).val=0)
    (hs : ∑ i, (q i).val=(1 : M.toStarSubalgebra))
    (c : I → ℂ) (hc : ∀ i, Commute (q i).val x) :
    ‖t-∑ i, c i*(traceFreeDimension hfactor hdiff (q i) : ℂ)‖ ≤
      ‖x-∑ i, c i • (q i).val‖ := by
  classical
  let Q : CornerPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) :=
    CornerPartition.ofFamily q ho hs
  let e : Fin Q.size ≃ I := (Fintype.equivFin I).symm
  have h := ht Q (fun i => c (e i)) (fun i => hc (e i))
  change ‖t-∑ i, c (e i)*(traceFreeDimension hfactor hdiff (q (e i)) : ℂ)‖ ≤
    ‖x-∑ i, c (e i) • (q (e i)).val‖ at h
  rw [Equiv.sum_comp e (fun i => c i*(traceFreeDimension hfactor hdiff (q i) : ℂ)),
    Equiv.sum_comp e (fun i => c i • (q i).val)] at h
  exact h

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_SpectralStates
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Additivity on commuting self-adjoint operators, proved using actual common
spectral refinements. The commutation hypothesis is essential to this proof. -/
open scoped BigOperators

/-! Positive spectral approximants, positivity of the constructed scalar, and
order preservation on commuting self-adjoint operators. -/
open scoped BigOperators CStarAlgebra

/-! A nonzero positive operator dominates a positive multiple of an actual
nonzero spectral projection. This proves faithfulness without linearity. -/
open scoped CStarAlgebra

/-! Unitary conjugacy preserves projection dimension and its constructed
spectral extension. No trace identity is assumed. -/
open scoped BigOperators
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem AlgebraProjection.equivalent_unitaryConjugate (p : AlgebraProjection M)
    (u : unitary M.toStarSubalgebra) : p.Equivalent (p.unitaryConjugate u) := by
  let v : PartialIsometry M :=
    { support := p
      val := (u : M.toStarSubalgebra)*p.val
      initial := by
        simp only [star_mul,p.property.isSelfAdjoint.star_eq]
        rw [mul_assoc,← mul_assoc (star (u : M.toStarSubalgebra)),
          Unitary.star_mul_self_of_mem u.property,one_mul,p.property.isIdempotentElem.eq] }
  refine ⟨v,rfl,?_⟩
  apply Subtype.ext
  change ((u : M.toStarSubalgebra)*p.val)*star ((u : M.toStarSubalgebra)*p.val)=
    (u : M.toStarSubalgebra)*p.val*star (u : M.toStarSubalgebra)
  simp only [star_mul,p.property.isSelfAdjoint.star_eq,mul_assoc]
  rw [← mul_assoc p.val,p.property.isIdempotentElem.eq]

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem traceFreeDimension_unitaryConjugate (p : AlgebraProjection M)
    (u : unitary M.toStarSubalgebra) :
    traceFreeDimension hfactor hdiff (p.unitaryConjugate u)=traceFreeDimension hfactor hdiff p :=
  (traceFreeDyadicSup_equivalent hfactor hdiff ⟨1,IsStarProjection.one _⟩
    (p.equivalent_unitaryConjugate u)).symm

theorem dimensionSpectralValue_unitary_conjugate
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (u : unitary M.toStarSubalgebra) (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    dimensionSpectralValue hfactor hdiff hfinite hunit
      (Unitary.conjStarAlgAut ℂ M.toStarSubalgebra u x)
      (hx.map (Unitary.conjStarAlgAut ℂ M.toStarSubalgebra u))=
      dimensionSpectralValue hfactor hdiff hfinite hunit x hx := by
  classical
  let φ := Unitary.conjStarAlgAut ℂ M.toStarSubalgebra u
  have hnorm (a : M.toStarSubalgebra) : ‖φ a‖=‖a‖ := by
    change ‖((u : M.toStarSubalgebra)*a)*(star u : unitary M.toStarSubalgebra)‖=‖a‖
    rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨Q,c,_,hQ,herr⟩ := exists_finite_spectral_approximation_preserving_commutant
    ⟨1,IsStarProjection.one _⟩ x hx (ε/2) (half_pos hε)
  simp only [one_mul,mul_one] at herr
  have hc := hQ x (Commute.refl x) (Commute.one_left x)
  let q (i : Fin Q.size) := (Q.piece i).unitaryConjugate u
  have ho (i j : Fin Q.size) (hij : i≠j) : (q i).val*(q j).val=0 := by
    change φ (Q.piece i).val*φ (Q.piece j).val=0
    exact (map_mul φ (Q.piece i).val (Q.piece j).val).symm.trans
      ((congrArg φ (Q.orthogonal i j hij)).trans (map_zero φ))
  have hs : (∑ i, (q i).val)=(1 : M.toStarSubalgebra) := by
    change (∑ i, φ (Q.piece i).val)=1
    exact (map_sum φ (fun i => (Q.piece i).val) Finset.univ).symm.trans
      ((congrArg φ Q.total).trans (map_one φ))
  have hcomm (i : Fin Q.size) : Commute (q i).val (φ x) :=
    (hc i).map φ
  have hmap : (∑ i, (c i : ℂ) • (q i).val)=φ (∑ i, (c i : ℂ) • (Q.piece i).val) := by
    change (∑ i, (c i : ℂ) • φ (Q.piece i).val)=_
    simp only [map_sum,map_smul]
  have hval := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit (φ x) (hx.map φ)).2.family_bound
    hfactor hdiff q ho hs (fun i => (c i : ℂ)) hcomm
  have hweight : (∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (q i) : ℂ))=
      ∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ) := by
    simp only [q,traceFreeDimension_unitaryConjugate hfactor hdiff]
  have hval' :
      ‖dimensionSpectralValue hfactor hdiff hfinite hunit (φ x) (hx.map φ) -
        ∑ i, (c i : ℂ) * (traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)‖ ≤
      ‖x - ∑ i, (c i : ℂ) • (Q.piece i).val‖ := by
    calc
      _ = ‖dimensionSpectralValue hfactor hdiff hfinite hunit (φ x) (hx.map φ) -
          ∑ i, (c i : ℂ) * (traceFreeDimension hfactor hdiff (q i) : ℂ)‖ :=
        congrArg (fun z : ℂ => ‖dimensionSpectralValue hfactor hdiff hfinite hunit
          (φ x) (hx.map φ) - z‖) hweight.symm
      _ ≤ ‖φ x - ∑ i, (c i : ℂ) • (q i).val‖ := hval
      _ = ‖φ (x - ∑ i, (c i : ℂ) • (Q.piece i).val)‖ :=
        congrArg (fun z : M.toStarSubalgebra => ‖z‖)
          ((congrArg (fun z => φ x - z) hmap).trans (map_sub φ x _).symm)
      _ = _ := hnorm _
  have hxval := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx).2
    Q (fun i => (c i : ℂ)) hc
  have htri := dist_triangle
    (dimensionSpectralValue hfactor hdiff hfinite hunit (φ x) (hx.map φ))
    (∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ))
    (dimensionSpectralValue hfactor hdiff hfinite hunit x hx)
  simp only [dist_eq_norm] at htri
  rw [norm_sub_rev (∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ))
    (dimensionSpectralValue hfactor hdiff hfinite hunit x hx)] at htri
  change ‖dimensionSpectralValue hfactor hdiff hfinite hunit (φ x) (hx.map φ)-
    dimensionSpectralValue hfactor hdiff hfinite hunit x hx‖ ≤ 0+ε
  linarith only [htri,hval',hxval,herr]

end

/-! The constructed scalar agrees on x*x and xx*, by an actual unitary polar
decomposition. This is a quadratic identity, not unrestricted additivity. -/
open scoped CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.spectralSquareCStar
attribute [local instance] OAI.Generator.Tracial.spectralSquareOrder
attribute [local instance] OAI.Generator.Tracial.spectralSquareStarOrder
theorem dimensionSpectralValue_star_mul_self
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (x : M.toStarSubalgebra) :
    dimensionSpectralValue hfactor hdiff hfinite hunit (star x*x) (IsSelfAdjoint.star_mul_self x)=
      dimensionSpectralValue hfactor hdiff hfinite hunit (x*star x) (IsSelfAdjoint.mul_star_self x) := by
  obtain ⟨u,hu⟩ := exists_unitary_polar_decomposition hfactor hfinite x
  let a := CFC.sqrt (star x*x)
  have ha : star a=a := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  have haa : a*a=star x*x := CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg _)
  have he : Unitary.conjStarAlgAut ℂ M.toStarSubalgebra u (star x*x)=x*star x := by
    change (u : M.toStarSubalgebra)*(star x*x)*star (u : M.toStarSubalgebra)=x*star x
    calc _ = ((u : M.toStarSubalgebra)*a)*star ((u : M.toStarSubalgebra)*a) := by
           rw [star_mul,ha,← haa]
           simp only [mul_assoc]
      _ = x*star x := by rw [hu]
  have h := dimensionSpectralValue_unitary_conjugate hfactor hdiff hfinite hunit
    u (star x*x) (IsSelfAdjoint.star_mul_self x)
  simpa only [he] using h.symm

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_LocalizedStates
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Localization of actual signed vector/dimension values. Fixed strict
sublevel sets, rather than a limiting strict inequality, supply Zorn bounds. -/
open Filter
open scoped Topology
section
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace AlgebraProjection

/-- A continuous orthogonally additive real charge nonnegative on G admits a
nonzero corner all of whose subprojections have nonnegative charge. -/
theorem exists_nonnegative_corner
    (μ : AlgebraProjection M → ℝ)
    (hadd : ∀ p q (ho : p.val*q.val=0), μ (orthogonalSum p q ho)=μ p+μ q)
    (hcont : ∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
      (a : I → AlgebraProjection M), Monotone a →
      ∀ p, IsLUB (Set.range a) p → Tendsto (fun i => μ (a i)) atTop (𝓝 (μ p)))
    (G : AlgebraProjection M) (hG : G.val≠0) (hμG : 0 ≤ μ G) :
    ∃ F : AlgebraProjection M, F ≤ G ∧ F.val≠0 ∧ ∀ p, p ≤ F → 0 ≤ μ p := by
  classical
  by_cases hall : ∀ p : AlgebraProjection M, p ≤ G → 0 ≤ μ p
  · exact ⟨G,le_rfl,hG,hall⟩
  push Not at hall
  obtain ⟨r,hrG,hr⟩ := hall
  let S : Set (AlgebraProjection M) := {p | p ≤ G ∧ μ p ≤ μ r}
  obtain ⟨v,hv⟩ := zorn_le₀ S (by
    intro c hc hchain
    by_cases hne : c.Nonempty
    · let : Nonempty c := hne.to_subtype
      let : IsDirected c (· ≤ ·) := ⟨by
        intro a b
        rcases hchain.total a.property b.property with h | h
        · exact ⟨b,h,le_rfl⟩
        · exact ⟨a,le_rfl,h⟩⟩
      obtain ⟨p,hp⟩ := exists_isLUB_monotone (fun q : c => q.val) (fun _ _ h => h)
      refine ⟨p,⟨?_,?_⟩,fun q hq => hp.1 ⟨⟨q,hq⟩,rfl⟩⟩
      · exact hp.2 (by rintro _ ⟨q,rfl⟩; exact (hc q.property).1)
      · exact le_of_tendsto (hcont c (fun q : c => q.val) (fun _ _ h => h) p hp)
          (Eventually.of_forall (fun q => (hc q.property).2))
    · exact ⟨r,⟨hrG,le_rfl⟩,fun q hq => (hne ⟨q,hq⟩).elim⟩)
  have hvG : v ≤ G := hv.1.1
  have hvneg : μ v < 0 := hv.1.2.trans_lt hr
  let F := remainder v G hvG
  have hF : F.val≠0 := by
    intro hz
    have he : G=v := Subtype.ext (sub_eq_zero.mp hz)
    rw [he] at hμG
    exact (not_lt_of_ge hμG) hvneg
  refine ⟨F,remainder_le v G hvG,hF,?_⟩
  intro p hp
  by_contra hnot
  have hpneg : μ p<0 := lt_of_not_ge hnot
  have ho : v.val*p.val=0 := projection_orthogonal_of_le
    (remainder_orthogonal v G hvG) le_rfl hp
  let q := orthogonalSum v p ho
  have hqG : q ≤ G := orthogonalSum_le ho hvG (hp.trans (remainder_le v G hvG))
  have he : μ q=μ v+μ p := hadd v p ho
  have hqμ : μ q ≤ μ r := by linarith [hv.1.2]
  have hqv : q ≤ v := hv.2 ⟨hqG,hqμ⟩ (le_orthogonalSum_left _ _ ho)
  have hqeq : q=v := le_antisymm hqv (le_orthogonalSum_left _ _ ho)
  rw [hqeq] at he
  linarith

end AlgebraProjection

end

/-! Tight multiplicative localization of an actual Hilbert vector functional
against the constructed projection dimension. The corner is constructed. -/

/-! Positive spectral approximants inside an actual projection corner, and
extension of localized projection inequalities to positive operators. -/
open scoped BigOperators CStarAlgebra

/-! Projection localization yields actual positive-operator inequalities for
bounded linear functionals, and a nearly cyclic functional on the corner. -/
open scoped BigOperators CStarAlgebra

/-! An actual positive normalized vector functional with arbitrarily small
multiplicative failure of cyclicity on a nonzero corner. No trace is assumed. -/
open scoped CStarAlgebra

/-! A full finite matrix partition can be rebased into every nonzero corner.
The legs are constructed partial isometries, not assumed matrix units. -/
open scoped BigOperators

/-! Extension of a vector functional through actual matrix-partition legs.
Finite coefficient identities transfer the corner quadratic inequality. -/
open scoped BigOperators CStarAlgebra

/-! Globally defined positive unital linear functionals with arbitrarily small multiplicative quadratic trace error. -/
open scoped BigOperators CStarAlgebra

end Generator.Tracial

end

end OAI
end


