-- Prove2me | Definitions.Def_OAIQ129G003
-- name    : OAIQ129G003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T20:17:08.164896+00:00
-- url     : https://prove2.me/theorems/5d36e618-6883-4b1c-a48d-65f89d1f9de3
-- title:
--   Definitions bundle OAIQ129G003 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 132 declarations of OpenAI's Lean: 16 definitions, 1 instance and 115 theorems. The definitions and types are `OAI.Generator.Tracial.AlgebraProjection.Equivalent`, `OAI.Generator.Tracial.AlgebraProjection.remainder`, `OAI.Generator.Tracial.CornerPartition.jointPiece`, `OAI.Generator.Tracial.EquivalentPartition.link`, `OAI.Generator.Tracial.IsDimensionSpectralValue`, `OAI.Generator.Tracial.centralSupport`, `OAI.Generator.Tracial.intervalCStar`, `OAI.Generator.Tracial.intervalLE`, `OAI.Generator.Tracial.positiveSupportCStar`, `OAI.Generator.Tracial.projectionOrbitClosure`, `OAI.Generator.Tracial.projectionOrbitVectors`, `OAI.Generator.Tracial.traceFreeBinaryPartition`, `OAI.Generator.Tracial.traceFreeDimension`, `OAI.Generator.Tracial.traceFreeDyadicCut`, `OAI.Generator.Tracial.traceFreeDyadicPartition`, `OAI.Generator.Tracial.traceFreeDyadicSup`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_Dimension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Dimension.lean), [`FactorGeneration_DyadicComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/DyadicComparison.lean), [`FactorGeneration_FiniteComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/FiniteComparison.lean), [`FactorGeneration_Pinching`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Pinching.lean), [`FactorGeneration_ProjectionComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/ProjectionComparison.lean), [`FactorGeneration_ProjectionLimits`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/ProjectionLimits.lean), [`FactorGeneration_SpectralApproximation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/SpectralApproximation.lean), [`FactorGeneration_SpectralDimension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/SpectralDimension.lean), [`FactorGeneration_SpectralPinching`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/SpectralPinching.lean), [`FactorGeneration_Supports`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Supports.lean).
--
--   **Imports.** It imports the bundles `OAIQ129G000` and `OAIQ129G001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ129G007`, `OAIQ129G008` and `OAIQ129G009`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ129G000
import Definitions.Def_OAIQ129G001

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
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
end OAIVecLookup
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_ProjectionLimits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A nonzero projection in a diffuse tracial algebra contains nonzero projections of arbitrarily small trace. -/

/-! Monotone projection limits with trace bounds, giving chain bounds for prescribed trace cuts. -/

/-! Exact trace cuts in a diffuse coordinate algebra. -/

/-! Algebraic part of Popa 1308.3982v3, Lemma 3.2: adding a supported
partial unitary in the residual corner. The small mixed-word estimates and
the existence of an appropriate patch are separate analytic requirements. -/

/-! Dyadic projections inside a diffuse algebra with faithful trace. -/
section
open UltrapowerBridge
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem card_dyadicIndex (n : ℕ) : Fintype.card (DyadicIndex n) = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih => change Fintype.card (DyadicIndex n × Bool) = _; simp [ih,pow_succ]

variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)

theorem orthogonal_subprojections {p q a b : AlgebraProjection M}
    (hpq : p.val*q.val=0) (ha : a ≤ p) (hb : b ≤ q) : a.val*b.val=0 := by
  calc a.val*b.val = (a.val*p.val)*(q.val*b.val) := by rw [projection_mul_of_le ha,hb]
       _ = a.val*(p.val*q.val)*b.val := by simp only [mul_assoc]
       _ = 0 := by rw [hpq,mul_zero,zero_mul]

end

/-! Finite spectral sums in the constructed dyadic projection algebras. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Supports
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.Generator.vectorOrbitClosure_complete
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

theorem mul_kernelProjection (x : M.toStarSubalgebra) : x*(kernelProjection x).val=0 := by
  apply Subtype.ext
  ext ξ
  exact Submodule.starProjection_apply_mem x.val.ker ξ

theorem kernelProjection_fixes (x : M.toStarSubalgebra) (ξ : H) (hξ : x.val ξ=0) :
    ((kernelProjection x).val : H →L[ℂ] H) ξ=ξ :=
  Submodule.starProjection_eq_self_iff.mpr hξ

/-- This is the largest algebra projection annihilated on the left by x. -/
theorem le_kernelProjection_iff (x : M.toStarSubalgebra) (q : AlgebraProjection M) :
    q ≤ kernelProjection x ↔ x*q.val=0 := by
  constructor
  · intro h
    calc x*q.val = x*((kernelProjection x).val*q.val) := by rw [h]
      _ = 0 := by rw [← mul_assoc,mul_kernelProjection,zero_mul]
  · intro h
    apply Subtype.ext
    ext ξ
    apply kernelProjection_fixes
    have he := congrArg (fun t : M.toStarSubalgebra => (t : H →L[ℂ] H) ξ) h
    exact he

theorem rangeProjection_mul (x : M.toStarSubalgebra) : (rangeProjection x).val*x=x := by
  have h := congrArg star (mul_kernelProjection (star x))
  simp only [star_mul,(kernelProjection (star x)).property.isSelfAdjoint.star_eq,
    star_star,star_zero] at h
  change (1-(kernelProjection (star x)).val)*x=x
  rw [sub_mul,one_mul,h,sub_zero]

/-- Minimality retains any prescribed corner supporting x. -/
theorem rangeProjection_le_iff (x : M.toStarSubalgebra) (q : AlgebraProjection M) :
    rangeProjection x ≤ q ↔ q.val*x=x := by
  constructor
  · intro h
    calc q.val*x = q.val*((rangeProjection x).val*x) := by rw [rangeProjection_mul]
      _ = x := by rw [← mul_assoc,h,rangeProjection_mul]
  · intro h
    let r : AlgebraProjection M := ⟨1-q.val,q.property.one_sub⟩
    have hz : star x*r.val=0 := by
      have hh := congrArg star h
      simp only [star_mul,q.property.isSelfAdjoint.star_eq] at hh
      change star x*(1-q.val)=0
      rw [mul_sub,mul_one,hh,sub_self]
    have hr := (le_kernelProjection_iff (star x) r).mpr hz
    have hs := projection_mul_of_le hr
    change (1-q.val)*(kernelProjection (star x)).val=1-q.val at hs
    change q.val*(1-(kernelProjection (star x)).val)=1-(kernelProjection (star x)).val
    simp only [sub_mul,one_mul] at hs
    simp only [mul_sub,mul_one]
    apply (sub_eq_sub_iff_add_eq_add).mpr
    have hh := (sub_eq_sub_iff_add_eq_add).mp hs
    simpa only [add_comm,add_left_comm,add_assoc] using hh

end

/-! Spectral sign cuts from continuous positive parts and actual range projections.
These are constructed operators, not assumed Borel functional calculus data. -/
open scoped CStarAlgebra
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance positiveSupportCStar : CStarAlgebra M.toStarSubalgebra := {}

end

/-! A polar operator is constructed by extending the isometry on a range.
No polar-decomposition or projection-comparison hypothesis is used. -/

/-! Polar decomposition inside the given concrete von Neumann algebra. -/
open scoped CStarAlgebra
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem rangeProjection_eq_closure_projection (x : M.toStarSubalgebra) :
    ((rangeProjection x).val : H →L[ℂ] H) = x.val.range.topologicalClosure.starProjection := by
  have he : (star x.val).kerᗮ = x.val.range.topologicalClosure := by
    simpa only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_adjoint]
      using (star x.val).orthogonal_ker
  change 1-(star x.val).ker.starProjection = _
  have hh := (Submodule.starProjection_orthogonal (star x.val).ker).symm
  simp only [he] at hh
  exact hh

attribute [local instance] OAI.Generator.Tracial.polarCStar
attribute [local instance] OAI.Generator.Tracial.polarOrder
attribute [local instance] OAI.Generator.Tracial.polarStarOrder
theorem exists_polar_decomposition (x : M.toStarSubalgebra) :
    ∃ v : M.toStarSubalgebra,
      v * CFC.sqrt (star x*x) = x ∧
      star v*v = (rangeProjection (CFC.sqrt (star x*x))).val ∧
      v*(rangeProjection (CFC.sqrt (star x*x))).val=v := by
  let a := CFC.sqrt (star x*x)
  have ha : IsSelfAdjoint a := (CFC.sqrt_nonneg _).isSelfAdjoint
  have haa : a*a=star x*x := CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg _)
  have hn (ξ : H) : ‖x.val ξ‖=‖a.val ξ‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have he := congrArg (fun t : M.toStarSubalgebra =>
      inner ℂ ξ ((t : H →L[ℂ] H) ξ)) haa
    have has : star a.val=a.val := congrArg Subtype.val ha.star_eq
    have hs (z : H →L[ℂ] H) : inner ℂ ξ ((star z*z) ξ) = (‖z ξ‖ : ℂ)^2 := by
      rw [mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right,inner_self_eq_norm_sq_to_K]
      rfl
    have he' : (‖a.val ξ‖ : ℂ)^2 = (‖x.val ξ‖ : ℂ)^2 := by
      calc _ = inner ℂ ξ ((star a.val*a.val) ξ) := (hs _).symm
           _ = inner ℂ ξ ((star x.val*x.val) ξ) := by rw [has]; exact he
           _ = _ := hs _
    exact_mod_cast he'.symm
  obtain ⟨v,hva,hvi,hvs⟩ := exists_isometric_range_factor a.val x.val hn
  let s := rangeProjection a
  have hs : (s.val : H →L[ℂ] H)=a.val.range.topologicalClosure.starProjection :=
    rangeProjection_eq_closure_projection a
  rw [← hs] at hvi hvs
  have hmem : v ∈ M := by
    rw [← M.commutant_commutant]
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro y hy
    have hya := (VonNeumannAlgebra.mem_commutant_iff.mp hy) a.val a.property
    have hyx := (VonNeumannAlgebra.mem_commutant_iff.mp hy) x.val x.property
    have hys := (VonNeumannAlgebra.mem_commutant_iff.mp hy) s.val.val s.val.property
    have hz : (y*v-v*y)*a.val=0 := by
      rw [sub_mul,mul_assoc,hva,mul_assoc,← hya,← mul_assoc,hva,hyx,sub_self]
    have hd := mul_closure_range_projection_eq_zero a.val (y*v-v*y) hz
    rw [← hs,sub_mul,mul_assoc,hvs,mul_assoc,← hys,← mul_assoc,hvs] at hd
    exact sub_eq_zero.mp hd
  exact ⟨⟨v,hmem⟩,Subtype.ext hva,Subtype.ext hvi,Subtype.ext hvs⟩

end

/-! Exact initial and final support projections of the constructed polar part. -/
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
attribute [local instance] OAI.Generator.Tracial.polarSupportsCStar
attribute [local instance] OAI.Generator.Tracial.polarSupportsOrder
local instance polarSupportsStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

theorem sqrt_rangeProjection (x : M.toStarSubalgebra) :
    rangeProjection (CFC.sqrt (star x*x)) = rangeProjection (star x) := by
  let a := CFC.sqrt (star x*x)
  have ha : star a=a := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  have he : star a.val*a.val=star x.val*x.val := by
    change ((star a*a : M.toStarSubalgebra) : H →L[ℂ] H)=_
    rw [ha,CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg _)]
    rfl
  have hk (z : H →L[ℂ] H) : (star z*z).ker=z.ker := by
    exact z.ker_adjoint_comp_self
  have hker : a.val.ker=x.val.ker := by rw [← hk a.val,he,hk]
  apply Subtype.ext
  apply Subtype.ext
  change 1-(star a.val).ker.starProjection=1-(star (star x.val)).ker.starProjection
  have has : star a.val=a.val := congrArg Subtype.val ha
  simp only [has,star_star,hker]

theorem exists_polar_with_supports (x : M.toStarSubalgebra) :
    ∃ v : M.toStarSubalgebra,
      v*CFC.sqrt (star x*x)=x ∧
      star v*v=(rangeProjection (star x)).val ∧
      v*star v=(rangeProjection x).val := by
  obtain ⟨v,hvx,hvi,hvs⟩ := exists_polar_decomposition x
  let a := CFC.sqrt (star x*x)
  let s := rangeProjection a
  have ht : IsStarProjection (v*star v) := by
    constructor
    · change (v*star v)*(v*star v)=v*star v
      calc _ = (v*(star v*v))*star v := by simp only [mul_assoc]
           _ = v*star v := by rw [hvi,hvs]
    · exact IsSelfAdjoint.mul_star_self v
  let t : AlgebraProjection M := ⟨v*star v,ht⟩
  have hxt : rangeProjection x ≤ t := by
    apply (rangeProjection_le_iff x t).mpr
    change (v*star v)*x=x
    calc _ = (v*star v)*(v*a) := by rw [hvx]
         _ = (v*(star v*v))*a := by simp only [mul_assoc]
         _ = x := by rw [hvi,hvs,hvx]
  have htx : t ≤ rangeProjection x := by
    let r := rangeProjection x
    have hz : (r.val*v-v)*a=0 := by
      rw [sub_mul,mul_assoc,hvx,rangeProjection_mul,sub_self]
    have he := mul_closure_range_projection_eq_zero a.val
      ((r.val*v-v : M.toStarSubalgebra) : H →L[ℂ] H)
      (congrArg Subtype.val hz)
    rw [← rangeProjection_eq_closure_projection a] at he
    have he' : (r.val*v-v)*s.val=0 := Subtype.ext he
    rw [sub_mul,mul_assoc,hvs] at he'
    change r.val*(v*star v)=v*star v
    rw [← mul_assoc,sub_eq_zero.mp he']
  refine ⟨v,hvx,?_,?_⟩
  · simpa only [sqrt_rangeProjection] using hvi
  · exact congrArg (fun z : AlgebraProjection M => z.val) (le_antisymm htx hxt)

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_ProjectionComparison
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A nonzero coefficient linking two projections produces an actual nonzero
partial isometry between subprojections. Scalar center supplies such coefficients. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem exists_partialIsometry_of_link (p q : AlgebraProjection M)
    (x : M.toStarSubalgebra) (hxp : x*p.val=x) (hqx : q.val*x=x) (hx : x≠0) :
    ∃ v : PartialIsometry M, v.support ≤ p ∧ v.target ≤ q ∧ v.support.val≠0 := by
  obtain ⟨v,hvx,hvi,hvf⟩ := exists_polar_with_supports x
  let w : PartialIsometry M := ⟨rangeProjection (star x),v,hvi⟩
  refine ⟨w,?_,?_,?_⟩
  · apply (rangeProjection_le_iff (star x) p).mpr
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq] using congrArg star hxp
  · have ht : w.target=rangeProjection x := Subtype.ext hvf
    rw [ht]
    exact (rangeProjection_le_iff x q).mpr hqx
  · intro hz
    have hv0 : v=0 := (CStarRing.star_mul_self_eq_zero_iff _).mp (hvi.trans hz)
    rw [hv0,zero_mul] at hvx
    exact hx hvx.symm

end

/-! Projection comparison and equal-trace equivalence in the actual factor.
Both polar decomposition and the maximal partial isometry are constructed. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_FiniteComparison
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.CornerPartition.single_pinch
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
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def projectionOrbitVectors (p : AlgebraProjection M) : Set H :=
  {y | ∃ a : M.toStarSubalgebra, ∃ x : H, y=a.val (p.val.val x)}

def projectionOrbitClosure (p : AlgebraProjection M) : Submodule ℂ H :=
  (Submodule.span ℂ (projectionOrbitVectors p)).topologicalClosure

instance projectionOrbitClosure_complete (p : AlgebraProjection M) :
    CompleteSpace (projectionOrbitClosure p) :=
  inferInstanceAs (CompleteSpace (Submodule.span ℂ (projectionOrbitVectors p)).topologicalClosure)

theorem projectionOrbitClosure_invariant_of_vectors (p : AlgebraProjection M)
    (T : H →L[ℂ] H)
    (hT : ∀ y ∈ projectionOrbitVectors p, T y ∈ projectionOrbitVectors p) :
    ∀ y ∈ projectionOrbitClosure p, T y ∈ projectionOrbitClosure p := by
  have h : projectionOrbitClosure p ≤ (projectionOrbitClosure p).comap T.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      intro y hy
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span (hT y hy))
    · exact (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  exact fun y hy => h hy

theorem projectionOrbitClosure_invariant (p : AlgebraProjection M) (a : M.toStarSubalgebra) :
    ∀ y ∈ projectionOrbitClosure p, a.val y ∈ projectionOrbitClosure p := by
  apply projectionOrbitClosure_invariant_of_vectors
  rintro y ⟨b,x,rfl⟩
  exact ⟨a*b,x,rfl⟩

theorem projectionOrbitClosure_commutant_invariant (p : AlgebraProjection M)
    (T : H →L[ℂ] H) (hT : T ∈ M.commutant) :
    ∀ y ∈ projectionOrbitClosure p, T y ∈ projectionOrbitClosure p := by
  apply projectionOrbitClosure_invariant_of_vectors
  rintro y ⟨a,x,rfl⟩
  refine ⟨a,T x,?_⟩
  have ha := VonNeumannAlgebra.mem_commutant_iff.mp hT a.val a.property
  have hp := VonNeumannAlgebra.mem_commutant_iff.mp hT p.val.val p.val.property
  have hea := congrArg (fun R : H →L[ℂ] H => R (p.val.val x)) ha
  have hep := congrArg (fun R : H →L[ℂ] H => R x) hp
  change a.val (T (p.val.val x))=T (a.val (p.val.val x)) at hea
  change p.val.val (T x)=T (p.val.val x) at hep
  exact hea.symm.trans (congrArg a.val hep.symm)

theorem projectionOrbitProjection_mem (p : AlgebraProjection M) :
    (projectionOrbitClosure p).starProjection ∈ M := by
  apply (VonNeumannAlgebra.IsStarProjection.mem_iff
    isStarProjection_starProjection M).mpr
  intro T hT
  rw [Submodule.range_starProjection]
  exact projectionOrbitClosure_commutant_invariant p T hT

def centralSupport (p : AlgebraProjection M) : AlgebraProjection M :=
  ⟨⟨(projectionOrbitClosure p).starProjection, projectionOrbitProjection_mem p⟩, by
    constructor
    · apply Subtype.ext
      exact (isStarProjection_starProjection (U := projectionOrbitClosure p)).isIdempotentElem.eq
    · apply Subtype.ext
      exact (isStarProjection_starProjection (U := projectionOrbitClosure p)).isSelfAdjoint.star_eq⟩

theorem centralSupport_commutes (p : AlgebraProjection M) (a : M.toStarSubalgebra) :
    a*(centralSupport p).val=(centralSupport p).val*a := by
  apply Subtype.ext
  exact (Generator.starProjection_commutes_of_invariant (projectionOrbitClosure p) a.val
    (projectionOrbitClosure_invariant p a)
    (projectionOrbitClosure_invariant p (star a))).symm

theorem le_centralSupport (p : AlgebraProjection M) : p ≤ centralSupport p := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  apply Submodule.starProjection_eq_self_iff.mpr
  apply Submodule.le_topologicalClosure
  exact Submodule.subset_span ⟨1,x,rfl⟩

theorem mul_centralSupport_eq_zero_of_no_links (p q : AlgebraProjection M)
    (hlink : ∀ a : M.toStarSubalgebra, q.val*a*p.val=0) :
    q.val*(centralSupport p).val=0 := by
  have hK : projectionOrbitClosure p ≤ q.val.val.ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro y ⟨a,x,rfl⟩
      exact congrArg (fun R : M.toStarSubalgebra => R.val x) (hlink a)
    · exact q.val.val.isClosed_ker
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  exact hK ((projectionOrbitClosure p).starProjection_apply_mem x)

/-- Scalar center forces every nonzero projection to have full central support. -/
theorem centralSupport_eq_one_of_factor
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (p : AlgebraProjection M) (hp : p.val≠0) : (centralSupport p).val=1 := by
  obtain ⟨z,hz⟩ := hfactor (centralSupport p).val (centralSupport_commutes p)
  have he := le_centralSupport p
  change (centralSupport p).val*p.val=p.val at he
  rw [hz,smul_mul_assoc,one_mul] at he
  have hz1 : z=1 := (smul_left_injective ℂ hp) (he.trans (one_smul ℂ p.val).symm)
  rw [hz,hz1,one_smul]

theorem traceFree_projection_eq_zero_or_eq_zero_of_no_links
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (p q : AlgebraProjection M) (hlink : ∀ a : M.toStarSubalgebra, q.val*a*p.val=0) :
    p.val=0 ∨ q.val=0 := by
  by_cases hp : p.val=0
  · exact Or.inl hp
  · right
    have h := mul_centralSupport_eq_zero_of_no_links p q hlink
    rwa [centralSupport_eq_one_of_factor hfactor p hp,mul_one] at h

end

/-! Trace-free upper bounds of arbitrary directed nets of partial isometries.
A weak operator ultralimit suffices: extension identities with each fixed net
member force the limit to satisfy b b* b = b. No trace or countability is used. -/
section
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace PartialIsometry

/-- Every monotone directed net has a partial-isometry upper bound, retaining
any prescribed bounds on its initial and final projections. -/
theorem traceFree_monotone_upper_bound
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (a : ι → PartialIsometry M) (ha : Monotone a)
    (p q : AlgebraProjection M) (hp : ∀ i, (a i).support ≤ p)
    (hq : ∀ i, (a i).target ≤ q) :
    ∃ v : PartialIsometry M, (∀ i, a i ≤ v) ∧ v.support ≤ p ∧ v.target ≤ q := by
  let ω : Ultrafilter ι := Ultrafilter.of atTop
  obtain ⟨T, _, ht⟩ := exists_weak_operator_ultralimit ω
    (fun i => (a i).val.val) 1 (by norm_num) (fun i => (a i).norm_le_one)
  let b : M.toStarSubalgebra := ⟨T, weak_operator_limit_mem M (fun i => (a i).val) T ht⟩
  have hb : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val.val x)) (ω : Filter ι)
      (𝓝 (inner ℂ y (b.val x))) := ht
  have hbp (i : ι) : b*(a i).support.val=(a i).val := by
    apply wot_limit_unique (fun j => (a j).val*(a i).support.val) _ _
      (wot_limit_mul_right _ _ _ hb)
    intro x y
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_ge_atTop i).filter_mono (Ultrafilter.of_le atTop)] with j hj
    exact (congrArg (fun z : M.toStarSubalgebra => inner ℂ y (z.val x)) (ha hj)).symm
  have hab (i : ι) : star (a i).val*b=(a i).support.val := by
    apply wot_limit_unique (fun j => star (a i).val*(a j).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    intro x y
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_ge_atTop i).filter_mono (Ultrafilter.of_le atTop)] with j hj
    exact (congrArg (fun z : M.toStarSubalgebra => inner ℂ y (z.val x))
      (cross_initial_rev (ha hj))).symm
  have hba (i : ι) : star b*(a i).val=(a i).support.val := by
    simpa only [star_mul, star_star, (a i).support.property.isSelfAdjoint.star_eq]
      using congrArg star (hab i)
  have hfix (i : ι) : (b*star b)*(a i).val=(a i).val := by
    rw [mul_assoc, hba i, hbp i]
  have hpartial : (b*star b)*b=b := by
    apply wot_limit_unique (fun i => (b*star b)*(a i).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    simpa only [hfix] using hb
  have hid : (star b*b)*(star b*b)=star b*b := by
    calc _ = star b*((b*star b)*b) := by simp only [mul_assoc]
         _ = star b*b := by rw [hpartial]
  let v : PartialIsometry M := ⟨⟨star b*b, ⟨hid, IsSelfAdjoint.star_mul_self b⟩⟩, b, rfl⟩
  refine ⟨v, hbp, ?_, ?_⟩
  · apply (v.support_le_iff_mul p).mpr
    apply wot_limit_unique (fun i => (a i).val*p.val) _ _
      (wot_limit_mul_right _ _ _ hb)
    simpa only [fun i => ((a i).support_le_iff_mul p).mp (hp i)] using hb
  · apply (v.target_le_iff_mul q).mpr
    apply wot_limit_unique (fun i => q.val*(a i).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    simpa only [fun i => ((a i).target_le_iff_mul q).mp (hq i)] using hb

end PartialIsometry
end

/-! Trace-free chain upper bounds and maximal partial isometries, with prescribed
initial and final projection bounds. The index set may be uncountable. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

theorem traceFree_chain_upper_bound (c : Set (PartialIsometry M))
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (p q : AlgebraProjection M) (hp : ∀ v ∈ c, v.support ≤ p)
    (hq : ∀ v ∈ c, v.target ≤ q) :
    ∃ v : PartialIsometry M, (∀ w ∈ c, w ≤ v) ∧ v.support ≤ p ∧ v.target ≤ q := by
  let : Nonempty c := hne.to_subtype
  let : IsDirected c (· ≤ ·) := ⟨by
    intro u v
    rcases hc.total u.property v.property with h | h
    · exact ⟨v, h, le_rfl⟩
    · exact ⟨u, le_rfl, h⟩⟩
  obtain ⟨v, hv, hvp, hvq⟩ := traceFree_monotone_upper_bound
    (fun w : c => w.val) (fun _ _ h => h) p q
    (fun w => hp w.val w.property) (fun w => hq w.val w.property)
  exact ⟨v, fun w hw => hv ⟨w,hw⟩, hvp, hvq⟩

theorem traceFree_exists_maximal_between (p q : AlgebraProjection M) :
    ∃ v : PartialIsometry M, v.support ≤ p ∧ v.target ≤ q ∧
      ∀ w : PartialIsometry M, w.support ≤ p → w.target ≤ q → v ≤ w → w ≤ v := by
  let S : Set (PartialIsometry M) := {v | v.support ≤ p ∧ v.target ≤ q}
  obtain ⟨v,hv⟩ := zorn_le₀ S (by
    intro c hc hchain
    by_cases hne : c.Nonempty
    · obtain ⟨v, hcv, hvp, hvq⟩ := traceFree_chain_upper_bound c hchain hne p q
        (fun w hw => (hc hw).1) (fun w hw => (hc hw).2)
      exact ⟨v, ⟨hvp, hvq⟩, hcv⟩
    · refine ⟨zero, ⟨?_, ?_⟩, ?_⟩
      · change p.val*0=0
        exact mul_zero _
      · apply (zero.target_le_iff_mul q).mpr
        exact mul_zero _
      · intro w hw
        exact (hne ⟨w,hw⟩).elim)
  exact ⟨v,hv.1.1,hv.1.2,fun w hp hq h => hv.2 ⟨hp,hq⟩ h⟩

end PartialIsometry
end

/-! Projection comparison from scalar center, without a supplied trace.
The maximal partial isometry, central support and polar linking are constructed. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))

include hfactor in
theorem traceFree_exists_nonzero_partialIsometry_between_projections
    (p q : AlgebraProjection M) (hp : p.val≠0) (hq : q.val≠0) :
    ∃ v : PartialIsometry M, v.support ≤ p ∧ v.target ≤ q ∧ v.support.val≠0 := by
  have hex : ∃ a : M.toStarSubalgebra, q.val*a*p.val≠0 := by
    by_contra hn
    have hz : ∀ a : M.toStarSubalgebra, q.val*a*p.val=0 := by
      simpa only [not_exists,not_not] using hn
    exact (traceFree_projection_eq_zero_or_eq_zero_of_no_links hfactor p q hz).elim hp hq
  obtain ⟨a,ha⟩ := hex
  apply exists_partialIsometry_of_link p q (q.val*a*p.val)
  · rw [mul_assoc,p.property.isIdempotentElem.eq]
  · rw [← mul_assoc,← mul_assoc,q.property.isIdempotentElem.eq]
  · exact ha

include hfactor in
theorem traceFree_exists_partialIsometry_comparison (p q : AlgebraProjection M) :
    ∃ v : PartialIsometry M, v.support ≤ p ∧ v.target ≤ q ∧
      (v.support=p ∨ v.target=q) := by
  obtain ⟨v,hvp,hvq,hmax⟩ := PartialIsometry.traceFree_exists_maximal_between p q
  let r : AlgebraProjection M :=
    ⟨p.val-v.support.val,v.support.property.sub_of_mul_eq_right p.property hvp⟩
  let s : AlgebraProjection M :=
    ⟨q.val-v.target.val,v.target.property.sub_of_mul_eq_right q.property hvq⟩
  have hrp : r ≤ p := by
    change p.val*(p.val-v.support.val)=p.val-v.support.val
    rw [mul_sub,p.property.isIdempotentElem.eq,hvp]
  have hsq : s ≤ q := by
    change q.val*(q.val-v.target.val)=q.val-v.target.val
    rw [mul_sub,q.property.isIdempotentElem.eq,hvq]
  have hzero : r.val=0 ∨ s.val=0 := by
    by_contra hn
    have hr : r.val≠0 := fun h => hn (Or.inl h)
    have hs : s.val≠0 := fun h => hn (Or.inr h)
    obtain ⟨w,hwr,hws,hw0⟩ :=
      traceFree_exists_nonzero_partialIsometry_between_projections hfactor r s hr hs
    have hpw : v.support.val*w.support.val=0 := by
      calc _ = v.support.val*(r.val*w.support.val) := by rw [hwr]
           _ = (v.support.val*r.val)*w.support.val := (mul_assoc _ _ _).symm
           _ = 0 := by
             change (v.support.val*(p.val-v.support.val))*w.support.val=0
             rw [mul_sub,projection_mul_of_le hvp,v.support.property.isIdempotentElem.eq,
               sub_self,zero_mul]
    have hqw : v.target.val*w.target.val=0 := by
      calc _ = v.target.val*(s.val*w.target.val) := by rw [hws]
           _ = (v.target.val*s.val)*w.target.val := (mul_assoc _ _ _).symm
           _ = 0 := by
             change (v.target.val*(q.val-v.target.val))*w.target.val=0
             rw [mul_sub,projection_mul_of_le hvq,v.target.property.isIdempotentElem.eq,
               sub_self,zero_mul]
    let u := PartialIsometry.patch v w hpw hqw
    have hup : u.support ≤ p := by
      change p.val*(v.support.val+w.support.val)=v.support.val+w.support.val
      rw [mul_add,hvp,show p.val*w.support.val=w.support.val from hwr.trans hrp]
    have huq : u.target ≤ q := by
      apply (u.target_le_iff_mul q).mpr
      change q.val*(v.val+w.val)=v.val+w.val
      rw [mul_add,(v.target_le_iff_mul q).mp hvq,
        (w.target_le_iff_mul q).mp (hws.trans hsq)]
    have hvu : v ≤ u := v.le_patch w hpw hqw
    exact (v.patch_ne w hpw hqw hw0) (le_antisymm (hmax u hup huq hvu) hvu)
  refine ⟨v,hvp,hvq,?_⟩
  rcases hzero with hr | hs
  · exact Or.inl (Subtype.ext (sub_eq_zero.mp hr).symm)
  · exact Or.inr (Subtype.ext (sub_eq_zero.mp hs).symm)

end Tracial

/-! The original finiteness predicate excludes proper self-equivalence of a
projection. Projection comparison is connected to the unchanged IsII1Factor
predicate, with no representation, trace, or separability premise. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Tracial
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

/-- A finite algebra has no partial isometry from a projection onto a proper
subprojection of itself. Finiteness is used on v + (1 - p). -/
theorem target_eq_support_of_finite
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (v : PartialIsometry M) (hv : v.target ≤ v.support) : v.target=v.support := by
  let r : AlgebraProjection M := ⟨1-v.support.val,v.support.property.one_sub⟩
  let w := onProjection r
  have hp : v.support.val*w.support.val=0 := by
    change v.support.val*(1-v.support.val)=0
    rw [mul_sub,mul_one,v.support.property.isIdempotentElem.eq,sub_self]
  have hq : v.target.val*w.target.val=0 := by
    rw [show w.target=r from onProjection_target r]
    change v.target.val*(1-v.support.val)=0
    rw [mul_sub,mul_one,projection_mul_of_le hv,sub_self]
  let u := patch v w hp hq
  have hu : star u.val*u.val=1 := by
    rw [u.initial]
    change v.support.val+(1-v.support.val)=1
    abel
  have huf := hfinite u.val hu
  change u.target.val=1 at huf
  rw [patch_target,show w.target=r from onProjection_target r] at huf
  apply Subtype.ext
  change v.target.val+(1-v.support.val)=1 at huf
  have he : v.target.val+(1-v.support.val)=v.support.val+(1-v.support.val) := by
    rw [huf]
    abel
  exact add_right_cancel he

/-- Finiteness also excludes a proper enlargement equivalent to a projection. -/
theorem target_eq_support_of_finite_of_le
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (v : PartialIsometry M) (hv : v.support ≤ v.target) : v.target=v.support := by
  have he : v.adjoint.target=v.support := by
    apply Subtype.ext
    change star v.val*star (star v.val)=v.support.val
    rw [star_star,v.initial]
  have h := target_eq_support_of_finite hfinite v.adjoint (by
    change v.adjoint.target ≤ v.target
    rw [he]
    exact hv)
  change v.adjoint.target=v.target at h
  rw [he] at h
  exact h.symm

end PartialIsometry
end Tracial

end

/-! Arbitrary-chain bounds with moving orthogonal initial and final supports, obtained from successive fixed-multiplier weak operator limits without a trace. -/

/-! Complete actual partial isometries to unitaries in a finite factor.
The construction uses projection comparison and finiteness, without a trace. -/
open scoped CStarAlgebra

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
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Tracial
variable {M : VonNeumannAlgebra H}

/-- A proper diffuse subprojection splits a nonzero corner into orthogonal pieces. -/
theorem traceFree_exists_orthogonal_split
    (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (p : AlgebraProjection M) (hp : p.val≠0) :
    ∃ q r : AlgebraProjection M, q ≤ p ∧ r ≤ p ∧ q.val≠0 ∧ r.val≠0 ∧
      q.val*r.val=0 ∧ q.val+r.val=p.val := by
  obtain ⟨q,hq,hq0,hqp,hpq,hqp'⟩ := hdiff p.val p.property hp
  let r : AlgebraProjection M := ⟨p.val-q,hq.sub_of_mul_eq_right p.property hpq⟩
  refine ⟨⟨q,hq⟩,r,hpq,?_,hq0,sub_ne_zero.mpr hqp.symm,?_,?_⟩
  · change p.val*(p.val-q)=p.val-q
    rw [mul_sub,p.property.isIdempotentElem.eq,hpq]
  · change q*(p.val-q)=0
    rw [mul_sub,hqp',hq.isIdempotentElem.eq,sub_self]
  · change q+(p.val-q)=p.val
    abel

/-- The two equivalent halves are constructed by an actual partial isometry.
No trace, finite-isometry property, or separability is needed for this lemma. -/
theorem traceFree_exists_halving
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (p : AlgebraProjection M) :
    ∃ v : PartialIsometry M, v.support.val*v.target.val=0 ∧
      v.support.val+v.target.val=p.val := by
  obtain ⟨v,hvp,hvq,hvo,hmax⟩ := PartialIsometry.traceFree_exists_maximal_orthogonal p
  let t := orthogonalSum v.support v.target hvo
  have htp : t ≤ p := orthogonalSum_le hvo hvp hvq
  let r : AlgebraProjection M := ⟨p.val-t.val,t.property.sub_of_mul_eq_right p.property htp⟩
  have hrp : r ≤ p := by
    change p.val*(p.val-t.val)=p.val-t.val
    rw [mul_sub,p.property.isIdempotentElem.eq,htp]
  have htr : t.val*r.val=0 := by
    change t.val*(p.val-t.val)=0
    rw [mul_sub,projection_mul_of_le htp,t.property.isIdempotentElem.eq,sub_self]
  have hr0 : r.val=0 := by
    by_contra hr
    obtain ⟨q,s,hqr,hsr,hq0,hs0,hqs,_⟩ := traceFree_exists_orthogonal_split hdiff r hr
    obtain ⟨w,hwq,hws,hw0⟩ :=
      traceFree_exists_nonzero_partialIsometry_between_projections hfactor q s hq0 hs0
    have hwr : w.support ≤ r := hwq.trans hqr
    have hwtr : w.target ≤ r := hws.trans hsr
    have hvt : v.support ≤ t := le_orthogonalSum_left _ _ hvo
    have hvtt : v.target ≤ t := le_orthogonalSum_right _ _ hvo
    have hpw := projection_orthogonal_of_le htr hvt hwr
    have hqw := projection_orthogonal_of_le htr hvtt hwtr
    have hcross := projection_orthogonal_of_le htr hvt hwtr
    have hcross' := PartialIsometry.orthogonal_reverse _ _
      (projection_orthogonal_of_le htr hvtt hwr)
    have hwo := projection_orthogonal_of_le hqs hwq hws
    let u := v.patch w hpw hqw
    have hup : u.support ≤ p := orthogonalSum_le hpw hvp (hwr.trans hrp)
    have huq : u.target ≤ p := by
      change p.val*u.target.val=u.target.val
      rw [PartialIsometry.patch_target]
      rw [mul_add,hvq,show p.val*w.target.val=w.target.val from hwtr.trans hrp]
    have huo : u.support.val*u.target.val=0 := by
      rw [PartialIsometry.patch_target]
      change (v.support.val+w.support.val)*(v.target.val+w.target.val)=0
      rw [add_mul,mul_add,mul_add,hvo,hcross,hcross',hwo,add_zero,zero_add]
    have hvu : v ≤ u := v.le_patch w hpw hqw
    exact (v.patch_ne w hpw hqw hw0) (le_antisymm (hmax u hup huq huo hvu) hvu)
  exact ⟨v,hvo,(sub_eq_zero.mp hr0).symm⟩

end Tracial

end

/-! Finite partitions with explicit equivalence witnesses and compatible binary
refinement. The common initial projection is halved once and its two pieces
are transported to every old piece, so all new pieces remain equivalent. -/
section
open scoped BigOperators
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Every ordered pair of pieces has a displayed equivalence witness. -/
def link (E : EquivalentPartition p ι) (i j : ι) : PartialIsometry M :=
  (E.leg j).compose (E.leg i).adjoint (by
    have h : (E.leg i).adjoint.target=(E.leg i).support := by
      apply Subtype.ext
      change star (E.leg i).val*star (star (E.leg i).val)=(E.leg i).support.val
      rw [star_star,(E.leg i).initial]
    rw [h,E.initial,E.initial])

theorem link_support (E : EquivalentPartition p ι) (i j : ι) :
    (E.link i j).support=(E.leg i).target := rfl

theorem link_target (E : EquivalentPartition p ι) (i j : ι) :
    (E.link i j).target=(E.leg j).target := by
  apply Subtype.ext
  change ((E.leg j).val*star (E.leg i).val)*star ((E.leg j).val*star (E.leg i).val)=_
  calc _ = (E.leg j).val*(star (E.leg i).val*(E.leg i).val)*star (E.leg j).val := by
           simp only [star_mul,star_star,mul_assoc]
       _ = (E.leg j).val*star (E.leg j).val := by
           rw [(E.leg i).initial,E.initial,← E.initial j,(E.leg j).mul_support]
       _ = _ := rfl

theorem refine_parent (E : EquivalentPartition p ι) (F : EquivalentPartition E.base κ) (i : ι) :
    (∑ j, ((E.refine F).leg (i,j)).target.val)=(E.leg i).target.val := by
  change (∑ j, ((E.leg i).compose (F.leg j) (by rw [E.initial]; exact F.bound j)).target.val)=_
  simp only [PartialIsometry.compose_target,← Finset.sum_mul,← Finset.mul_sum,F.total]
  rw [← E.initial i,(E.leg i).mul_support]
  rfl

end EquivalentPartition
end Tracial

/-! Coherent dyadic equivalent partitions and matrix units, constructed from
scalar center and diffuseness without a trace. DyadicIndex is reused as a
finite binary index type; no tracial partition construction is used. -/
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Tracial
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A partition of a nonzero projection has no zero piece, since every
piece is equivalent to every other piece by the displayed links. -/
theorem target_ne_zero (E : EquivalentPartition p ι) (hp : p.val≠0) (i : ι) :
    (E.leg i).target.val≠0 := by
  intro hi
  have hz (j : ι) : (E.leg j).target.val=0 := by
    have hw : (E.link i j).val=0 := by
      have hm := (E.link i j).mul_support
      rw [E.link_support,hi,mul_zero] at hm
      exact hm.symm
    rw [← E.link_target i j]
    change (E.link i j).val*star (E.link i j).val=0
    rw [hw,zero_mul]
  have ht := E.total
  simp only [hz,Finset.sum_const_zero] at ht
  exact hp ht.symm

end EquivalentPartition

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

/-- Choose the actual two-leg partition supplied by trace-free halving. -/
def traceFreeBinaryPartition (p : AlgebraProjection M) : EquivalentPartition p Bool :=
  let h := traceFree_exists_halving hfactor hdiff p
  EquivalentPartition.ofHalving h.choose h.choose_spec.1 h.choose_spec.2

/-- A coherent family: each successor halves the previous common initial
projection once and transports that halving to all its equivalent pieces. -/
def traceFreeDyadicPartition (p : AlgebraProjection M) :
    (n : ℕ) → EquivalentPartition p (DyadicIndex n)
  | 0 => EquivalentPartition.singleton p
  | n+1 =>
    let E := traceFreeDyadicPartition p n
    E.refine (traceFreeBinaryPartition hfactor hdiff E.base)

end Tracial

end

/-! Actual sums of countable orthogonal partial isometries, including least
initial/final support identities. No trace or countable-cofinality premise. -/
namespace Tracial

/-! Projection equivalence and subequivalence are witnessed by actual partial
isometries in the original algebra. No dimension or trace oracle is used. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

theorem adjoint_target (v : PartialIsometry M) : v.adjoint.target=v.support := by
  apply Subtype.ext
  change star v.val*star (star v.val)=v.support.val
  rw [star_star,v.initial]

theorem compose_target_of_eq (v w : PartialIsometry M) (h : w.target=v.support) :
    (v.compose w (le_of_eq h)).target=v.target := by
  apply Subtype.ext
  rw [compose_target,h,v.mul_support]
  rfl

end PartialIsometry
namespace AlgebraProjection

def Equivalent (p q : AlgebraProjection M) : Prop :=
  ∃ v : PartialIsometry M, v.support=p ∧ v.target=q

theorem subequivalent_refl (p : AlgebraProjection M) : p.Subequivalent p :=
  ⟨PartialIsometry.onProjection p,rfl,le_of_eq (PartialIsometry.onProjection_target p)⟩

theorem subequivalent_of_le {p q : AlgebraProjection M} (h : p ≤ q) :
    p.Subequivalent q :=
  ⟨PartialIsometry.onProjection p,rfl,(le_of_eq (PartialIsometry.onProjection_target p)).trans h⟩

theorem subequivalent_trans {p q r : AlgebraProjection M}
    (h : p.Subequivalent q) (k : q.Subequivalent r) : p.Subequivalent r := by
  obtain ⟨v,hv,hvq⟩ := h
  obtain ⟨w,hw,hwr⟩ := k
  have hc : v.target ≤ w.support := by rw [hw]; exact hvq
  exact ⟨w.compose v hc,hv,(w.compose_target_le v hc).trans hwr⟩

theorem equivalent_refl (p : AlgebraProjection M) : p.Equivalent p :=
  ⟨PartialIsometry.onProjection p,rfl,PartialIsometry.onProjection_target p⟩

theorem equivalent_symm {p q : AlgebraProjection M} (h : p.Equivalent q) : q.Equivalent p := by
  obtain ⟨v,hv,hvq⟩ := h
  exact ⟨v.adjoint,hvq,v.adjoint_target.trans hv⟩

theorem equivalent_trans {p q r : AlgebraProjection M}
    (h : p.Equivalent q) (k : q.Equivalent r) : p.Equivalent r := by
  obtain ⟨v,hv,hvq⟩ := h
  obtain ⟨w,hw,hwr⟩ := k
  have hc : v.target=w.support := hvq.trans hw.symm
  exact ⟨w.compose v (le_of_eq hc),hv,(w.compose_target_of_eq v hc).trans hwr⟩

theorem Equivalent.subequivalent {p q : AlgebraProjection M} (h : p.Equivalent q) :
    p.Subequivalent q := by
  obtain ⟨v,hv,hvq⟩ := h
  exact ⟨v,hv,le_of_eq hvq⟩

/-- Scalar-center comparison gives totality of actual subequivalence. -/
theorem subequivalent_total
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (p q : AlgebraProjection M) : p.Subequivalent q ∨ q.Subequivalent p := by
  obtain ⟨v,hp,hq,h⟩ := traceFree_exists_partialIsometry_comparison hfactor p q
  rcases h with h | h
  · exact Or.inl ⟨v,h,hq⟩
  · exact Or.inr ⟨v.adjoint,h,by rw [v.adjoint_target]; exact hp⟩

end AlgebraProjection

/-! Finiteness excludes an infinite family of nonzero equivalent orthogonal
projections. The shift and both of its least supports are constructed. -/

/-! Finite comparison and cancellation with actual partial isometries.
No trace, dimension, or representation is assumed. -/
namespace AlgebraProjection

variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
/-- Mutual subequivalence is equivalence in a finite algebra. -/
theorem equivalent_of_mutual_subequivalent {p q : AlgebraProjection M}
    (hpq : p.Subequivalent q) (hqp : q.Subequivalent p) : p.Equivalent q := by
  obtain ⟨v,hv,hvq⟩ := hpq
  obtain ⟨w,hw,hwp⟩ := hqp
  have hc : v.target ≤ w.support := by rw [hw]; exact hvq
  let u := w.compose v hc
  have hu : u.target ≤ u.support := by
    change u.target ≤ v.support
    rw [hv]
    exact (w.compose_target_le v hc).trans hwp
  have he : u.target=p := (u.target_eq_support_of_finite hfinite hu).trans hv
  have hw' : w.target=p := le_antisymm hwp (by
    rw [← he]; exact w.compose_target_le v hc)
  exact ⟨w.adjoint,hw',w.adjoint_target.trans hw⟩

include hfinite in
/-- Equivalent comparable projections in a finite algebra coincide. -/
theorem eq_of_equivalent_of_le {p q : AlgebraProjection M}
    (he : p.Equivalent q) (hle : p ≤ q) : p=q := by
  obtain ⟨v,hv,ht⟩ := he
  exact ht.symm.trans ((v.target_eq_support_of_finite_of_le hfinite (by
    rw [hv,ht]; exact hle)).trans hv) |>.symm

include hfinite in
/-- Any embedding onto a subprojection of an equivalent projection is onto. -/
theorem target_eq_of_equivalent (v : PartialIsometry M) (q : AlgebraProjection M)
    (he : v.support.Equivalent q) (hle : v.target ≤ q) : v.target=q := by
  have hv : v.target.Equivalent v.support := ⟨v.adjoint,rfl,v.adjoint_target⟩
  exact eq_of_equivalent_of_le hfinite (equivalent_trans hv he) hle

theorem subequivalent_orthogonalSum {p q r s : AlgebraProjection M}
    (hp : p.val*r.val=0) (hq : q.val*s.val=0)
    (h₁ : p.Subequivalent q) (h₂ : r.Subequivalent s) :
    (orthogonalSum p r hp).Subequivalent (orthogonalSum q s hq) := by
  obtain ⟨v,hv,hvq⟩ := h₁
  obtain ⟨w,hw,hws⟩ := h₂
  have hi : v.support.val*w.support.val=0 := by rw [hv,hw]; exact hp
  have ht := projection_orthogonal_of_le hq hvq hws
  refine ⟨v.patch w hi ht,Subtype.ext (by
    change v.support.val+w.support.val=_
    rw [hv,hw]
    rfl),?_⟩
  have he : (v.patch w hi ht).target=orthogonalSum v.target w.target ht :=
    Subtype.ext (v.patch_target w hi ht)
  rw [he]
  exact orthogonalSum_le ht (hvq.trans (le_orthogonalSum_left _ _ hq))
    (hws.trans (le_orthogonalSum_right _ _ hq))

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))

include hfinite hfactor in
/-- Cancel equivalent orthogonal pieces from a subequivalence. -/
theorem subequivalent_cancel {p q r s : AlgebraProjection M}
    (hp : p.val*r.val=0) (hq : q.val*s.val=0) (he : p.Equivalent q)
    (h : (orthogonalSum p r hp).Subequivalent (orthogonalSum q s hq)) :
    r.Subequivalent s := by
  rcases subequivalent_total hfactor r s with hgood | hrev
  · exact hgood
  · obtain ⟨v,hv,ht⟩ := equivalent_symm he
    obtain ⟨w,hw,hwr⟩ := hrev
    have hi : v.support.val*w.support.val=0 := by rw [hv,hw]; exact hq
    have ho : v.target.val*w.target.val=0 := by
      rw [ht]; exact projection_orthogonal_of_le hp le_rfl hwr
    let u := v.patch w hi ho
    have hus : u.support=orthogonalSum q s hq := Subtype.ext (by
      change v.support.val+w.support.val=_; rw [hv,hw]; rfl)
    have hut : u.target ≤ orthogonalSum p r hp := by
      have hu : u.target=orthogonalSum v.target w.target ho :=
        Subtype.ext (v.patch_target w hi ho)
      rw [hu]
      exact orthogonalSum_le ho (by rw [ht]; exact le_orthogonalSum_left _ _ hp)
        (hwr.trans (le_orthogonalSum_right _ _ hp))
    have heq : u.support.Equivalent (orthogonalSum p r hp) := by
      rw [hus]
      exact equivalent_of_mutual_subequivalent hfinite ⟨u,hus,hut⟩ h
    have hu := congrArg Subtype.val (target_eq_of_equivalent hfinite u _ heq hut)
    rw [PartialIsometry.patch_target,ht] at hu
    change p.val+w.target.val=p.val+r.val at hu
    have hw' : w.target=r := Subtype.ext (add_left_cancel hu)
    exact (equivalent_symm (show s.Equivalent r from ⟨w,hw,hw'⟩)).subequivalent

include hfinite hfactor in
theorem equivalent_cancel {p q r s : AlgebraProjection M}
    (hp : p.val*r.val=0) (hq : q.val*s.val=0) (he : p.Equivalent q)
    (h : (orthogonalSum p r hp).Equivalent (orthogonalSum q s hq)) :
    r.Equivalent s :=
  equivalent_of_mutual_subequivalent hfinite
    (subequivalent_cancel hfinite hfactor hp hq he h.subequivalent)
    (subequivalent_cancel hfinite hfactor hq hp (equivalent_symm he)
      (equivalent_symm h).subequivalent)

/-- The relative complement is the actual difference of the operators. -/
def remainder (p q : AlgebraProjection M) (h : p ≤ q) : AlgebraProjection M :=
  ⟨q.val-p.val,p.property.sub_of_mul_eq_right q.property h⟩

theorem remainder_orthogonal (p q : AlgebraProjection M) (h : p ≤ q) :
    p.val*(remainder p q h).val=0 := by
  change p.val*(q.val-p.val)=0
  rw [mul_sub,projection_mul_of_le h,p.property.isIdempotentElem.eq,sub_self]

theorem orthogonalSum_remainder (p q : AlgebraProjection M) (h : p ≤ q) :
    orthogonalSum p (remainder p q h) (remainder_orthogonal p q h)=q :=
  Subtype.ext (by change p.val+(q.val-p.val)=q.val; abel)

theorem remainder_le (p q : AlgebraProjection M) (h : p ≤ q) : remainder p q h ≤ q := by
  change q.val*(q.val-p.val)=q.val-p.val
  rw [mul_sub,q.property.isIdempotentElem.eq,h]

include hfinite hfactor in
theorem remainder_equivalent {p q P Q : AlgebraProjection M}
    (hp : p ≤ P) (hq : q ≤ Q) (he : p.Equivalent q) (h : P.Equivalent Q) :
    (remainder p P hp).Equivalent (remainder q Q hq) := by
  apply equivalent_cancel hfinite hfactor
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
namespace AlgebraProjection

theorem finsetSum_le_iff {ι : Type*} (a : ι → AlgebraProjection M) (s : Finset ι)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i≠j → (a i).val*(a j).val=0) (p : AlgebraProjection M) :
    finsetSum a s ho ≤ p ↔ ∀ i ∈ s, a i ≤ p := by
  classical
  constructor
  · intro h i hi
    apply le_trans ?_ h
    change (∑ j ∈ s, (a j).val)*(a i).val=(a i).val
    rw [Finset.sum_mul]
    exact (Finset.sum_eq_single_of_mem i hi
      (fun j hj hji => ho j hj i hi hji)).trans (a i).property.isIdempotentElem.eq
  · intro h
    change p.val*(∑ i ∈ s, (a i).val)=∑ i ∈ s, (a i).val
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl h

end AlgebraProjection
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

theorem subset_val (E : EquivalentPartition p ι) (s : Finset ι) :
    (E.subset s).val=∑ i ∈ s, (E.leg i).target.val := rfl

theorem subset_le_iff (E : EquivalentPartition p ι) (s : Finset ι) (q : AlgebraProjection M) :
    E.subset s ≤ q ↔ ∀ i ∈ s, (E.leg i).target ≤ q :=
  AlgebraProjection.finsetSum_le_iff _ _ _ _

theorem subset_le (E : EquivalentPartition p ι) (s : Finset ι) : E.subset s ≤ p :=
  (E.subset_le_iff s p).mpr (fun i _ => E.bound i)

theorem subset_mono (E : EquivalentPartition p ι) {s t : Finset ι} (h : s ⊆ t) :
    E.subset s ≤ E.subset t :=
  (E.subset_le_iff s _).mpr (fun i hi => (E.subset_le_iff t _).mp le_rfl i (h hi))

theorem subset_univ (E : EquivalentPartition p ι) : E.subset Finset.univ=p :=
  Subtype.ext E.total

theorem subset_empty (E : EquivalentPartition p ι) : (E.subset ∅).val=0 := by
  simp only [subset_val,Finset.sum_empty]

/-- A bijection of subsets gives a sum of explicit matrix-unit links. -/
theorem subset_equivalent_of_equiv (E : EquivalentPartition p ι) (s t : Finset ι)
    (e : s ≃ t) : (E.subset s).Equivalent (E.subset t) := by
  let a (i : s) := E.link i.val (e i).val
  obtain ⟨v,_,hs,ht⟩ := PartialIsometry.exists_finsetSum a Finset.univ
    (by
      intro i _ j _ hij
      exact E.orthogonal i.val j.val (fun h => hij (Subtype.ext h)))
    (by
      intro i _ j _ hij
      change (E.link i.val (e i).val).target.val*(E.link j.val (e j).val).target.val=0
      rw [E.link_target,E.link_target]
      exact E.orthogonal _ _ (fun h => hij (e.injective (Subtype.ext h))))
  refine ⟨v,Subtype.ext ?_,Subtype.ext ?_⟩
  · rw [hs]
    change (∑ i : s, (E.leg i.val).target.val)=∑ i ∈ s, (E.leg i).target.val
    simpa only [Finset.attach_eq_univ] using
      (Finset.sum_attach s (fun i => (E.leg i).target.val))
  · rw [ht]
    change (∑ i : s, (E.link i.val (e i).val).target.val)=_
    simp only [E.link_target]
    rw [e.sum_comp (fun i : t => (E.leg i.val).target.val)]
    change (∑ i : t, (E.leg i.val).target.val)=∑ i ∈ t, (E.leg i).target.val
    simpa only [Finset.attach_eq_univ] using
      (Finset.sum_attach t (fun i => (E.leg i).target.val))

theorem subset_equivalent_of_card_eq (E : EquivalentPartition p ι) (s t : Finset ι)
    (h : s.card=t.card) : (E.subset s).Equivalent (E.subset t) :=
  E.subset_equivalent_of_equiv s t (Finset.equivOfCardEq h)

/-- Subset sums stay compatible with refinement to all children. -/
theorem subset_refine {κ : Type*} [Fintype κ] (E : EquivalentPartition p ι)
    (F : EquivalentPartition E.base κ) (s : Finset ι) :
    (E.refine F).subset (s ×ˢ Finset.univ)=E.subset s := by
  apply Subtype.ext
  rw [subset_val,Finset.sum_product]
  exact Finset.sum_congr rfl (fun i _ => E.refine_parent F i)

/-! Exact finite cardinal comparison of sums of equivalent nonzero projections.
Finiteness prevents a larger collection from embedding in a smaller one. -/

theorem subset_mul_piece_of_not_mem (E : EquivalentPartition p ι) (s : Finset ι)
    (i : ι) (hi : i ∉ s) : (E.subset s).val*(E.leg i).target.val=0 := by
  rw [subset_val,Finset.sum_mul]
  exact Finset.sum_eq_zero (fun j hj => E.orthogonal j i (fun h => hi (h ▸ hj)))

theorem subset_le_subset_iff (E : EquivalentPartition p ι) (hp : p.val≠0)
    (s t : Finset ι) : E.subset s ≤ E.subset t ↔ s ⊆ t := by
  constructor
  · intro h i hi
    by_contra hit
    have hh := (E.subset_le_iff s _).mp h i hi
    change (E.subset t).val*(E.leg i).target.val=(E.leg i).target.val at hh
    rw [E.subset_mul_piece_of_not_mem t i hit] at hh
    exact E.target_ne_zero hp i hh.symm
  · exact E.subset_mono

theorem subset_subequivalent_of_card_le (E : EquivalentPartition p ι)
    (s t : Finset ι) (h : s.card ≤ t.card) : (E.subset s).Subequivalent (E.subset t) := by
  obtain ⟨u,hut,hu⟩ := Finset.exists_subset_card_eq h
  exact AlgebraProjection.subequivalent_trans
    (E.subset_equivalent_of_card_eq s u hu.symm).subequivalent
    (AlgebraProjection.subequivalent_of_le (E.subset_mono hut))

/-- The witness-based comparison agrees exactly with cardinal comparison. -/
theorem subset_subequivalent_iff_card_le
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (E : EquivalentPartition p ι) (hp : p.val≠0) (s t : Finset ι) :
    (E.subset s).Subequivalent (E.subset t) ↔ s.card ≤ t.card := by
  refine ⟨fun h => ?_,E.subset_subequivalent_of_card_le s t⟩
  by_contra hn
  have hlt : t.card < s.card := Nat.lt_of_not_ge hn
  obtain ⟨u,hus,hu⟩ := Finset.exists_subset_card_eq (Nat.le_of_lt hlt)
  have hsu : (E.subset s).Subequivalent (E.subset u) :=
    AlgebraProjection.subequivalent_trans h
      (E.subset_equivalent_of_card_eq t u hu.symm).subequivalent
  have hle : E.subset u ≤ E.subset s := E.subset_mono hus
  have he : E.subset u=E.subset s := AlgebraProjection.eq_of_equivalent_of_le hfinite
    (AlgebraProjection.equivalent_of_mutual_subequivalent hfinite
      (AlgebraProjection.subequivalent_of_le hle) hsu) hle
  have hs : s ⊆ u := (E.subset_le_subset_iff hp s u).mp (le_of_eq he.symm)
  have hc := Finset.card_le_card hs
  omega

theorem subset_orthogonal_of_disjoint (E : EquivalentPartition p ι)
    (s t : Finset ι) (h : Disjoint s t) : (E.subset s).val*(E.subset t).val=0 := by
  rw [subset_val,subset_val,Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mul_sum]
  exact Finset.sum_eq_zero (fun j hj => E.orthogonal i j (fun he =>
    Finset.disjoint_left.mp h hi (he.symm ▸ hj)))

theorem subset_union [DecidableEq ι] (E : EquivalentPartition p ι)
    (s t : Finset ι) (h : Disjoint s t) :
    E.subset (s ∪ t)=orthogonalSum (E.subset s) (E.subset t)
      (E.subset_orthogonal_of_disjoint s t h) :=
  Subtype.ext (Finset.sum_union h)

theorem subset_insert [DecidableEq ι] (E : EquivalentPartition p ι)
    (s : Finset ι) (i : ι) (hi : i ∉ s) :
    (E.subset (insert i s)).val=(E.subset s).val+(E.leg i).target.val := by
  rw [subset_val,Finset.sum_insert hi,add_comm]
  rfl

end EquivalentPartition
end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Dimension
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.CornerPartition.single_pinch
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

/-! Finite rounding by actual subset projections. A maximal fitting subset
leaves a remainder smaller in comparison than any unused equivalent piece. -/
namespace Tracial

section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

theorem exists_maximal_fitting_subset (E : EquivalentPartition p ι) (q : AlgebraProjection M) :
    ∃ s : Finset ι, (E.subset s).Subequivalent q ∧
      ∀ t : Finset ι, (E.subset t).Subequivalent q → t.card ≤ s.card := by
  classical
  let F : Finset (Finset ι) := Finset.univ.filter (fun s => (E.subset s).Subequivalent q)
  have h0 : (E.subset ∅).Subequivalent q := AlgebraProjection.subequivalent_of_le (by
    change q.val*(E.subset ∅).val=(E.subset ∅).val
    rw [E.subset_empty,mul_zero])
  have hF : F.Nonempty := ⟨∅,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h0⟩⟩
  obtain ⟨s,hs,hmax⟩ := F.exists_max_image Finset.card hF
  exact ⟨s,(Finset.mem_filter.mp hs).2,fun t ht =>
    hmax t (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩)⟩

/-- A further piece in the remainder would enlarge the fitting subset. -/
theorem maximal_remainder_not_subequivalent (E : EquivalentPartition p ι)
    (q : AlgebraProjection M) (s : Finset ι)
    (hmax : ∀ t : Finset ι, (E.subset t).Subequivalent q → t.card ≤ s.card)
    (v : PartialIsometry M) (hv : v.support=E.subset s) (ht : v.target ≤ q)
    (i : ι) (hi : i ∉ s) :
    ¬(E.leg i).target.Subequivalent (AlgebraProjection.remainder v.target q ht) := by
  classical
  intro h
  obtain ⟨w,hw,hwr⟩ := h
  have ho₁ : v.support.val*w.support.val=0 := by
    rw [hv,hw]
    exact E.subset_mul_piece_of_not_mem s i hi
  have ho₂ : v.target.val*w.target.val=0 :=
    projection_orthogonal_of_le (AlgebraProjection.remainder_orthogonal v.target q ht)
      le_rfl hwr
  let u := v.patch w ho₁ ho₂
  have hus : u.support=E.subset (insert i s) := Subtype.ext (by
    change v.support.val+w.support.val=_
    rw [hv,hw,E.subset_insert s i hi])
  have hut : u.target ≤ q := by
    have he : u.target=orthogonalSum v.target w.target ho₂ :=
      Subtype.ext (v.patch_target w ho₁ ho₂)
    rw [he]
    exact orthogonalSum_le ho₂ ht (hwr.trans (AlgebraProjection.remainder_le _ _ ht))
  have hc := hmax (insert i s) ⟨u,hus,hut⟩
  rw [Finset.card_insert_of_notMem hi] at hc
  omega

/-- Every projection inside the partition unit lies between subset sums whose
cardinalities differ by at most one. This is operator comparison, not a trace
estimate and not an assumed dimension rounding law. -/
theorem exists_subset_rounding
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (E : EquivalentPartition p ι) (q : AlgebraProjection M) (hqp : q ≤ p) :
    ∃ s t : Finset ι, s ⊆ t ∧ t.card ≤ s.card+1 ∧
      (E.subset s).Subequivalent q ∧ q.Subequivalent (E.subset t) ∧
      ∀ a : Finset ι, (E.subset a).Subequivalent q → a.card ≤ s.card := by
  classical
  obtain ⟨s,hs,hmax⟩ := E.exists_maximal_fitting_subset q
  by_cases hsall : s=Finset.univ
  · refine ⟨s,s,Finset.Subset.refl _,Nat.le_succ _,hs,?_,hmax⟩
    rw [hsall,E.subset_univ]
    exact AlgebraProjection.subequivalent_of_le hqp
  · obtain ⟨i,hi⟩ : ∃ i : ι, i ∉ s := by
      by_contra h
      apply hsall
      ext i
      simp only [Finset.mem_univ,iff_true]
      exact Classical.not_not.mp (fun hi => h ⟨i,hi⟩)
    obtain ⟨v,hv,ht⟩ := hs
    let r := AlgebraProjection.remainder v.target q ht
    have hr : r.Subequivalent (E.leg i).target :=
      (AlgebraProjection.subequivalent_total hfactor (E.leg i).target r).resolve_left
        (E.maximal_remainder_not_subequivalent q s hmax v hv ht i hi)
    have hv' : v.target.Equivalent (E.subset s) := ⟨v.adjoint,rfl,v.adjoint_target.trans hv⟩
    have ho := E.subset_mul_piece_of_not_mem s i hi
    have hupper := AlgebraProjection.subequivalent_orthogonalSum
      (AlgebraProjection.remainder_orthogonal v.target q ht) ho hv'.subequivalent hr
    rw [AlgebraProjection.orthogonalSum_remainder] at hupper
    have he : orthogonalSum (E.subset s) (E.leg i).target ho=E.subset (insert i s) :=
      Subtype.ext (E.subset_insert s i hi).symm
    rw [he] at hupper
    exact ⟨s,insert i s,Finset.subset_insert _ _,by rw [Finset.card_insert_of_notMem hi],
      ⟨v,hv,ht⟩,hupper,hmax⟩

end EquivalentPartition

/-! The dyadic lower cut on projections below p and its normalized faithful monotone supremum, capped at one. -/

theorem dyadicWeight_le_one (n : ℕ) (s : Finset (DyadicIndex n)) : dyadicWeight n s ≤ 1 := by
  apply (div_le_one (pow_pos (by norm_num : (0 : ℝ)<2) n)).mpr
  have h : s.card ≤ 2^n := (Finset.card_le_univ s).trans_eq (card_dyadicIndex n)
  exact_mod_cast h

theorem dyadicWeight_children (n : ℕ) (s : Finset (DyadicIndex n)) :
    dyadicWeight (n+1) (s ×ˢ (Finset.univ : Finset Bool))=dyadicWeight n s := by
  change ((s ×ˢ (Finset.univ : Finset Bool)).card : ℝ)/2^(n+1)=(s.card : ℝ)/2^n
  rw [Finset.card_product,Finset.card_univ,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat,pow_succ]
  exact mul_div_mul_right _ _ (by norm_num : (2 : ℝ)≠0)

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

/-- Membership contains an actual partial-isometry witness through Subequivalent. -/
def traceFreeDyadicCut (p q : AlgebraProjection M) : Set ℝ :=
  {x | ∃ n, ∃ s : Finset (DyadicIndex n),
    ((traceFreeDyadicPartition hfactor hdiff p n).subset s).Subequivalent q ∧
      x=dyadicWeight n s}

def traceFreeDyadicSup (p q : AlgebraProjection M) : ℝ :=
  sSup (traceFreeDyadicCut hfactor hdiff p q)

theorem traceFreeDyadicCut_zero_mem (p q : AlgebraProjection M) :
    0 ∈ traceFreeDyadicCut hfactor hdiff p q := by
  refine ⟨0,∅,AlgebraProjection.subequivalent_of_le ?_,?_⟩
  · change q.val*((traceFreeDyadicPartition hfactor hdiff p 0).subset ∅).val=_
    rw [EquivalentPartition.subset_empty,mul_zero]
  · simp only [dyadicWeight,Finset.card_empty,Nat.cast_zero,zero_div]

theorem traceFreeDyadicCut_bddAbove (p q : AlgebraProjection M) :
    BddAbove (traceFreeDyadicCut hfactor hdiff p q) := by
  refine ⟨1,?_⟩
  rintro x ⟨n,s,_,rfl⟩
  exact dyadicWeight_le_one n s

theorem traceFreeDyadicSup_nonneg (p q : AlgebraProjection M) :
    0 ≤ traceFreeDyadicSup hfactor hdiff p q :=
  le_csSup (traceFreeDyadicCut_bddAbove hfactor hdiff p q)
    (traceFreeDyadicCut_zero_mem hfactor hdiff p q)

theorem traceFreeDyadicSup_le_one (p q : AlgebraProjection M) :
    traceFreeDyadicSup hfactor hdiff p q ≤ 1 := by
  apply csSup_le ⟨0,traceFreeDyadicCut_zero_mem hfactor hdiff p q⟩
  rintro x ⟨n,s,_,rfl⟩
  exact dyadicWeight_le_one n s

theorem traceFreeDyadicSup_lower_bound (p q : AlgebraProjection M) (n : ℕ)
    (s : Finset (DyadicIndex n))
    (h : ((traceFreeDyadicPartition hfactor hdiff p n).subset s).Subequivalent q) :
    dyadicWeight n s ≤ traceFreeDyadicSup hfactor hdiff p q :=
  le_csSup (traceFreeDyadicCut_bddAbove hfactor hdiff p q) ⟨n,s,h,rfl⟩

theorem traceFreeDyadicCut_mono (p : AlgebraProjection M) {q r : AlgebraProjection M}
    (h : q.Subequivalent r) :
    traceFreeDyadicCut hfactor hdiff p q ⊆ traceFreeDyadicCut hfactor hdiff p r := by
  rintro x ⟨n,s,hs,hx⟩
  exact ⟨n,s,AlgebraProjection.subequivalent_trans hs h,hx⟩

theorem traceFreeDyadicSup_mono (p : AlgebraProjection M) {q r : AlgebraProjection M}
    (h : q.Subequivalent r) :
    traceFreeDyadicSup hfactor hdiff p q ≤ traceFreeDyadicSup hfactor hdiff p r :=
  csSup_le_csSup (traceFreeDyadicCut_bddAbove hfactor hdiff p r)
    ⟨0,traceFreeDyadicCut_zero_mem hfactor hdiff p q⟩
    (traceFreeDyadicCut_mono hfactor hdiff p h)

theorem traceFreeDyadicSup_zero (p q : AlgebraProjection M) (hp : p.val≠0) (hq : q.val=0) :
    traceFreeDyadicSup hfactor hdiff p q=0 := by
  apply le_antisymm ?_ (traceFreeDyadicSup_nonneg hfactor hdiff p q)
  apply csSup_le ⟨0,traceFreeDyadicCut_zero_mem hfactor hdiff p q⟩
  rintro x ⟨n,s,⟨v,hv,ht⟩,rfl⟩
  have htz : v.target.val=0 := by
    change q.val*v.target.val=v.target.val at ht
    rw [hq,zero_mul] at ht
    exact ht.symm
  have hvz : v.val=0 := by
    have h := v.target_mul
    rw [htz,zero_mul] at h
    exact h.symm
  have hsz : ((traceFreeDyadicPartition hfactor hdiff p n).subset s).val=0 := by
    rw [← hv,← v.initial,hvz,star_zero,zero_mul]
  have hs : s ⊆ ∅ :=
    ((traceFreeDyadicPartition hfactor hdiff p n).subset_le_subset_iff hp s ∅).mp (by
      change ((traceFreeDyadicPartition hfactor hdiff p n).subset ∅).val*
        ((traceFreeDyadicPartition hfactor hdiff p n).subset s).val=_
      rw [hsz,mul_zero])
  have he : s=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun i hi => Finset.notMem_empty i (hs hi))
  simp only [he,dyadicWeight,Finset.card_empty,Nat.cast_zero,zero_div,le_refl]

end

/-! Common refinements compare arbitrary dyadic levels. The supremum takes
the exact dyadic value on every reference subset projection, and finite
rounding bounds every projection with an explicit error at each level. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem dyadicWeight_le_iff (n : ℕ) (s t : Finset (DyadicIndex n)) :
    dyadicWeight n s ≤ dyadicWeight n t ↔ s.card ≤ t.card := by
  unfold dyadicWeight
  rw [div_le_div_iff_of_pos_right (pow_pos (by norm_num : (0 : ℝ)<2) n)]
  exact Nat.cast_le

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

theorem traceFreeDyadic_exists_refined_subset (p : AlgebraProjection M) (n m : ℕ)
    (hnm : n ≤ m) (s : Finset (DyadicIndex n)) :
    ∃ t : Finset (DyadicIndex m),
      (traceFreeDyadicPartition hfactor hdiff p m).subset t=
        (traceFreeDyadicPartition hfactor hdiff p n).subset s ∧
      dyadicWeight m t=dyadicWeight n s := by
  induction m, hnm using Nat.le_induction with
  | base => exact ⟨s,rfl,rfl⟩
  | succ m _ ih =>
    obtain ⟨t,ht,hw⟩ := ih
    refine ⟨t ×ˢ (Finset.univ : Finset Bool),?_,(dyadicWeight_children m t).trans hw⟩
    change ((traceFreeDyadicPartition hfactor hdiff p m).refine _).subset _=_
    rw [EquivalentPartition.subset_refine,ht]

/-- Comparison between any two levels agrees with the real dyadic weights. -/
theorem traceFreeDyadic_comparison_iff_weight
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p : AlgebraProjection M) (hp : p.val≠0) (n m : ℕ)
    (s : Finset (DyadicIndex n)) (t : Finset (DyadicIndex m)) :
    ((traceFreeDyadicPartition hfactor hdiff p n).subset s).Subequivalent
      ((traceFreeDyadicPartition hfactor hdiff p m).subset t) ↔
        dyadicWeight n s ≤ dyadicWeight m t := by
  obtain ⟨s',hs',hws⟩ := traceFreeDyadic_exists_refined_subset hfactor hdiff p n (max n m)
    (le_max_left _ _) s
  obtain ⟨t',ht',hwt⟩ := traceFreeDyadic_exists_refined_subset hfactor hdiff p m (max n m)
    (le_max_right _ _) t
  rw [← hs',← ht',← hws,← hwt]
  rw [EquivalentPartition.subset_subequivalent_iff_card_le hfinite _ hp,dyadicWeight_le_iff]

theorem traceFreeDyadicSup_subset
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p : AlgebraProjection M) (hp : p.val≠0) (n : ℕ) (s : Finset (DyadicIndex n)) :
    traceFreeDyadicSup hfactor hdiff p ((traceFreeDyadicPartition hfactor hdiff p n).subset s)=
      dyadicWeight n s := by
  apply le_antisymm ?_ (traceFreeDyadicSup_lower_bound hfactor hdiff p _ n s
    (AlgebraProjection.subequivalent_refl _))
  apply csSup_le ⟨0,traceFreeDyadicCut_zero_mem hfactor hdiff p _⟩
  rintro x ⟨m,t,h,rfl⟩
  exact (traceFreeDyadic_comparison_iff_weight hfactor hdiff hfinite p hp m n t s).mp h

/-- At every level the cut supremum has actual lower and upper operator
witnesses, with a numerical gap at most 2^(-n). -/
theorem traceFreeDyadicSup_rounding
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p q : AlgebraProjection M) (hp : p.val≠0) (hq : q ≤ p) (n : ℕ) :
    ∃ s t : Finset (DyadicIndex n), s ⊆ t ∧ t.card ≤ s.card+1 ∧
      ((traceFreeDyadicPartition hfactor hdiff p n).subset s).Subequivalent q ∧
      q.Subequivalent ((traceFreeDyadicPartition hfactor hdiff p n).subset t) ∧
      dyadicWeight n s ≤ traceFreeDyadicSup hfactor hdiff p q ∧
      traceFreeDyadicSup hfactor hdiff p q ≤ dyadicWeight n t ∧
      dyadicWeight n t ≤ dyadicWeight n s+1/2^n := by
  obtain ⟨s,t,hst,hcard,hs,ht,_⟩ :=
    (traceFreeDyadicPartition hfactor hdiff p n).exists_subset_rounding hfactor q hq
  refine ⟨s,t,hst,hcard,hs,ht,traceFreeDyadicSup_lower_bound hfactor hdiff p q n s hs,?_,?_⟩
  · have h := traceFreeDyadicSup_mono hfactor hdiff p ht
    rwa [traceFreeDyadicSup_subset hfactor hdiff hfinite p hp] at h
  · change (t.card : ℝ)/2^n ≤ (s.card : ℝ)/2^n+1/2^n
    rw [← add_div]
    apply (div_le_div_iff_of_pos_right (pow_pos (by norm_num : (0 : ℝ)<2) n)).mpr
    exact_mod_cast hcard

end

/-! Orthogonal lower approximants fit disjoint collections of the reference
pieces. Equivalent complements and finite cancellation enforce the capacity. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

theorem subset_complement [DecidableEq ι] (E : EquivalentPartition p ι) (s : Finset ι) :
    E.subset (Finset.univ \ s)=AlgebraProjection.remainder (E.subset s) p (E.subset_le s) := by
  classical
  apply Subtype.ext
  change (∑ i ∈ Finset.univ \ s, (E.leg i).target.val)=p.val-(E.subset s).val
  rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ s),E.total]
  rfl

/-- Two orthogonal fitting projections cannot use more pieces than the unit. -/
theorem orthogonal_fitting_card_bound
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (E : EquivalentPartition p ι) (hp : p.val≠0)
    (q r : AlgebraProjection M) (hqp : q ≤ p) (hrp : r ≤ p) (ho : q.val*r.val=0)
    (s t : Finset ι) (hs : (E.subset s).Subequivalent q) (ht : (E.subset t).Subequivalent r) :
    s.card+t.card ≤ Fintype.card ι := by
  classical
  obtain ⟨v,hv,hvr⟩ := ht
  have hvp := hvr.trans hrp
  have hqv : q.val*v.target.val=0 := projection_orthogonal_of_le ho le_rfl hvr
  have hqr : q ≤ AlgebraProjection.remainder v.target p hvp := by
    change (p.val-v.target.val)*q.val=q.val
    rw [sub_mul,hqp,PartialIsometry.orthogonal_reverse _ _ hqv,sub_zero]
  have he : v.target.Equivalent (E.subset t) := ⟨v.adjoint,rfl,v.adjoint_target.trans hv⟩
  have hc := AlgebraProjection.remainder_equivalent hfinite hfactor hvp (E.subset_le t)
    he (AlgebraProjection.equivalent_refl p)
  rw [← E.subset_complement t] at hc
  have hh : (E.subset s).Subequivalent (E.subset (Finset.univ \ t)) :=
    AlgebraProjection.subequivalent_trans hs (AlgebraProjection.subequivalent_trans
      (AlgebraProjection.subequivalent_of_le hqr) hc.subequivalent)
  have hn := (E.subset_subequivalent_iff_card_le hfinite hp s _).mp hh
  have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ t)
  rw [Finset.card_univ] at hcard
  omega

/-- Disjoint replacement of one collection lets the actual witnesses be added. -/
theorem orthogonal_fitting_union
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (E : EquivalentPartition p ι) (hp : p.val≠0)
    (q r : AlgebraProjection M) (hqp : q ≤ p) (hrp : r ≤ p) (ho : q.val*r.val=0)
    (s t : Finset ι) (hs : (E.subset s).Subequivalent q) (ht : (E.subset t).Subequivalent r) :
    ∃ u : Finset ι, u.card=s.card+t.card ∧
      (E.subset u).Subequivalent (orthogonalSum q r ho) := by
  classical
  obtain ⟨t',hst,hct⟩ := exists_disjoint_card s t
    (E.orthogonal_fitting_card_bound hfinite hfactor hp q r hqp hrp ho s t hs ht)
  have ht' : (E.subset t').Subequivalent r := AlgebraProjection.subequivalent_trans
    (E.subset_equivalent_of_card_eq t' t hct).subequivalent ht
  refine ⟨s ∪ t',by rw [Finset.card_union_of_disjoint hst,hct],?_⟩
  rw [E.subset_union s t' hst]
  exact AlgebraProjection.subequivalent_orthogonalSum
    (E.subset_orthogonal_of_disjoint s t' hst) ho hs ht'

theorem orthogonal_upper_union
    (E : EquivalentPartition p ι) (q r : AlgebraProjection M) (ho : q.val*r.val=0)
    (s t : Finset ι) (hs : q.Subequivalent (E.subset s)) (ht : r.Subequivalent (E.subset t))
    (hcard : s.card+t.card ≤ Fintype.card ι) :
    ∃ u : Finset ι, u.card=s.card+t.card ∧
      (orthogonalSum q r ho).Subequivalent (E.subset u) := by
  classical
  obtain ⟨t',hst,hct⟩ := exists_disjoint_card s t hcard
  have ht' : r.Subequivalent (E.subset t') := AlgebraProjection.subequivalent_trans ht
    (E.subset_equivalent_of_card_eq t t' hct.symm).subequivalent
  refine ⟨s ∪ t',by rw [Finset.card_union_of_disjoint hst,hct],?_⟩
  rw [E.subset_union s t' hst]
  exact AlgebraProjection.subequivalent_orthogonalSum ho
    (E.subset_orthogonal_of_disjoint s t' hst) hs ht'

end EquivalentPartition
end

/-! Orthogonal additivity of the constructed dyadic dimension. Numerical
rounding errors tend to zero; every lower and upper bound uses actual
partial-isometry witnesses in the original finite diffuse factor. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
theorem traceFreeDyadicSup_lower_add
    (p q r : AlgebraProjection M) (hp : p.val≠0) (hqp : q ≤ p) (hrp : r ≤ p)
    (ho : q.val*r.val=0) (n : ℕ) (s t : Finset (DyadicIndex n))
    (hs : ((traceFreeDyadicPartition hfactor hdiff p n).subset s).Subequivalent q)
    (ht : ((traceFreeDyadicPartition hfactor hdiff p n).subset t).Subequivalent r) :
    dyadicWeight n s+dyadicWeight n t ≤
      traceFreeDyadicSup hfactor hdiff p (orthogonalSum q r ho) := by
  obtain ⟨u,huc,hu⟩ := (traceFreeDyadicPartition hfactor hdiff p n).orthogonal_fitting_union
    hfinite hfactor hp q r hqp hrp ho s t hs ht
  have h := traceFreeDyadicSup_lower_bound hfactor hdiff p _ n u hu
  simpa only [dyadicWeight,huc,Nat.cast_add,add_div] using h

include hfinite in
theorem traceFreeDyadicSup_upper_add
    (p q r : AlgebraProjection M) (hp : p.val≠0) (ho : q.val*r.val=0)
    (n : ℕ) (s t : Finset (DyadicIndex n))
    (hs : q.Subequivalent ((traceFreeDyadicPartition hfactor hdiff p n).subset s))
    (ht : r.Subequivalent ((traceFreeDyadicPartition hfactor hdiff p n).subset t)) :
    traceFreeDyadicSup hfactor hdiff p (orthogonalSum q r ho) ≤
      dyadicWeight n s+dyadicWeight n t := by
  by_cases hc : s.card+t.card ≤ Fintype.card (DyadicIndex n)
  · obtain ⟨u,huc,hu⟩ := (traceFreeDyadicPartition hfactor hdiff p n).orthogonal_upper_union
      q r ho s t hs ht hc
    have h := traceFreeDyadicSup_mono hfactor hdiff p hu
    rw [traceFreeDyadicSup_subset hfactor hdiff hfinite p hp] at h
    simpa only [dyadicWeight,huc,Nat.cast_add,add_div] using h
  · apply le_trans (traceFreeDyadicSup_le_one hfactor hdiff p _)
    have hn : 2^n ≤ s.card+t.card := by rw [card_dyadicIndex] at hc; omega
    change 1 ≤ (s.card : ℝ)/2^n+(t.card : ℝ)/2^n
    rw [← add_div]
    apply (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ)<2) n)).mpr
    simp only [one_mul]
    exact_mod_cast hn

include hfinite in
/-- The dyadic supremum is additive on actual orthogonal projections below p. -/
theorem traceFreeDyadicSup_orthogonal_add
    (p q r : AlgebraProjection M) (hp : p.val≠0) (hqp : q ≤ p) (hrp : r ≤ p)
    (ho : q.val*r.val=0) :
    traceFreeDyadicSup hfactor hdiff p (orthogonalSum q r ho)=
      traceFreeDyadicSup hfactor hdiff p q+traceFreeDyadicSup hfactor hdiff p r := by
  apply eq_of_all_dyadic_errors
  intro n
  obtain ⟨s,t,_,_,hs,ht,hql,hqu,hqe⟩ :=
    traceFreeDyadicSup_rounding hfactor hdiff hfinite p q hp hqp n
  obtain ⟨a,b,_,_,ha,hb,hrl,hru,hre⟩ :=
    traceFreeDyadicSup_rounding hfactor hdiff hfinite p r hp hrp n
  have hlo := traceFreeDyadicSup_lower_add hfactor hdiff hfinite p q r hp hqp hrp ho n s a hs ha
  have hhi := traceFreeDyadicSup_upper_add hfactor hdiff hfinite p q r hp ho n t b ht hb
  rw [show (2 : ℝ)/2^n=2*(1/2^n) by ring]
  apply abs_le.mpr
  constructor <;> linarith

end Tracial

/-! Classification of projection comparison by the constructed finite
dimension, and a wrapper for exactly the original IsII1Factor predicate.
No normality or trace-extension claim is made here. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Tracial
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

/-- The same constructed lower cut, now normalized at the algebra identity. -/
def traceFreeDimension (q : AlgebraProjection M) : ℝ :=
  traceFreeDyadicSup hfactor hdiff ⟨1,IsStarProjection.one _⟩ q

end Tracial

end

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

theorem traceFreeDimension_nonneg (q : AlgebraProjection M) :
    0 ≤ traceFreeDimension hfactor hdiff q :=
  traceFreeDyadicSup_nonneg hfactor hdiff _ q

theorem traceFreeDimension_le_one (q : AlgebraProjection M) :
    traceFreeDimension hfactor hdiff q ≤ 1 :=
  traceFreeDyadicSup_le_one hfactor hdiff _ q

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

namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)

theorem piece_le (i : Fin Q.size) : Q.piece i ≤ p := by
  change p.val * (Q.piece i).val = (Q.piece i).val
  rw [← Q.total, Finset.sum_mul]
  simpa only [(Q.piece i).property.isIdempotentElem.eq] using
    (Finset.sum_eq_single i (fun j _ hji => Q.orthogonal j i hji)
      (fun h => (h (Finset.mem_univ i)).elim))

end CornerPartition

/-! Actual compression energies and the energy lost by finite pinching.
No existence statement about small-energy partitions is assumed here. -/

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
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.Generator.vectorOrbitClosure_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual sign splitting inside a prescribed residual corner. -/

/-! The constructed spectral splitting preserves the compressed operator.
This is distinct from using that splitting to reduce other operators' energy. -/

/-! Interval bounds propagated through constructed spectral corner splits. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance intervalCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance intervalOrder_rcdd0da_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance intervalPreorder_rcdd0da_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance intervalLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE

end

/-! Finite dyadic trees of actual spectral interval cuts. -/

/-! Constructed cuts preserve commutation with other operators. -/

/-! Spectral interval partitions in the commutant of a prescribed operator. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_SpectralApproximation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Common finite refinements of two commuting corner partitions. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace CornerPartition
variable {p : AlgebraProjection M} (Q R : CornerPartition p)
variable (hc : ∀ i j, Commute (Q.piece i).val (R.piece j).val)

def jointPiece (a : Fin Q.size × Fin R.size) : AlgebraProjection M :=
  ⟨(Q.piece a.1).val*(R.piece a.2).val,
    (Q.piece a.1).property.mul (R.piece a.2).property (hc a.1 a.2)⟩

theorem jointPiece_le_left (a : Fin Q.size × Fin R.size) : Q.jointPiece R hc a ≤ Q.piece a.1 := by
  change (Q.piece a.1).val*((Q.piece a.1).val*(R.piece a.2).val)=(Q.piece a.1).val*(R.piece a.2).val
  rw [← mul_assoc,(Q.piece a.1).property.isIdempotentElem.eq]

theorem jointPiece_le_right (a : Fin Q.size × Fin R.size) : Q.jointPiece R hc a ≤ R.piece a.2 := by
  change (R.piece a.2).val*((Q.piece a.1).val*(R.piece a.2).val)=(Q.piece a.1).val*(R.piece a.2).val
  rw [← mul_assoc,← (hc a.1 a.2).eq,mul_assoc,(R.piece a.2).property.isIdempotentElem.eq]

theorem jointPiece_orthogonal (a b : Fin Q.size × Fin R.size) (hab : a ≠ b) :
    (Q.jointPiece R hc a).val*(Q.jointPiece R hc b).val=0 := by
  by_cases h : a.1=b.1
  · have h₂ : a.2 ≠ b.2 := fun h₂ => hab (Prod.ext h h₂)
    exact orthogonal_subprojections (R.orthogonal a.2 b.2 h₂)
      (Q.jointPiece_le_right R hc a) (Q.jointPiece_le_right R hc b)
  · exact orthogonal_subprojections (Q.orthogonal a.1 b.1 h)
      (Q.jointPiece_le_left R hc a) (Q.jointPiece_le_left R hc b)

/-- A spectral sum on Q is represented exactly on the common refinement. -/
theorem joint_sum_left (c : Fin Q.size → ℂ) :
    (∑ a : Fin Q.size × Fin R.size, c a.1 • (Q.jointPiece R hc a).val)=
      ∑ i, c i • (Q.piece i).val := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ j, c i • ((Q.piece i).val*(R.piece j).val))=_
  rw [← Finset.smul_sum,← Finset.mul_sum,R.total,projection_mul_of_le (Q.piece_le i)]

theorem joint_sum_right (c : Fin R.size → ℂ) :
    (∑ a : Fin Q.size × Fin R.size, c a.2 • (Q.jointPiece R hc a).val)=
      ∑ j, c j • (R.piece j).val := by
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  change (∑ i, c j • ((Q.piece i).val*(R.piece j).val))=_
  rw [← Finset.smul_sum,← Finset.sum_mul,Q.total]
  have hleft : p.val*(R.piece j).val=(R.piece j).val := R.piece_le j
  rw [hleft]

end CornerPartition

/-! Simultaneous finite spectral approximation of two commuting self-adjoint
operators. The same actual partition is used for both. -/

end

/-! Finite spectral approximation for an actual normal operator. -/

/-! Transport constructed spectral partitions through an actual inclusion of
von Neumann algebras on the same Hilbert space. -/

/-! Finite simultaneous spectral approximation of any commuting self-adjoint
family, preserving a prior partition and the entire common commutant. -/

/-! Finite orthogonal families can be completed to unit partitions. Refining
blocks retains explicit disjoint index sets whose sums recover those blocks. -/
open scoped BigOperators
open UltrapowerBridge

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
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
theorem traceFreeDimension_finsetSum
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} (q : I → AlgebraProjection M) (s : Finset I)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i≠j → (q i).val*(q j).val=0) :
    traceFreeDimension hfactor hdiff (AlgebraProjection.finsetSum q s ho)=
      ∑ i ∈ s, traceFreeDimension hfactor hdiff (q i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hz : (AlgebraProjection.finsetSum q ∅ ho).val=0 := by simp [AlgebraProjection.finsetSum]
    simpa only [Finset.sum_empty,traceFreeDimension] using traceFreeDyadicSup_zero hfactor hdiff
      ⟨1,IsStarProjection.one _⟩ _ hunit hz
  | @insert i s hi ih =>
    have hos : ∀ j ∈ s, ∀ k ∈ s, j≠k → (q j).val*(q k).val=0 :=
      fun j hj k hk => ho j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)
    let r := AlgebraProjection.finsetSum q s hos
    have hqr : (q i).val*r.val=0 := by
      change (q i).val*(∑ j ∈ s, (q j).val)=0
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero (fun j hj => ho i (Finset.mem_insert_self _ _) j
        (Finset.mem_insert_of_mem hj) (fun he => hi (he.symm ▸ hj)))
    have he : AlgebraProjection.finsetSum q (insert i s) ho=orthogonalSum (q i) r hqr := by
      apply Subtype.ext
      exact Finset.sum_insert hi
    rw [he,Finset.sum_insert hi]
    have hadd := traceFreeDyadicSup_orthogonal_add hfactor hdiff hfinite
      ⟨1,IsStarProjection.one _⟩ (q i) r hunit (one_mul _) (one_mul _) hqr
    change traceFreeDimension hfactor hdiff (orthogonalSum (q i) r hqr)=
      traceFreeDimension hfactor hdiff (q i)+traceFreeDimension hfactor hdiff r at hadd
    rw [hadd,ih hos]

include hfinite in
theorem traceFreeDimension_sum_of_total
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Fintype I] (q : I → AlgebraProjection M)
    (ho : ∀ i j, i≠j → (q i).val*(q j).val=0)
    (p : AlgebraProjection M) (hp : ∑ i, (q i).val=p.val) :
    ∑ i, traceFreeDimension hfactor hdiff (q i)=traceFreeDimension hfactor hdiff p := by
  classical
  have he : AlgebraProjection.finsetSum q Finset.univ (fun i _ j _ => ho i j)=p := Subtype.ext hp
  rw [← he]
  exact (traceFreeDimension_finsetSum hfactor hdiff hfinite hunit q Finset.univ _).symm

include hfinite in
/-- A finite orthogonal spectral value has the required operator-norm bound. -/
theorem traceFreeDimension_spectralWeight_norm_le
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Fintype I] (q : I → AlgebraProjection M)
    (ho : ∀ i j, i≠j → (q i).val*(q j).val=0) (c : I → ℂ) :
    ‖∑ i, c i*(traceFreeDimension hfactor hdiff (q i) : ℂ)‖ ≤
      ‖∑ i, c i • (q i).val‖ := by
  classical
  let a : M.toStarSubalgebra := ∑ i, c i • (q i).val
  have hpiece (i : I) : a*(q i).val=c i • (q i).val := by
    dsimp [a]
    rw [Finset.sum_mul]
    apply (Finset.sum_eq_single i ?_ ?_).trans
      (by rw [smul_mul_assoc,(q i).property.isIdempotentElem.eq])
    · intro j _ hji
      rw [smul_mul_assoc,ho j i hji,smul_zero]
    · intro h; exact (h (Finset.mem_univ i)).elim
  have hterm (i : I) : ‖c i*(traceFreeDimension hfactor hdiff (q i) : ℂ)‖ ≤
      ‖a‖*traceFreeDimension hfactor hdiff (q i) := by
    by_cases hz : (q i).val=0
    · have hD := traceFreeDyadicSup_zero hfactor hdiff ⟨1,IsStarProjection.one _⟩ (q i) hunit hz
      change traceFreeDimension hfactor hdiff (q i)=0 at hD
      simp only [hD,Complex.ofReal_zero,mul_zero,norm_zero,le_refl]
    · have hnorm := norm_mul_le a (q i).val
      rw [hpiece i,norm_smul] at hnorm
      have hpos : 0 < ‖(q i).val‖ := norm_pos_iff.mpr hz
      have hci : ‖c i‖ ≤ ‖a‖ := by nlinarith
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (traceFreeDimension_nonneg hfactor hdiff _)]
      exact mul_le_mul_of_nonneg_right hci (traceFreeDimension_nonneg hfactor hdiff _)
  have hdim : (∑ i, traceFreeDimension hfactor hdiff (q i)) ≤ 1 := by
    rw [← traceFreeDimension_finsetSum hfactor hdiff hfinite hunit q Finset.univ
      (fun i _ j _ => ho i j)]
    exact traceFreeDimension_le_one hfactor hdiff _
  calc
    ‖∑ i, c i*(traceFreeDimension hfactor hdiff (q i) : ℂ)‖ ≤
        ∑ i, ‖c i*(traceFreeDimension hfactor hdiff (q i) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖a‖*traceFreeDimension hfactor hdiff (q i) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = ‖a‖*(∑ i, traceFreeDimension hfactor hdiff (q i)) := (Finset.mul_sum _ _ _).symm
    _ ≤ ‖a‖ := by nlinarith [norm_nonneg a]

include hfinite in
/-- In a fixed orthogonal partition, the spectral-value map is contractive. -/
theorem traceFreeDimension_spectralWeight_sub_norm_le
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Fintype I] (q : I → AlgebraProjection M)
    (ho : ∀ i j, i≠j → (q i).val*(q j).val=0) (c d : I → ℂ) :
    ‖(∑ i, c i*(traceFreeDimension hfactor hdiff (q i) : ℂ))-
      (∑ i, d i*(traceFreeDimension hfactor hdiff (q i) : ℂ))‖ ≤
      ‖(∑ i, c i • (q i).val)-(∑ i, d i • (q i).val)‖ := by
  simpa only [sub_mul,sub_smul,Finset.sum_sub_distrib] using
    traceFreeDimension_spectralWeight_norm_le hfactor hdiff hfinite hunit q ho (fun i => c i-d i)

/-! Spectral dimension weights agree under common commuting refinements.
Contractivity is proved for two commuting partitions, not noncommuting inputs. -/
namespace CornerPartition
variable {p : AlgebraProjection M} (Q R : CornerPartition p)
variable (hc : ∀ i j, Commute (Q.piece i).val (R.piece j).val)

include hfinite in
theorem dimension_joint_row (hunit : (1 : M.toStarSubalgebra) ≠ 0) (i : Fin Q.size) :
    ∑ j, traceFreeDimension hfactor hdiff (Q.jointPiece R hc (i,j))=
      traceFreeDimension hfactor hdiff (Q.piece i) := by
  apply traceFreeDimension_sum_of_total hfactor hdiff hfinite hunit
    (fun j => Q.jointPiece R hc (i,j))
    (fun j k hjk => Q.jointPiece_orthogonal R hc (i,j) (i,k) (fun h => hjk (congrArg Prod.snd h)))
  change (∑ j, (Q.piece i).val*(R.piece j).val)=(Q.piece i).val
  rw [← Finset.mul_sum,R.total,projection_mul_of_le (Q.piece_le i)]

include hfinite in
theorem dimension_joint_column (hunit : (1 : M.toStarSubalgebra) ≠ 0) (j : Fin R.size) :
    ∑ i, traceFreeDimension hfactor hdiff (Q.jointPiece R hc (i,j))=
      traceFreeDimension hfactor hdiff (R.piece j) := by
  apply traceFreeDimension_sum_of_total hfactor hdiff hfinite hunit
    (fun i => Q.jointPiece R hc (i,j))
    (fun i k hik => Q.jointPiece_orthogonal R hc (i,j) (k,j) (fun h => hik (congrArg Prod.fst h)))
  change (∑ i, (Q.piece i).val*(R.piece j).val)=(R.piece j).val
  rw [← Finset.sum_mul,Q.total]
  exact R.piece_le j

include hfinite in
theorem dimension_weight_joint_left (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (c : Fin Q.size → ℂ) :
    (∑ a : Fin Q.size × Fin R.size,
      c a.1*(traceFreeDimension hfactor hdiff (Q.jointPiece R hc a) : ℂ))=
        ∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [← Finset.mul_sum,← Complex.ofReal_sum,dimension_joint_row hfactor hdiff hfinite Q R hc hunit]

include hfinite in
theorem dimension_weight_joint_right (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (c : Fin R.size → ℂ) :
    (∑ a : Fin Q.size × Fin R.size,
      c a.2*(traceFreeDimension hfactor hdiff (Q.jointPiece R hc a) : ℂ))=
        ∑ i, c i*(traceFreeDimension hfactor hdiff (R.piece i) : ℂ) := by
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  rw [← Finset.mul_sum,← Complex.ofReal_sum,dimension_joint_column hfactor hdiff hfinite Q R hc hunit]

include hfinite hc in
/-- Changing between two commuting partitions preserves the norm estimate. -/
theorem dimension_weight_cross_norm_le (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (c : Fin Q.size → ℂ) (d : Fin R.size → ℂ) :
    ‖(∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ))-
      (∑ j, d j*(traceFreeDimension hfactor hdiff (R.piece j) : ℂ))‖ ≤
      ‖(∑ i, c i • (Q.piece i).val)-(∑ j, d j • (R.piece j).val)‖ := by
  have h := traceFreeDimension_spectralWeight_sub_norm_le hfactor hdiff hfinite hunit
    (Q.jointPiece R hc) (Q.jointPiece_orthogonal R hc) (fun a => c a.1) (fun a => d a.2)
  rwa [Q.dimension_weight_joint_left hfactor hdiff hfinite R hc hunit c,
    Q.dimension_weight_joint_right hfactor hdiff hfinite R hc hunit d,
    Q.joint_sum_left R hc c,Q.joint_sum_right R hc d] at h

end CornerPartition

end

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

/-- Approximation specification, not an assumed linear trace. -/
def IsDimensionSpectralValue (x : M.toStarSubalgebra) (t : ℂ) : Prop :=
  ∀ (Q : CornerPartition ⟨1,IsStarProjection.one _⟩) (c : Fin Q.size → ℂ),
    (∀ i, Commute (Q.piece i).val x) →
      ‖t-∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)‖ ≤
        ‖x-∑ i, c i • (Q.piece i).val‖

end

/-! The constructed spectral value is bounded and extends the actual
projection dimension. These laws do not assert noncommuting additivity. -/

/-! Finite-family tests and real homogeneity for the constructed spectral value.
These statements do not assert additivity for noncommuting operators. -/
open scoped BigOperators

end Generator.Tracial

end

end OAI
end


