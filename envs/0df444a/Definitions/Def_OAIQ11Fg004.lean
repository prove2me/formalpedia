-- Prove2me | Definitions.Def_OAIQ11Fg004
-- name    : OAIQ11Fg004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T09:34:15.897136+00:00
-- url     : https://prove2.me/theorems/5113cdd2-5b83-4685-8f19-42f26da197f3
-- title:
--   Definitions bundle OAIQ11Fg004 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 120 declarations of OpenAI's Lean: 34 definitions, 2 inductive types or structures, 4 instances and 80 theorems. The definitions and types are `OAI.Generator.FreeConvolution.begins`, `OAI.Generator.FreeConvolution.cancellation`, `OAI.Generator.FreeConvolution.creation`, `OAI.Generator.FreeConvolution.delta`, `OAI.Generator.FreeConvolution.inverseLetter`, `OAI.Generator.FreeConvolution.leftRegularHom`, `OAI.Generator.FreeConvolution.letter`, `OAI.Generator.FreeConvolution.realRegular`, `OAI.Generator.FreeConvolution.regular`, `OAI.Generator.MatrixUnitSystem.amplify`, `OAI.Generator.MatrixUnitSystem.bellPartition`, `OAI.Generator.MatrixUnitSystem.bellPiece`, `OAI.Generator.MatrixUnitSystem.coefficientEval`, `OAI.Generator.MatrixUnitSystem.coefficientHom`, `OAI.Generator.MatrixUnitSystem.concreteCoefficientHom`, `OAI.Generator.MatrixUnitSystem.fullProjection`, `OAI.Generator.MatrixUnitSystem.product`, `OAI.Generator.MatrixUnitSystem.reindex`, `OAI.Generator.MatrixUnitSystem.relativeEquiv`, `OAI.Generator.Tracial.AlgebraProjection.finsetSum`, `OAI.Generator.Tracial.AlgebraProjection.remainder`, `OAI.Generator.Tracial.AlgebraProjection.unitaryConjugate`, `OAI.Generator.Tracial.CornerPartition.Refines`, `OAI.Generator.Tracial.CornerPartition.binary`, `OAI.Generator.Tracial.CornerPartition.ofFamily`, `OAI.Generator.Tracial.CornerUnitary`, `OAI.Generator.Tracial.PartialUnitary`, `OAI.Generator.Tracial.PartialUnitary.completed`, `OAI.Generator.Tracial.PartialUnitary.val`, `OAI.Generator.Tracial.centralSupport`, `OAI.Generator.Tracial.kernelProjection`, `OAI.Generator.Tracial.orthogonalSum`, `OAI.Generator.Tracial.polarSupportsOrder`, `OAI.Generator.Tracial.rangeProjection`, `OAI.Generator.Tracial.unitaryPolarCStar`, `OAI.UltrapowerBridge.quotientStarAlgHom`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `FactorGeneration_AmplificationEncoding`, `FactorGeneration_Coefficients`, `FactorGeneration_Convolution`, `FactorGeneration_CoordinateUnitaries`, `FactorGeneration_DyadicComparison`, `FactorGeneration_FiniteComparison`, `FactorGeneration_LocalizedStates`, `FactorGeneration_MatrixAlgebras`, `FactorGeneration_MatrixGenerators`, `FactorGeneration_MatrixRefinement`, `FactorGeneration_MatrixUnits`, `FactorGeneration_NormalDimension`, `FactorGeneration_PartialIsometries`, `FactorGeneration_PartialUnitaries`, `FactorGeneration_Pinching`, `FactorGeneration_ProjectionComparison`, `FactorGeneration_ProjectionLimits`, `FactorGeneration_SpectralPinching`, `FactorGeneration_SpectralStates`, `FactorGeneration_Supports`, `FactorGeneration_Ultrapower`.
--
--   **Imports.** It imports the bundles `OAIQ11Fg000`, `OAIQ11Fg001` and `OAIQ11Fg002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ11Fg007`, `OAIQ11Fg008`, `OAIQ11Fg009` and `OAIQ11Fg010`; the statements `OAI.Generator.Tracial.CornerPartition.exists_indexed_orthogonal_refinement_budget` and `OAI.Generator.Tracial.exists_supported_corner_partial_sequence`; the proof of `OAI_Generator_Tracial_exists_coordinate_monotone_upper`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ11Fg000
import Definitions.Def_OAIQ11Fg001
import Definitions.Def_OAIQ11Fg002

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Ultrapower
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace UltrapowerBridge

section
open Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (l : Filter ℕ)

theorem quotientMap_eq_iff (a b : Bounded M) :
    quotientMap τ l a = quotientMap τ l b ↔ TraceRel τ l a b := Quotient.eq

instance instStarRingTracialQuotient : StarRing (TracialQuotient τ l) where
  star_involutive a := Quotient.inductionOn a (fun a => by
    change quotientMap τ l (star (star a)) = quotientMap τ l a
    rw [star_star])
  star_mul a b := Quotient.inductionOn₂ a b (fun a b => by
    change quotientMap τ l (star (a*b)) = quotientMap τ l (star b*star a)
    rw [star_mul])
  star_add a b := Quotient.inductionOn₂ a b (fun a b => by
    change quotientMap τ l (star (a+b)) = quotientMap τ l (star a+star b)
    rw [star_add])

instance instStarModuleComplexTracialQuotient : StarModule ℂ (TracialQuotient τ l) where
  star_smul c a := Quotient.inductionOn a (fun a =>
    congrArg (quotientMap τ l) (star_smul c a))

def quotientStarAlgHom : Bounded M →⋆ₐ[ℂ] TracialQuotient τ l where
  __ := quotientMap τ l
  commutes' _ := rfl
  map_star' := quotientMap_star τ l

end

open Filter
open scoped Topology

end UltrapowerBridge

/-! Commutation with every bounded subalgebra sequence implies uniform coordinate commutator decay. -/
open Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_ProjectionLimits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A nonzero projection in a diffuse tracial algebra contains nonzero projections of arbitrarily small trace. -/

/-! Monotone projection limits with trace bounds, giving chain bounds for prescribed trace cuts. -/

/-! Exact trace cuts in a diffuse coordinate algebra. -/

/-! Algebraic part of Popa 1308.3982v3, Lemma 3.2: adding a supported
partial unitary in the residual corner. The small mixed-word estimates and
the existence of an appropriate patch are separate analytic requirements. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- An actual operator with identical initial and final support p. -/
structure CornerUnitary (p : AlgebraProjection M) where
  val : M.toStarSubalgebra
  initial : star val * val = p.val
  final : val * star val = p.val

namespace CornerUnitary
variable {p q : AlgebraProjection M}

theorem norm_sq (v : CornerUnitary p) : ‖v.val‖*‖v.val‖=‖p.val‖ := by
  rw [← CStarRing.norm_star_mul_self,v.initial]

theorem norm_le_one (v : CornerUnitary p) : ‖v.val‖ ≤ 1 := by
  have he := v.norm_sq
  have hp := p.property.norm_le
  nlinarith [norm_nonneg v.val]

end CornerUnitary

end

/-! Dyadic projections inside a diffuse algebra with faithful trace. -/

/-! Finite spectral sums in the constructed dyadic projection algebras. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_PartialIsometries
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual partial isometries, allowing distinct initial and final projections,
with the extension order and its exact trace distance. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace PartialIsometry

theorem support_mono {v w : PartialIsometry M} (h : v ≤ w) : v.support ≤ w.support :=
  support_le_of_extends h

end PartialIsometry

end

/-! Actual L2 limits of partial isometries and upper bounds of increasing
sequences, using their exact support-trace distance. -/

/-! Orthogonal patching with distinct source and target supports. -/

/-! A maximal actual partial isometry between subprojections of prescribed
projections. Chain upper bounds are constructed L2 limits, not assumed. -/
open Filter
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Supports
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Kernel and range projections constructed in the actual von Neumann algebra.
Membership follows from commutant invariance, with no spectral theorem assumed. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def kernelProjection (x : M.toStarSubalgebra) : AlgebraProjection M :=
  ⟨⟨x.val.ker.starProjection,kernelProjection_mem x⟩,by
    constructor
    · apply Subtype.ext
      exact (isStarProjection_starProjection
        (U := x.val.ker)).isIdempotentElem.eq
    · apply Subtype.ext
      exact (isStarProjection_starProjection
        (U := x.val.ker)).isSelfAdjoint.star_eq⟩

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

/-- The projection onto the closed range of x, expressed via ker(x*). -/
def rangeProjection (x : M.toStarSubalgebra) : AlgebraProjection M :=
  ⟨1-(kernelProjection (star x)).val,(kernelProjection (star x)).property.one_sub⟩

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
local instance polarSupportsOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
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
-- module Solutions.OAIQ11_FG.FactorGeneration_ProjectionComparison
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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
-- module Solutions.OAIQ11_FG.FactorGeneration_Pinching
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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

def Refines (R : CornerPartition p) : Prop := ∀ i, ∃ j, R.piece i ≤ Q.piece j

end CornerPartition

end

/-! Actual finite refinement of a corner partition by partitions of its blocks.
The dependent family of block sizes is flattened without changing any piece.
No small-energy partition is an input to these constructions. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace CornerPartition
variable {p : AlgebraProjection M}

/-- Reindex an explicitly finite orthogonal family by Fin. -/
def ofFamily {ι : Type*} [Fintype ι] (a : ι → AlgebraProjection M)
    (ha : ∀ i j, i ≠ j → (a i).val*(a j).val=0)
    (ht : ∑ i, (a i).val=p.val) : CornerPartition p where
  size := Fintype.card ι
  piece i := a ((Fintype.equivFin ι).symm i)
  orthogonal i j hij := ha _ _ (fun h => hij ((Fintype.equivFin ι).symm.injective h))
  total := by simpa only using (Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => (a i).val)).trans ht

end CornerPartition

end

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
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralPinching
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual sign splitting inside a prescribed residual corner. -/
section
open scoped CStarAlgebra BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace CornerPartition
/-- Splitting p at an explicitly given subprojection q. -/
def binary (p q : AlgebraProjection M) (hq : q ≤ p) : CornerPartition p :=
  ofFamily (fun b : Bool => if b then q else
    ⟨p.val-q.val,q.property.sub_of_mul_eq_right p.property hq⟩)
    (by
      intro i j hij
      cases i <;> cases j
      · exact (hij rfl).elim
      · change (p.val-q.val)*q.val=0
        rw [sub_mul,hq,q.property.isIdempotentElem.eq,sub_self]
      · change q.val*(p.val-q.val)=0
        rw [mul_sub,projection_mul_of_le hq,q.property.isIdempotentElem.eq,sub_self]
      · exact (hij rfl).elim)
    (by
      rw [Fintype.sum_bool]
      change q.val+(p.val-q.val)=p.val
      abel)

end CornerPartition

end

/-! The constructed spectral splitting preserves the compressed operator.
This is distinct from using that splitting to reduce other operators' energy. -/

/-! Interval bounds propagated through constructed spectral corner splits. -/

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
-- module Solutions.OAIQ11_FG.FactorGeneration_MatrixUnits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Actual finite matrix algebras from matrix-unit laws. No factor or trace
hypothesis is needed for the algebraic construction. -/
open scoped BigOperators

namespace MatrixUnitSystem
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A]
variable (E : MatrixUnitSystem ι A)

variable [StarModule ℂ A]

instance algebra_finiteDimensional : FiniteDimensional ℂ E.algebra := by
  change FiniteDimensional ℂ E.hom.toAlgHom.range
  exact FiniteDimensional.of_surjective E.hom.toAlgHom.rangeRestrict.toLinearMap
    E.hom.toAlgHom.rangeRestrict_surjective

/-! Commuting unital systems multiply to a larger full matrix algebra.
This proves compatibility algebraically; it does not construct a system in
a relative commutant or establish irreducibility of an infinite union. -/
open scoped BigOperators
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

variable (F : MatrixUnitSystem κ A)
variable (hc : ∀ i j k l, Commute (E.entry i j) (F.entry k l))

def product : MatrixUnitSystem (ι × κ) A where
  entry a b := E.entry a.1 b.1 * F.entry a.2 b.2
  star_entry a b := by
    rw [star_mul,E.star_entry,F.star_entry]
    exact (hc _ _ _ _).eq.symm
  mul_entry a b c d := by
    have hr : (E.entry a.1 b.1*F.entry a.2 b.2)*(E.entry c.1 d.1*F.entry c.2 d.2)=
        (E.entry a.1 b.1*E.entry c.1 d.1)*(F.entry a.2 b.2*F.entry c.2 d.2) := by
      calc _ = E.entry a.1 b.1*(F.entry a.2 b.2*E.entry c.1 d.1)*F.entry c.2 d.2 := by
              simp only [mul_assoc]
           _ = _ := by rw [(hc c.1 d.1 a.2 b.2).eq.symm]; simp only [mul_assoc]
    rw [hr,E.mul_entry,F.mul_entry]
    by_cases h1 : b.1=c.1 <;> by_cases h2 : b.2=c.2 <;>
      simp [h1,h2,Prod.ext_iff]
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum,F.total,mul_one,E.total]

/-! Corner amplification inside the actual matrix-unit commutant. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

def amplify (o : ι) (x : A) : A := ∑ i, E.entry i o*x*E.entry o i

/-! Diffuseness passes to the full matrix-unit commutant by splitting a
compressed projection and amplifying the split. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

open scoped BigOperators
variable {ι κ A B : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A]
variable [Ring B] [StarRing B] [Algebra ℂ B]
variable (E : MatrixUnitSystem ι A)

/-! Actual matrix amplification by coefficients in the full matrix-unit
commutant. The evaluation homomorphism is proved surjective algebraically. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

def coefficientEval (a : Matrix ι ι E.commutant) : A :=
  ∑ i,∑ j,E.commutant.subtype (a i j)*E.entry i j

theorem coefficientEval_mul (a b : Matrix ι ι E.commutant) :
    E.coefficientEval (a*b)=E.coefficientEval a*E.coefficientEval b := by
  simp only [coefficientEval,Matrix.mul_apply,map_sum,map_mul,
    Finset.sum_mul,Finset.mul_sum]
  have he (i j k l : ι) :
      ((a i j).val*E.entry i j)*((b k l).val*E.entry k l)=
        (a i j).val*(b k l).val*(E.entry i j*E.entry k l) := by
    rw [mul_assoc,← mul_assoc (E.entry i j),((b k l).property i j).eq]
    simp only [mul_assoc]
  change (∑ i,∑ j,∑ k,(a i k).val*(b k j).val*E.entry i j) =
    ∑ k,∑ l,∑ i,∑ j,((a i j).val*E.entry i j)*((b k l).val*E.entry k l)
  simp only [he,E.mul_entry,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
  conv_lhs =>
    arg 2
    intro i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_comm

theorem coefficientEval_star (a : Matrix ι ι E.commutant) :
    E.coefficientEval (star a)=star (E.coefficientEval a) := by
  simp only [coefficientEval,star_sum,star_mul,E.star_entry,Matrix.star_apply,
    map_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact ((star (a i j)).property j i).eq.symm

theorem coefficientEval_one : E.coefficientEval 1=1 := by
  simpa [coefficientEval,Matrix.one_apply,apply_ite,ite_mul] using E.total

def coefficientHom : Matrix ι ι E.commutant →⋆ₐ[ℂ] A where
  toFun := E.coefficientEval
  map_one' := E.coefficientEval_one
  map_mul' := E.coefficientEval_mul
  map_zero' := by simp [coefficientEval]
  map_add' a b := by simp [coefficientEval,add_mul,Finset.sum_add_distrib]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    change E.coefficientEval (c • 1)=algebraMap ℂ A c
    simp only [coefficientEval,Matrix.smul_apply,map_smul,smul_mul_assoc,
      ← Finset.smul_sum]
    change c • E.coefficientEval 1=algebraMap ℂ A c
    rw [E.coefficientEval_one,Algebra.algebraMap_eq_smul_one]
  map_star' := E.coefficientEval_star

end MatrixUnitSystem

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_MatrixAlgebras
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Equal-trace finite partitions extend to actual matrix units in the same
factor. The theorem also retains a prescribed corner as the sum of diagonals. -/
open scoped BigOperators

/-! The matrix-unit image in the original represented algebra, with its
finite dimensionality and weak-operator closedness proved. -/
open scoped BigOperators

/-! The actual relative commutant in M is a diffuse scalar-center von
Neumann algebra, with the restricted faithful trace available from M. -/
namespace MatrixUnitSystem

section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (E : MatrixUnitSystem ι M.toStarSubalgebra)

def relativeEquiv : E.commutant ≃⋆ₐ[ℂ] E.relativeVonNeumann.toStarSubalgebra where
  toFun a := ⟨a.val.val,⟨a,rfl⟩⟩
  invFun a := ⟨⟨a.val,((E.relativeStar_mem a.val).mp a.property).1⟩,
    fun i j => Subtype.ext (((E.relativeStar_mem a.val).mp a.property).2 i j)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

end

/-! Passing an irreducible inclusion through a common finite matrix algebra
preserves irreducibility of the actual relative commutants. -/

open UltrapowerBridge Tracial

end MatrixUnitSystem

/-! Explicit Bell projections in two equal finite matrix factors. -/
open scoped BigOperators

/-! Exact normalized traces of constructed matrix algebras and all their
commuting product refinements. -/
open scoped BigOperators
namespace MatrixUnitSystem

open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {n : ℕ} [NeZero n]
variable (E F : MatrixUnitSystem (ZMod n) M.toStarSubalgebra)
variable (hc : ∀ i j k l,Commute (E.entry i j) (F.entry k l))

def bellPiece (s f : ZMod n) : AlgebraProjection M :=
  ⟨(E.product F hc).hom (Bell.projection s f),by
    constructor
    · show (E.product F hc).hom (Bell.projection s f) *
        (E.product F hc).hom (Bell.projection s f) = _
      rw [← map_mul,Bell.projection_mul,ite_eq_left ⟨rfl,rfl⟩]
    · show star ((E.product F hc).hom (Bell.projection s f)) = _
      rw [← map_star,Bell.projection_star]⟩

theorem bellPiece_orthogonal (a b : ZMod n × ZMod n) (h : a≠b) :
    (E.bellPiece F hc a.1 a.2).val * (E.bellPiece F hc b.1 b.2).val = 0 := by
  change (E.product F hc).hom _ * (E.product F hc).hom _ = 0
  rw [← map_mul,Bell.projection_mul,ite_eq_right (fun he => h (Prod.ext he.1 he.2)),map_zero]

theorem bellPiece_total :
    (∑ a : ZMod n × ZMod n,(E.bellPiece F hc a.1 a.2).val) = 1 := by
  change (∑ a : ZMod n × ZMod n,(E.product F hc).hom (Bell.projection a.1 a.2))=1
  rw [← map_sum,Fintype.sum_prod_type,Bell.projection_total,map_one]

def bellPartition : CornerPartition (identityProjection M) where
  size := Fintype.card (ZMod n × ZMod n)
  piece i := let a := (Fintype.equivFin (ZMod n × ZMod n)).symm i
    E.bellPiece F hc a.1 a.2
  orthogonal _ _ h := E.bellPiece_orthogonal F hc _ _
    (fun he => h ((Fintype.equivFin (ZMod n × ZMod n)).symm.injective he))
  total := ((Fintype.equivFin (ZMod n × ZMod n)).symm.sum_comp
    (fun a => (E.bellPiece F hc a.1 a.2).val)).trans (E.bellPiece_total F hc)

end MatrixUnitSystem

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_MatrixRefinement
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! A normal element of a diffuse finite factor has L2 approximations in
constructed full dyadic matrix algebras. No prescribed MASA is needed. -/

/-! Concrete commutants reverse matrix-algebra inclusion. Expectations are
compatible with restriction to an intermediate represented subalgebra. -/

/-! Quantitative energy descent retaining a prescribed finite matrix algebra
in an irreducible inclusion. All expectations and refinements are constructed. -/

/-! Reindex full matrix units without changing their actual algebra or
relative commutant. This keeps iterated constructions indexed by Fin n. -/
namespace MatrixUnitSystem
open scoped BigOperators
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

def reindex (E : MatrixUnitSystem ι A) (e : κ ≃ ι) : MatrixUnitSystem κ A where
  entry i j := E.entry (e i) (e j)
  star_entry i j := E.star_entry _ _
  mul_entry i j k l := by simpa only [e.apply_eq_iff_eq] using E.mul_entry (e i) (e j) (e k) (e l)
  total := (e.sum_comp (fun i => E.entry i i)).trans E.total

open UltrapowerBridge

end MatrixUnitSystem

/-! An actual full matrix algebra of any positive finite size can be
constructed in the relative commutant. No commuting matrix units are assumed. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_AmplificationEncoding
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! One arbitrary operator and a pair of self-adjoint operators generate the same weakly closed star algebra. -/
open scoped ComplexStarModule

/-! Two self-adjoint generators for an actual two-by-two amplification
whose actual commutant has four self-adjoint generators. Spectral separation
is proved, and the final generation uses the surjective coefficient map. -/
open scoped BigOperators
namespace MatrixUnitSystem
open MatrixEncoding
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (E : MatrixUnitSystem (Fin 2) M.toStarSubalgebra)

def concreteCoefficientHom : Matrix (Fin 2) (Fin 2) E.commutant →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  M.toStarSubalgebra.subtype.comp E.coefficientHom

end MatrixUnitSystem

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Coefficients
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Coefficientwise absolute-value product comparison, retaining all convolution terms contributing to the same group element. -/
section
open scoped BigOperators
variable {G : Type*} [Monoid G]

omit [Monoid G] in
@[simp] theorem normCoefficients_support (f : MonoidAlgebra ℂ G) :
    (normCoefficients f).coeff.support = f.coeff.support := by
  ext g
  simp only [Finsupp.mem_support_iff, normCoefficients_apply, ne_eq, norm_eq_zero]

end

/-! The coefficientwise ordered ring of real finite group-ring sums.
The multiplication is actual collected convolution. -/
open scoped BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Convolution
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.predualFunctionals_normed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Coordinate masks and permutations on the actual complex square-summable space.
These implement the Hilbert-space operations used in lem:length-one-convolution. -/

/-! Length-one convolution bounds for the left regular representation of a free group on an arbitrary basis. -/
section
open scoped BigOperators InnerProductSpace
attribute [local instance] Classical.propDecidable Classical.decEq
namespace FreeConvolution
variable {A : Type*}

def inverseLetter (a : Letter A) : Letter A := (a.1, !a.2)
def letter (a : Letter A) : FreeGroup A := FreeGroup.mk [a]
def begins (a : Letter A) (w : FreeGroup A) : Prop := w.toWord.head? = some a

@[simp] theorem inverseLetter_inverse (a : Letter A) : inverseLetter (inverseLetter a) = a := by
  cases a; simp [inverseLetter]

@[simp] theorem letter_toWord (a : Letter A) : (letter a).toWord = [a] := by
  simp [letter]

@[simp] theorem letter_inverse (a : Letter A) : letter (inverseLetter a) = (letter a)⁻¹ := by
  simp [letter, FreeGroup.inv_mk, FreeGroup.invRev, inverseLetter]

@[simp] theorem letter_true (a : A) : letter (a, true) = FreeGroup.of a := rfl

@[simp] theorem leftRegular_apply (g : FreeGroup A) (f : SquareSpace (FreeGroup A))
    (x : FreeGroup A) : leftRegular g f x = f (g⁻¹ * x) := rfl

@[simp] theorem leftRegular_norm (g : FreeGroup A) (f : SquareSpace (FreeGroup A)) :
    ‖leftRegular g f‖ = ‖f‖ := coordinatePermute_norm _ _

def creation (a : Letter A) (f : SquareSpace (FreeGroup A)) : SquareSpace (FreeGroup A) :=
  leftRegular (letter a) (coordinateMask {w | ¬ begins (inverseLetter a) w} f)

def cancellation (a : Letter A) (f : SquareSpace (FreeGroup A)) : SquareSpace (FreeGroup A) :=
  leftRegular (letter a) (coordinateMask {w | begins (inverseLetter a) w} f)

end FreeConvolution

end

/-! Group-ring action on ℓ² and the coefficient-vector identity. -/
section
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq
namespace FreeConvolution
variable {A : Type*}
local notation "H" => SquareSpace (FreeGroup A)
local notation "Op" => H →L[ℂ] H

def leftRegularHom : FreeGroup A →* Op where
  toFun := leftRegular
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_inv_rev, mul_assoc]

def regular : MonoidAlgebra ℂ (FreeGroup A) →ₐ[ℂ] Op :=
  MonoidAlgebra.lift ℂ Op (FreeGroup A) leftRegularHom

def realRegular : MonoidAlgebra ℝ (FreeGroup A) →ₐ[ℝ] Op :=
  MonoidAlgebra.lift ℝ Op (FreeGroup A) leftRegularHom

def delta : H := lp.single 2 1 1

@[simp] theorem delta_apply (x : FreeGroup A) : (delta : H) x = if x = 1 then 1 else 0 := by
  by_cases hx : x = 1 <;> simp [delta, lp.single_apply, hx]

@[simp] theorem delta_norm : ‖(delta : H)‖ = 1 := by
  simp [delta, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

@[simp] theorem leftRegular_delta_apply (g x : FreeGroup A) :
    leftRegular g (delta : H) x = if x = g then 1 else 0 := by
  simp [inv_mul_eq_one, eq_comm]

end FreeConvolution

end

/-! The finite coefficient L² identity from orthonormality of reduced-word images. -/

/-! Multiplicity-weighted length-one convolution bounds. -/
open scoped BigOperators
open Generator.FreeConvolution

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_PartialUnitaries
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Popa's extension order on actual supported partial unitaries, and its
exact L2 distance identity. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

structure PartialUnitary (M : VonNeumannAlgebra H) where
  support : AlgebraProjection M
  unitary : CornerUnitary support

namespace PartialUnitary
abbrev val (v : PartialUnitary M) := v.unitary.val

@[ext] theorem ext {v w : PartialUnitary M} (h : v.val=w.val) : v=w := by
  have hp : v.support=w.support := by
    apply Subtype.ext
    calc v.support.val = star v.val*v.val := v.unitary.initial.symm
         _ = star w.val*w.val := by rw [h]
         _ = w.support.val := w.unitary.initial
  cases v with | mk p v =>
    cases w with | mk q w =>
      dsimp at hp
      subst q
      congr 1
      cases v
      cases w
      congr 1

end PartialUnitary

end

/-! Actual L2 limits of partial unitaries and upper bounds of increasing
sequences, using their exact support-trace distance. -/

/-! Actual orthogonal corner unitaries from dyadic trace cuts. These supply
weakly vanishing scalar matrix coefficients for the scalar-commutant case
of Popa's coordinate nonintertwining criterion. -/

/-! Popa 1308.3982v3, §1.5, scalar-target specialization. The sequence is
constructed from actual dyadic trace cuts in each nonzero corner; neither
nonintertwining nor Haar existence is an assumption. -/
open Filter
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_CoordinateUnitaries
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Complete each supported partial unitary by the identity on its orthogonal
complement. If the quotient support is one, the quotient value is unchanged. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def PartialUnitary.completed (v : PartialUnitary M) : M.toStarSubalgebra :=
  v.val+(1-v.support.val)

end

/-! Ordered independence with actual coordinate unitaries in the included
algebra, obtained by completing the constructed partial-unitary coordinates. -/

/-! Two coordinate-unitary witnesses produce the reduced-moment Haar precursor
while retaining actual unitary coordinates in the included algebra. -/

/-! Full integer endpoint moments and an actual included coordinate-unitary
Haar witness, before imposing an operator topology on generated algebras. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_FiniteComparison
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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

/-! Trace-free chain upper bounds and maximal partial isometries, with prescribed
initial and final projection bounds. The index set may be uncountable. -/

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

/-! Arbitrary-chain bounds with moving orthogonal initial and final supports, obtained from successive fixed-multiplier weak operator limits without a trace. -/
namespace Tracial
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Orthogonality passes to subprojections in both variables. -/
theorem projection_orthogonal_of_le {p q r s : AlgebraProjection M}
    (h : p.val*q.val=0) (hr : r ≤ p) (hs : s ≤ q) : r.val*s.val=0 := by
  calc _ = (r.val*p.val)*(q.val*s.val) := by rw [projection_mul_of_le hr,hs]
       _ = r.val*(p.val*q.val)*s.val := by simp only [mul_assoc]
       _ = 0 := by rw [h,mul_zero,zero_mul]

namespace PartialIsometry

/-! Simultaneous least initial and final support bounds for arbitrary directed
partial-isometry nets. The actual ultralimit is chosen once for all bounds. -/

/-- The initial and final projections of this upper bound are the respective
least upper bounds of the net's initial and final projections. -/
theorem traceFree_monotone_least_supports
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (a : ι → PartialIsometry M) (ha : Monotone a) :
    ∃ v : PartialIsometry M, (∀ i, a i ≤ v) ∧
      (∀ p : AlgebraProjection M, (∀ i, (a i).support ≤ p) → v.support ≤ p) ∧
      (∀ q : AlgebraProjection M, (∀ i, (a i).target ≤ q) → v.target ≤ q) := by
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
  · intro p hp
    apply (v.support_le_iff_mul p).mpr
    apply wot_limit_unique (fun i => (a i).val*p.val) _ _
      (wot_limit_mul_right _ _ _ hb)
    simpa only [fun i => ((a i).support_le_iff_mul p).mp (hp i)] using hb
  · intro q hq
    apply (v.target_le_iff_mul q).mpr
    apply wot_limit_unique (fun i => q.val*(a i).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    simpa only [fun i => ((a i).target_le_iff_mul q).mp (hq i)] using hb

end PartialIsometry
end Tracial

/-! Complete actual partial isometries to unitaries in a finite factor.
The construction uses projection comparison and finiteness, without a trace. -/
open scoped CStarAlgebra
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance unitaryPolarCStar : CStarAlgebra M.toStarSubalgebra := {}

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_DyadicComparison
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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

/-- The sum of two orthogonal projections, in the original algebra. -/
def orthogonalSum (p q : AlgebraProjection M) (h : p.val*q.val=0) : AlgebraProjection M :=
  ⟨p.val+q.val,p.property.add q.property h⟩

theorem le_orthogonalSum_left (p q : AlgebraProjection M) (h : p.val*q.val=0) :
    p ≤ orthogonalSum p q h := by
  change (p.val+q.val)*p.val=p.val
  rw [add_mul,p.property.isIdempotentElem.eq,PartialIsometry.orthogonal_reverse _ _ h,add_zero]

theorem le_orthogonalSum_right (p q : AlgebraProjection M) (h : p.val*q.val=0) :
    q ≤ orthogonalSum p q h := by
  change (p.val+q.val)*q.val=q.val
  rw [add_mul,h,q.property.isIdempotentElem.eq,zero_add]

theorem orthogonalSum_le {p q r : AlgebraProjection M} (h : p.val*q.val=0)
    (hp : p ≤ r) (hq : q ≤ r) : orthogonalSum p q h ≤ r := by
  change r.val*(p.val+q.val)=p.val+q.val
  rw [mul_add,hp,hq]

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
namespace PartialIsometry

theorem compose_target (v w : PartialIsometry M) (h : w.target ≤ v.support) :
    (compose v w h).target.val=v.val*w.target.val*star v.val := by
  change (v.val*w.val)*star (v.val*w.val)=v.val*(w.val*star w.val)*star v.val
  simp only [star_mul,mul_assoc]

end PartialIsometry

end Tracial

/-! Coherent dyadic equivalent partitions and matrix units, constructed from
scalar center and diffuseness without a trace. DyadicIndex is reused as a
finite binary index type; no tracial partition construction is used. -/
open scoped BigOperators

end

/-! Actual sums of countable orthogonal partial isometries, including least
initial/final support identities. No trace or countable-cofinality premise. -/
namespace Tracial

/-! Projection equivalence and subequivalence are witnessed by actual partial
isometries in the original algebra. No dimension or trace oracle is used. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

theorem compose_target_of_eq (v w : PartialIsometry M) (h : w.target=v.support) :
    (v.compose w (le_of_eq h)).target=v.target := by
  apply Subtype.ext
  rw [compose_target,h,v.mul_support]
  rfl

end PartialIsometry
namespace AlgebraProjection

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

theorem equivalent_trans {p q r : AlgebraProjection M}
    (h : p.Equivalent q) (k : q.Equivalent r) : p.Equivalent r := by
  obtain ⟨v,hv,hvq⟩ := h
  obtain ⟨w,hw,hwr⟩ := k
  have hc : v.target=w.support := hvq.trans hw.symm
  exact ⟨w.compose v (le_of_eq hc),hv,(w.compose_target_of_eq v hc).trans hwr⟩

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
/-- Comparison respects subtraction of equivalent pieces. -/
theorem remainder_subequivalent {p q P Q : AlgebraProjection M}
    (hp : p ≤ P) (hq : q ≤ Q) (he : p.Equivalent q) (h : P.Subequivalent Q) :
    (remainder p P hp).Subequivalent (remainder q Q hq) := by
  apply subequivalent_cancel hfinite hfactor
    (remainder_orthogonal p P hp) (remainder_orthogonal q Q hq) he
  simpa only [orthogonalSum_remainder] using h

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
namespace PartialIsometry

theorem exists_finsetSum {ι : Type*} (a : ι → PartialIsometry M) (s : Finset ι)
    (hp : ∀ i ∈ s, ∀ j ∈ s, i≠j → (a i).support.val*(a j).support.val=0)
    (hq : ∀ i ∈ s, ∀ j ∈ s, i≠j → (a i).target.val*(a j).target.val=0) :
    ∃ v : PartialIsometry M, v.val=∑ i ∈ s, (a i).val ∧
      v.support.val=∑ i ∈ s, (a i).support.val ∧
      v.target.val=∑ i ∈ s, (a i).target.val := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨zero,by simp [zero],by simp [zero],by simp [zero,target]⟩
  | @insert i s hi ih =>
    obtain ⟨v,hv,hs,ht⟩ := ih
      (fun j hj k hk => hp j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
      (fun j hj k hk => hq j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
    have ho₁ : (a i).support.val*v.support.val=0 := by
      rw [hs,Finset.mul_sum]
      exact Finset.sum_eq_zero (fun j hj => hp i (Finset.mem_insert_self _ _) j
        (Finset.mem_insert_of_mem hj) (fun h => hi (h.symm ▸ hj)))
    have ho₂ : (a i).target.val*v.target.val=0 := by
      rw [ht,Finset.mul_sum]
      exact Finset.sum_eq_zero (fun j hj => hq i (Finset.mem_insert_self _ _) j
        (Finset.mem_insert_of_mem hj) (fun h => hi (h.symm ▸ hj)))
    refine ⟨(a i).patch v ho₁ ho₂,?_,?_,?_⟩
    · change (a i).val+v.val=_
      rw [hv,Finset.sum_insert hi]
    · change (a i).support.val+v.support.val=_
      rw [hs,Finset.sum_insert hi]
    · rw [patch_target,ht,Finset.sum_insert hi]

end PartialIsometry
namespace AlgebraProjection

theorem isStarProjection_sum {ι : Type*} (a : ι → AlgebraProjection M) (s : Finset ι)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i≠j → (a i).val*(a j).val=0) :
    IsStarProjection (∑ i ∈ s, (a i).val) := by
  obtain ⟨v,_,hs,_⟩ := PartialIsometry.exists_finsetSum
    (fun i => PartialIsometry.onProjection (a i)) s ho
    (by simpa only [PartialIsometry.onProjection_target] using ho)
  change v.support.val=(∑ i ∈ s, (a i).val) at hs
  exact hs ▸ v.support.property

def finsetSum {ι : Type*} (a : ι → AlgebraProjection M) (s : Finset ι)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i≠j → (a i).val*(a j).val=0) : AlgebraProjection M :=
  ⟨∑ i ∈ s, (a i).val,isStarProjection_sum a s ho⟩

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
end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_NormalDimension
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Increasing projection suprema and compatible sequential comparison.
The witnesses live in the original algebra; no trace or dimension is used. -/
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace AlgebraProjection

/-- Actual least upper bounds for arbitrary nonempty directed projection nets. -/
theorem exists_isLUB_monotone
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (q : I → AlgebraProjection M) (hq : Monotone q) :
    ∃ p : AlgebraProjection M, IsLUB (Set.range q) p := by
  obtain ⟨v,hv,hs,_⟩ := PartialIsometry.traceFree_monotone_least_supports
    (fun i => PartialIsometry.onProjection (q i)) (fun _ _ h => hq h)
  refine ⟨v.support,?_,?_⟩
  · rintro _ ⟨i,rfl⟩
    exact PartialIsometry.support_mono (hv i)
  · intro p hp
    exact hs p (fun i => hp ⟨i,rfl⟩)

end AlgebraProjection
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

theorem vectorValue_eq_norm_sq (ξ : H) (p : AlgebraProjection M) :
    vectorValue ξ p = ‖p.val.val ξ‖^2 := by
  have hs : star p.val.val=p.val.val := congrArg Subtype.val p.property.isSelfAdjoint.star_eq
  have hi : p.val.val (p.val.val ξ)=p.val.val ξ :=
    congrArg (fun a : M.toStarSubalgebra => a.val ξ) p.property.isIdempotentElem.eq
  have he : inner ℂ (p.val.val ξ) (p.val.val ξ)=inner ℂ ξ (p.val.val ξ) := by
    rw [← ContinuousLinearMap.adjoint_inner_right p.val.val]
    rw [← ContinuousLinearMap.star_eq_adjoint,hs,hi]
  rw [vectorValue,← he,inner_self_eq_norm_sq_to_K]
  norm_cast

theorem vectorValue_nonneg (ξ : H) (p : AlgebraProjection M) : 0 ≤ vectorValue ξ p := by
  rw [vectorValue_eq_norm_sq]
  positivity

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

/-- Retains the matrix-coefficient limit of the concrete projection supremum.
The ultrafilter is the fixed extension of atTop, not a countable subsequence. -/
theorem exists_isLUB_monotone_vector_limit
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (a : ι → AlgebraProjection M) (ha : Monotone a) :
    ∃ p : AlgebraProjection M, IsLUB (Set.range a) p ∧
      ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val.val x))
        ((Ultrafilter.of atTop : Ultrafilter ι) : Filter ι) (𝓝 (inner ℂ y (p.val.val x))) := by
  let ω : Ultrafilter ι := Ultrafilter.of atTop
  obtain ⟨T, _, ht⟩ := exists_weak_operator_ultralimit ω
    (fun i => ((a i).val : H →L[ℂ] H)) 1 (by norm_num)
    (fun i => (a i).property.norm_le)
  let b : M.toStarSubalgebra := ⟨T, weak_operator_limit_mem M (fun i => (a i).val) T ht⟩
  have hb (x y : H) : Tendsto (fun i => inner ℂ y (((a i).val : H →L[ℂ] H) x))
    (ω : Filter ι) (𝓝 (inner ℂ y ((b : H →L[ℂ] H) x))) := ht x y
  have hadj (i : ι) (x y : H) :
      inner ℂ x (((a i).val : H →L[ℂ] H) y) =
      inner ℂ (((a i).val : H →L[ℂ] H) x) y := by
    have hs : star (((a i).val : H →L[ℂ] H)) = ((a i).val : H →L[ℂ] H) :=
      congrArg Subtype.val (a i).property.isSelfAdjoint.star_eq
    calc inner ℂ x (((a i).val : H →L[ℂ] H) y) =
          inner ℂ x (star (((a i).val : H →L[ℂ] H)) y) := by rw [hs]
         _ = inner ℂ (((a i).val : H →L[ℂ] H) x) y := by
           rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have hself : star b = b := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    have hh := (hb y x).star
    change Tendsto (fun i => (starRingEnd ℂ) (inner ℂ x (((a i).val : H →L[ℂ] H) y)))
      (ω : Filter ι) (𝓝 ((starRingEnd ℂ) (inner ℂ x ((b : H →L[ℂ] H) y)))) at hh
    simp only [inner_conj_symm] at hh
    have eq := tendsto_nhds_unique (hb x y) (hh.congr (fun i => (hadj i y x).symm))
    change inner ℂ y (star (b : H →L[ℂ] H) x) = inner ℂ y ((b : H →L[ℂ] H) x)
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    exact eq.symm
  have hba (i : ι) : b * (a i).val = (a i).val := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (hb (((a i).val : H →L[ℂ] H) x) y)
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_ge_atTop i).filter_mono (Ultrafilter.of_le atTop)] with j hj
    exact (congrArg (fun z : M.toStarSubalgebra => inner ℂ y ((z : H →L[ℂ] H) x)) (ha hj)).symm
  have hab (i : ι) : (a i).val * b = (a i).val := by
    have h := congrArg star (hba i)
    simpa only [star_mul, hself, (a i).property.isSelfAdjoint.star_eq] using h
  have hid : b * b = b := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (hb ((b : H →L[ℂ] H) x) y)
    exact (hb x y).congr (fun i =>
      (congrArg (fun z : M.toStarSubalgebra => inner ℂ y ((z : H →L[ℂ] H) x)) (hab i)).symm)
  refine ⟨⟨b,⟨hid,hself⟩⟩,⟨?_,?_⟩,hb⟩
  · rintro _ ⟨i,rfl⟩
    exact hba i
  · intro p hp
    change p.val*b=b
    apply wot_limit_unique (fun i => p.val*(a i).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    have hpa (i : ι) : p.val*(a i).val=(a i).val := hp ⟨i,rfl⟩
    simpa only [hpa] using hb

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
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralStates
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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

def AlgebraProjection.unitaryConjugate (p : AlgebraProjection M)
    (u : unitary M.toStarSubalgebra) : AlgebraProjection M :=
  ⟨Unitary.conjStarAlgAut ℂ M.toStarSubalgebra u p.val,
    p.property.map (Unitary.conjStarAlgAut ℂ M.toStarSubalgebra u)⟩

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

end

/-! The constructed scalar agrees on x*x and xx*, by an actual unitary polar
decomposition. This is a quadratic identity, not unrestricted additivity. -/
open scoped CStarAlgebra

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_LocalizedStates
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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

section
-- module Solutions.OAIQ11_FG.FactorGeneration_MatrixGenerators
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Diagonal projections and one full-support rank-one projection generate
every finite full matrix algebra, including matrices larger than size two. -/
namespace MatrixUnitSystem
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

def fullProjection : A := E.hom (fullProjectionMatrix (ι := ι))

end MatrixUnitSystem

/-! Two actual self-adjoint generators for the weak closure of countably
many pairwise commuting finite full matrix factors. -/

/-! The retained tensor extensions supply commuting factors generating
exactly the original matrix-union weak closure. -/

/-! The represented irreducible matrix subfactor can be constructed together
with two self-adjoint generators, without hyperfinite uniqueness. -/

end Generator

end

end OAI
end


