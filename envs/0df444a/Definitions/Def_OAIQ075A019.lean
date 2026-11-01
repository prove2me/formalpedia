-- Prove2me | Definitions.Def_OAIQ075A019
-- name    : OAIQ075A019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:13:20.037805+00:00
-- url     : https://prove2.me/theorems/2e34f893-332d-4428-aa6c-e1c9799abfc0
-- title:
--   Definitions bundle OAIQ075A019 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 21 declarations of OpenAI's Lean: 21 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_CornerTrace`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/CornerTrace.lean), [`FactorGeneration_Expectations`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/Expectations.lean), [`FactorGeneration_HilbertLimits`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/HilbertLimits.lean), [`FactorGeneration_MatrixRefinement`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/MatrixRefinement.lean), [`FactorGeneration_SpectralTruncation`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/SpectralTruncation.lean), [`FactorGeneration_Subfactors`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/FactorGeneration/Subfactors.lean).
--
--   **Imports.** It imports the bundles `OAIQ075A013` and `OAIQ075A014` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ075A026`; the proof of `OAI_KadisonSimilarity_exists_corner_intertwiner_of_column_tests`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ075A013
import Definitions.Def_OAIQ075A014

section
-- module Solutions.OAIQ075_KS.FactorGeneration_CornerTrace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Trace estimates in the actual ambient algebra. The corner scalar uses
its normalized trace. These estimates do not assume or assert the existence
of a local-quantizing projection. -/

/-! Actual noncommutative L1 on the coordinate algebra: trace(sqrt(x* x)).
The supported L2-to-L1 estimate retains the square root of the support trace.
No quantizing projection or conditional expectation theorem is assumed. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (τ : TracialRepresentation M)

attribute [local instance] OAI.Generator.Tracial.instCStarAlgebraSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions
attribute [local instance] OAI.Generator.Tracial.instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions
attribute [local instance] OAI.Generator.Tracial.instLESubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions
attribute [local instance] OAI.Generator.Tracial.instStarOrderedRingSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions
theorem trace_nonneg_of_nonneg (a : M.toStarSubalgebra) (ha : 0 ≤ a) :
    0 ≤ (τ.trace a).re := by
  have hs := (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  have h := congrArg Complex.re (τ.trace_star_mul (CFC.sqrt a))
  rw [hs,CFC.sqrt_mul_sqrt_self a ha] at h
  rw [h]
  simp only [← Complex.ofReal_pow,Complex.ofReal_re]
  positivity

end

/-! A finite compression-energy estimate yields a nonzero corner projection with simultaneous L1 control. -/

/-! The scalar trace estimate for a term with two supported patch letters.
It reduces to the actual compressed middle coefficient and keeps trace(q),
not trace(p), as the scale of the error. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_HilbertLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Multiplication and adjoint limits in L2, with the necessary uniform
operator norm bounds stated explicitly. -/
namespace Tracial
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem norm₂_limit_trace {I : Type*} {l : Filter I}
    (a : I → M.toStarSubalgebra) (b : M.toStarSubalgebra)
    (h : Tendsto (fun i => τ.norm₂ (a i-b)) l (𝓝 0)) :
    Tendsto (fun i => τ.trace (a i)) l (𝓝 (τ.trace b)) := by
  apply (tendsto_iff_norm_sub_tendsto_zero).mpr
  apply squeeze_zero (fun i => norm_nonneg _)
    (fun i => ?_) h
  rw [← trace_sub]
  exact τ.norm_trace_le_norm₂ _

end Tracial

/-! A separating vector for a concrete von Neumann algebra is cyclic for its
commutant. The original representation need not be cyclic for the algebra. -/

/-! Restrict the faithful trace representation to the closure of M times its
trace vector. This constructs a faithful, isometric, cyclic representation on
an actual Hilbert subspace. No Banach predual or WOT-closed image is asserted. -/

/-! A real linear functional continuous for bounded trace-two-norm sequences
is WOT continuous on the unit ball. Closed convex slices of the trace-vector
ball supply the conversion; no identification of the two topologies is assumed. -/
open Filter
open scoped Topology

/-! On a uniformly operator-norm bounded family in a faithfully vector-traced
von Neumann algebra, L2 convergence implies strong and adjoint-strong convergence
in the original Hilbert space. -/
open Filter
open scoped Topology

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_SpectralTruncation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Positivity of the tracial pairing does not require the two positive
operators to commute. These estimates will control spectral truncation. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

attribute [local instance] OAI.Generator.Tracial.tracePairingCStar
attribute [local instance] OAI.Generator.Tracial.tracePairingOrder
attribute [local instance] OAI.Generator.Tracial.tracePairingPreorder
attribute [local instance] OAI.Generator.Tracial.tracePairingLE
attribute [local instance] OAI.Generator.Tracial.tracePairingStarOrder
theorem trace_mul_nonneg (a b : M.toStarSubalgebra) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ (τ.trace (a*b)).re := by
  let s := CFC.sqrt a
  have hs : star s=s := (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  have h := trace_nonneg_of_nonneg τ (star s*b*s) (star_left_conjugate_nonneg hb s)
  rw [hs,τ.trace_mul_comm (s*b) s,← mul_assoc,CFC.sqrt_mul_sqrt_self a ha] at h
  exact h

theorem trace_mul_mono (a b c : M.toStarSubalgebra) (ha : 0 ≤ a) (hbc : b ≤ c) :
    (τ.trace (a*b)).re ≤ (τ.trace (a*c)).re := by
  have h := trace_mul_nonneg τ a (c-b) ha (sub_nonneg.mpr hbc)
  rw [mul_sub,trace_sub,Complex.sub_re] at h
  linarith

theorem trace_mul_le_norm (a x : M.toStarSubalgebra) (ha : 0 ≤ a)
    (hx : IsSelfAdjoint x) :
    (τ.trace (a*x)).re ≤ ‖x‖ * (τ.trace a).re := by
  have h := trace_mul_mono τ a x (algebraMap ℝ M.toStarSubalgebra ‖x‖) ha
    hx.le_algebraMap_norm_self
  rw [Algebra.algebraMap_eq_smul_one,mul_smul_comm,mul_one,← Complex.coe_smul,
    cornerTrace_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at h
  exact h

theorem norm₂_sub_sq (x y : M.toStarSubalgebra) :
    τ.norm₂ (x-y)^2 = τ.norm₂ x^2 + τ.norm₂ y^2 -
      2*(τ.trace (star x*y)).re := by
  have h := norm_sub_sq (𝕜 := ℂ) (baseVector τ x) (baseVector τ y)
  rw [← map_sub,baseVector_inner_trace] at h
  change τ.norm₂ (x-y)^2 = τ.norm₂ x^2 - 2*(τ.trace (star x*y)).re + τ.norm₂ y^2 at h
  linarith

end

/-! Upper spectral truncation of a self-adjoint operator. The truncation
remains in the original operator ball and has a positive discarded part. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.truncationCStar
attribute [local instance] OAI.Generator.Tracial.truncationOrder
attribute [local instance] OAI.Generator.Tracial.truncationLE
attribute [local instance] OAI.Generator.Tracial.truncationStarOrder
theorem upperTruncate_cfc (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (C : ℝ) :
    upperTruncate a C = cfc (fun t : ℝ => min t C) a := by
  have hf : (fun t : ℝ => min t C) = fun t => t-(t-C)⁺ := by
    funext t
    simp only [_root_.posPart_def]
    by_cases h : t ≤ C
    · rw [min_eq_left h,max_eq_right (sub_nonpos.mpr h),sub_zero]
    · rw [min_eq_right (le_of_not_ge h),max_eq_left (sub_nonneg.mpr (le_of_not_ge h))]
      ring
  rw [hf,cfc_sub (fun t : ℝ => t) (fun t => (t-C)⁺) a,cfc_id' ℝ a]
  unfold upperTruncate
  congr 1
  rw [CFC.posPart_def,cfcₙ_eq_cfc]
  have hs : cfc (fun t : ℝ => t-C) a = a-algebraMap ℝ M.toStarSubalgebra C := by
    rw [cfc_sub (fun t : ℝ => t) (fun _ => C) a,cfc_id' ℝ a,cfc_const C a ha]
  rw [← hs,← cfc_comp (fun t : ℝ => t⁺) (fun t => t-C) a]
  rfl

theorem upperTruncate_selfAdjoint (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (C : ℝ) :
    IsSelfAdjoint (upperTruncate a C) :=
  ha.sub (CFC.posPart_nonneg _).isSelfAdjoint

theorem upperTruncate_norm_le (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a)
    (C R : ℝ) (hC : 0 ≤ C) (hR : ‖a‖ ≤ R) : ‖upperTruncate a C‖ ≤ R := by
  obtain (hH | hH) := subsingleton_or_nontrivial H
  · have ha0 : a=0 := Subtype.ext (Subsingleton.elim _ _)
    have hz : upperTruncate a C=0 := Subtype.ext (Subsingleton.elim _ _)
    simpa only [hz,norm_zero] using (norm_nonneg a).trans hR
  rw [upperTruncate_cfc a ha C]
  apply norm_cfc_le ((norm_nonneg a).trans hR)
  intro t ht
  have htR := (spectrum.norm_le_norm_of_mem ht).trans hR
  rw [Real.norm_eq_abs,abs_le] at htR ⊢
  exact ⟨le_min htR.1 (by linarith), (min_le_left _ _).trans htR.2⟩

theorem upperTruncate_discard_mul (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (C : ℝ) :
    (a-algebraMap ℝ M.toStarSubalgebra C)⁺ * upperTruncate a C =
      C • (a-algebraMap ℝ M.toStarSubalgebra C)⁺ := by
  let b := a-algebraMap ℝ M.toStarSubalgebra C
  have hb : IsSelfAdjoint b := ha.sub (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all C))
  have he : upperTruncate a C = algebraMap ℝ M.toStarSubalgebra C-b⁻ := by
    have hh := CFC.posPart_sub_negPart b hb
    have heq : a=b+algebraMap ℝ M.toStarSubalgebra C := by dsimp [b]; abel
    change a-b⁺=algebraMap ℝ M.toStarSubalgebra C-b⁻
    nth_rw 1 [heq]
    nth_rw 1 [← hh]
    abel
  rw [he,mul_sub,CFC.posPart_mul_negPart,sub_zero,
    Algebra.algebraMap_eq_smul_one,mul_smul_comm,mul_one]

theorem upperTruncate_distance (τ : TracialRepresentation M)
    (a x : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (hx : IsSelfAdjoint x) :
    τ.norm₂ (upperTruncate a ‖x‖-x)^2 +
      τ.norm₂ ((a-algebraMap ℝ M.toStarSubalgebra ‖x‖)⁺)^2 ≤ τ.norm₂ (a-x)^2 := by
  let d := (a-algebraMap ℝ M.toStarSubalgebra ‖x‖)⁺
  let z := upperTruncate a ‖x‖
  have hd : 0 ≤ d := CFC.posPart_nonneg _
  have had : a=z+d := by dsimp [z,d,upperTruncate]; abel
  have hdz : d*z=‖x‖ • d := upperTruncate_discard_mul a ha ‖x‖
  have ht := trace_mul_le_norm τ d x hd hx
  have hsq := norm₂_sub_sq τ (a-x) d
  have hid : a-x-d=z-x := by rw [had]; abel
  rw [hid,(ha.sub hx).star_eq,τ.trace_mul_comm (a-x) d] at hsq
  have htrace : (τ.trace (d*(a-x))).re =
      τ.norm₂ d^2+‖x‖*(τ.trace d).re-(τ.trace (d*x)).re := by
    rw [had,mul_sub,mul_add,trace_sub,cornerTrace_add,hdz,← Complex.coe_smul,
      cornerTrace_smul,Complex.sub_re,Complex.add_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [norm₂_sq_trace τ,hd.isSelfAdjoint.star_eq]
    ring
  rw [htrace] at hsq
  change τ.norm₂ (z-x)^2 + τ.norm₂ d^2 ≤ τ.norm₂ (a-x)^2
  linarith

end

/-! Spectral truncation forces a self-adjoint least-distance point in a
subalgebra ball to have norm at most the norm of the ambient test operator. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.interiorCStar
attribute [local instance] OAI.Generator.Tracial.interiorOrder
attribute [local instance] OAI.Generator.Tracial.interiorPreorder
attribute [local instance] OAI.Generator.Tracial.interiorLE
attribute [local instance] OAI.Generator.Tracial.interiorStarOrder
theorem included_upperTruncate (hNM : N ≤ M) (a : N.toStarSubalgebra)
    (ha : IsSelfAdjoint a) (C : ℝ) :
    coordinateInclusion hNM (upperTruncate a C)=upperTruncate (coordinateInclusion hNM a) C := by
  rw [upperTruncate_cfc a ha C,
    upperTruncate_cfc _ (included_selfAdjoint hNM a ha) C]
  exact (coordinateInclusion hNM).map_cfc (fun t : ℝ => min t C) a
    (by fun_prop) (by fun_prop) ha (included_selfAdjoint hNM a ha)

theorem selfAdjoint_norm_le_of_bounds (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a)
    (C : ℝ) (hC : 0 ≤ C) (hu : a ≤ algebraMap ℝ M.toStarSubalgebra C)
    (hl : -a ≤ algebraMap ℝ M.toStarSubalgebra C) : ‖a‖ ≤ C := by
  obtain (hA | hA) := subsingleton_or_nontrivial M.toStarSubalgebra
  · simpa only [Subsingleton.elim a 0,norm_zero] using hC
  have hpos : ∀ t ∈ spectrum ℝ a,t ≤ C := by
    apply (cfc_le_iff (fun t : ℝ => t) (fun _ => C) a).mp
    rw [cfc_id' ℝ a ha,cfc_const C a ha]
    exact hu
  have hneg : ∀ t ∈ spectrum ℝ a,-t ≤ C := by
    apply (cfc_le_iff (fun t : ℝ => -t) (fun _ => C) a).mp
    rw [cfc_neg (fun t : ℝ => t) a,cfc_id' ℝ a ha,cfc_const C a ha]
    exact hl
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum ha with h | h
  · exact hpos _ h
  · simpa using hneg _ h

theorem selfAdjoint_ball_minimum_upper (τ : TracialRepresentation M) (hNM : N ≤ M)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (R : ℝ)
    (c : N.toStarSubalgebra) (hc : IsSelfAdjoint c) (hcR : ‖c‖ ≤ R)
    (hmin : ∀ a : N.toStarSubalgebra, IsSelfAdjoint a → ‖a‖ ≤ R →
      τ.norm₂ (x-coordinateInclusion hNM c) ≤ τ.norm₂ (x-coordinateInclusion hNM a)) :
    coordinateInclusion hNM c ≤ algebraMap ℝ M.toStarSubalgebra ‖x‖ := by
  have hz := hmin (upperTruncate c ‖x‖) (upperTruncate_selfAdjoint c hc ‖x‖)
    (upperTruncate_norm_le c hc ‖x‖ R (norm_nonneg _) hcR)
  rw [included_upperTruncate hNM c hc] at hz
  have hd := upperTruncate_distance τ (coordinateInclusion hNM c) x
    (included_selfAdjoint hNM c hc) hx
  have hrev (a b : M.toStarSubalgebra) : τ.norm₂ (a-b)=τ.norm₂ (b-a) := norm_sub_rev _ _
  rw [hrev x,hrev x] at hz
  have he : τ.norm₂ ((coordinateInclusion hNM c-algebraMap ℝ M.toStarSubalgebra ‖x‖)⁺)=0 := by
    nlinarith [show 0 ≤ τ.norm₂ (coordinateInclusion hNM c-x) from norm_nonneg _,
      show 0 ≤ τ.norm₂ (upperTruncate (coordinateInclusion hNM c) ‖x‖-x) from norm_nonneg _,
      show 0 ≤ τ.norm₂ ((coordinateInclusion hNM c-algebraMap ℝ M.toStarSubalgebra ‖x‖)⁺) from norm_nonneg _]
  exact sub_nonpos.mp ((CFC.posPart_eq_zero_iff _
    ((included_selfAdjoint hNM c hc).sub (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all ‖x‖)))).mp
      ((τ.norm₂_eq_zero_iff _).mp he))

theorem selfAdjoint_ball_minimum_norm (τ : TracialRepresentation M) (hNM : N ≤ M)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (R : ℝ)
    (c : N.toStarSubalgebra) (hc : IsSelfAdjoint c) (hcR : ‖c‖ ≤ R)
    (hmin : ∀ a : N.toStarSubalgebra, IsSelfAdjoint a → ‖a‖ ≤ R →
      τ.norm₂ (x-coordinateInclusion hNM c) ≤ τ.norm₂ (x-coordinateInclusion hNM a)) :
    ‖c‖ ≤ ‖x‖ := by
  have hu := selfAdjoint_ball_minimum_upper τ hNM x hx R c hc hcR hmin
  have hn := selfAdjoint_ball_minimum_upper τ hNM (-x) hx.neg R (-c) hc.neg
    (by simpa using hcR) (by
      intro a ha hRa
      have h := hmin (-a) ha.neg (by simpa using hRa)
      have hneg (b : M.toStarSubalgebra) : τ.norm₂ (-b)=τ.norm₂ b := norm_neg _
      rw [map_neg,show -x- -(coordinateInclusion hNM c)=-(x-coordinateInclusion hNM c) by abel,
        show -x-coordinateInclusion hNM a=-(x-coordinateInclusion hNM (-a)) by rw [map_neg]; abel,
        hneg,hneg]
      exact h)
  rw [map_neg,norm_neg] at hn
  exact selfAdjoint_norm_le_of_bounds _ (included_selfAdjoint hNM c hc) ‖x‖ (norm_nonneg _) hu hn

end

/-! Two-sided spectral clipping and trace-norm control. The auxiliary trace
is explicit; the trace-free construction supplies it on its actual closure. -/
open scoped CStarAlgebra
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Subfactors
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The actual von Neumann algebra of operators in N commuting with a finite
projection partition. Its double-commutant identity and completeness are
proved, so spectral approximation can be performed inside this algebra. -/

/-! Irreducibility passes to actual corners. Spectral approximation reduces
self-adjoint corner commutants to their projections; no corner-factor or
normalized-trace existence statement is assumed. -/

/-! The relative commutant of a finite block algebra consists of scalars on
each block. This statement is proved from coordinate irreducibility. -/

/-! Orthogonality to the prescribed subalgebra is stronger than global
centering. It is preserved by compressions and conjugations from that
subalgebra and removes every block scalar term exactly. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

namespace TraceOrthogonal
variable {P : StarSubalgebra ℂ M.toStarSubalgebra} {x : M.toStarSubalgebra}
variable (hx : TraceOrthogonal τ P x)
include hx

theorem trace_zero : τ.trace x=0 := by simpa using hx (1 : P)

end TraceOrthogonal

/-! Quantitative control of the scalar energy that survives compatible
refinement. An orthogonal residual changes none of the block traces. -/

end

/-! A corner whose only projections are zero and its unit is scalar.
The proof constructs spectral approximations; minimality is not a scalar-corner axiom. -/

/-! Diffuseness descends to an irreducible von Neumann subalgebra of a
diffuse finite tracial algebra. Finiteness follows from the actual faithful trace. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Expectations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The orthogonal subalgebra representative of a self-adjoint ambient
operator is constructed, with its operator norm bound. -/
section
open scoped ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem selfAdjoint_pairing_im (τ : TracialRepresentation M)
    (a b : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    (τ.trace (a*b)).im=0 := by
  apply Complex.conj_eq_iff_im.mp
  have hi := inner_conj_symm (𝕜 := ℂ) (baseVector τ a) (baseVector τ b)
  rw [baseVector_inner_trace,baseVector_inner_trace,ha.star_eq,hb.star_eq] at hi
  simpa only [τ.trace_mul_comm b a] using hi

end

/-! A bounded trace-preserving subalgebra projection from self-adjoint least-distance points. Tracial orthogonality gives uniqueness and the bimodule identities. -/
section
open scoped ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

namespace TraceOrthogonal
variable {P : StarSubalgebra ℂ M.toStarSubalgebra} {x y : M.toStarSubalgebra}
theorem sub (hx : TraceOrthogonal τ P x) (hy : TraceOrthogonal τ P y) :
    TraceOrthogonal τ P (x-y) := by
  intro a
  rw [mul_sub,trace_sub,hx a,hy a,sub_self]
theorem eq_zero (hx : TraceOrthogonal τ P x) (hP : x ∈ P) : x=0 := by
  have h := hx ⟨star x,P.star_mem' hP⟩
  change τ.trace (star x*x)=0 at h
  have hr := congrArg Complex.re h
  rw [← norm₂_sq_trace τ] at hr
  exact (τ.norm₂_eq_zero_iff x).mp (sq_eq_zero_iff.mp hr)
end TraceOrthogonal

theorem subalgebra_representative_unique (x y z : M.toStarSubalgebra)
    (hy : y.val ∈ N) (hz : z.val ∈ N)
    (hxy : TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) (x-y))
    (hxz : TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) (x-z)) : y=z := by
  have h := hxz.sub τ hxy
  have he : (x-z)-(x-y)=y-z := by abel
  rw [he] at h
  exact sub_eq_zero.mp (h.eq_zero τ (N.sub_mem hy hz))

end

/-! The constructed expectation preserves adjoints, is a bimodule map,
and is the orthogonal projection for the trace norm. -/

/-! Positivity of the constructed expectation. The negative spectral part
is an actual subalgebra test operator; tracial orthogonality eliminates it. -/

/-! The constructed expectation satisfies the Schwarz inequality and is
contractive in operator norm. -/

/-! Actual nested subalgebras satisfy the expectation tower identity.
The resulting energy identity is the decreasing-subfactor step of A.1.2. -/

/-! Conditional expectations onto a decreasing sequence of actual
subalgebras converge in L2. This supplies the limiting argument in A.1.2;
it does not construct that source's decreasing subfactors. -/
open Filter
open scoped Topology BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixRefinement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem mapped_reindex_relative (E : MatrixUnitSystem ι N.toStarSubalgebra)
    (e : κ ≃ ι) (f : N.toStarSubalgebra →⋆ₐ[ℂ] M.toStarSubalgebra) :
    ((E.reindex e).map f).relativeVonNeumann=(E.map f).relativeVonNeumann := by
  apply le_antisymm
  · exact (E.map f).relative_antitone _ (E.map_algebra_mono _ (E.reindex_algebra e).ge f)
  · exact ((E.reindex e).map f).relative_antitone _ ((E.reindex e).map_algebra_mono _
      (E.reindex_algebra e).le f)

end MatrixUnitSystem

/-! An actual full matrix algebra of any positive finite size can be
constructed in the relative commutant. No commuting matrix units are assumed. -/

end Generator

end

end OAI
end


