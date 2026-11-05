-- Prove2me | Definitions.Def_KadisonRingroseSupport1
-- name    : KadisonRingroseSupport1
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T14:33:09.307323+00:00
-- url     : https://prove2.me/theorems/20019515-74f1-4994-a428-2776503f9d99
-- title:
--   Bounded Hochschild vanishing: supporting development, part 1
-- statement:
--   Part 1 of the supporting Lean development for the vanishing of higher bounded Hochschild cohomology of von Neumann algebras. It contains the `OAI.Compat` backports for this platform's Lean and Mathlib, and the definitions used by statements of the published child theorems: predual convergence and preadjoints, $2$-norm continuity on balls, walk words, free moments, atomic laws, the Hilbert space maps of the Liouville argument, the finite path tests, and the coboundaries and differential of cochains, in source order, together with the proved lemmas their bodies and instances rely on. No result is assumed.
--
--   **Formalization Note** Definitions of this development carry proof fields and `Classical.choose` terms, so their dependencies are proved here. The code is OpenAI's, carved from `lean/OAI/Analysis` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`. The `private` keyword is removed from declarations kept here so that later files can use them.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_KadisonRingrose

set_option linter.all false

namespace OAI
end OAI
namespace OAI.BoundedHochschild
end OAI.BoundedHochschild
namespace OAI.BoundedHochschild.CentralCorner
end OAI.BoundedHochschild.CentralCorner
namespace OAI.BoundedHochschild.ExpectedEmbedding
end OAI.BoundedHochschild.ExpectedEmbedding
namespace OAI.BoundedHochschild.KadisonRingrose
end OAI.BoundedHochschild.KadisonRingrose
namespace OAI.BoundedHochschild.WeakAlgebra
end OAI.BoundedHochschild.WeakAlgebra
namespace OAI.BoundedHochschild.WeakSubspace
end OAI.BoundedHochschild.WeakSubspace
namespace OAI.FinitePathMain
end OAI.FinitePathMain
namespace OAI.Generator
end OAI.Generator
namespace OAI.Generator.Tracial
end OAI.Generator.Tracial
namespace OAI.HochschildApproximation
end OAI.HochschildApproximation
namespace OAI.HochschildBlockAssembly
end OAI.HochschildBlockAssembly
namespace OAI.HochschildBlockError
end OAI.HochschildBlockError
namespace OAI.HochschildBlockSpan
end OAI.HochschildBlockSpan
namespace OAI.HochschildBlockWords
end OAI.HochschildBlockWords
namespace OAI.HochschildCStarQuotient
end OAI.HochschildCStarQuotient
namespace OAI.HochschildCatalan
end OAI.HochschildCatalan
namespace OAI.HochschildCatalanMoments
end OAI.HochschildCatalanMoments
namespace OAI.HochschildCatalanWords
end OAI.HochschildCatalanWords
namespace OAI.HochschildCentralComparison
end OAI.HochschildCentralComparison
namespace OAI.HochschildCesaro
end OAI.HochschildCesaro
namespace OAI.HochschildCollision
end OAI.HochschildCollision
namespace OAI.HochschildComparison
end OAI.HochschildComparison
namespace OAI.HochschildComparison.Frame
end OAI.HochschildComparison.Frame
namespace OAI.HochschildComparison.PartialIso
end OAI.HochschildComparison.PartialIso
namespace OAI.HochschildComparison.PartialUnitary
end OAI.HochschildComparison.PartialUnitary
namespace OAI.HochschildCorners
end OAI.HochschildCorners
namespace OAI.HochschildDiffuse
end OAI.HochschildDiffuse
namespace OAI.HochschildDixmier
end OAI.HochschildDixmier
namespace OAI.HochschildDomination
end OAI.HochschildDomination
namespace OAI.HochschildDomination.PreHilbert
end OAI.HochschildDomination.PreHilbert
namespace OAI.HochschildFinitePhase
end OAI.HochschildFinitePhase
namespace OAI.HochschildFiniteTests
end OAI.HochschildFiniteTests
namespace OAI.HochschildFirstLetter
end OAI.HochschildFirstLetter
namespace OAI.HochschildFourPoint
end OAI.HochschildFourPoint
namespace OAI.HochschildFourPoint.HochschildPositiveDecomposition
end OAI.HochschildFourPoint.HochschildPositiveDecomposition
namespace OAI.HochschildFreeMoments
end OAI.HochschildFreeMoments
namespace OAI.HochschildFreeSums
end OAI.HochschildFreeSums
namespace OAI.HochschildFreeWords
end OAI.HochschildFreeWords
namespace OAI.HochschildGoodPatterns
end OAI.HochschildGoodPatterns
namespace OAI.HochschildGradedFree
end OAI.HochschildGradedFree
namespace OAI.HochschildIndexedHaagerup
end OAI.HochschildIndexedHaagerup
namespace OAI.HochschildLength
end OAI.HochschildLength
namespace OAI.HochschildLiouville
end OAI.HochschildLiouville
namespace OAI.HochschildMartingale
end OAI.HochschildMartingale
namespace OAI.HochschildMatrixDilation
end OAI.HochschildMatrixDilation
namespace OAI.HochschildMatrixSystems
end OAI.HochschildMatrixSystems
namespace OAI.HochschildMatrixSystems.MatrixSystem
end OAI.HochschildMatrixSystems.MatrixSystem
namespace OAI.HochschildMoments
end OAI.HochschildMoments
namespace OAI.HochschildNewtonPolar
end OAI.HochschildNewtonPolar
namespace OAI.HochschildNormalPart
end OAI.HochschildNormalPart
namespace OAI.HochschildPatching
end OAI.HochschildPatching
namespace OAI.HochschildPatching.ProductTaylor
end OAI.HochschildPatching.ProductTaylor
namespace OAI.HochschildPaths
end OAI.HochschildPaths
namespace OAI.HochschildPolar
end OAI.HochschildPolar
namespace OAI.HochschildPolynomial
end OAI.HochschildPolynomial
namespace OAI.HochschildPositiveDecomposition
end OAI.HochschildPositiveDecomposition
namespace OAI.HochschildProbability
end OAI.HochschildProbability
namespace OAI.HochschildQuantization
end OAI.HochschildQuantization
namespace OAI.HochschildRangeCount
end OAI.HochschildRangeCount
namespace OAI.HochschildRare
end OAI.HochschildRare
namespace OAI.HochschildRigidity
end OAI.HochschildRigidity
namespace OAI.HochschildRootPhase
end OAI.HochschildRootPhase
namespace OAI.HochschildSakai
end OAI.HochschildSakai
namespace OAI.HochschildSplitWord
end OAI.HochschildSplitWord
namespace OAI.HochschildTraceNorm
end OAI.HochschildTraceNorm
namespace OAI.HochschildTracePolynomial
end OAI.HochschildTracePolynomial
namespace OAI.HochschildTransfer
end OAI.HochschildTransfer
namespace OAI.HochschildTypeII
end OAI.HochschildTypeII
namespace OAI.HochschildUltrafilter
end OAI.HochschildUltrafilter
namespace OAI.HochschildUltrapower
end OAI.HochschildUltrapower
namespace OAI.HochschildUnitaryLift
end OAI.HochschildUnitaryLift
namespace OAI.HochschildWalk
end OAI.HochschildWalk
namespace OAI.HochschildWordEval
end OAI.HochschildWordEval
namespace OAI.MissingFinitePaths
end OAI.MissingFinitePaths
namespace OAI.NaimarkZFC
end OAI.NaimarkZFC
namespace OAI.NaimarkZFC.HNNWord
end OAI.NaimarkZFC.HNNWord
namespace OAI.PopaCenter
end OAI.PopaCenter
namespace OAI.PopaCenter.System
end OAI.PopaCenter.System
namespace OAI.PopaCorner
end OAI.PopaCorner
namespace OAI.PopaCorners
end OAI.PopaCorners
namespace OAI.PopaCorners.CornerIso
end OAI.PopaCorners.CornerIso
namespace OAI.PopaFinite
end OAI.PopaFinite
namespace OAI.PopaMatrices
end OAI.PopaMatrices
namespace OAI.PopaMatrices.System
end OAI.PopaMatrices.System
namespace OAI.PopaPatching
end OAI.PopaPatching
namespace OAI.PopaPatching.Rep
end OAI.PopaPatching.Rep
namespace OAI.PopaQuantization
end OAI.PopaQuantization
namespace OAI.PopaSeparable
end OAI.PopaSeparable
namespace OAI.PopaTypeII
end OAI.PopaTypeII
namespace OAI.TracialUltrapower
end OAI.TracialUltrapower
namespace OAI.WeakPureInfiniteness
end OAI.WeakPureInfiniteness

section
namespace OAI

theorem ite_eq_left {α : Sort*} {c : Prop} {_ : Decidable c} {a b : α} (h : c) : ite c a b = a := if_pos h
theorem ite_eq_right {α : Sort*} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) : ite c a b = b := if_neg h
theorem dite_eq_left {α : Sort*} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort*} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h

theorem Compat.map_le_map_iff {F A B : Type*}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
    (f : F) (hf : Function.Injective f) {x y : A} : f x ≤ f y ↔ x ≤ y := by
  let φ : A →⋆ₙₐ[ℂ] B := NonUnitalStarAlgHomClass.toNonUnitalStarAlgHom f
  have hφ : Function.Injective φ := hf
  change φ x ≤ φ y ↔ x ≤ y
  refine ⟨?_, (OrderHomClass.mono φ ·)⟩
  rw [← sub_nonneg, ← sub_nonneg (a := y), ← map_sub φ]
  simp_rw [nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts, QuasispectrumRestricts.nnreal_iff]
  rintro ⟨h₁, h₂⟩
  have h_sa : IsSelfAdjoint (y - x) := hφ (by rw [map_star]; exact h₁)
  refine ⟨h_sa, ?_⟩
  have key : ∀ a : A, IsSelfAdjoint a → quasispectrum ℝ (φ a) = quasispectrum ℝ a := by
    intro a ha
    have h := (ha.inr ℂ).map_spectrum_real (Unitization.starMap φ) (Unitization.starMap_injective hφ)
    rw [Unitization.starMap_inr] at h
    rw [Unitization.quasispectrum_eq_spectrum_inr' ℝ ℂ (φ a), Unitization.quasispectrum_eq_spectrum_inr' ℝ ℂ a]
    exact h
  rwa [← key _ h_sa]

theorem Compat.norm_le_norm_of_le_of_nonneg {A : Type*}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {a b : A}
    (hab : a ≤ b) (ha : 0 ≤ a := by cfc_tac) : ‖a‖ ≤ ‖b‖ :=
  _root_.CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab

open ComplexOrder in

theorem Compat.norm_map_star_mul_sq_le {A : Type*}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (f : A →ₚ[ℂ] ℂ) (x y : A) :
    ‖f (star x * y)‖ ^ 2 ≤ ‖f (star x * x)‖ * ‖f (star y * y)‖ := by
  have key : ∀ z : ℂ, 0 ≤ z → ‖z‖ = z.re := by
    intro z hz
    have h := Complex.nonneg_iff.mp hz
    have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using h.2.symm)
    conv_lhs => rw [hz']
    rw [Complex.norm_real, Real.norm_of_nonneg h.1]
  have hx : 0 ≤ f (star x * x) := f.map_nonneg (star_mul_self_nonneg x)
  have hy : 0 ≤ f (star y * y) := f.map_nonneg (star_mul_self_nonneg y)
  have h : ‖f (star x * y)‖ ≤ √(f (star x * x)).re * √(f (star y * y)).re :=
    norm_inner_le_norm (𝕜 := ℂ) (f.toPreGNS x) (f.toPreGNS y)
  rw [key _ hx, key _ hy]
  have hxr := (Complex.nonneg_iff.mp hx).1
  have hyr := (Complex.nonneg_iff.mp hy).1
  calc ‖f (star x * y)‖ ^ 2 ≤ (√(f (star x * x)).re * √(f (star y * y)).re) ^ 2 := by gcongr
    _ = _ := by rw [mul_pow, Real.sq_sqrt hxr, Real.sq_sqrt hyr]
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open Filter Topology
namespace BoundedHochschild
variable {M X I : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def PredualTendsto (a : I → M) (l : Filter I) (b : M) : Prop :=
  ∀ z : X, Tendsto (fun i => e.symm (a i) z) l (𝓝 (e.symm b z))

lemma predual_tendsto_unique {a : I → M} {l : Filter I} [l.NeBot] {b c : M}
    (hb : PredualTendsto e a l b) (hc : PredualTendsto e a l c) : b = c := by
  apply e.symm.injective
  ext z
  exact tendsto_nhds_unique (hb z) (hc z)

lemma predual_tendsto_const (m : M) (l : Filter I) :
    PredualTendsto e (fun _ => m) l m := fun _ => tendsto_const_nhds

lemma predual_tendsto_add {a b : I → M} {l : Filter I} {c d : M}
    (ha : PredualTendsto e a l c) (hb : PredualTendsto e b l d) :
    PredualTendsto e (fun i => a i+b i) l (c+d) := by
  intro z
  simpa only [map_add,add_apply] using (ha z).add (hb z)

lemma predual_tendsto_smul {a : I → M} {l : Filter I} {b : M}
    (ha : PredualTendsto e a l b) (c : ℂ) :
    PredualTendsto e (fun i => c • a i) l (c • b) := by
  intro z
  simpa only [LinearIsometryEquiv.map_smulₛₗ,smul_apply,smul_eq_mul]
    using (ha z).const_mul (starRingEnd ℂ c)

lemma exists_predual_ultralimit (u : Ultrafilter I) (a : I → M) (C : ℝ)
    (hb : ∀ i, ‖a i‖ ≤ C) :
    ∃ b : M, ‖b‖ ≤ C ∧ PredualTendsto e a u b := by
  let j : I → WeakDual ℂ X := fun i => StrongDual.toWeakDual (e.symm (a i))
  have hmem : (u.map j : Filter (WeakDual ℂ X)) ≤
      𝓟 (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ X) C) := by
    rw [Ultrafilter.coe_map,Filter.map_le_iff_le_comap, Filter.comap_principal]
    apply Filter.le_principal_iff.mpr
    exact Filter.Eventually.of_forall fun i => by
      simpa [j,Metric.mem_closedBall] using hb i
  obtain ⟨b,hb',ht⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual ℂ X) C).ultrafilter_le_nhds (u.map j) hmem
  refine ⟨e (WeakDual.toStrongDual b),?_,?_⟩
  · simpa only [LinearIsometryEquiv.norm_map,Set.mem_preimage,
      Metric.mem_closedBall,dist_zero_right] using hb'
  · intro z
    have hjt : Tendsto j (u : Filter I) (𝓝 b) := by
      simpa only [Ultrafilter.coe_map, Filter.Tendsto] using ht
    have hz := (WeakDual.eval_continuous z).tendsto b |>.comp hjt
    change Tendsto (fun i => e.symm (a i) z) (u : Filter I) (𝓝 (b z)) at hz
    simpa only [LinearIsometryEquiv.symm_apply_apply, WeakDual.toStrongDual_apply] using hz

end BoundedHochschild

open Filter Topology
namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

end BoundedHochschild

open Filter Topology
namespace BoundedHochschild
variable {M X I J : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma predual_tendsto_neg {a : I → M} {l : Filter I} {b : M}
    (h : PredualTendsto e a l b) : PredualTendsto e (fun i => -a i) l (-b) := by
  intro z
  simpa only [map_neg,neg_apply] using (h z).neg

lemma predual_tendsto_sub {a b : I → M} {l : Filter I} {c d : M}
    (ha : PredualTendsto e a l c) (hb : PredualTendsto e b l d) :
    PredualTendsto e (fun i => a i-b i) l (c-d) := by
  simpa only [sub_eq_add_neg] using predual_tendsto_add e ha (predual_tendsto_neg e hb)

lemma predual_norm_le {a : I → M} {l : Filter I} [l.NeBot] {b : M} (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ᶠ i in l, ‖a i‖ ≤ C) (h : PredualTendsto e a l b) : ‖b‖ ≤ C := by
  rw [← e.symm.norm_map b]
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro z
  apply le_of_tendsto (h z).norm
  filter_upwards [ha] with i hi
  calc
    ‖e.symm (a i) z‖ ≤ ‖e.symm (a i)‖ * ‖z‖ := (e.symm (a i)).le_opNorm z
    _ ≤ C * ‖z‖ := mul_le_mul_of_nonneg_right (by simpa using hi) (norm_nonneg _)

def HasPreadjoint (L : M →L[ℂ] M) : Prop :=
  ∀ z : X, ∃ z' : X, ∀ a : M, e.symm (L a) z = e.symm a z'

lemma HasPreadjoint.tendsto {L : M →L[ℂ] M} (hL : HasPreadjoint e L)
    {a : I → M} {l : Filter I} {b : M} (h : PredualTendsto e a l b) :
    PredualTendsto e (fun i => L (a i)) l (L b) := by
  intro z
  obtain ⟨z',hz'⟩ := hL z
  simpa only [hz'] using h z'
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

namespace HochschildRigidity
open Finset

section FourierWindows
variable {L : ℕ} [NeZero L]

end FourierWindows

section TraceHilbertSpace
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ)
lemma preGNS_norm_mul_le (a b : A) :
    ‖τ.toPreGNS (a * b)‖ ≤ ‖a‖ * ‖τ.toPreGNS b‖ := by
  calc
    _ = ‖τ.leftMulMapPreGNS a (τ.toPreGNS b)‖ := rfl
    _ ≤ ‖τ.leftMulMapPreGNS a‖ * ‖τ.toPreGNS b‖ :=
      (τ.leftMulMapPreGNS a).le_opNorm _
    _ ≤ _ := by
      gcongr
      unfold PositiveLinearMap.leftMulMapPreGNS
      exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
lemma preGNS_norm_one (h1 : τ 1 = 1) : ‖τ.toPreGNS 1‖ = 1 := by
  have h := congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS 1))
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul, h1,
    ← Complex.ofReal_pow, Complex.ofReal_re, Complex.one_re] at h
  nlinarith [norm_nonneg (τ.toPreGNS 1)]
lemma preGNS_norm_le (h1 : τ 1 = 1) (a : A) : ‖τ.toPreGNS a‖ ≤ ‖a‖ := by
  simpa only [mul_one, preGNS_norm_one τ h1] using preGNS_norm_mul_le τ a 1

lemma preGNS_norm_eq_zero_iff
    (hf : ∀ a : A, τ (star a * a) = 0 → a = 0) (a : A) :
    ‖τ.toPreGNS a‖ = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply hf
    simpa only [PositiveLinearMap.ofPreGNS_toPreGNS, h, Complex.ofReal_zero,
      zero_pow (by decide : 2 ≠ 0)] using (τ.preGNS_norm_sq (τ.toPreGNS a)).symm
  · rintro rfl
    simp
end TraceHilbertSpace
end HochschildRigidity
end
end OAI
end

section
namespace OAI

noncomputable section

namespace TracialUltrapower
noncomputable section
open Filter
open scoped Topology BoundedContinuousFunction

section Modulus
variable {A E : Type*} [SeminormedAddCommGroup A] [SeminormedAddCommGroup E]

def BallSequential (q : A → E) (R : A → A) : Prop :=
  ∀ x : ℕ → A, (∃ r : ℝ, ∀ j, ‖x j‖ ≤ r) →
    Tendsto (fun j => ‖q (x j)‖) atTop (𝓝 0) →
    Tendsto (fun j => ‖q (R (x j))‖) atTop (𝓝 0)

def BallModulus (q : A → E) (R : A → A) : Prop :=
  ∀ r : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ x : A,
    ‖x‖ ≤ r → ‖q x‖ < δ → ‖q (R x)‖ < ε

end Modulus

section NullSubmodule
variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [SeminormedAddCommGroup E] [NormedSpace ℂ E]
variable (q : A →ₗ[ℂ] E) (ω : Filter ℕ)

end NullSubmodule

section ClosedNullSpace
variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [SeminormedAddCommGroup E] [NormedSpace ℂ E]

end ClosedNullSpace

section UltraSeminorm
variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [SeminormedAddCommGroup E] [NormedSpace ℂ E]
variable (q : A →L[ℂ] E) (ω : Ultrafilter ℕ)

end UltraSeminorm

section TraceIdeal
open scoped ComplexOrder
open HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)

def traceHilbertMap : A →L[ℂ] τ.PreGNS :=
  τ.toPreGNS.toLinearMap.mkContinuous 1 (fun a => by
    change ‖τ.toPreGNS a‖ ≤ 1 * ‖a‖
    rw [one_mul]
    exact preGNS_norm_le τ h1 a)

@[simp] theorem traceHilbertMap_apply (a : A) :
    traceHilbertMap τ h1 a = τ.toPreGNS a := rfl
end TraceIdeal
end
end TracialUltrapower
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
namespace HochschildMartingale

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
variable {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} {f : ℕ → Ω → H}

end HochschildMartingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace HochschildWalk
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (μ : Measure G) [IsProbabilityMeasure μ]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def word {n : ℕ} (ω : Fin n → G) : G := (List.ofFn ω).prod
end HochschildWalk
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open MeasureTheory ProbabilityTheory Filter Topology
namespace HochschildWalk
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (μ : Measure G) [IsProbabilityMeasure μ]

variable {H : Type*} [NormedAddCommGroup H]

end HochschildWalk

open MeasureTheory ProbabilityTheory Filter Topology
namespace HochschildProbability

end HochschildProbability

namespace HochschildWalk
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (μ : Measure G) [IsProbabilityMeasure μ]
variable {H : Type*} [NormedAddCommGroup H]

end HochschildWalk

open Filter Topology
namespace HochschildFiniteTests

end HochschildFiniteTests

open MeasureTheory ProbabilityTheory Filter Topology
namespace HochschildWalk
open HochschildFiniteTests
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (μ : Measure G) [IsProbabilityMeasure μ]
variable {H : Type*} [NormedAddCommGroup H]

def FreeMomentsInProbability (φ : G → ℝ) (time : ℕ → ℕ) : Prop :=
  ∀ r (q : FreeGroup (Fin r)), q ≠ 1 → ∀ δ > 0,
    Tendsto (fun k => (Measure.pi (fun _ : Fin r × Fin (time k) => μ)).real
      {w | δ ≤ φ (FreeGroup.lift (fun i => word (fun j => w (i,j))) q)}) atTop (nhds 0)
end HochschildWalk
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildLiouville
open HochschildRigidity HochschildWalk HochschildFirstLetter TracialUltrapower
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))

def hilbertMap : A →L[ℂ] τ.GNS :=
  UniformSpace.Completion.toComplL.comp (TracialUltrapower.traceHilbertMap τ h1)

@[simp] lemma hilbertMap_norm (a : A) : ‖hilbertMap τ h1 a‖ = ‖τ.toPreGNS a‖ :=
  UniformSpace.Completion.norm_coe _

variable {G : Type*} [Group G]
variable (ρ : G →* unitary A) (R : A →L[ℂ] A)

def algebraD (g : G) : A := R (ρ g : A) * (ρ g⁻¹ : A)
def hilbertD (g : G) : τ.GNS := hilbertMap τ h1 (algebraD ρ R g)
end HochschildLiouville
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity
variable {M X I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

def TraceInPredual : Prop := ∃ z : X, ∀ x : M, τ x = star (e.symm x z)

omit [StarOrderedRing M] in
lemma trace_predual_tendsto (hτ : TraceInPredual e τ)
    {a : I → M} {l : Filter I} {b : M} (h : PredualTendsto e a l b) :
    Tendsto (fun i => τ (a i)) l (𝓝 (τ b)) := by
  obtain ⟨z,hz⟩ := hτ
  simpa only [hz] using (h z).star

lemma preGNS_norm_le_of_predual_tendsto
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hτ : TraceInPredual e τ) {a : I → M} {l : Filter I} [l.NeBot] {b : M}
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ᶠ i in l, ‖τ.toPreGNS (a i)‖ ≤ C)
    (h : PredualTendsto e a l b) : ‖τ.toPreGNS b‖ ≤ C := by
  have ht := trace_predual_tendsto e τ hτ ((hL (star b)).tendsto e h)
  have ht' : Tendsto (fun i => inner ℂ (τ.toPreGNS b) (τ.toPreGNS (a i))) l
      (𝓝 (inner ℂ (τ.toPreGNS b) (τ.toPreGNS b))) := by
    simpa only [PositiveLinearMap.preGNS_inner_def,PositiveLinearMap.ofPreGNS_toPreGNS,ContinuousLinearMap.mul_apply'] using ht
  have hb : ‖inner ℂ (τ.toPreGNS b) (τ.toPreGNS b)‖ ≤ ‖τ.toPreGNS b‖ * C := by
    apply le_of_tendsto ht'.norm
    filter_upwards [ha] with i hi
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hi (norm_nonneg _))
  simp only [inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg _)] at hb
  nlinarith [norm_nonneg (τ.toPreGNS b)]

end BoundedHochschild

namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity HochschildLiouville TracialUltrapower
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (τ : M →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
  (htr : ∀ a b : M, τ (a*b)=τ (b*a))

include h1 htr

end BoundedHochschild

open MeasureTheory Filter Topology
open scoped ENNReal
namespace HochschildWalk
variable {G : Type*} [MeasurableSpace G] [MeasurableSingletonClass G]

def atomicLaw (p : ℕ → ℝ) (a : ℕ → G) : Measure G :=
  Measure.sum (fun j => ENNReal.ofReal (p j) • Measure.dirac (a j))
end HochschildWalk
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity
variable {M X I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

theorem exists_bounded_preGNS_limit
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hτ : TraceInPredual e τ) {a : ℕ → M} (C : ℝ) (ha : ∀ i, ‖a i‖ ≤ C)
    (hc : CauchySeq (fun i => τ.toPreGNS (a i))) :
    ∃ b : M, ‖b‖ ≤ C ∧ Tendsto (fun i => ‖τ.toPreGNS (a i-b)‖) atTop (𝓝 0) := by
  let u : Ultrafilter ℕ := Ultrafilter.of atTop
  have hu : (u : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨b,hb,ht⟩ := exists_predual_ultralimit e u a C ha
  refine ⟨b,hb,?_⟩
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hc (ε/2) (half_pos hε)
  refine ⟨N,fun n hn => ?_⟩
  have hsmall : ∀ᶠ m in (u : Filter ℕ), ‖τ.toPreGNS (a n-a m)‖ ≤ ε/2 := by
    apply hu
    filter_upwards [eventually_ge_atTop N] with m hm
    simpa only [map_sub,← dist_eq_norm] using (hN n hn m hm).le
  have hbound := preGNS_norm_le_of_predual_tendsto e τ hL hτ (ε/2) (half_pos hε).le
    hsmall (predual_tendsto_sub e (predual_tendsto_const e (a n) (u : Filter ℕ)) ht)
  simpa only [Real.dist_eq,sub_zero,abs_norm] using hbound.trans_lt (half_lt_self hε)

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity
variable {M I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (τ : M →ₚ[ℂ] ℂ)

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (Star.star a*a)=0 → a=0)

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (Star.star a*a)=0 → a=0)

structure IsSupportProjection (a p : M) : Prop where
  proj : IsStarProjection p
  left : p*a=a
  right : a*p=a
  annihilate : ∀ x : M, a*x=0 → p*x=0
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open MeasureTheory Filter Topology
open scoped ComplexOrder
namespace HochschildRare
open HochschildWalk
variable {M : Type*} [CStarAlgebra M]

def signedValue {A : Type*} (v : A → unitary M) (a : A × Bool) : unitary M :=
  if a.2 then v a.1 else (v a.1)⁻¹

def pathValue {A : Type*} {r n : ℕ} (v : A → unitary M)
    (w : Fin r × Fin n → A × Bool) (i : Fin r) : unitary M :=
  word (fun j => signedValue v (w (i,j)))

def FinitePathTests [PartialOrder M] (τ : M →ₚ[ℂ] ℂ) : Prop :=
  ∀ (C D T : Type) [Fintype C] [Fintype D] [Fintype T],
    Nonempty D → ∀ (v : C → unitary M) (r n : T → ℕ)
      (w : ∀ t, Fin (r t) × Fin (n t) → (C ⊕ D) × Bool)
      (q : ∀ t, FreeGroup (Fin (r t))),
    (∀ t, q t ≠ 1) →
    (∀ t, ∃ (s : Fin (r t) → Fin (n t)) (a : Fin (r t) → D),
      (∀ i, (w t (i,s i)).1 = Sum.inr (a i)) ∧
      (∀ i z, (w t z).1 = Sum.inr (a i) → z=(i,s i))) →
    ∀ ε : ℝ, 0 < ε → ∃ u : D → unitary M,
      ∀ t, ‖τ (FreeGroup.lift (pathValue (Sum.elim v u) (w t)) (q t) : M)‖ < ε
end HochschildRare
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open Filter Topology
namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

end BoundedHochschild

namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

def leftCoboundary {n : ℕ} (f : Cochain M n) : Cochain M (n+1) :=
  (((ContinuousLinearMap.compContinuousMultilinearMapL ℂ (fun _ : Fin n => M) M M).flip f).comp
    (ContinuousLinearMap.mul ℂ M)).uncurryLeft

@[simp] lemma leftCoboundary_apply {n : ℕ} (f : Cochain M n) (v : Fin (n+1) → M) :
    leftCoboundary f v = v 0 * f (fun i => v i.succ) := rfl

def rightCoboundary {n : ℕ} (f : Cochain M n) : Cochain M (n+1) :=
  ((ContinuousLinearMap.mul ℂ M).compContinuousMultilinearMap f).uncurryRight

@[simp] lemma rightCoboundary_apply {n : ℕ} (f : Cochain M n) (v : Fin (n+1) → M) :
    rightCoboundary f v = f (fun i => v i.castSucc) * v (Fin.last n) := rfl

def middleCoboundary {n : ℕ} (f : Cochain M (n+1)) (j : Fin (n+1)) : Cochain M (n+2) :=
  (((ContinuousMultilinearMap.curryMidEquiv ℂ (fun _ : Fin (n+1) => M) M j).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((ContinuousLinearMap.compL ℂ M M (Cochain M n) (f.curryMid j)).comp
      (ContinuousLinearMap.mul ℂ M))).uncurryMid j.castSucc

@[simp] lemma middleCoboundary_apply {n : ℕ} (f : Cochain M (n+1)) (j : Fin (n+1))
    (v : Fin (n+2) → M) : middleCoboundary f j v = f (mergeInputs v j) := by
  change f (j.insertNth (v j.castSucc * v (j.castSucc.succAbove j))
    (fun i => v (j.castSucc.succAbove (j.succAbove i)))) = _
  congr 1
  apply (Fin.insertNth_eq_iff).mpr
  constructor
  · simp [mergeInputs, Fin.succAbove_of_le_castSucc]
  · funext i
    change v (j.castSucc.succAbove (j.succAbove i)) = mergeInputs v j (j.succAbove i)
    by_cases h : i.castSucc < j
    · rw [Fin.succAbove_of_castSucc_lt _ _ h]
      have h' : i.castSucc.castSucc < j.castSucc := by simpa using h
      rw [Fin.succAbove_of_castSucc_lt _ _ h']
      simp [mergeInputs, h]
    · have hj : j ≤ i.castSucc := le_of_not_gt h
      rw [Fin.succAbove_of_le_castSucc _ _ hj]
      have h' : j.castSucc ≤ i.succ.castSucc := by
        simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] at *
        omega
      rw [Fin.succAbove_of_le_castSucc _ _ h']
      have hh : ¬i.succ < j := by
        simp only [Fin.lt_def, Fin.val_succ, Fin.le_def, Fin.val_castSucc] at *
        omega
      have hn : i.succ ≠ j := by
        intro he; have he' := congrArg Fin.val he
        simp only [Fin.val_succ] at he'
        have := j.isLt
        simp only [Fin.le_def, Fin.val_castSucc] at hj
        omega
      simp [mergeInputs, hh, hn]

def differential : {n : ℕ} → Cochain M n → Cochain M (n+1)
  | 0, f => leftCoboundary f - rightCoboundary f
  | n+1, f => leftCoboundary f + ∑ j : Fin (n+1), ((-1:ℂ)^(j.val+1)) • middleCoboundary f j +
      ((-1:ℂ)^(n+1+1)) • rightCoboundary f

@[simp] theorem differential_apply {n : ℕ} (f : Cochain M n) (v : Fin (n+1) → M) :
    differential f v = differentialValue f v := by
  cases n with
  | zero => simp [differential, differentialValue, sub_eq_add_neg]
  | succ n => simp only [differential, differentialValue, add_apply, sum_apply, smul_apply,
      leftCoboundary_apply, rightCoboundary_apply, middleCoboundary_apply]
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open Filter Topology
open scoped ComplexOrder
namespace HochschildSakai
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma imag_square (a : M) (t : ℝ) :
    star (1+Complex.I • (t • a))*(1+Complex.I • (t • a))=
      1+t • (Complex.I • (a-star a))+(t^2) • (star a*a) := by
  have ht : star t=t := rfl
  have hi : star Complex.I = -Complex.I := by simp
  simp only [star_add,star_one,star_smul,ht,hi]
  simp only [add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,mul_smul_comm]
  simp only [smul_add,smul_sub,neg_smul]
  match_scalars <;> ring_nf
  all_goals simp

omit [PartialOrder M] [StarOrderedRing M] in
lemma norm_one_bound : ‖(1:M)‖ ≤ 1 := by
  nontriviality M
  simp

omit [PartialOrder M] [StarOrderedRing M] in
lemma norm_imag_add_sq (a : M) (ha : IsSelfAdjoint a) (t : ℝ) :
    ‖(1:M)+Complex.I • (t • a)‖^2 ≤ 1+t^2*‖a‖^2 := by
  rw [pow_two,← CStarRing.norm_star_mul_self,imag_square,ha.star_eq,sub_self,
    smul_zero,smul_zero,add_zero]
  calc
    ‖(1:M)+t^2 • (a*a)‖ ≤ ‖(1:M)‖+‖t^2 • (a*a)‖ := norm_add_le _ _
    _ ≤ 1+t^2*‖a‖^2 := by
      rw [norm_smul,Real.norm_of_nonneg (sq_nonneg _),ha.norm_mul_self]
      exact add_le_add (norm_one_bound (M := M)) le_rfl

lemma imag_linear_bound (a : M) (C : ℝ)
    (h : ∀ t : ℝ, ‖(1:M)+Complex.I • (t • a)‖^2 ≤ 1+t^2*C) (t : ℝ) :
    t • (Complex.I • (a-star a)) ≤ algebraMap ℝ M (t^2*C) := by
  have hn := CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := (1:M)+Complex.I • (t • a))
  have hh := hn.trans (algebraMap_mono M (h t))
  rw [imag_square] at hh
  have hp : 0 ≤ t^2 • (star a*a) := smul_nonneg (sq_nonneg _) (star_mul_self_nonneg a)
  have h := (le_add_of_nonneg_right hp).trans hh
  simpa only [map_add,map_one,add_le_add_iff_left] using h

theorem isSelfAdjoint_of_norm_imag_add (a : M) (C : ℝ)
    (h : ∀ t : ℝ, ‖(1:M)+Complex.I • (t • a)‖^2 ≤ 1+t^2*C) :
    IsSelfAdjoint a := by
  let b := Complex.I • (a-star a)
  have hb (t : ℝ) (ht : 0 < t) : b ≤ algebraMap ℝ M (t*C) := by
    have hh := imag_linear_bound a C h t
    have heq : algebraMap ℝ M (t^2*C)=t • algebraMap ℝ M (t*C) := by
      rw [Algebra.smul_def,← map_mul]
      congr 1
      ring
    rw [heq] at hh
    exact (smul_le_smul_iff_of_pos_left ht).mp hh
  have hnb (t : ℝ) (ht : 0 < t) : -b ≤ algebraMap ℝ M (t*C) := by
    have hh := imag_linear_bound a C h (-t)
    have heq : algebraMap ℝ M ((-t)^2*C)=t • algebraMap ℝ M (t*C) := by
      rw [Algebra.smul_def,← map_mul]
      congr 1
      ring
    rw [heq,neg_smul,← smul_neg] at hh
    exact (smul_le_smul_iff_of_pos_left ht).mp hh
  have hb0 : b ≤ 0 := by
    have ht : Tendsto (fun t : ℝ => algebraMap ℝ M (t*C)) (𝓝[>] 0) (𝓝 0) := by
      have ht : Tendsto (fun t : ℝ => t*C) (𝓝[>] 0) (𝓝 (0*C)) :=
        ((continuousAt_id (x := (0:ℝ))).mul_const C).tendsto.mono_left inf_le_left
      simpa only [zero_mul,map_zero,Function.comp_def] using
        (continuous_algebraMap ℝ M).continuousAt.tendsto.comp ht
    exact ge_of_tendsto ht (by filter_upwards [self_mem_nhdsWithin] with t ht using hb t ht)
  have hn0 : -b ≤ 0 := by
    have ht : Tendsto (fun t : ℝ => algebraMap ℝ M (t*C)) (𝓝[>] 0) (𝓝 0) := by
      have ht : Tendsto (fun t : ℝ => t*C) (𝓝[>] 0) (𝓝 (0*C)) :=
        ((continuousAt_id (x := (0:ℝ))).mul_const C).tendsto.mono_left inf_le_left
      simpa only [zero_mul,map_zero,Function.comp_def] using
        (continuous_algebraMap ℝ M).continuousAt.tendsto.comp ht
    exact ge_of_tendsto ht (by filter_upwards [self_mem_nhdsWithin] with t ht using hnb t ht)
  have hz : b=0 := le_antisymm hb0 (neg_nonpos.mp hn0)
  have ha : a-star a=0 := (smul_eq_zero.mp hz).resolve_left Complex.I_ne_zero
  exact (sub_eq_zero.mp ha).symm

end HochschildSakai

open Filter Topology
namespace HochschildSakai
open BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

theorem isSelfAdjoint_of_predual_tendsto {a : I → M} {l : Filter I} [l.NeBot]
    {b : M} (C : ℝ) (_hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C)
    (hsa : ∀ i, IsSelfAdjoint (a i)) (ht : PredualTendsto e a l b) :
    IsSelfAdjoint b := by
  let := CStarAlgebra.spectralOrder M
  let := CStarAlgebra.spectralOrderedRing M
  apply isSelfAdjoint_of_norm_imag_add b (C^2)
  intro t
  have htC : 0 ≤ 1+t^2*C^2 := by positivity
  have hnorm (i : I) : ‖(1:M)+Complex.I • (t • a i)‖ ≤ Real.sqrt (1+t^2*C^2) := by
    apply (Real.le_sqrt (norm_nonneg _) htC).mpr
    exact (norm_imag_add_sq (a i) (hsa i) t).trans (by
      gcongr
      exact ha i)
  have htw : PredualTendsto e (fun i => (1:M)+Complex.I • (t • a i)) l
      ((1:M)+Complex.I • (t • b)) := by
    simp only [← Complex.coe_smul]
    exact predual_tendsto_add e (predual_tendsto_const e 1 l)
      (predual_tendsto_smul e (predual_tendsto_smul e ht (t:ℂ)) Complex.I)
  exact (Real.le_sqrt (norm_nonneg _) htC).mp
    (predual_norm_le e _ (Real.sqrt_nonneg _) (Eventually.of_forall hnorm) htw)

lemma star_eq_of_sum_sub_selfAdjoint (a b : M)
    (hadd : IsSelfAdjoint (a+b)) (hsub : IsSelfAdjoint (Complex.I • (a-b))) :
    b=star a := by
  have h1 := hadd.star_eq
  have h2 := hsub.star_eq
  simp only [star_add] at h1
  have h3 : -(star a-star b)=a-b := by
    apply (smul_right_injective M Complex.I_ne_zero)
    simpa only [star_smul,star_sub,Complex.star_def,map_sub,map_id,Complex.conj_I,
      neg_smul,smul_neg] using h2
  have h4 : (2:ℂ) • (b-star a)=0 := by
    have h3' : star b-star a=a-b := by simpa only [neg_sub] using h3
    calc
      (2:ℂ) • (b-star a) = (a+b-(star a+star b)) - (a-b-(star b-star a)) := by module
      _ = 0 := by rw [h1,h3']; simp
  exact sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_left (by norm_num))

theorem predual_tendsto_star_bounded {a : I → M} {l : Filter I}
    {b : M} (C : ℝ) (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C)
    (ht : PredualTendsto e a l b) :
    PredualTendsto e (fun i => star (a i)) l (star b) := by
  intro z
  rw [Filter.tendsto_iff_ultrafilter]
  intro u hu
  have htu : PredualTendsto e a (u : Filter I) b := fun x => (ht x).mono_left hu
  obtain ⟨c,_,hc⟩ := exists_predual_ultralimit e u (fun i => star (a i)) C
    (fun i => by simpa only [norm_star] using ha i)
  have hadd : IsSelfAdjoint (b+c) :=
    isSelfAdjoint_of_predual_tendsto e (2*C) (by positivity)
      (fun i => (norm_add_le (a i) (star (a i))).trans (by
        simpa only [norm_star,two_mul] using add_le_add (ha i) (ha i)))
      (fun i => by simp only [IsSelfAdjoint,star_add,star_star,add_comm])
      (predual_tendsto_add e htu hc)
  have hsub : IsSelfAdjoint (Complex.I • (b-c)) :=
    isSelfAdjoint_of_predual_tendsto e (2*C) (by positivity)
      (fun i => by
        rw [norm_smul,Complex.norm_I,one_mul]
        exact (norm_sub_le (a i) (star (a i))).trans (by
          simpa only [norm_star,two_mul] using add_le_add (ha i) (ha i)))
      (fun i => by simp [IsSelfAdjoint,star_smul,Complex.conj_I,sub_eq_add_neg,add_comm])
      (predual_tendsto_smul e (predual_tendsto_sub e htu hc) Complex.I)
  have hc' := star_eq_of_sum_sub_selfAdjoint b c hadd hsub
  exact hc' ▸ hc z

end HochschildSakai

open Filter Topology
namespace HochschildSakai
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem mem_predual_of_bounded_weak_continuity [CompleteSpace X]
    (F : StrongDual ℂ (StrongDual ℂ X))
    (hF : ∀ (a : Finset X → StrongDual ℂ X),
      (∀ s, ‖a s‖ ≤ 1) →
      (∀ x, Tendsto (fun s => a s x) atTop (𝓝 0)) →
      Tendsto (fun s => F (a s)) atTop (𝓝 0)) :
    ∃ x : X, ∀ f : StrongDual ℂ X, F f=f x := by
  classical
  let : NormedAddCommGroup (StrongDual ℂ X) := inferInstance
  let : NormedSpace ℂ (StrongDual ℂ X) := inferInstance
  let : NormedAddCommGroup (StrongDual ℂ (StrongDual ℂ X)) := inferInstance
  let j := NormedSpace.inclusionInDoubleDual ℂ X
  let j₀ : X →ₗ[ℂ] Module.Dual ℂ (StrongDual ℂ X) :=
    (ContinuousLinearMap.coeLM ℂ).comp j.toLinearMap
  have hsmall (ε : ℝ) (hε : 0 < ε) : ∃ s : Finset X,
      ∀ f : StrongDual ℂ X, ‖f‖ ≤ 1 → (∀ x ∈ s, f x=0) → ‖F f‖ ≤ ε := by
    by_contra h
    push Not at h
    choose a ha haz hFa using h
    have ha0 (x : X) : Tendsto (fun s => a s x) atTop (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      apply Filter.eventually_atTop.mpr
      refine ⟨{x},fun s hs => ?_⟩
      exact (haz s x (hs (Finset.mem_singleton_self x))).symm
    have hh := (hF a ha ha0).norm.eventually (gt_mem_nhds (show ‖(0:ℂ)‖ < ε by simpa only [norm_zero] using hε))
    obtain ⟨s,hs⟩ := hh.exists
    exact (not_lt_of_ge (le_of_lt hs)) (hFa s)
  have happ (ε : ℝ) (hε : 0 < ε) : ∃ x : X, ‖F-j x‖ ≤ ε := by
    obtain ⟨s,hs⟩ := hsmall ε hε
    let W : Submodule ℂ (Module.Dual ℂ (StrongDual ℂ X)) :=
      Submodule.span ℂ (j₀ '' (s : Set X))
    have hfin : (j₀ '' (s : Set X)).Finite := s.finite_toSet.image j₀
    let : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ hfin
    let K : Submodule ℂ (StrongDual ℂ X) := W.dualCoannihilator
    let : NormedAddCommGroup K := inferInstance
    let : NormedSpace ℂ K := inferInstance
    let FK : StrongDual ℂ K := F.comp K.subtypeL
    have hFK : ‖FK‖ ≤ ε := by
      apply ContinuousLinearMap.opNorm_le_of_unit_norm hε.le
      intro f hf
      apply hs f hf.le
      intro x hx
      have hmem : j₀ x ∈ W := Submodule.subset_span ⟨x,hx,rfl⟩
      exact ((Submodule.mem_dualCoannihilator (Φ := W) f.val).mp f.property) (j₀ x) hmem
    obtain ⟨G,hG,hGn⟩ := _root_.exists_extension_norm_eq K FK
    have hmem : (F-G).toLinearMap ∈ W := by
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W)]
      apply (Submodule.mem_dualAnnihilator _).mpr
      intro f hf
      change F f-G f=0
      exact sub_eq_zero.mpr (hG ⟨f,hf⟩).symm
    have hle : W ≤ LinearMap.range j₀ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨x,_,rfl⟩
      exact ⟨x,rfl⟩
    obtain ⟨x,hx⟩ := hle hmem
    have hx' : j x=F-G := by
      ext f
      exact LinearMap.congr_fun hx f
    refine ⟨x,?_⟩
    rw [hx']
    calc
      ‖F-(F-G)‖ = ‖G‖ := congrArg norm (sub_sub_cancel F G)
      _ = ‖FK‖ := hGn
      _ ≤ ε := hFK

  have hclosed : IsClosed (Set.range j) :=
    (NormedSpace.inclusionInDoubleDualLi ℂ (E := X)).isometry.isClosedEmbedding.isClosed_range
  have hmem : F ∈ closure (Set.range j) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨x,hx⟩ := happ (ε/2) (half_pos hε)
    refine ⟨j x,⟨x,rfl⟩,?_⟩
    rw [dist_eq_norm]
    exact hx.trans_lt (half_lt_self hε)
  obtain ⟨x,hx⟩ := hclosed.closure_eq ▸ hmem
  exact ⟨x,fun f => by rw [← hx]; rfl⟩

end HochschildSakai

open Filter Topology
namespace HochschildSakai
open BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

theorem exists_star_predual_vector (z : X) :
    ∃ w : X, ∀ a : M, e.symm (star a) z = star (e.symm a w) := by
  let : NormedAddCommGroup (StrongDual ℂ X) := inferInstance
  let : NormedSpace ℂ (StrongDual ℂ X) := inferInstance
  let L : StrongDual ℂ X →ₗ[ℂ] ℂ :=
    { toFun := fun f => star (e.symm (star (e f)) z)
      map_add' := by intro f g; simp
      map_smul' := by intro r f; simp [map_smulₛₗ] }
  have hb (f : StrongDual ℂ X) : ‖L f‖ ≤ ‖z‖ * ‖f‖ := by
    change ‖star (e.symm (star (e f)) z)‖ ≤ _
    rw [norm_star,mul_comm]
    simpa only [e.symm.norm_map,norm_star,e.norm_map] using
      (e.symm (star (e f))).le_opNorm z
  let F := L.mkContinuous ‖z‖ hb
  have hF (a : Finset X → StrongDual ℂ X) (ha : ∀ s, ‖a s‖ ≤ 1)
      (hta : ∀ x, Tendsto (fun s => a s x) atTop (𝓝 0)) :
      Tendsto (fun s => F (a s)) atTop (𝓝 0) := by
    have ht : PredualTendsto e (fun s => e (a s)) atTop 0 := by
      intro x
      simpa using hta x
    have hs := predual_tendsto_star_bounded e 1 zero_le_one
      (fun s => by simpa only [e.norm_map] using ha s) ht
    simpa [F,L] using (hs z).star
  obtain ⟨w,hw⟩ := mem_predual_of_bounded_weak_continuity F hF
  refine ⟨w,fun a => ?_⟩
  have hh := congrArg star (hw (e.symm a))
  simpa [F,L] using hh

theorem predual_tendsto_star {a : I → M} {l : Filter I} {b : M}
    (ha : PredualTendsto e a l b) :
    PredualTendsto e (fun i => star (a i)) l (star b) := by
  intro z
  obtain ⟨w,hw⟩ := exists_star_predual_vector e z
  simpa only [hw] using (ha w).star
end HochschildSakai
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open Filter Topology
namespace HochschildSakai
open BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

theorem nonneg_of_bounded_predual_limit {a : I → M} {l : Filter I} [l.NeBot]
    {b : M} (C : ℝ) (hC : 0 ≤ C) (ha : ∀ᶠ i in l, ‖a i‖ ≤ C)
    (hp : ∀ᶠ i in l, 0 ≤ a i) (ht : PredualTendsto e a l b) : 0 ≤ b := by
  have hs : PredualTendsto e (fun i => star (a i)) l b := by
    intro z
    apply (ht z).congr'
    filter_upwards [hp] with i hi
    rw [(IsSelfAdjoint.of_nonneg hi).star_eq]
  have hb : IsSelfAdjoint b := predual_tendsto_unique e (predual_tendsto_star e ht) hs
  let c := algebraMap ℝ M C
  have hc : 0 ≤ c := algebraMap_nonneg M hC
  have hac : ∀ᶠ i in l, ‖c-a i‖ ≤ C := by
    filter_upwards [ha,hp] with i hn hi
    have hai : a i ≤ c := (CStarAlgebra.norm_le_iff_le_algebraMap (a i) hC hi).mp hn
    exact (CStarAlgebra.norm_le_iff_le_algebraMap (c-a i) hC (sub_nonneg.mpr hai)).mpr
      (sub_le_self _ hi)
  have hbc : ‖c-b‖ ≤ C := predual_norm_le e C hC hac
    (predual_tendsto_sub e (predual_tendsto_const e c l) ht)
  have hsa : IsSelfAdjoint (c-b) := (IsSelfAdjoint.of_nonneg hc).sub hb
  have hle : c-b ≤ c := hsa.le_algebraMap_norm_self.trans (algebraMap_mono M hbc)
  exact le_of_add_le_add_left (show c+0 ≤ c+b by
    simpa only [add_zero] using sub_le_iff_le_add.mp hle)

theorem le_of_bounded_predual_limit {a : I → M} {l : Filter I} [l.NeBot]
    {b c : M} (C : ℝ) (hC : 0 ≤ C) (ha : ∀ᶠ i in l, ‖a i‖ ≤ C)
    (hp : ∀ᶠ i in l, a i ≤ c) (ht : PredualTendsto e a l b) : b ≤ c := by
  apply sub_nonneg.mp
  apply nonneg_of_bounded_predual_limit e (‖c‖+C) (add_nonneg (norm_nonneg _) hC)
    ?_ (hp.mono fun _ hi => sub_nonneg.mpr hi)
    (predual_tendsto_sub e (predual_tendsto_const e c l) ht)
  filter_upwards [ha] with i hi
  exact (norm_sub_le c (a i)).trans (by gcongr)

theorem ge_of_bounded_predual_limit {a : I → M} {l : Filter I} [l.NeBot]
    {b c : M} (C : ℝ) (hC : 0 ≤ C) (ha : ∀ᶠ i in l, ‖a i‖ ≤ C)
    (hp : ∀ᶠ i in l, c ≤ a i) (ht : PredualTendsto e a l b) : c ≤ b := by
  apply sub_nonneg.mp
  apply nonneg_of_bounded_predual_limit e (C+‖c‖) (add_nonneg hC (norm_nonneg _))
    ?_ (hp.mono fun _ hi => sub_nonneg.mpr hi)
    (predual_tendsto_sub e ht (predual_tendsto_const e c l))
  filter_upwards [ha] with i hi
  exact (norm_sub_le (a i) c).trans (by gcongr)

theorem exists_monotone_predual_limit [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (a : I → M) (hm : Monotone a) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) :
    ∃ b : M, ‖b‖ ≤ C ∧ IsLUB (Set.range a) b ∧ PredualTendsto e a atTop b := by
  let u : Ultrafilter I := Ultrafilter.of atTop
  have hu : (u : Filter I) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨b,hb,ht⟩ := exists_predual_ultralimit e u a C ha
  have hlu (v : Ultrafilter I) (hv : (v : Filter I) ≤ atTop) (c : M)
      (hc : PredualTendsto e a (v : Filter I) c) : IsLUB (Set.range a) c := by
    constructor
    · rintro _ ⟨i,rfl⟩
      apply ge_of_bounded_predual_limit e C hC (Eventually.of_forall ha) ?_ hc
      exact hv ((eventually_ge_atTop i).mono fun j hj => hm hj)
    · intro d hd
      apply le_of_bounded_predual_limit e C hC (Eventually.of_forall ha) ?_ hc
      exact Eventually.of_forall fun i => hd (Set.mem_range_self i)
  have hbL := hlu u hu b ht
  refine ⟨b,hb,hbL,fun z => ?_⟩
  rw [Filter.tendsto_iff_ultrafilter]
  intro v hv
  obtain ⟨c,_hc,hct⟩ := exists_predual_ultralimit e v a C ha
  have hcb : c=b := (hlu v hv c hct).unique hbL
  exact hcb ▸ hct z
end HochschildSakai
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open Filter Topology
open scoped ComplexOrder
namespace HochschildUltrapower
open BoundedHochschild
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (hω : (ω : Filter ℕ) ≤ atTop)
include hω

end HochschildUltrapower

open Filter Topology
namespace HochschildSakai
open BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma norm_add_smul_sq_of_star_mul_zero (x y : M) (hxy : star y*x=0) (t : ℝ) :
    ‖y+t • x‖^2 ≤ ‖y‖^2+t^2*‖x‖^2 := by
  have hyx : star x*y=0 := by simpa only [star_mul,star_star,star_zero] using congrArg star hxy
  rw [pow_two, ← CStarRing.norm_star_mul_self]
  have he : star (y+t • x)*(y+t • x)=star y*y+(t^2) • (star x*x) := by
    simp only [star_add,star_smul,star_trivial,add_mul,mul_add,mul_smul_comm,
      smul_mul_assoc,smul_smul,hxy,hyx,smul_zero,add_zero,zero_add,pow_two]
  rw [he]
  apply (norm_add_le _ _).trans_eq
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg t),
    CStarRing.norm_star_mul_self,CStarRing.norm_star_mul_self]
  ring

theorem projection_range_limit (p : M) (hp : IsStarProjection p)
    {a : I → M} {l : Filter I} [l.NeBot] {b : M}
    (C : ℝ) (_hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C)
    (hpa : ∀ i, p*a i=a i) (ht : PredualTendsto e a l b) : p*b=b := by
  let q := 1-p
  have hq : IsStarProjection q := hp.one_sub
  let y := q*b
  have hqy : q*y=y := by dsimp [y]; rw [← mul_assoc,hq.isIdempotentElem.eq]
  have hy (i : I) : star y*a i=0 := by
    have hqa : q*a i=0 := by dsimp [q]; rw [sub_mul,one_mul,hpa i,sub_self]
    dsimp [y]
    rw [star_mul,hq.isSelfAdjoint.star_eq,mul_assoc,hqa,mul_zero]
  have hbound (t : ℝ) : ‖y+t • b‖^2 ≤ ‖y‖^2+t^2*C^2 := by
    have hpos : 0 ≤ ‖y‖^2+t^2*C^2 := by positivity
    have hn (i : I) : ‖y+t • a i‖ ≤ Real.sqrt (‖y‖^2+t^2*C^2) := by
      apply (Real.le_sqrt (norm_nonneg _) hpos).mpr
      exact (norm_add_smul_sq_of_star_mul_zero (a i) y (hy i) t).trans (by gcongr; exact ha i)
    have ht' : PredualTendsto e (fun i => y+t • a i) l (y+t • b) := by
      simp only [← Complex.coe_smul]
      exact predual_tendsto_add e (predual_tendsto_const e y l) (predual_tendsto_smul e ht (t:ℂ))
    exact (Real.le_sqrt (norm_nonneg _) hpos).mp
      (predual_norm_le e _ (Real.sqrt_nonneg _) (Eventually.of_forall hn) ht')
  have hzero : ‖y‖=0 := by
    by_contra hy0
    have hyp : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy0)
    let t : ℝ := ‖y‖^2/(C^2+1)
    have ht0 : 0 < t := div_pos (sq_pos_of_pos hyp) (by positivity)
    have hlow : (1+t)*‖y‖ ≤ ‖y+t • b‖ := by
      calc
        (1+t)*‖y‖ = ‖(1+t) • y‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity)]
        _ = ‖q*(y+t • b)‖ := by rw [mul_add,mul_smul_comm,hqy]; congr 1; module
        _ ≤ ‖q‖*‖y+t • b‖ := norm_mul_le _ _
        _ ≤ 1*‖y+t • b‖ := by gcongr; exact hq.norm_le
        _ = ‖y+t • b‖ := one_mul _
    have hs := hbound t
    have hs' : ((1+t)*‖y‖)^2 ≤ ‖y+t • b‖^2 := by gcongr
    have hte : t*(C^2+1)=‖y‖^2 := by dsimp [t]; field_simp
    nlinarith [sq_nonneg (t*‖y‖)]
  have hqb : q*b=0 := norm_eq_zero.mp hzero
  dsimp [q] at hqb
  simpa only [sub_mul,one_mul,sub_eq_zero,eq_comm] using hqb

theorem predual_tendsto_projection_mul_bounded (p : M) (hp : IsStarProjection p)
    {a : I → M} {l : Filter I} {b : M}
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C)
    (ht : PredualTendsto e a l b) :
    PredualTendsto e (fun i => p*a i) l (p*b) := by
  intro z
  rw [Filter.tendsto_iff_ultrafilter]
  intro u hu
  have htu : PredualTendsto e a (u : Filter I) b := fun x => (ht x).mono_left hu
  have hpa (i : I) : ‖p*a i‖ ≤ C :=
    (norm_mul_le _ _).trans (by simpa using (mul_le_mul hp.norm_le (ha i) (norm_nonneg _) zero_le_one))
  obtain ⟨c,_,hc⟩ := exists_predual_ultralimit e u (fun i => p*a i) C hpa
  have hpc : p*c=c := projection_range_limit e p hp C hC hpa
    (fun i => by rw [← mul_assoc,hp.isIdempotentElem.eq]) hc
  have hq : IsStarProjection (1-p) := hp.one_sub
  have hqa (i : I) : ‖(1-p)*a i‖ ≤ C :=
    (norm_mul_le _ _).trans (by simpa using (mul_le_mul hq.norm_le (ha i) (norm_nonneg _) zero_le_one))
  have hqt : PredualTendsto e (fun i => (1-p)*a i) (u : Filter I) (b-c) := by
    simpa only [sub_mul,one_mul] using predual_tendsto_sub e htu hc
  have hqc := projection_range_limit e (1-p) hq C hC hqa
    (fun i => by rw [← mul_assoc,hq.isIdempotentElem.eq]) hqt
  have hcb : c=p*b := by
    rw [sub_mul,one_mul,mul_sub,hpc] at hqc
    have hh : p*b-c=0 := sub_eq_self.mp hqc
    exact (sub_eq_zero.mp hh).symm
  exact hcb ▸ hc z

theorem projection_mul_hasPreadjoint [CompleteSpace X] (p : M)
    (hp : IsStarProjection p) : HasPreadjoint e (ContinuousLinearMap.mul ℂ M p) := by
  intro z
  let : NormedAddCommGroup (StrongDual ℂ X) := inferInstance
  let : NormedSpace ℂ (StrongDual ℂ X) := inferInstance
  let L : StrongDual ℂ X →ₗ[ℂ] ℂ :=
    { toFun := fun f => e.symm (p*e f) z
      map_add' := by intro f g; simp [mul_add]
      map_smul' := by intro r f; simp [map_smulₛₗ] }
  have hb (f : StrongDual ℂ X) : ‖L f‖ ≤ (‖p‖*‖z‖)*‖f‖ := by
    change ‖e.symm (p*e f) z‖ ≤ _
    calc
      _ ≤ ‖e.symm (p*e f)‖*‖z‖ := (e.symm (p*e f)).le_opNorm z
      _ = ‖p*e f‖*‖z‖ := by rw [e.symm.norm_map]
      _ ≤ (‖p‖*‖e f‖)*‖z‖ := by gcongr; exact norm_mul_le _ _
      _ = (‖p‖*‖z‖)*‖f‖ := by rw [e.norm_map]; ring
  let F := L.mkContinuous (‖p‖*‖z‖) hb
  have hF (a : Finset X → StrongDual ℂ X) (ha : ∀ s, ‖a s‖ ≤ 1)
      (hta : ∀ x, Tendsto (fun s => a s x) atTop (𝓝 0)) :
      Tendsto (fun s => F (a s)) atTop (𝓝 0) := by
    have ht : PredualTendsto e (fun s => e (a s)) atTop 0 := by
      intro x
      simpa using hta x
    have hh := predual_tendsto_projection_mul_bounded e p hp 1 zero_le_one
      (fun s => by simpa only [e.norm_map] using ha s) ht
    simpa [F,L] using hh z
  obtain ⟨w,hw⟩ := mem_predual_of_bounded_weak_continuity F hF
  refine ⟨w,fun a => ?_⟩
  simpa [F,L] using hw (e.symm a)

end HochschildSakai

open Filter Topology

namespace HochschildSakai
open BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma isGLB_of_antitone_predual_limit [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (a : I → M) (hm : Antitone a) {p : M} (ht : PredualTendsto e a atTop p)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) : IsGLB (Set.range a) p := by
  constructor
  · rintro _ ⟨i,rfl⟩
    apply le_of_bounded_predual_limit e C hC (Eventually.of_forall ha) ?_ ht
    exact (eventually_ge_atTop i).mono fun j hj => hm hj
  · intro d hd
    apply ge_of_bounded_predual_limit e C hC (Eventually.of_forall ha) ?_ ht
    exact Eventually.of_forall fun i => hd (Set.mem_range_self i)

lemma exists_antitone_predual_limit [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (a : I → M) (hm : Antitone a) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) :
    ∃ p : M, ‖p‖ ≤ C ∧ IsGLB (Set.range a) p ∧ PredualTendsto e a atTop p := by
  obtain ⟨b,hb,_,ht⟩ := exists_monotone_predual_limit e (fun i => -a i)
    (fun i j hij => neg_le_neg (hm hij)) C hC
    (fun i => by simpa only [norm_neg] using ha i)
  have ht' : PredualTendsto e a atTop (-b) := by
    simpa only [neg_neg] using predual_tendsto_neg e ht
  exact ⟨-b,by simpa only [norm_neg] using hb,
    isGLB_of_antitone_predual_limit e a hm ht' C hC ha,ht'⟩

lemma isGLB_star_conjugate {a : I → M} {p : M} (hp : IsGLB (Set.range a) p)
    (u : Mˣ) : IsGLB (Set.range (fun i => star (u:M)*a i*u)) (star (u:M)*p*u) := by
  constructor
  · rintro _ ⟨i,rfl⟩
    exact star_left_conjugate_le_conjugate (hp.1 (Set.mem_range_self i)) _
  · intro d hd
    have hx : star (↑(u⁻¹):M)*d*(↑(u⁻¹):M) ≤ p := by
      apply hp.2
      rintro _ ⟨i,rfl⟩
      have hh := star_left_conjugate_le_conjugate (hd (Set.mem_range_self i)) (↑(u⁻¹):M)
      simpa [← mul_assoc,← star_mul] using hh
    have hh := star_left_conjugate_le_conjugate hx (u:M)
    simpa [← mul_assoc,← star_mul] using hh

lemma le_of_positive_fixed (a b : M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hba : b*a=a) : a ≤ b := by
  have hab : a*b=a := by
    simpa only [star_mul,(IsSelfAdjoint.of_nonneg ha0).star_eq,
      (IsSelfAdjoint.of_nonneg hb0).star_eq] using congrArg star hba
  have hcomm : Commute b (1-a) := by
    change b*(1-a)=(1-a)*b
    rw [mul_sub,sub_mul,mul_one,one_mul,hba,hab]
  have hh := hcomm.mul_nonneg hb0 (sub_nonneg.mpr ha1)
  simpa only [mul_sub,mul_one,hba,sub_nonneg] using hh

theorem power_limit_fixed (b p : M) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hp : IsGLB (Set.range (fun n : ℕ => b^n)) p)
    (ht : PredualTendsto e (fun n : ℕ => b^n) atTop p) : b*p=p := by
  have hbsa := IsSelfAdjoint.of_nonneg hb0
  have hnorm (n : ℕ) : ‖b^n‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (CStarAlgebra.pow_nonneg hb0 n)).mpr
      (by simpa only [pow_zero] using CStarAlgebra.pow_antitone hb0 hb1 (Nat.zero_le n))
  have ht1 : PredualTendsto e (fun n : ℕ => b^(n+1)) atTop p :=
    fun z => (ht z).comp (tendsto_add_atTop_nat 1)
  have ht2 : PredualTendsto e (fun n : ℕ => b^(n+2)) atTop p :=
    fun z => (ht z).comp (tendsto_add_atTop_nat 2)
  have hconj (t : ℝ) (ht0 : 0 ≤ t) :
      (1+t • b)*p*(1+t • b)=(1+t)^2 • p := by
    let c : M := 1+t • b
    have hc0 : 1 ≤ c := le_add_of_nonneg_right (smul_nonneg ht0 hb0)
    have hcu : IsUnit c := CStarAlgebra.isUnit_of_le 1 hc0
    obtain ⟨u,hu⟩ := hcu
    have hcsa : IsSelfAdjoint c := (IsSelfAdjoint.of_nonneg (zero_le_one.trans hc0))
    have hgl : IsGLB (Set.range (fun n : ℕ => c*b^n*c)) (c*p*c) := by
      simpa only [hu,hcsa.star_eq] using isGLB_star_conjugate hp u
    have heq (n : ℕ) : c*b^n*c = b^n+(2*t) • b^(n+1)+(t^2) • b^(n+2) := by
      dsimp [c]
      rw [show n+2=(n+1)+1 by omega,pow_succ,pow_succ]
      simp only [add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,mul_smul_comm,
        ← pow_succ',← pow_succ]
      module
    have htc : PredualTendsto e (fun n : ℕ => c*b^n*c) atTop ((1+t)^2 • p) := by
      have hh := predual_tendsto_add e
        (predual_tendsto_add e ht (predual_tendsto_smul e ht1 ((2*t:ℝ):ℂ)))
        (predual_tendsto_smul e ht2 ((t^2:ℝ):ℂ))
      simp only [Complex.coe_smul] at hh
      have he : p+(2*t) • p+t^2 • p=(1+t)^2 • p := by module
      simpa only [heq,he] using hh
    have hant : Antitone (fun n : ℕ => c*b^n*c) := by
      intro n m hnm
      simpa only [hcsa.star_eq] using
        star_left_conjugate_le_conjugate (CStarAlgebra.pow_antitone hb0 hb1 hnm) c
    have hbound (n : ℕ) : ‖c*b^n*c‖ ≤ ‖c‖^2 := by
      calc
        ‖c*b^n*c‖ ≤ (‖c‖*‖b^n‖)*‖c‖ := (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
        _ ≤ (‖c‖*1)*‖c‖ := by gcongr; exact hnorm n
        _ = ‖c‖^2 := by ring
    exact hgl.unique (isGLB_of_antitone_predual_limit e _ hant htc _ (sq_nonneg _) hbound)
  have h1 := hconj 1 zero_le_one
  have h2 := hconj 2 (by norm_num)
  have hppos : 0 ≤ p := hp.2 (by rintro _ ⟨n,rfl⟩; exact CStarAlgebra.pow_nonneg hb0 n)
  have hpsa := IsSelfAdjoint.of_nonneg hppos
  have hbp : b*p*b=p := by
    have hid : (1+(2:ℝ) • b)*p*(1+(2:ℝ) • b) - (2:ℝ) • ((1+b)*p*(1+b)) =
        (2:ℝ) • (b*p*b) - p := by
      simp only [add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,mul_smul_comm]
      module
    have h1' : (1+b)*p*(1+b)=(4:ℝ) • p := by norm_num at h1 ⊢; exact h1
    have h2' : (1+(2:ℝ) • b)*p*(1+(2:ℝ) • b)=(9:ℝ) • p := by norm_num at h2 ⊢; exact h2
    rw [h1',h2'] at hid
    have hh : (2:ℝ) • (b*p*b-p)=0 := by
      calc
        _ = ((2:ℝ) • (b*p*b)-p)-((9:ℝ) • p-(2:ℝ) • ((4:ℝ) • p)) := by module
        _ = 0 := sub_eq_zero.mpr hid.symm
    exact sub_eq_zero.mp ((smul_eq_zero.mp hh).resolve_left (by norm_num))
  have hab : b*p+p*b=(2:ℝ) • p := by
    have h1' : (1+b)*p*(1+b)=(4:ℝ) • p := by norm_num at h1 ⊢; exact h1
    have he : (1+b)*p*(1+b)=p+(b*p+p*b)+b*p*b := by noncomm_ring
    rw [he,hbp] at h1'
    calc
      b*p+p*b = (p+(b*p+p*b)+p)-(2:ℝ) • p := by module
      _ = (4:ℝ) • p-(2:ℝ) • p := by rw [h1']
      _ = (2:ℝ) • p := by module
  have hz : (1-b)*p*(1-b)=0 := by
    have he : (1-b)*p*(1-b)=p-(b*p+p*b)+b*p*b := by noncomm_ring
    rw [he,hbp,hab]
    module
  let s := CFC.sqrt p
  have hs : s*s=p := CFC.sqrt_mul_sqrt_self p
  have hssa : star s=s := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg p)).star_eq
  have hx : s*(1-b)=0 := by
    apply (CStarRing.star_mul_self_eq_zero_iff _).mp
    simpa only [star_mul,hssa,star_sub,star_one,hbsa.star_eq,mul_assoc,← hs] using hz
  have hpx : p*(1-b)=0 := by rw [← hs,mul_assoc,hx,mul_zero]
  have hxp : (1-b)*p=0 := by
    simpa only [star_mul,star_sub,star_one,hbsa.star_eq,hpsa.star_eq,star_zero]
      using congrArg star hpx
  simpa only [sub_mul,one_mul,sub_eq_zero,eq_comm] using hxp

theorem exists_power_projection (b : M) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∃ p : M, IsStarProjection p ∧ PredualTendsto e (fun n : ℕ => b^n) atTop p ∧
      b*p=p ∧ ∀ x : M, b*x=x → p*x=x := by
  have hbn (n : ℕ) : ‖b^n‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (CStarAlgebra.pow_nonneg hb0 n)).mpr
      (by simpa only [pow_zero] using CStarAlgebra.pow_antitone hb0 hb1 (Nat.zero_le n))
  obtain ⟨p,_,hp,ht⟩ := exists_antitone_predual_limit e (fun n : ℕ => b^n)
    (CStarAlgebra.pow_antitone hb0 hb1) 1 zero_le_one hbn
  have hp0 : 0 ≤ p := hp.2 (by rintro _ ⟨n,rfl⟩; exact CStarAlgebra.pow_nonneg hb0 n)
  have hp1 : p ≤ 1 := by simpa only [pow_zero] using hp.1 (Set.mem_range_self 0)
  have hbp := power_limit_fixed e b p hb0 hb1 hp ht
  have hpsq : p*p ≤ p := by
    simpa only [pow_two,pow_one] using CStarAlgebra.pow_antitone hp0 hp1 (by omega : 1 ≤ 2)
  let q : M := p+(p-p*p)
  have hq0 : 0 ≤ q := add_nonneg hp0 (sub_nonneg.mpr hpsq)
  have hq1 : q ≤ 1 := by
    have hneg : 0 ≤ (1-p)*(1-p) := (IsSelfAdjoint.of_nonneg (sub_nonneg.mpr hp1)).mul_self_nonneg
    have he : q=1-(1-p)*(1-p) := by dsimp [q]; noncomm_ring
    rw [he]
    exact sub_le_self _ hneg
  have hbq : b*q=q := by
    dsimp [q]
    rw [mul_add,mul_sub,← mul_assoc,hbp]
  have hpowq (n : ℕ) : b^n*q=q := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ',mul_assoc,ih,hbq]
  have hqle : q ≤ p := hp.2 (by
    rintro _ ⟨n,rfl⟩
    exact le_of_positive_fixed q _ hq0 hq1 (CStarAlgebra.pow_nonneg hb0 n) (hpowq n))
  have hpsq' : p ≤ p*p := sub_nonpos.mp (by
    simpa [q,add_assoc,add_comm,add_left_comm] using add_le_add_left hqle (-p))
  have hproj : IsStarProjection p := ⟨le_antisymm hpsq hpsq',(IsSelfAdjoint.of_nonneg hp0)⟩
  refine ⟨p,hproj,ht,hbp,?_⟩
  intro x hx
  let a : M := x*star x
  let r : ℝ := ‖a‖+1
  have hr : 0 < r := by dsimp [r]; positivity
  have ha0 : 0 ≤ a := mul_star_self_nonneg x
  have hca0 : 0 ≤ r⁻¹ • a := smul_nonneg (inv_nonneg.mpr hr.le) ha0
  have hcan : ‖r⁻¹ • a‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    exact (inv_mul_le_one₀ hr).mpr (by dsimp [r]; linarith)
  have hca1 : r⁻¹ • a ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hca0).mp hcan
  have hba : b*(r⁻¹ • a)=r⁻¹ • a := by dsimp [a]; rw [mul_smul_comm,← mul_assoc,hx]
  have hbna (n : ℕ) : b^n*(r⁻¹ • a)=r⁻¹ • a := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ',mul_assoc,ih,hba]
  have hcap : r⁻¹ • a ≤ p := hp.2 (by
    rintro _ ⟨n,rfl⟩
    exact le_of_positive_fixed _ _ hca0 hca1 (CStarAlgebra.pow_nonneg hb0 n) (hbna n))
  have hpa : p*a=a := by
    have hh := congrArg (fun z : M => r • z)
      (hproj.mul_right_and_mul_left_of_nonneg_of_le hca0 hcap).2
    simpa only [mul_smul_comm,smul_smul,mul_inv_cancel₀ hr.ne',one_smul] using hh
  have hzero : (1-p)*x=0 := by
    apply (CStarRing.mul_star_self_eq_zero_iff _).mp
    rw [star_mul,star_sub,star_one,hproj.isSelfAdjoint.star_eq,← mul_assoc,
      mul_assoc (1-p) x (star x)]
    change ((1-p)*a)*(1-p)=0
    rw [sub_mul,one_mul,hpa,sub_self,zero_mul]
  simpa only [sub_mul,one_mul,sub_eq_zero,eq_comm] using hzero

lemma exists_support_contraction (a : M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ p : M, IsSupportProjection a p ∧
      PredualTendsto e (fun n : ℕ => 1-(1-a)^n) atTop p := by
  obtain ⟨q,hq,ht,hbq,hqx⟩ := exists_power_projection e (1-a)
    (sub_nonneg.mpr ha1) (sub_le_self _ ha0)
  have haq : a*q=0 := by
    have hh := hbq
    rw [sub_mul,one_mul] at hh
    exact sub_eq_self.mp hh
  have hqa : q*a=0 := by
    simpa only [star_mul,hq.isSelfAdjoint.star_eq,(IsSelfAdjoint.of_nonneg ha0).star_eq,star_zero]
      using congrArg Star.star haq
  refine ⟨1-q,⟨hq.one_sub,?_,?_,?_⟩,?_⟩
  · simp only [sub_mul,one_mul,hqa,sub_zero]
  · simp only [mul_sub,mul_one,haq,sub_zero]
  · intro x hx
    have hbx : (1-a)*x=x := by simp only [sub_mul,one_mul,hx,sub_zero]
    simp only [sub_mul,one_mul,hqx x hbx,sub_self]
  · exact predual_tendsto_sub e (predual_tendsto_const e 1 (atTop : Filter ℕ)) ht

include e in

theorem exists_support_projection (a : M) (ha : 0 ≤ a) :
    ∃ p : M, IsSupportProjection a p := by
  let r : ℝ := ‖a‖+1
  have hr : 0 < r := by dsimp [r]; positivity
  have hi : 0 < r⁻¹ := inv_pos.mpr hr
  have hn : ‖r⁻¹ • a‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hi]
    exact (inv_mul_le_one₀ hr).mpr (by dsimp [r]; linarith)
  have hsa : 0 ≤ r⁻¹ • a := smul_nonneg hi.le ha
  obtain ⟨p,hp,_⟩ := exists_support_contraction e (r⁻¹ • a) hsa
    ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hsa).mp hn)
  refine ⟨p,hp.proj,?_,?_,?_⟩
  · have hh := congrArg (fun z : M => r • z) hp.left
    simpa only [mul_smul_comm,smul_smul,mul_inv_cancel₀ hr.ne',one_smul] using hh
  · have hh := congrArg (fun z : M => r • z) hp.right
    simpa only [smul_mul_assoc,smul_smul,mul_inv_cancel₀ hr.ne',one_smul] using hh
  · intro x hx
    apply hp.annihilate x
    simp only [smul_mul_assoc,hx,smul_zero]

include e in

theorem exists_dyadic_projection (a : M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ p : M, IsStarProjection p ∧ 0 ≤ (2:ℝ) • a-p ∧ (2:ℝ) • a-p ≤ 1 := by
  let b : M := a-(1/2:ℝ) • (1:M)
  let c : M := b⁺
  let d : M := b⁻
  have hbsa : IsSelfAdjoint b := (IsSelfAdjoint.of_nonneg ha0).sub
    (IsSelfAdjoint.of_nonneg (smul_nonneg (by norm_num : (0:ℝ) ≤ 1/2) zero_le_one))
  have hb : c-d=b := CFC.posPart_sub_negPart b hbsa
  have hc0 : 0 ≤ c := CFC.posPart_nonneg b
  have hd0 : 0 ≤ d := CFC.negPart_nonneg b
  obtain ⟨p,hp⟩ := exists_support_projection e c hc0
  have hpd : p*d=0 := hp.annihilate d (CFC.posPart_mul_negPart b)
  have hdp : d*p=0 := by
    simpa only [star_mul,(IsSelfAdjoint.of_nonneg hd0).star_eq,
      hp.proj.isSelfAdjoint.star_eq,star_zero] using congrArg star hpd
  have hcp : b*p=c := by rw [← hb,sub_mul,hp.right,hdp,sub_zero]
  have hpc : p*b=c := by rw [← hb,mul_sub,hp.left,hpd,sub_zero]
  have hac : Commute a p := by
    change a*p=p*a
    have hh := hcp.trans hpc.symm
    dsimp [b] at hh
    simpa only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,
      sub_left_inj] using hh
  have har : 0 ≤ a*(1-p) :=
    (show Commute a (1-p) from (Commute.one_right a).sub_right hac).mul_nonneg ha0
      (sub_nonneg.mpr hp.proj.le_one)
  have hal : 0 ≤ (1-a)*p :=
    ((Commute.one_left p).sub_left hac).mul_nonneg (sub_nonneg.mpr ha1) hp.proj.nonneg
  have hpa : a*p=c+(1/2:ℝ) • p := by
    dsimp [b] at hcp
    rw [sub_mul,smul_mul_assoc,one_mul] at hcp
    exact sub_eq_iff_eq_add.mp hcp
  have hlow : 0 ≤ a-(1/2:ℝ) • p := by
    have he : a-(1/2:ℝ) • p=c+a*(1-p) := by
      rw [mul_sub,mul_one,hpa]
      module
    rw [he]
    exact add_nonneg hc0 har
  have hhigh : 0 ≤ (1/2:ℝ) • (1:M)-(a-(1/2:ℝ) • p) := by
    have he : (1/2:ℝ) • (1:M)-(a-(1/2:ℝ) • p)=(1-a)*p+d := by
      rw [sub_mul,one_mul,hpa]
      have haa : a=c-d+(1/2:ℝ) • (1:M) := by
        exact (sub_eq_iff_eq_add.mp hb.symm)
      conv_lhs => rw [haa]
      module
    rw [he]
    exact add_nonneg hal hd0
  refine ⟨p,hp.proj,?_,?_⟩
  · have hh := smul_nonneg (by norm_num : (0:ℝ) ≤ 2) hlow
    convert hh using 1; module
  · apply sub_nonneg.mp
    have hh := smul_nonneg (by norm_num : (0:ℝ) ≤ 2) hhigh
    convert hh using 1; module

include e in

theorem dual_zero_of_projection_zero (F : StrongDual ℂ M)
    (hF : ∀ p : M, IsStarProjection p → F p=0) : F=0 := by
  have hbound : ∀ n : ℕ, ∀ a : M, 0 ≤ a → a ≤ 1 → ‖F a‖ ≤ (1/2:ℝ)^n * ‖F‖ := by
    intro n
    induction n with
    | zero =>
      intro a ha0 ha1
      simpa only [pow_zero,one_mul] using (F.le_opNorm a).trans
        (mul_le_of_le_one_right (norm_nonneg _)
          ((CStarAlgebra.norm_le_one_iff_of_nonneg _ ha0).mpr ha1))
    | succ n ih =>
      intro a ha0 ha1
      obtain ⟨p,hp,h0,h1⟩ := exists_dyadic_projection e a ha0 ha1
      have hh := ih ((2:ℝ) • a-p) h0 h1
      have he : F ((2:ℝ) • a-p)=(2:ℝ) • F a := by
        simp only [map_sub, ← Complex.coe_smul, map_smul, hF p hp, sub_zero]
      rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
      rw [pow_succ]
      nlinarith
  have hz (a : M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : F a=0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    have ht : Tendsto (fun n : ℕ => (1/2:ℝ)^n * ‖F‖) atTop (𝓝 0) := by
      simpa only [zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
          (by norm_num : (1/2:ℝ)<1)).mul_const ‖F‖
    exact ge_of_tendsto ht (Eventually.of_forall fun n => hbound n a ha0 ha1)
  have hpos (a : M) (ha : 0 ≤ a) : F a=0 := by
    let r : ℝ := ‖a‖+1
    have hr : 0 < r := by dsimp [r]; positivity
    have hc0 : 0 ≤ r⁻¹ • a := smul_nonneg (inv_nonneg.mpr hr.le) ha
    have hcn : ‖r⁻¹ • a‖ ≤ 1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
      exact (inv_mul_le_one₀ hr).mpr (by dsimp [r]; linarith)
    have hh := hz (r⁻¹ • a) hc0 ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hc0).mp hcn)
    simp only [← Complex.coe_smul, map_smul] at hh
    exact (smul_eq_zero.mp hh).resolve_left (by exact_mod_cast inv_ne_zero hr.ne')
  have hker : (⊤ : Submodule ℂ M) ≤ F.ker := by
    rw [← CStarAlgebra.span_nonneg]
    exact Submodule.span_le.mpr hpos
  ext a
  exact hker (Submodule.mem_top)

include e in

theorem projection_span_dense :
    (Submodule.span ℂ {p : M | IsStarProjection p}).topologicalClosure=⊤ := by
  let S := (Submodule.span ℂ {p : M | IsStarProjection p}).topologicalClosure
  let : IsClosed (S : Set M) := Submodule.isClosed_topologicalClosure _
  apply top_unique
  intro a _
  change a ∈ S
  apply (Submodule.Quotient.mk_eq_zero S).mp
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ)
  intro F
  have hzero : F.comp S.mkQL=0 := dual_zero_of_projection_zero e (F.comp S.mkQL) (by
    intro p hp
    have hm : p ∈ S := (Submodule.le_topologicalClosure _)
      (Submodule.subset_span hp)
    have hh : (Submodule.Quotient.mk (p := S) p : M ⧸ S)=0 :=
      (Submodule.Quotient.mk_eq_zero S).mpr hm
    change F (Submodule.Quotient.mk p)=0
    rw [hh,map_zero])
  exact congrArg (fun G : StrongDual ℂ M => G a) hzero
end HochschildSakai
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open Filter Topology
namespace HochschildSakai
open BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def leftMatrixFunctional (z : X) (b : M) : StrongDual ℂ (StrongDual ℂ X) :=
  let L : StrongDual ℂ X →ₗ[ℂ] ℂ :=
    { toFun := fun f => e.symm (star b*e f) z
      map_add' := by intro f g; simp [mul_add]
      map_smul' := by intro r f; simp [map_smulₛₗ] }
  L.mkContinuous (‖b‖*‖z‖) (by
    intro f
    change ‖e.symm (star b*e f) z‖ ≤ _
    calc
      _ ≤ ‖e.symm (star b*e f)‖*‖z‖ := (e.symm (star b*e f)).le_opNorm z
      _ = ‖star b*e f‖*‖z‖ := by rw [e.symm.norm_map]
      _ ≤ (‖star b‖*‖e f‖)*‖z‖ := by gcongr; exact norm_mul_le _ _
      _ = (‖b‖*‖z‖)*‖f‖ := by rw [norm_star,e.norm_map]; ring)

lemma leftMatrixFunctional_apply (z : X) (b : M) (f : StrongDual ℂ X) :
    leftMatrixFunctional e z b f=e.symm (star b*e f) z := rfl

lemma leftMatrixFunctional_norm (z : X) (b : M) :
    ‖leftMatrixFunctional e z b‖ ≤ ‖z‖*‖b‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg z) (norm_nonneg b))
  intro f
  rw [leftMatrixFunctional_apply]
  calc
    _ ≤ ‖e.symm (star b*e f)‖*‖z‖ := (e.symm (star b*e f)).le_opNorm z
    _ = ‖star b*e f‖*‖z‖ := by rw [e.symm.norm_map]
    _ ≤ (‖star b‖*‖e f‖)*‖z‖ := by gcongr; exact norm_mul_le _ _
    _ = (‖z‖*‖b‖)*‖f‖ := by rw [norm_star,e.norm_map]; ring

def starLeftMatrixMap (z : X) : M →L[ℂ] StrongDual ℂ (StrongDual ℂ X) := by
  let : NormedAddCommGroup (StrongDual ℂ X) := inferInstance
  let : NormedSpace ℂ (StrongDual ℂ X) := inferInstance
  let : NormedAddCommGroup (StrongDual ℂ (StrongDual ℂ X)) := inferInstance
  let : NormedSpace ℂ (StrongDual ℂ (StrongDual ℂ X)) := inferInstance
  let K : M →ₗ[ℂ] StrongDual ℂ (StrongDual ℂ X) :=
    { toFun := leftMatrixFunctional e z
      map_add' := by
        intro b c
        ext f
        simp only [leftMatrixFunctional_apply,star_add,add_mul,map_add,
          add_apply]
      map_smul' := by
        intro r b
        ext f
        simp only [leftMatrixFunctional_apply,star_smul,smul_mul_assoc,map_smulₛₗ,
          smul_apply,RingHom.id_apply,starRingEnd_apply,
          star_star] }
  exact K.mkContinuous ‖z‖ (leftMatrixFunctional_norm e z)

variable [PartialOrder M] [StarOrderedRing M] [CompleteSpace X]

theorem mul_hasPreadjoint (a : M) : HasPreadjoint e (ContinuousLinearMap.mul ℂ M a) := by
  intro z
  let : NormedAddCommGroup (StrongDual ℂ X) := inferInstance
  let : NormedSpace ℂ (StrongDual ℂ X) := inferInstance
  let : NormedAddCommGroup (StrongDual ℂ (StrongDual ℂ X)) := inferInstance
  let : NormedSpace ℂ (StrongDual ℂ (StrongDual ℂ X)) := inferInstance
  let K := starLeftMatrixMap e z
  let J := NormedSpace.inclusionInDoubleDual ℂ X
  let S := (LinearMap.range J.toLinearMap).comap K.toLinearMap
  have hc : IsClosed (S : Set M) := by
    change IsClosed (K ⁻¹' Set.range J)
    apply IsClosed.preimage (f := K) K.continuous
    exact (NormedSpace.inclusionInDoubleDualLi ℂ (E := X)).isometry.isClosedEmbedding.isClosed_range
  have hspan : Submodule.span ℂ {p : M | IsStarProjection p} ≤ S := by
    apply Submodule.span_le.mpr
    intro p hp
    obtain ⟨w,hw⟩ := projection_mul_hasPreadjoint e p hp z
    refine ⟨w,?_⟩
    ext f
    change f w=e.symm (star p*e f) z
    rw [hp.isSelfAdjoint.star_eq]
    simpa using (hw (e f)).symm
  have htop : (⊤ : Submodule ℂ M) ≤ S := by
    rw [← projection_span_dense e]
    exact Submodule.topologicalClosure_minimal _ hspan hc
  obtain ⟨w,hw⟩ := htop (show star a ∈ (⊤ : Submodule ℂ M) from Submodule.mem_top)
  refine ⟨w,fun b => ?_⟩
  have hh := congrArg (fun G : StrongDual ℂ (StrongDual ℂ X) => G (e.symm b)) hw
  change e.symm b w=e.symm (star (star a)*e (e.symm b)) z at hh
  simpa using hh.symm

theorem mul_right_hasPreadjoint (a : M) :
    HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a) := by
  intro z
  obtain ⟨w,hw⟩ := exists_star_predual_vector e z
  obtain ⟨v,hv⟩ := mul_hasPreadjoint e (star a) w
  obtain ⟨u,hu⟩ := exists_star_predual_vector e v
  refine ⟨u,fun b => ?_⟩
  have hh := hw (star a*star b)
  simp only [star_mul,star_star] at hh
  have hvb : e.symm (star a*star b) w=e.symm (star b) v := by
    simpa using hv (star b)
  rw [hvb,hu b,star_star] at hh
  simpa using hh

end HochschildSakai

open Filter Topology
namespace HochschildSakai
open BoundedHochschild
variable {M X : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

theorem abstract_multiplication_normal :
    (∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a)) ∧
    (∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a)) := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  exact ⟨mul_hasPreadjoint e,mul_right_hasPreadjoint e⟩
end HochschildSakai
end
end OAI
end


