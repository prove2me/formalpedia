-- Prove2me | Definitions.Def_OAIQ240Bp009
-- name    : OAIQ240Bp009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:50:30.570992+00:00
-- url     : https://prove2.me/theorems/90362285-4ac9-47ba-9e1e-a983f6b909a0
-- title:
--   Definitions bundle OAIQ240Bp009 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 39 declarations of OpenAI's Lean: 16 definitions and 23 theorems. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupSubtypeAmbientMemSubmoduleRealHMap`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupSubtypeJetAmbientHDivRealOfNatMemSubmoduleCOne`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedSpaceRealSubtypeAmbientMemSubmoduleHMap`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedSpaceRealSubtypeJetAmbientHDivOfNatMemSubmoduleCOne`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.Surface`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusBasepoint`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusBranch`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusCoordinate`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.annulusInverse`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.infinityBranch`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.infinityChart`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.infinityFallback`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.infinityInverse`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.normalChartAt`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.realChart`, `OAI.SymplecticBallPacking.Hamiltonian.planarCurl`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`BallPacking_Cauchy_GreenFormula`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Cauchy/GreenFormula.lean), [`BallPacking_Fredholm_NonlinearReduction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/NonlinearReduction.lean), [`BallPacking_Holder_NonlinearCR`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Holder/NonlinearCR.lean), [`BallPacking_Rigidity_RadialForm`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Rigidity/RadialForm.lean), [`BallPacking_Surfaces_QuadricAnnulusDomain`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Surfaces/QuadricAnnulusDomain.lean), [`BallPacking_Surfaces_QuadricCurveManifold`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Surfaces/QuadricCurveManifold.lean).
--
--   **Imports.** It imports the bundles `OAIQ240Bp005`, `OAIQ240Bp006` and `OAIQ240Bp007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ240Bp012` and `OAIQ240Bp013`; the statement `OAI_PackingSufficiencySupport_Hamiltonian_exists_thin_planar_embedding`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ240Bp005
import Definitions.Def_OAIQ240Bp006
import Definitions.Def_OAIQ240Bp007

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_NonlinearCR
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter

namespace HolderCompletion
variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

section Superposition
variable {f : E → F} (hf : BoundedCThree f)
  {b : D → E} (hb : Differentiable ℝ b) {B : ℝ} (hB : 0 ≤ B)
  (hbB : ∀ x, ‖fderiv ℝ b x‖ ≤ B)

local instance instNormedAddCommGroupSubtypeJetAmbientHDivRealOfNatMemSubmoduleCOne : NormedAddCommGroup (COne D E) := inferInstance
local instance instNormedSpaceRealSubtypeJetAmbientHDivOfNatMemSubmoduleCOne : NormedSpace ℝ (COne D E) := inferInstance
local instance instNormedAddCommGroupSubtypeAmbientMemSubmoduleRealHMap : NormedAddCommGroup (HMap D F) := inferInstance
local instance instNormedSpaceRealSubtypeAmbientMemSubmoduleHMap : NormedSpace ℝ (HMap D F) := inferInstance

end Superposition
end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_RadialForm
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SymplecticBallPacking.Hamiltonian
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

def planarCurl (alpha : Plane → Plane →L[ℝ] ℝ) (p : Plane) : ℝ :=
  fderiv ℝ alpha p (1,0) (0,1) - fderiv ℝ alpha p (0,1) (1,0)

 theorem integral_compact_partial_fst {f : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ z, fderiv ℝ f z (1,0))=0 := by
  have hd : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (1,0)) :=
    (hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
  have hdc := hc.fderiv_apply (𝕜 := ℝ) (1,0)
  rw [Measure.volume_eq_prod ℝ ℝ,integral_prod_symm _
    (hd.continuous.integrable_of_hasCompactSupport hdc)]
  have he (y : ℝ) : (∫ x, fderiv ℝ f (x,y) (1,0))=0 := by
    apply integral_eq_zero_of_hasDerivAt_of_integrable
      (f := fun x => f (x,y))
    · intro x
      exact ((hf.differentiable (by simp) (x,y)).hasFDerivAt).comp_hasDerivAt x
        ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))
    · exact (hd.continuous.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.left_slice hdc y)
    · exact (hf.continuous.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.left_slice hc y)
  simp_rw [he]
  exact integral_zero _ _

 theorem integral_compact_partial_snd {f : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (∫ z, fderiv ℝ f z (0,1))=0 := by
  have hd : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (0,1)) :=
    (hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
  have hdc := hc.fderiv_apply (𝕜 := ℝ) (0,1)
  rw [Measure.volume_eq_prod ℝ ℝ,integral_prod _
    (hd.continuous.integrable_of_hasCompactSupport hdc)]
  have he (x : ℝ) : (∫ y, fderiv ℝ f (x,y) (0,1))=0 := by
    apply integral_eq_zero_of_hasDerivAt_of_integrable
      (f := fun y => f (x,y))
    · intro y
      exact ((hf.differentiable (by simp) (x,y)).hasFDerivAt).comp_hasDerivAt y
        ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
    · exact (hd.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
        (HasCompactSupport.right_slice hdc x)
    · exact (hf.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
        (HasCompactSupport.right_slice hc x)
  simp_rw [he]
  exact integral_zero _ _

 theorem compact_planar_stokes {α : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (hc : HasCompactSupport α) :
    (∫ z, fderiv ℝ α z (1,0) (0,1) - fderiv ℝ α z (0,1) (1,0))=0 := by
  have h1 : ContDiff ℝ ∞ (fun z => α z (0,1)) := hα.clm_apply contDiff_const
  have h2 : ContDiff ℝ ∞ (fun z => α z (1,0)) := hα.clm_apply contDiff_const
  have hc1 : HasCompactSupport (fun z => α z (0,1)) := hc.comp_left (g := fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0,1)) rfl
  have hc2 : HasCompactSupport (fun z => α z (1,0)) := hc.comp_left (g := fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1,0)) rfl
  have he1 (z v : ℝ × ℝ) : fderiv ℝ (fun z => α z (0,1)) z v=fderiv ℝ α z v (0,1) := by
    rw [fderiv_clm_apply (hα.differentiable (by simp) z) (differentiableAt_const _)]
    simp only [add_apply,ContinuousLinearMap.comp_apply,fderiv_const_apply,
      zero_apply,map_zero,zero_add,ContinuousLinearMap.flip_apply]
  have he2 (z v : ℝ × ℝ) : fderiv ℝ (fun z => α z (1,0)) z v=fderiv ℝ α z v (1,0) := by
    rw [fderiv_clm_apply (hα.differentiable (by simp) z) (differentiableAt_const _)]
    simp only [add_apply,ContinuousLinearMap.comp_apply,fderiv_const_apply,
      zero_apply,map_zero,zero_add,ContinuousLinearMap.flip_apply]
  have hd1 : ContDiff ℝ ∞ (fun z => fderiv ℝ (fun z => α z (0,1)) z (1,0)) :=
    (h1.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
  have hd2 : ContDiff ℝ ∞ (fun z => fderiv ℝ (fun z => α z (1,0)) z (0,1)) :=
    (h2.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
  simp_rw [← he1,← he2]
  rw [integral_sub
    (hd1.continuous.integrable_of_hasCompactSupport
      (hc1.fderiv_apply (𝕜 := ℝ) (1,0)))
    (hd2.continuous.integrable_of_hasCompactSupport
      (hc2.fderiv_apply (𝕜 := ℝ) (0,1))),
    integral_compact_partial_fst h1 hc1,integral_compact_partial_snd h2 hc2,sub_self]

end SymplecticBallPacking.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Cauchy_GreenFormula
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.instNormedAddCommGroupContinuousLinearMapRealIdComplex_solutions_4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.instNormedSpaceRealContinuousLinearMapIdComplex_solutions_4
omit [CompleteSpace E] in
lemma tailIntegralJet_integrable {g : ℂ → E} (hgC : Continuous g) (hi : Integrable g) (x : ℂ) :
    Integrable (tailIntegralJet g x) := by
  obtain ⟨A,B,hA,hB,hjet,hL⟩ := tailCauchyKernel_bounds
  exact (hi.norm.const_mul A).mono' (tailIntegralJet_continuous hgC x).aestronglyMeasurable
    (Eventually.of_forall fun w => tailIntegralJet_bound hA (fun z => (hjet z).2) g x w)

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_NonlinearReduction
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.OAI.ContinuousLinearMap.FredholmPackage

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter
open HolderCompletion
section
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

variable {D : X →L[ℝ] Y} (pkg : D.FredholmPackage)

variable {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F) {t : ℝ} {x : X}
  (hD : HasFDerivAt (fun y => F (t,y)) D x)

include hD in
omit [CompleteSpace Y] in
lemma parametricEssential_vertical_derivative [CompleteSpace Y] :
    HasFDerivAt (fun y : pkg.decDom.X₁ => parametricEssential pkg F ((t,((domCoords pkg) x).2),y))
      pkg.equiv.toContinuousLinearMap ((domCoords pkg) x).1 := by
  have hi : HasFDerivAt (fun y : pkg.decDom.X₁ => (domCoords pkg).symm (y,((domCoords pkg) x).2))
      ((domCoords pkg).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ pkg.decDom.X₁ pkg.decDom.X₀))
      ((domCoords pkg) x).1 :=
    (domCoords pkg).symm.hasFDerivAt.comp _ (hasFDerivAt_id _ |>.prodMk (hasFDerivAt_const _ _))
  have hx : (domCoords pkg).symm (((domCoords pkg) x).1,((domCoords pkg) x).2)=x :=
    (domCoords pkg).symm_apply_apply x
  have hD' : HasFDerivAt (fun y => F (t,y)) D
      ((domCoords pkg).symm (((domCoords pkg) x).1,((domCoords pkg) x).2)) := hx.symm ▸ hD
  have hd := hD'.comp (((domCoords pkg) x).1) hi
  have ho := ((codCoords pkg).hasFDerivAt.comp _ hd).fst
  have he : (ContinuousLinearMap.fst ℝ pkg.decCodom.X₁ pkg.decCodom.X₀).comp
      ((codCoords pkg).toContinuousLinearMap.comp (D.comp
        ((domCoords pkg).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ pkg.decDom.X₁ pkg.decDom.X₀))))=
        pkg.equiv.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro y
    change ((codCoords pkg) (D ((domCoords pkg).symm (y,0)))).1=pkg.equiv y
    rw [fredholm_original_coords,(domCoords pkg).apply_symm_apply]
  exact he ▸ ho

include hF hD in
lemma parametricEssential_invertible :
    ((fderiv ℝ (parametricEssential pkg F) (parametricBase pkg t x)).comp
      (ContinuousLinearMap.inr ℝ (ℝ × pkg.decDom.X₀) pkg.decDom.X₁)).IsInvertible := by
  have hd := ((parametricEssential_smooth pkg hF).differentiable (by simp) (parametricBase pkg t x)).hasFDerivAt
  have hi : HasFDerivAt (fun y : pkg.decDom.X₁ => ((t,((domCoords pkg) x).2),y))
      (ContinuousLinearMap.inr ℝ (ℝ × pkg.decDom.X₀) pkg.decDom.X₁) ((domCoords pkg) x).1 :=
    (hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _)
  have hh := hd.comp (((domCoords pkg) x).1) hi
  have he := hh.unique (parametricEssential_vertical_derivative pkg hD)
  rw [he]
  exact ⟨pkg.equiv,rfl⟩

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricCurveManifold
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Filter
section
variable {m : ℕ} (a : Fin m → ℂ) [ha : Fact (Injective a)] [ha0 : Fact (∀ j,a j≠0)]

def normalChartAt (x : locus a) : NormalChart a :=
  (exists_normalChart_at ha.out ha0.out x).choose

def realChart (x : locus a) : OpenPartialHomeomorph (locus a) RealModel :=
  ((normalChartAt a x).sliceChart x).trans Complex.equivRealProdCLM.toHomeomorph.toOpenPartialHomeomorph

@[simp] theorem realChart_source (x : locus a) :
    (realChart a x).source=((normalChartAt a x).sliceChart x).source := by
  simp [realChart]

end
section

variable {m : ℕ} (a : Fin m → ℂ) (ε : Fin m → Bool)

 def infinityBranch : Set (locus a) := {x | x.val.1≠0 ∧
    x.val.1⁻¹∈infinityRegion a ∧ ∀ j,0<(endSign (ε j)*(x.val.1⁻¹*x.val.2 j)).re}

 theorem normalized_coordinate_sq {x : locus a} (hx : x.val.1≠0) (j : Fin m) :
    (x.val.1⁻¹*x.val.2 j)^2=1-a j*(x.val.1⁻¹)^2 := by
  rw [mul_pow,mem_locus.mp x.property j]
  field_simp

 theorem infinityPoint_inverse {x : locus a} (hx : x∈infinityBranch a ε) :
    infinityPoint a ε x.val.1⁻¹=x.val := by
  apply Prod.ext (inv_inv _)
  funext j
  have hs : (endSign (ε j)*(x.val.1⁻¹*x.val.2 j))^2=1-a j*(x.val.1⁻¹)^2 := by
    rw [mul_pow,endSign_sq,one_mul,normalized_coordinate_sq a hx.1]
  change (x.val.1⁻¹)⁻¹*(endSign (ε j)*Complex.sqrt (1-a j*(x.val.1⁻¹)^2))=x.val.2 j
  rw [← hs,sqrt_of_sq_pos (hx.2.2 j),← mul_assoc (endSign (ε j)),endSign_mul_self,one_mul,inv_inv]
  field_simp [hx.1]

 def infinityFallback : locus a := ⟨(0,fun j => Complex.sqrt (-a j)),by
   apply mem_locus.mpr
   intro j
   dsimp only
   rw [sqrt_sq_complex,zero_pow (by decide : (2 : ℕ)≠0),zero_sub]⟩

 def infinityInverse (s : ℂ) : locus a := by
  classical
  exact if h : s≠0 then ⟨infinityPoint a ε s,infinityPoint_mem a ε h⟩ else infinityFallback a

@[simp] theorem infinityInverse_val {s : ℂ} (hs : s≠0) :
    (infinityInverse a ε s).val=infinityPoint a ε s := by
  simp only [infinityInverse,dite_eq_left hs]

 theorem infinityBranch_open : IsOpen (infinityBranch a ε) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have ht : Continuous (fun x : locus a => x.val.1) := continuous_fst.comp continuous_subtype_val
  have hi : ContinuousAt (fun x : locus a => x.val.1⁻¹) x := ht.continuousAt.inv₀ hx.1
  have H : ∀ᶠ y in 𝓝 x,y.val.1≠0 := (isOpen_ne_fun ht continuous_const).mem_nhds hx.1
  have R : ∀ᶠ y in 𝓝 x,y.val.1⁻¹∈infinityRegion a :=
    hi.preimage_mem_nhds ((infinityRegion_open a).mem_nhds hx.2.1)
  have W : ∀ j,∀ᶠ y in 𝓝 x,0<(endSign (ε j)*(y.val.1⁻¹*y.val.2 j)).re := by
    intro j
    have hw : ContinuousAt (fun x : locus a => x.val.2 j) x := by fun_prop
    have hc : ContinuousAt (fun x : locus a =>
        (endSign (ε j)*(x.val.1⁻¹*x.val.2 j)).re) x :=
      Complex.continuous_re.continuousAt.comp
        (continuousAt_const.mul (hi.mul hw))
    exact hc.preimage_mem_nhds (isOpen_Ioi.mem_nhds (hx.2.2 j))
  filter_upwards [H,R,Filter.eventually_all.mpr W] with y hy hr hw
  exact ⟨hy,hr,hw⟩

 def infinityChart : OpenPartialHomeomorph (locus a) ℂ where
  toFun x := x.val.1⁻¹
  invFun := infinityInverse a ε
  source := infinityBranch a ε
  target := infinityDomain a
  map_source' _ hx := ⟨inv_ne_zero hx.1,hx.2.1⟩
  map_target' s hs := by
    change (infinityInverse a ε s).val.1≠0 ∧ _
    rw [infinityInverse_val a ε hs.1]
    refine ⟨inv_ne_zero hs.1,?_,?_⟩
    · change (s⁻¹)⁻¹∈infinityRegion a
      simpa only [inv_inv] using hs.2
    · intro j
      change 0<(endSign (ε j)*((s⁻¹)⁻¹*(s⁻¹*infinityRoot a ε s j))).re
      rw [inv_inv,← mul_assoc s,mul_inv_cancel₀ hs.1,one_mul]
      exact infinityRoot_positive a ε hs.2 j
  left_inv' x hx := by
    apply Subtype.ext
    rw [infinityInverse_val a ε (inv_ne_zero hx.1)]
    exact infinityPoint_inverse a ε hx
  right_inv' s hs := by
    rw [infinityInverse_val a ε hs.1,infinityPoint_coordinate]
  open_source := infinityBranch_open a ε
  open_target := infinityDomain_open a
  continuousOn_toFun := by
    intro x hx
    exact (((continuous_fst.comp continuous_subtype_val).continuousAt).inv₀ hx.1).continuousWithinAt
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply continuous_induced_rng.mpr
    have hc : ContinuousOn (infinityPoint a ε) (infinityDomain a) :=
      fun s hs => (infinityPoint_contDiffAt a ε hs).continuousAt.continuousWithinAt
    rw [continuousOn_iff_continuous_domRestrict] at hc
    exact hc.congr fun s => (infinityInverse_val a ε s.property.1).symm

@[simp] theorem infinityChart_apply (x : locus a) : infinityChart a ε x=x.val.1⁻¹ := rfl
@[simp] theorem infinityChart_source : (infinityChart a ε).source=infinityBranch a ε := rfl
@[simp] theorem infinityChart_target : (infinityChart a ε).target=infinityDomain a := rfl

end

variable {m : ℕ} (a : Fin m → ℂ)

@[simp] theorem infinity_end_count : Fintype.card (Fin m → Bool)=2^m := by simp

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricAnnulusDomain
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Topology
open Set Function Filter
open scoped Manifold
open Manifold
variable (m : ℕ)

theorem annulusPoint_contDiffAt {s : ℂ} (hs : s∈annulusDomain m) :
    ContDiffAt ℂ ∞ (annulusPoint m) s := by
  apply ContDiffAt.prodMk
  · exact (sqrt_contDiffAt hs.2.1).comp s (baseSquare_contDiffAt hs.1)
  · apply contDiffAt_pi.mpr
    intro j
    by_cases hj0 : j=0
    · subst j
      simpa using plus_contDiffAt hs.1
    by_cases hj1 : j=1
    · subst j
      have hn : (1 : Fin (m+2))≠0 := by simp
      simpa only [ite_eq_right hn,ite_true, if_true] using minus_contDiffAt hs.1
    · have hj : 1<j.val := by
        have h0 : j.val≠0 := fun h => hj0 (Fin.ext h)
        have h1 : j.val≠1 := fun h => hj1 (Fin.ext (by simpa using h))
        omega
      have hb : ContDiffAt ℂ ∞ (fun t : ℂ => parameters m j-baseSquare t) s :=
        contDiffAt_const.sub (baseSquare_contDiffAt hs.1)
      have hr := (sqrt_contDiffAt (hs.2.2 j hj)).comp s hb
      have hh : ContDiffAt ℂ ∞ (fun t => Complex.I*Complex.sqrt (parameters m j-baseSquare t)) s :=
        contDiffAt_const.mul hr
      simpa only [annulusPoint,ite_eq_right hj0,ite_eq_right hj1] using hh

def annulusCoordinate : Affine (m+2) →L[ℂ] ℂ :=
  ((ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.snd ℂ ℂ (Fin (m+2) → ℂ)))+
  ((ContinuousLinearMap.proj 1).comp (ContinuousLinearMap.snd ℂ ℂ (Fin (m+2) → ℂ)))

@[simp] theorem annulusCoordinate_apply (x : Affine (m+2)) : annulusCoordinate m x=x.2 0+x.2 1 := rfl

@[simp] theorem annulusCoordinate_point (s : ℂ) : annulusCoordinate m (annulusPoint m s)=s := by
  simp

theorem annulusCoordinate_mul {x : Affine (m+2)} (hx : x∈locus (parameters m)) :
    annulusCoordinate m x*(x.2 0-x.2 1)=1 := by
  have h0 := mem_locus.mp hx 0
  have h1 := mem_locus.mp hx 1
  simp only [parameters_zero,parameters_one] at h0 h1
  change (x.2 0+x.2 1)*(x.2 0-x.2 1)=1
  linear_combination h0-h1

theorem annulusCoordinate_ne_zero {x : Affine (m+2)} (hx : x∈locus (parameters m)) :
    annulusCoordinate m x≠0 := by
  intro h
  have he := annulusCoordinate_mul m hx
  rw [h,zero_mul] at he
  exact zero_ne_one he

theorem inverse_coordinate {x : Affine (m+2)} (hx : x∈locus (parameters m)) :
    (annulusCoordinate m x)⁻¹=x.2 0-x.2 1 := by
  apply mul_left_cancel₀ (annulusCoordinate_ne_zero m hx)
  rw [mul_inv_cancel₀ (annulusCoordinate_ne_zero m hx),annulusCoordinate_mul m hx]

abbrev Surface := locus (parameters m)

def annulusBranch : Set (Surface m) := {x | annulusCoordinate m x.val∈annulusDomain m ∧
  0<x.val.1.re ∧ ∀ j : Fin (m+2),1<j.val → 0<(x.val.2 j).im}

def annulusBasepoint : Surface m := ⟨annulusPoint m 1,annulusPoint_mem m one_ne_zero⟩

def annulusInverse (s : ℂ) : Surface m := by
  classical
  exact if h : s≠0 then ⟨annulusPoint m s,annulusPoint_mem m h⟩ else annulusBasepoint m

@[simp] theorem annulusInverse_val {s : ℂ} (hs : s≠0) :
    (annulusInverse m s).val=annulusPoint m s := by
  simp only [annulusInverse,dite_eq_left hs]

theorem annulusBranch_isOpen : IsOpen (annulusBranch m) := by
  have hc : Continuous (fun x : Surface m => annulusCoordinate m x.val) :=
    (annulusCoordinate m).continuous.comp continuous_subtype_val
  have ht : Continuous (fun x : Surface m => x.val.1.re) :=
    Complex.continuous_re.comp (continuous_fst.comp continuous_subtype_val)
  have hw : ∀ j : Fin (m+2),Continuous (fun x : Surface m => (x.val.2 j).im) :=
    fun j => Complex.continuous_im.comp
      ((continuous_apply j).comp (continuous_snd.comp continuous_subtype_val))
  change IsOpen ((fun x : Surface m => annulusCoordinate m x.val) ⁻¹' annulusDomain m ∩
    ({x : Surface m | 0<x.val.1.re} ∩ {x : Surface m | ∀ j,1<j.val → 0<(x.val.2 j).im}))
  refine ((annulusDomain_isOpen m).preimage hc).inter ((isOpen_lt continuous_const ht).inter ?_)
  simp only [ofPred_forall]
  exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ => isOpen_lt continuous_const (hw j)

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

end

end OAI
end


