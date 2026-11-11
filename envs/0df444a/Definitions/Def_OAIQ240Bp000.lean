-- Prove2me | Definitions.Def_OAIQ240Bp000
-- name    : OAIQ240Bp000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:42:56.895318+00:00
-- url     : https://prove2.me/theorems/3292e3df-235f-4f5c-905f-22c5551b16a6
-- title:
--   Definitions bundle OAIQ240Bp000 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 156 declarations of OpenAI's Lean: 74 definitions, 9 inductive types or structures and 73 theorems. The definitions and types are `OAI.ContinuousLinearMap.FredholmPackage.codCoords`, `OAI.ContinuousLinearMap.FredholmPackage.domCoords`, `OAI.ContinuousLinearMap.FredholmPackage.finitePerturbation`, `OAI.HigherDimensionalBallPacking.Rigidity.AffineLineCurve`, `OAI.HigherDimensionalBallPacking.Rigidity.Compatible`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.AtlasForm`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.AtlasForm.SupportedIn`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.AtlasForm.chartExtension`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.AtlasForm.chartMass`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.AtlasForm.exterior`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.AtlasForm.smul`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.AtlasPartition`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.AtlasPartition.mass`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.AtlasSmoothMap`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.AtlasSmoothMap.comp`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.AtlasSmoothMap.pullback`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.AtlasSmoothMap.restrict`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.CoordinateSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.ModelAtlasSmoothMap`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.ModelAtlasSmoothMap.toCoordinates`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.SignedModelAtlas`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.SignedModelAtlas.toCoordinates`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.SignedSmoothAtlas`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.SignedSmoothAtlas.chartedSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.SignedSmoothAtlas.restrict`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.alternationCLM`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.collarCutoff`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.collarRise`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.collarVolumeForm`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.coordinateVector`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.coordinateVolume`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.formFlux`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.initialCollarDensity`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.tailCLM`, `OAI.HigherDimensionalBallPacking.Rigidity.Degree.timeSpaceCoordinates`, `OAI.HigherDimensionalBallPacking.Rigidity.End`, `OAI.HigherDimensionalBallPacking.Rigidity.FiniteZeroGerm`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Ambient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.BoundedCThree`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.BoundedCThree.bound` and 43 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `BallPacking_Degree_BoxContinuation`, `BallPacking_Degree_ChartFormZeroExtension`, `BallPacking_Degree_EuclideanAtlasTransport`, `BallPacking_Degree_HomotopyFlux`, `BallPacking_Fredholm_CompactFredholmAlternative`, `BallPacking_Fredholm_SurjectiveParametricReduction`, `BallPacking_Holder_BanachSpace`, `BallPacking_Holder_MarkedJets`, `BallPacking_Holder_NonlinearCR`, `BallPacking_Moduli_ZeroCharts`, `BallPacking_Rigidity_Adapted`, `BallPacking_Rigidity_CompatibleStructures`, `BallPacking_Rigidity_RadialForm`.
--
--   **Imports.** It imports the published bundle `Def_BallPacking`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ240Bp005`, `OAIQ240Bp006` and `OAIQ240Bp007`; the statements `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_czero_compactness_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_gradient_bound_bp240` and `OAI.HigherDimensionalBallPacking.Rigidity.packing_two_line_reduction_bp240`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_BallPacking

section
-- module Solutions.OAIQ240_BP.BallPacking_Degree_HomotopyFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.Degree

section
open scoped ContDiff Topology
open Set Filter MeasureTheory
variable {m : ℕ}
abbrev CoordinateSpace (m : ℕ) := Fin m → ℝ

def coordinateVector (i : Fin m) : CoordinateSpace m := Pi.single i 1

def formFlux (w : CoordinateSpace (m+1) → CoordinateSpace (m+1) [⋀^Fin m]→L[ℝ] ℝ)
    (i : Fin (m+1)) (x : CoordinateSpace (m+1)) : ℝ :=
  (-1:ℝ)^i.val • w x (i.removeNth coordinateVector)


def coordinateVolume (m : ℕ) : CoordinateSpace m [⋀^Fin m]→L[ℝ] ℝ where
  toAlternatingMap := (Pi.basisFun ℝ (Fin m)).det
  cont := by
    change Continuous (fun v : Fin m → CoordinateSpace m => (Pi.basisFun ℝ (Fin m)).det v)
    simp only [Pi.basisFun_det_apply]
    exact continuous_id.matrix_det


end
section
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
variable {M I : Type*} [TopologicalSpace M] {d k : ℕ}

structure SignedSmoothAtlas (M I : Type*) [TopologicalSpace M] (d : ℕ) where
  chart : I → OpenPartialHomeomorph M (CoordinateSpace d)
  cover : ∀ x : M,∃ i,x∈(chart i).source
  sign : I → ℝ
  sign_sq : ∀ i,sign i*sign i=1
  transition_smooth : ∀ i j,ContDiffOn ℝ ∞ (chart j ∘ (chart i).symm)
    ((chart i).symm ≫ₕ chart j).source
  orientation : ∀ i j,∀ q∈((chart i).symm ≫ₕ chart j).source,
    sign i*(fderiv ℝ (chart j ∘ (chart i).symm) q).det =
      sign j*|(fderiv ℝ (chart j ∘ (chart i).symm) q).det|

structure AtlasForm (a : SignedSmoothAtlas M I d) (k : ℕ) where
  form : I → CoordinateSpace d → CoordinateSpace d [⋀^Fin k]→L[ℝ] ℝ
  smooth : ∀ i,ContDiffOn ℝ ∞ (form i) (a.chart i).target
  compatible : ∀ i j,∀ q∈((a.chart i).symm ≫ₕ a.chart j).source,
    form i q=(form j (a.chart j ((a.chart i).symm q))).compContinuousLinearMap
      (fderiv ℝ (a.chart j ∘ (a.chart i).symm) q)

namespace AtlasForm
variable {a : SignedSmoothAtlas M I d} (α : AtlasForm a k)

def SupportedIn (K : Set M) : Prop :=
  ∀ i q,q∈(a.chart i).target → (a.chart i).symm q∉K → α.form i q=0

lemma contDiffOn_extDeriv (i : I) : ContDiffOn ℝ ∞ (extDeriv (α.form i)) (a.chart i).target := by
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (CoordinateSpace d) ℝ).contDiff.comp_contDiffOn
    ((contDiffOn_infty_iff_fderiv_of_isOpen (a.chart i).open_target).mp (α.smooth i)).2

def exterior : AtlasForm a (k+1) where
  form := fun i => extDeriv (α.form i)
  smooth := α.contDiffOn_extDeriv
  compatible i j q hq := by
    let g := a.chart j ∘ (a.chart i).symm
    have he : α.form i =ᶠ[𝓝 q] (fun y => (α.form j (g y)).compContinuousLinearMap (fderiv ℝ g y)) := by
      filter_upwards [((a.chart i).symm ≫ₕ a.chart j).open_source.mem_nhds hq] with y hy
      exact α.compatible i j y hy
    have hgt : g q∈(a.chart j).target := (a.chart j).map_source hq.2
    have hω := ((α.smooth j).contDiffAt ((a.chart j).open_target.mem_nhds hgt)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    rw [he.extDeriv_eq]
    exact extDeriv_pullback hω
      ((a.transition_smooth i j).contDiffAt (((a.chart i).symm ≫ₕ a.chart j).open_source.mem_nhds hq)) (by
        rw [minSmoothness_of_isRCLikeNormedField]
        exact WithTop.coe_le_coe.mpr le_top)

def smul (f : M → ℝ)
    (hf : ∀ i,ContDiffOn ℝ ∞ (f ∘ (a.chart i).symm) (a.chart i).target) : AtlasForm a k where
  form := fun i q => f ((a.chart i).symm q) • α.form i q
  smooth i := (hf i).smul (α.smooth i)
  compatible i j q hq := by
    have he := (a.chart j).left_inv hq.2
    simp only [OpenPartialHomeomorph.symm_symm] at he
    change f ((a.chart i).symm q) • α.form i q = _
    rw [α.compatible i j q hq,he]
    ext v
    rfl

end AtlasForm

end
open scoped ContDiff Topology
open Set Filter Function MeasureTheory



end HigherDimensionalBallPacking.Rigidity.Degree
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Degree_ChartFormZeroExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.Degree

section
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
variable {d k : ℕ}

variable {M I : Type*} [TopologicalSpace M] [T2Space M]
  {a : SignedSmoothAtlas M I d} (α : AtlasForm a k)

def AtlasForm.chartExtension (i : I) :
    CoordinateSpace d → CoordinateSpace d [⋀^Fin k]→L[ℝ] ℝ :=
  (a.chart i).target.indicator (α.form i)

def AtlasForm.chartMass {a : SignedSmoothAtlas M I d} (α : AtlasForm a d) (i : I) : ℝ :=
  ∫ q,a.sign i*α.chartExtension i q coordinateVector


end
section
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
variable {M I : Type*} [TopologicalSpace M] [T2Space M] {d k : ℕ}
  {a : SignedSmoothAtlas M I d}

variable [Fintype I]
structure AtlasPartition (a : SignedSmoothAtlas M I d) (K : Set M) where
  weight : I → M → ℝ
  smooth : ∀ i j,ContDiffOn ℝ ∞ (weight i ∘ (a.chart j).symm) (a.chart j).target
  sum_one : ∀ x∈K,∑i,weight i x=1
  subordinate : ∀ i,tsupport (weight i)⊆(a.chart i).source

namespace AtlasPartition
variable {K : Set M} (p : AtlasPartition a K)

def mass (Ω : AtlasForm a d) : ℝ :=
  ∑i,(Ω.smul (p.weight i) (p.smooth i)).chartMass i

end AtlasPartition

end
section
open scoped ContDiff Topology
open Set Function Filter
variable {A B Z : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] {k : ℕ}

def alternationCLM : (ContinuousMultilinearMap ℝ (fun _ : Fin k => A) ℝ) →L[ℝ]
    (A [⋀^Fin k]→L[ℝ] ℝ) where
  toFun := ContinuousMultilinearMap.alternatization
  map_add' := map_add _
  map_smul' r f := by
    ext v
    simp only [RingHom.id_apply,ContinuousMultilinearMap.alternatization_apply_apply,
      smul_apply,ContinuousAlternatingMap.smul_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    exact smul_comm _ _ _
  cont := by
    rw [ContinuousAlternatingMap.isEmbedding_toContinuousMultilinearMap.continuous_iff]
    change Continuous (fun f : ContinuousMultilinearMap ℝ (fun _ : Fin k => A) ℝ =>
      ∑σ : Equiv.Perm (Fin k),Equiv.Perm.sign σ • f.domDomCongr σ)
    apply continuous_finsetSum
    intro σ hσ
    exact (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ A ℝ σ).continuous.const_smul _

lemma alternationCLM_alternating (w : A [⋀^Fin k]→L[ℝ] ℝ) :
    alternationCLM w.toContinuousMultilinearMap=(k.factorial:ℝ) • w := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  change (ContinuousMultilinearMap.alternatization w.toContinuousMultilinearMap).toAlternatingMap=_
  rw [ContinuousMultilinearMap.alternatization_apply_toAlternatingMap]
  change MultilinearMap.alternatization w.toAlternatingMap.toMultilinearMap=
    (k.factorial:ℝ) • w.toAlternatingMap
  simpa only [Fintype.card_fin,Nat.cast_smul_eq_nsmul] using w.toAlternatingMap.coe_alternatization

lemma contDiffOn_alternating_of_multilinear {f : Z → A [⋀^Fin k]→L[ℝ] ℝ} {S : Set Z}
    (hf : ContDiffOn ℝ ∞ (fun z => (f z).toContinuousMultilinearMap) S) : ContDiffOn ℝ ∞ f S := by
  have h := (alternationCLM (A := A) (k := k)).contDiff.comp_contDiffOn hf
  have hn : (k.factorial:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  convert h.const_smul (k.factorial:ℝ)⁻¹ using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  simp only [Function.comp_apply]
  rw [alternationCLM_alternating,smul_smul,inv_mul_cancel₀ hn,one_smul]

lemma contDiffOn_alternating_comp {f : Z → B [⋀^Fin k]→L[ℝ] ℝ}
    {g : Z → A →L[ℝ] B} {S : Set Z}
    (hf : ContDiffOn ℝ ∞ f S) (hg : ContDiffOn ℝ ∞ g S) :
    ContDiffOn ℝ ∞ (fun z => (f z).compContinuousLinearMap (g z)) S := by
  apply contDiffOn_alternating_of_multilinear
  have hp : ContDiffOn ℝ ∞ (fun z => ((fun _ : Fin k => g z),(f z).toContinuousMultilinearMap)) S :=
    (contDiffOn_pi.mpr (fun _ => hg)).prodMk
      ((ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ : (B [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => B) ℝ).contDiff.comp_contDiffOn hf)
  have ha : ContDiff ℝ ∞ (fun p : (Fin k → A →L[ℝ] B) ×
      ContinuousMultilinearMap ℝ (fun _ : Fin k => B) ℝ => p.2.compContinuousLinearMap p.1) :=
    (show AnalyticOnNhd ℝ _ univ from ContinuousMultilinearMap.analyticOnNhd_uncurry_compContinuousLinearMap).contDiff
  exact ha.comp_contDiffOn hp


end
section
open scoped ContDiff Topology Manifold
open Set Function Filter
variable {M I P : Type*} [TopologicalSpace M]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  {d k : ℕ} {a : SignedSmoothAtlas M I d}

structure AtlasSmoothMap (a : SignedSmoothAtlas M I d) (P : Type*)
    [NormedAddCommGroup P] [NormedSpace ℝ P] where
  map : M → P
  smooth : ∀ i,ContDiffOn ℝ ∞ (map ∘ (a.chart i).symm) (a.chart i).target

namespace AtlasSmoothMap
variable (f : AtlasSmoothMap a P)
lemma derivative_transition (i j : I) {q : CoordinateSpace d}
    (hq : q∈((a.chart i).symm ≫ₕ a.chart j).source) :
    fderiv ℝ (f.map ∘ (a.chart i).symm) q=
      (fderiv ℝ (f.map ∘ (a.chart j).symm) (a.chart j ((a.chart i).symm q))).comp
        (fderiv ℝ (a.chart j ∘ (a.chart i).symm) q) := by
  let g := a.chart j ∘ (a.chart i).symm
  have he : (f.map ∘ (a.chart i).symm) =ᶠ[𝓝 q] ((f.map ∘ (a.chart j).symm) ∘ g) := by
    filter_upwards [((a.chart i).symm ≫ₕ a.chart j).open_source.mem_nhds hq] with r hr
    simp only [Function.comp_apply,g]
    exact congrArg f.map ((a.chart j).left_inv hr.2).symm
  rw [he.fderiv_eq]
  apply fderiv_comp
  · exact ((f.smooth j).contDiffAt ((a.chart j).open_target.mem_nhds ((a.chart j).map_source hq.2))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  · exact ((a.transition_smooth i j).contDiffAt (((a.chart i).symm ≫ₕ a.chart j).open_source.mem_nhds hq)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)

def pullback (w : P → P [⋀^Fin k]→L[ℝ] ℝ) (hw : ContDiff ℝ ∞ w) : AtlasForm a k where
  form i q := (w (f.map ((a.chart i).symm q))).compContinuousLinearMap
    (fderiv ℝ (f.map ∘ (a.chart i).symm) q)
  smooth i := contDiffOn_alternating_comp (hw.comp_contDiffOn (f.smooth i))
    ((contDiffOn_infty_iff_fderiv_of_isOpen (a.chart i).open_target).mp (f.smooth i)).2
  compatible i j q hq := by
    change (w (f.map ((a.chart i).symm q))).compContinuousLinearMap _=
      ((w (f.map ((a.chart j).symm (a.chart j ((a.chart i).symm q))))).compContinuousLinearMap _).compContinuousLinearMap _
    have he := (a.chart j).left_inv hq.2
    simp only [OpenPartialHomeomorph.symm_symm] at he
    rw [he,f.derivative_transition i j hq]
    rfl

end AtlasSmoothMap

end
open scoped ContDiff Topology
open Set Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity.Degree
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Degree_BoxContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.Degree

section
open scoped ContDiff Topology
open Set Filter MeasureTheory
variable {m : ℕ}

lemma tail_smooth : ContDiff ℝ ∞ (Fin.tail : CoordinateSpace (m+1) → CoordinateSpace m) := by
  exact contDiff_pi.mpr (fun i => contDiff_pi.mp contDiff_id i.succ)


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {m : ℕ}

def tailCLM (m : ℕ) : CoordinateSpace (m+1) →L[ℝ] CoordinateSpace m :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj i.succ)

def collarVolumeForm (θ : ℝ → ℝ) (ρ : CoordinateSpace m → ℝ) (v : CoordinateSpace (m+1)) :
    CoordinateSpace (m+1) [⋀^Fin m]→L[ℝ] ℝ :=
  (θ (v 0)*ρ (Fin.tail v)) • (coordinateVolume m).compContinuousLinearMap (tailCLM m)

lemma collarVolumeForm_smooth {θ : ℝ → ℝ} {ρ : CoordinateSpace m → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hρ : ContDiff ℝ ∞ ρ) : ContDiff ℝ ∞ (collarVolumeForm θ ρ) :=
  ((hθ.comp (contDiff_pi.mp contDiff_id 0)).mul (hρ.comp tail_smooth)).smul contDiff_const


end
section
open scoped ContDiff Topology
open Set Function Filter

def collarRise (a b t : ℝ) : ℝ := Real.smoothTransition ((t-a)/(b-a))
lemma collarRise_smooth (a b : ℝ) : ContDiff ℝ ∞ (collarRise a b) :=
  (show ContDiff ℝ ∞ Real.smoothTransition from contDiff_infty.mpr (fun _ => Real.smoothTransition.contDiff)).comp
    ((contDiff_id.sub contDiff_const).div_const _)

def collarCutoff (a b c d t : ℝ) : ℝ := collarRise a b t-collarRise c d t
lemma collarCutoff_smooth (a b c d : ℝ) : ContDiff ℝ ∞ (collarCutoff a b c d) :=
  (collarRise_smooth a b).sub (collarRise_smooth c d)


end
section
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory Manifold
variable {M I : Type*} [TopologicalSpace M] [T2Space M] [Fintype I] {d : ℕ}
  (a : SignedSmoothAtlas M I d)

@[instance_reducible] def SignedSmoothAtlas.chartedSpace : ChartedSpace (CoordinateSpace d) M where
  atlas := range a.chart
  chartAt x := a.chart (a.cover x).choose
  mem_chart_source x := (a.cover x).choose_spec
  chart_mem_atlas _ := mem_range_self _


end
open scoped ContDiff Topology Manifold
open Set Function Filter
variable {M I : Type*} [TopologicalSpace M] {d : ℕ}

def SignedSmoothAtlas.restrict (a : SignedSmoothAtlas M I d)
    (J : Set I) (W : TopologicalSpace.Opens M) (hW : Nonempty W)
    (hcover : ∀ x : W,∃ i∈J,x.val∈(a.chart i).source) : SignedSmoothAtlas W J d where
  chart i := (a.chart i.val).subtypeRestr hW
  cover x := by
    obtain ⟨i,hi,hx⟩ := hcover x
    refine ⟨⟨i,hi⟩,?_⟩
    simpa only [OpenPartialHomeomorph.subtypeRestr_source,Set.mem_preimage] using hx
  sign i := a.sign i.val
  sign_sq i := a.sign_sq i.val
  transition_smooth i j := by
    let c := (a.chart i.val).subtypeRestr hW
    let b := (a.chart j.val).subtypeRestr hW
    have hsub : (c.symm ≫ₕ b).source ⊆ ((a.chart i.val).symm ≫ₕ a.chart j.val).source := by
      intro q hq
      refine ⟨(a.chart i.val).subtypeRestr_target_subset hW hq.1,?_⟩
      have he := (a.chart i.val).subtypeRestr_symm_apply hW hq.1
      change ((c.symm q).val)=(a.chart i.val).symm q at he
      change (a.chart i.val).symm q∈(a.chart j.val).source
      rw [←he]
      simpa only [OpenPartialHomeomorph.symm_symm,OpenPartialHomeomorph.subtypeRestr_source,Set.mem_preimage,c,b] using hq.2
    apply ((a.transition_smooth i.val j.val).mono hsub).congr
    intro q hq
    change a.chart j.val (((a.chart i.val).subtypeRestr hW).symm q).val=_
    exact congrArg (a.chart j.val) ((a.chart i.val).subtypeRestr_symm_apply hW hq.1)
  orientation i j q hq := by
    let c := (a.chart i.val).subtypeRestr hW
    let b := (a.chart j.val).subtypeRestr hW
    have he : (b ∘ c.symm) =ᶠ[𝓝 q] (a.chart j.val ∘ (a.chart i.val).symm) := by
      filter_upwards [(c.symm ≫ₕ b).open_source.mem_nhds hq] with r hr
      change a.chart j.val (((a.chart i.val).subtypeRestr hW).symm r).val=_
      exact congrArg (a.chart j.val) ((a.chart i.val).subtypeRestr_symm_apply hW hr.1)
    change a.sign i.val*(fderiv ℝ (b ∘ c.symm) q).det =
      a.sign j.val*|(fderiv ℝ (b ∘ c.symm) q).det|
    rw [he.fderiv_eq]
    apply a.orientation i.val j.val q
    refine ⟨(a.chart i.val).subtypeRestr_target_subset hW hq.1,?_⟩
    have he := (a.chart i.val).subtypeRestr_symm_apply hW hq.1
    change ((c.symm q).val)=(a.chart i.val).symm q at he
    change (a.chart i.val).symm q∈(a.chart j.val).source
    rw [←he]
    simpa only [OpenPartialHomeomorph.symm_symm,OpenPartialHomeomorph.subtypeRestr_source,Set.mem_preimage,c,b] using hq.2



end HigherDimensionalBallPacking.Rigidity.Degree
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Degree_EuclideanAtlasTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.Degree

section
open scoped ContDiff Topology Manifold
open Set Function Filter
variable {M I B : Type*} [TopologicalSpace M]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] {d : ℕ}

structure SignedModelAtlas (M I B : Type*) [TopologicalSpace M]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] where
  chart : I → OpenPartialHomeomorph M B
  cover : ∀ x : M,∃ i,x∈(chart i).source
  sign : I → ℝ
  sign_sq : ∀ i,sign i*sign i=1
  transition_smooth : ∀ i j,ContDiffOn ℝ ∞ (chart j ∘ (chart i).symm)
    ((chart i).symm ≫ₕ chart j).source
  orientation : ∀ i j,∀ q∈((chart i).symm ≫ₕ chart j).source,
    sign i*(fderiv ℝ (chart j ∘ (chart i).symm) q).det =
      sign j*|(fderiv ℝ (chart j ∘ (chart i).symm) q).det|

omit [FiniteDimensional ℝ B] in
lemma conjugate_clm_det [FiniteDimensional ℝ B]
    (e : B ≃L[ℝ] CoordinateSpace d) (A : B →L[ℝ] B) :
    (e.toContinuousLinearMap.comp (A.comp e.symm.toContinuousLinearMap)).det=A.det := by
  exact LinearMap.det_conj A.toLinearMap e.toLinearEquiv

def SignedModelAtlas.toCoordinates (a : SignedModelAtlas M I B)
    (e : B ≃L[ℝ] CoordinateSpace d) : SignedSmoothAtlas M I d where
  chart i := (a.chart i).trans e.toHomeomorph.toOpenPartialHomeomorph
  cover x := by
    obtain ⟨i,hi⟩ := a.cover x
    exact ⟨i,hi,mem_univ _⟩
  sign := a.sign
  sign_sq := a.sign_sq
  transition_smooth i j := by
    let c := (a.chart i).trans e.toHomeomorph.toOpenPartialHomeomorph
    let b := (a.chart j).trans e.toHomeomorph.toOpenPartialHomeomorph
    have hs : MapsTo e.symm (c.symm ≫ₕ b).source ((a.chart i).symm ≫ₕ a.chart j).source := by
      intro q hq
      exact ⟨hq.1.2,hq.2.1⟩
    exact (e.contDiff.comp_contDiffOn ((a.transition_smooth i j).comp e.symm.contDiff.contDiffOn hs))
  orientation i j q hq := by
    let c := (a.chart i).trans e.toHomeomorph.toOpenPartialHomeomorph
    let b := (a.chart j).trans e.toHomeomorph.toOpenPartialHomeomorph
    have hs : e.symm q∈((a.chart i).symm ≫ₕ a.chart j).source := ⟨hq.1.2,hq.2.1⟩
    have hd := ((a.transition_smooth i j).contDiffAt
      (((a.chart i).symm ≫ₕ a.chart j).open_source.mem_nhds hs)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    have he := e.hasFDerivAt.comp q (hd.hasFDerivAt.comp q e.symm.hasFDerivAt)
    have he' : fderiv ℝ (b ∘ c.symm) q =
      e.toContinuousLinearMap.comp ((fderiv ℝ (a.chart j ∘ (a.chart i).symm) (e.symm q)).comp
        e.symm.toContinuousLinearMap) := he.fderiv
    change a.sign i*(fderiv ℝ (b ∘ c.symm) q).det =a.sign j*|(fderiv ℝ (b ∘ c.symm) q).det|
    rw [he',conjugate_clm_det]
    exact a.orientation i j (e.symm q) hs


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

def timeSpaceCoordinates (e : E ≃L[ℝ] CoordinateSpace m) : (ℝ × E) ≃L[ℝ] CoordinateSpace (m+1) where
  toFun v := Fin.cons v.1 (e v.2)
  invFun v := (v 0,e.symm (Fin.tail v))
  left_inv v := by simp only [Fin.cons_zero,Fin.tail_cons,e.symm_apply_apply,Prod.mk.eta]
  right_inv v := by simp only [e.apply_symm_apply,Fin.cons_self_tail]
  map_add' v w := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' r v := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  continuous_toFun := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_fst
    · exact (continuous_apply j).comp (e.continuous.comp continuous_snd)
  continuous_invFun := (continuous_apply 0).prodMk (e.symm.continuous.comp (continuous_pi (fun i => continuous_apply i.succ)))


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
variable {m : ℕ}

def initialCollarDensity (a b : ℝ) (ρ : CoordinateSpace m → ℝ) (v : CoordinateSpace (m+1)) : ℝ :=
  deriv (collarRise a b) (v 0)*ρ (Fin.tail v)


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {M I B P : Type*} [TopologicalSpace M]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup P] [NormedSpace ℝ P] {d : ℕ}

structure ModelAtlasSmoothMap (a : SignedModelAtlas M I B) (P : Type*)
    [NormedAddCommGroup P] [NormedSpace ℝ P] where
  map : M → P
  smooth : ∀ i,ContDiffOn ℝ ∞ (map ∘ (a.chart i).symm) (a.chart i).target

def ModelAtlasSmoothMap.toCoordinates {a : SignedModelAtlas M I B}
    (f : ModelAtlasSmoothMap a P) (e : B ≃L[ℝ] CoordinateSpace d) :
    AtlasSmoothMap (a.toCoordinates e) P where
  map := f.map
  smooth i := (f.smooth i).comp e.symm.contDiff.contDiffOn (fun _ h => h.2)

 def AtlasSmoothMap.restrict {a : SignedSmoothAtlas M I d} (f : AtlasSmoothMap a P)
    (J : Set I) (W : TopologicalSpace.Opens M) (hW : Nonempty W)
    (hcover : ∀ x : W,∃ i∈J,x.val∈(a.chart i).source) :
    AtlasSmoothMap (a.restrict J W hW hcover) P where
  map x := f.map x.val
  smooth i := by
    let c := (a.chart i.val).subtypeRestr hW
    apply ((f.smooth i.val).mono ((a.chart i.val).subtypeRestr_target_subset hW)).congr
    intro q hq
    change f.map (c.symm q).val=f.map ((a.chart i.val).symm q)
    exact congrArg f.map ((a.chart i.val).subtypeRestr_symm_apply hW hq)

 def AtlasSmoothMap.comp {a : SignedSmoothAtlas M I d} (f : AtlasSmoothMap a P)
    {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (g : P → Q) (hg : ContDiff ℝ ∞ g) : AtlasSmoothMap a Q where
  map := g ∘ f.map
  smooth i := hg.comp_contDiffOn (f.smooth i)


end

end HigherDimensionalBallPacking.Rigidity.Degree
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_BanachSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped BoundedContinuousFunction Topology ContDiff
open Set Filter
section

variable (X E : Type*) [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev Pairs := {p : X × X // p.1 ≠ p.2}

abbrev Ambient := (X →ᵇ E) × (Pairs X →ᵇ E)

def graph (α : ℝ) : Submodule ℝ (Ambient X E) where
  carrier := {u | ∀ p : Pairs X,
    u.2 p = (dist p.val.1 p.val.2 ^ α)⁻¹ • (u.1 p.val.1 - u.1 p.val.2)}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv p
    simp only [Prod.fst_add, Prod.snd_add, BoundedContinuousFunction.add_apply,
      hu p, hv p]
    rw [show u.1 p.val.1 + v.1 p.val.1 - (u.1 p.val.2 + v.1 p.val.2) =
      (u.1 p.val.1 - u.1 p.val.2) + (v.1 p.val.1 - v.1 p.val.2) by abel, smul_add]
  smul_mem' := by
    intro c u hu p
    change c • u.2 p = (dist p.val.1 p.val.2 ^ α)⁻¹ •
      (c • u.1 p.val.1 - c • u.1 p.val.2)
    rw [hu p, ← smul_sub, smul_comm]

abbrev Holder (α : ℝ) := graph X E α

variable {X E}

def valueCLM (α : ℝ) : Holder X E α →L[ℝ] (X →ᵇ E) :=
  (ContinuousLinearMap.fst ℝ (X →ᵇ E) (Pairs X →ᵇ E)).comp (graph X E α).subtypeL

def incrementCLM (α : ℝ) : Holder X E α →L[ℝ] (Pairs X →ᵇ E) :=
  (ContinuousLinearMap.snd ℝ (X →ᵇ E) (Pairs X →ᵇ E)).comp (graph X E α).subtypeL

variable {α : ℝ}

@[simp] lemma valueCLM_apply (u : Holder X E α) (x : X) :
    valueCLM α u x = u.val.1 x := rfl

@[simp] lemma incrementCLM_apply (u : Holder X E α) (p : Pairs X) :
    incrementCLM α u p = u.val.2 p := rfl

lemma increment_eq (u : Holder X E α) (p : Pairs X) :
    incrementCLM α u p = (dist p.val.1 p.val.2 ^ α)⁻¹ •
      (valueCLM α u p.val.1 - valueCLM α u p.val.2) := u.property p

lemma value_norm_le (u : Holder X E α) : ‖valueCLM α u‖ ≤ ‖u‖ :=
  le_max_left _ _

lemma increment_norm_le (u : Holder X E α) : ‖incrementCLM α u‖ ≤ ‖u‖ :=
  le_max_right _ _

lemma norm_value_le (u : Holder X E α) (x : X) : ‖valueCLM α u x‖ ≤ ‖u‖ :=
  (BoundedContinuousFunction.norm_coe_le_norm _ _).trans (value_norm_le u)

lemma norm_increment_le (u : Holder X E α) (p : Pairs X) :
    ‖incrementCLM α u p‖ ≤ ‖u‖ :=
  (BoundedContinuousFunction.norm_coe_le_norm _ _).trans (increment_norm_le u)

lemma norm_sub_value_le (u : Holder X E α) (x y : X) :
    ‖valueCLM α u x - valueCLM α u y‖ ≤ ‖u‖ * dist x y ^ α := by
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, norm_zero]
    positivity
  have hd : 0 < dist x y ^ α := Real.rpow_pos_of_pos (dist_pos.mpr hxy) α
  have h := norm_increment_le u ⟨(x,y),hxy⟩
  rw [increment_eq, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hd.le)] at h
  change (dist x y ^ α)⁻¹ * ‖valueCLM α u x - valueCLM α u y‖ ≤ ‖u‖ at h
  have hh := mul_le_mul_of_nonneg_right h hd.le
  simpa only [mul_assoc, mul_left_comm (dist x y ^ α)⁻¹, inv_mul_cancel₀ hd.ne', mul_one] using hh

@[ext] lemma value_ext {u v : Holder X E α}
    (h : ∀ x, valueCLM α u x = valueCLM α v x) : u = v := by
  apply Subtype.ext
  apply Prod.ext
  · exact BoundedContinuousFunction.ext h
  · apply BoundedContinuousFunction.ext
    intro p
    rw [← incrementCLM_apply, ← incrementCLM_apply, increment_eq, increment_eq, h, h]

def ofBound (f : X → E) (hf : Continuous f) (M H : ℝ)
    (hM : ∀ x, ‖f x‖ ≤ M) (_hH : 0 ≤ H)
    (hh : ∀ x y, ‖f x - f y‖ ≤ H * dist x y ^ α) : Holder X E α := by
  let g : Pairs X → E := fun p => (dist p.val.1 p.val.2 ^ α)⁻¹ • (f p.val.1 - f p.val.2)
  have hg : Continuous g := by
    have hd : Continuous (fun p : Pairs X => dist p.val.1 p.val.2) :=
      (continuous_fst.comp continuous_subtype_val).dist
        (continuous_snd.comp continuous_subtype_val)
    exact ((hd.rpow_const (fun p => Or.inl (dist_ne_zero.mpr p.property))).inv₀
      (fun p => (Real.rpow_pos_of_pos (dist_pos.mpr p.property) α).ne')).smul
        ((hf.comp (continuous_fst.comp continuous_subtype_val)).sub
          (hf.comp (continuous_snd.comp continuous_subtype_val)))
  have hgM : ∀ p, ‖g p‖ ≤ H := by
    intro p
    have hp : 0 < dist p.val.1 p.val.2 ^ α := Real.rpow_pos_of_pos (dist_pos.mpr p.property) α
    dsimp [g]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
    calc
      _ ≤ (dist p.val.1 p.val.2 ^ α)⁻¹ * (H * dist p.val.1 p.val.2 ^ α) :=
        mul_le_mul_of_nonneg_left (hh _ _) (inv_nonneg.mpr hp.le)
      _ = H := by field_simp
  exact ⟨(BoundedContinuousFunction.ofNormedAddCommGroup f hf M hM,
    BoundedContinuousFunction.ofNormedAddCommGroup g hg H hgM),fun p => rfl⟩

@[simp] lemma ofBound_value (f : X → E) (hf : Continuous f) (M H : ℝ)
    (hM : ∀ x, ‖f x‖ ≤ M) (hH : 0 ≤ H)
    (hh : ∀ x y, ‖f x - f y‖ ≤ H * dist x y ^ α) (x : X) :
    valueCLM α (ofBound f hf M H hM hH hh) x = f x := rfl

lemma ofBound_norm_le (f : X → E) (hf : Continuous f) (M H : ℝ)
    (hM0 : 0 ≤ M) (hM : ∀ x, ‖f x‖ ≤ M) (hH : 0 ≤ H)
    (hh : ∀ x y, ‖f x - f y‖ ≤ H * dist x y ^ α) :
    ‖ofBound f hf M H hM hH hh‖ ≤ max M H := by
  change max _ _ ≤ max M H
  apply max_le_max
  · exact (BoundedContinuousFunction.norm_le hM0).mpr hM
  · apply (BoundedContinuousFunction.norm_le hH).mpr
    intro p
    have hp : 0 < dist p.val.1 p.val.2 ^ α := Real.rpow_pos_of_pos (dist_pos.mpr p.property) α
    change ‖(dist p.val.1 p.val.2 ^ α)⁻¹ • (f p.val.1 - f p.val.2)‖ ≤ H
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
    calc
      _ ≤ (dist p.val.1 p.val.2 ^ α)⁻¹ * (H * dist p.val.1 p.val.2 ^ α) :=
        mul_le_mul_of_nonneg_left (hh _ _) (inv_nonneg.mpr hp.le)
      _ = H := by field_simp

section LinearOperations
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def mapCLM (α : ℝ) (L : E →L[ℝ] F) : Holder X E α →L[ℝ] Holder X F α :=
  (((L.compLeftContinuousBounded X).prodMap (L.compLeftContinuousBounded (Pairs X))).comp
    (graph X E α).subtypeL).codRestrict (graph X F α) (by
      intro u p
      change L (u.val.2 p) = (dist p.val.1 p.val.2 ^ α)⁻¹ •
        (L (u.val.1 p.val.1) - L (u.val.1 p.val.2))
      rw [u.property p, map_smul, map_sub])

@[simp] lemma mapCLM_value (L : E →L[ℝ] F) (u : Holder X E α) (x : X) :
    valueCLM α (mapCLM α L u) x = L (valueCLM α u x) := rfl

def const (α : ℝ) (e : E) : Holder X E α :=
  ⟨(BoundedContinuousFunction.const X e, 0), by intro p; simp⟩

@[simp] lemma const_value (e : E) (x : X) : valueCLM α (const α e) x = e := rfl

end LinearOperations

section Bilinear
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma bilin_sub_bound (B : E →L[ℝ] F →L[ℝ] G)
    (u : Holder X E α) (v : Holder X F α) (x y : X) :
    ‖B (valueCLM α u x) (valueCLM α v x) - B (valueCLM α u y) (valueCLM α v y)‖ ≤
      (2 * ‖B‖ * ‖u‖ * ‖v‖) * dist x y ^ α := by
  have he : B (valueCLM α u x) (valueCLM α v x) - B (valueCLM α u y) (valueCLM α v y) =
    B (valueCLM α u x - valueCLM α u y) (valueCLM α v x) +
      B (valueCLM α u y) (valueCLM α v x - valueCLM α v y) := by
    simp only [map_sub, sub_apply]
    abel
  rw [he]
  calc
    _ ≤ ‖B (valueCLM α u x - valueCLM α u y) (valueCLM α v x)‖ +
        ‖B (valueCLM α u y) (valueCLM α v x - valueCLM α v y)‖ := norm_add_le _ _
    _ ≤ (‖B‖ * ‖valueCLM α u x - valueCLM α u y‖) * ‖valueCLM α v x‖ +
        (‖B‖ * ‖valueCLM α u y‖) * ‖valueCLM α v x - valueCLM α v y‖ :=
      add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
    _ ≤ (‖B‖ * (‖u‖ * dist x y ^ α)) * ‖v‖ +
        (‖B‖ * ‖u‖) * (‖v‖ * dist x y ^ α) := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_left (norm_sub_value_le u x y) (norm_nonneg B))
          (norm_value_le v x) (norm_nonneg _) (by positivity)
      · exact mul_le_mul (mul_le_mul_of_nonneg_left (norm_value_le u y) (norm_nonneg B))
          (norm_sub_value_le v x y) (norm_nonneg _) (by positivity)
    _ = _ := by ring

def bilin (B : E →L[ℝ] F →L[ℝ] G) (u : Holder X E α) (v : Holder X F α) : Holder X G α :=
  ofBound (fun x => B (valueCLM α u x) (valueCLM α v x))
    ((B.continuous.comp (valueCLM α u).continuous).clm_apply (valueCLM α v).continuous)
    (‖B‖ * ‖u‖ * ‖v‖) (2 * ‖B‖ * ‖u‖ * ‖v‖)
    (fun x => (B.le_opNorm₂ _ _).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (norm_value_le u x) (norm_nonneg B))
        (norm_value_le v x) (norm_nonneg _) (by positivity)))
    (by positivity) (bilin_sub_bound B u v)

@[simp] lemma bilin_value (B : E →L[ℝ] F →L[ℝ] G)
    (u : Holder X E α) (v : Holder X F α) (x : X) :
    valueCLM α (bilin B u v) x = B (valueCLM α u x) (valueCLM α v x) := rfl

lemma bilin_norm (B : E →L[ℝ] F →L[ℝ] G) (u : Holder X E α) (v : Holder X F α) :
    ‖bilin B u v‖ ≤ (2 * ‖B‖) * ‖u‖ * ‖v‖ := by
  unfold bilin
  refine (ofBound_norm_le _ _ _ _ (by positivity) _ _ _).trans ?_
  apply max_le
  · nlinarith [mul_nonneg (mul_nonneg (norm_nonneg B) (norm_nonneg u)) (norm_nonneg v)]
  · exact le_rfl

def bilinCLM (B : E →L[ℝ] F →L[ℝ] G) :
    Holder X E α →L[ℝ] Holder X F α →L[ℝ] Holder X G α :=
  LinearMap.mkContinuous₂
    { toFun := fun u =>
        { toFun := bilin B u
          map_add' := fun v w => by
            apply value_ext
            intro x
            simp only [bilin_value, map_add, BoundedContinuousFunction.add_apply]
          map_smul' := fun c v => by
            apply value_ext
            intro x
            simp only [bilin_value, map_smul, BoundedContinuousFunction.smul_apply,
              RingHom.id_apply] }
      map_add' := fun u v => by
        apply LinearMap.ext
        intro w
        apply value_ext
        intro x
        change valueCLM α (bilin B (u+v) w) x =
          valueCLM α (bilin B u w + bilin B v w) x
        simp only [bilin_value, map_add, BoundedContinuousFunction.add_apply, add_apply]
      map_smul' := fun c u => by
        apply LinearMap.ext
        intro v
        apply value_ext
        intro x
        change valueCLM α (bilin B (c • u) v) x = valueCLM α (c • bilin B u v) x
        simp only [bilin_value, map_smul, BoundedContinuousFunction.smul_apply, smul_apply] }
    (2 * ‖B‖) (bilin_norm B)

@[simp] lemma bilinCLM_value (B : E →L[ℝ] F →L[ℝ] G)
    (u : Holder X E α) (v : Holder X F α) (x : X) :
    valueCLM α (bilinCLM B u v) x = B (valueCLM α u x) (valueCLM α v x) := rfl

end Bilinear

variable (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D]

abbrev JetAmbient (α : ℝ) := Holder D E α × Holder D (D →L[ℝ] E) α

def jetGraph (α : ℝ) : Submodule ℝ (JetAmbient (E := E) D α) where
  carrier := {u | ∀ x, HasFDerivAt (valueCLM α u.1) (valueCLM α u.2 x) x}
  zero_mem' := by
    intro x
    convert! hasFDerivAt_const (𝕜 := ℝ) (0 : E) x using 1
    all_goals try with_reducible_and_instances rfl
  add_mem' := by
    intro u v hu hv x
    exact (hu x).add (hv x)
  smul_mem' := by
    intro c u hu x
    exact (hu x).const_smul c

abbrev COneHolder (α : ℝ) := jetGraph (E := E) D α

variable {D}

def jetValueCLM (α : ℝ) : COneHolder (E := E) D α →L[ℝ] Holder D E α :=
  (ContinuousLinearMap.fst ℝ _ _).comp (jetGraph (E := E) D α).subtypeL

def jetDerivCLM (α : ℝ) : COneHolder (E := E) D α →L[ℝ] Holder D (D →L[ℝ] E) α :=
  (ContinuousLinearMap.snd ℝ _ _).comp (jetGraph (E := E) D α).subtypeL

lemma hasFDerivAt (u : COneHolder (E := E) D α) (x : D) :
    HasFDerivAt (valueCLM α (jetValueCLM α u))
      (valueCLM α (jetDerivCLM α u) x) x := u.property x

lemma jetDeriv_norm_le (u : COneHolder (E := E) D α) : ‖jetDerivCLM α u‖ ≤ ‖u‖ :=
  le_max_right _ _

lemma jet_norm_deriv_le (u : COneHolder (E := E) D α) (x : D) :
    ‖valueCLM α (jetDerivCLM α u) x‖ ≤ ‖u‖ :=
  (norm_value_le _ _).trans (jetDeriv_norm_le u)

end
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions : NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions : NormedSpace ℝ (E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_1_rc955ba_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace

lemma norm_sub_le_of_deriv_bound {f : E → F} (hf : Differentiable ℝ f)
    {M : ℝ} (hM : ∀ x, ‖fderiv ℝ f x‖ ≤ M) (x y : E) :
    ‖f x - f y‖ ≤ M * ‖x - y‖ :=
  Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hf z)
    (fun z _ => hM z) convex_univ (mem_univ y) (mem_univ x)

local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_2_rc955ba_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions_2_rc955ba_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
structure BoundedCThree (f : E → F) : Prop where
  smooth : ContDiff ℝ ∞ f
  bounded : ∃ M : ℝ, 0 ≤ M ∧ (∀ x, ‖f x‖ ≤ M) ∧
    (∀ x, ‖fderiv ℝ f x‖ ≤ M) ∧
    (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) ∧
    (∀ x, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x‖ ≤ M)

namespace BoundedCThree
variable {f : E → F}

local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_1_rc955ba_2 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_2_rc955ba_2 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions_2_rc955ba_2 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
def bound (hf : BoundedCThree f) : ℝ := Classical.choose hf.bounded

lemma bound_nonneg (hf : BoundedCThree f) : 0 ≤ hf.bound :=
  (Classical.choose_spec hf.bounded).1

lemma norm_le (hf : BoundedCThree f) (x : E) : ‖f x‖ ≤ hf.bound :=
  (Classical.choose_spec hf.bounded).2.1 x

lemma norm_fderiv_le (hf : BoundedCThree f) (x : E) : ‖fderiv ℝ f x‖ ≤ hf.bound :=
  (Classical.choose_spec hf.bounded).2.2.1 x

lemma norm_fderiv₂_le (hf : BoundedCThree f) (x : E) :
    ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ hf.bound :=
  (Classical.choose_spec hf.bounded).2.2.2.1 x

lemma fderiv_smooth (hf : BoundedCThree f) : ContDiff ℝ ∞ (fderiv ℝ f) :=
  hf.smooth.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)

end BoundedCThree

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_NonlinearCR
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

 def ThirdHolderOn {X F : Type*} [NormedAddCommGroup X] [NormedAddCommGroup F]
    (f : X → F) (s : Set X) (H : ℝ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, ‖f x-f y‖ ≤ H*‖x-y‖^((1:ℝ)/3)

 theorem thirdHolderOn_of_bounded_lipschitz {X F : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup F]
    {f : X → F} {s : Set X} {A L : ℝ} (hA : 0≤A) (hL : 0≤L)
    (hb : ∀ x ∈ s, ‖f x‖ ≤ A) (hl : ∀ x ∈ s, ∀ y ∈ s, ‖f x-f y‖ ≤ L*‖x-y‖) :
    ThirdHolderOn f s (2*A+L) := by
  intro x hx y hy
  have hr : 0≤‖x-y‖^((1:ℝ)/3) := Real.rpow_nonneg (norm_nonneg _) _
  by_cases hd : ‖x-y‖≤1
  · have hh := Real.self_le_rpow_of_le_one (norm_nonneg (x-y)) hd (show (1:ℝ)/3≤1 by norm_num)
    exact (hl x hx y hy).trans ((mul_le_mul_of_nonneg_left hh hL).trans
      (mul_le_mul_of_nonneg_right (by linarith) hr))
  · have hh := Real.one_le_rpow (le_of_not_ge hd) (show (0:ℝ)≤1/3 by norm_num)
    have hnorm : ‖f x-f y‖ ≤ 2*A := (norm_sub_le _ _).trans (by linarith [hb x hx,hb y hy])
    have hmul := mul_le_mul_of_nonneg_left hh (show 0≤2*A+L by positivity)
    nlinarith

namespace HolderCompletion
variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev HMap (D E : Type*) [MetricSpace D] [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  Holder D E ((1:ℝ)/3)

abbrev COne (D E : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] := COneHolder (E := E) D ((1:ℝ)/3)

def ofBoundedDeriv (f : D → F) (hf : Differentiable ℝ f) (M L : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hval : ∀ x, ‖f x‖ ≤ M)
    (hder : ∀ x, ‖fderiv ℝ f x‖ ≤ L) : HMap D F :=
  ofBound f hf.continuous M (2*M+L) hval (by positivity) (by
    intro x y
    rw [dist_eq_norm]
    exact thirdHolderOn_of_bounded_lipschitz hM hL (fun z _ => hval z)
      (fun z _ w _ => norm_sub_le_of_deriv_bound hf hder z w) x (mem_univ x) y (mem_univ y))

@[simp] lemma ofBoundedDeriv_value (f : D → F) (hf : Differentiable ℝ f) (M L : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hval : ∀ x, ‖f x‖ ≤ M)
    (hder : ∀ x, ‖fderiv ℝ f x‖ ≤ L) (x : D) :
    valueCLM _ (ofBoundedDeriv f hf M L hM hL hval hder) x = f x := rfl

def cValue (u : COne D E) : D →ᵇ E := valueCLM _ (jetValueCLM _ u)
def cDeriv (u : COne D E) : D →ᵇ (D →L[ℝ] E) := valueCLM _ (jetDerivCLM _ u)

lemma c_hasFDerivAt (u : COne D E) (x : D) : HasFDerivAt (cValue u) (cDeriv u x) x :=
  hasFDerivAt u x

lemma c_differentiable (u : COne D E) : Differentiable ℝ (cValue u) :=
  fun x => (c_hasFDerivAt u x).differentiableAt

lemma c_deriv_bound (u : COne D E) (x : D) : ‖cDeriv u x‖ ≤ ‖u‖ := jet_norm_deriv_le u x

@[simp] lemma cValue_add (u v : COne D E) (x : D) : cValue (u+v) x = cValue u x+cValue v x := rfl
@[simp] lemma cValue_smul (c : ℝ) (u : COne D E) (x : D) : cValue (c • u) x = c • cValue u x := rfl

section Superposition
variable {f : E → F} (hf : BoundedCThree f)
  {b : D → E} (hb : Differentiable ℝ b) {B : ℝ} (hB : 0 ≤ B)
  (hbB : ∀ x, ‖fderiv ℝ b x‖ ≤ B)

include hb hbB in
lemma base_fderiv_bound (u : COne D E) (x : D) :
    ‖fderiv ℝ (fun z => b z+cValue u z) x‖ ≤ B + ‖u‖ := by
  have hd : HasFDerivAt (fun z => b z+cValue u z) (fderiv ℝ b x+cDeriv u x) x := by
    convert! (hb x).hasFDerivAt.add (c_hasFDerivAt u x) using 1
    all_goals try with_reducible_and_instances rfl
  rw [hd.fderiv]
  exact (norm_add_le _ _).trans (add_le_add (hbB x) (c_deriv_bound u x))

include hf hb in
lemma superpose_differentiable (u : COne D E) :
    Differentiable ℝ (fun z => f (b z+cValue u z)) :=
  (hf.smooth.differentiable (by simp)).comp (hb.add (c_differentiable u))

include hb hbB in
lemma superpose_fderiv_bound (u : COne D E) (x : D) :
    ‖fderiv ℝ (fun z => f (b z+cValue u z)) x‖ ≤ hf.bound * (B+‖u‖) := by
  have hd : HasFDerivAt (fun z => f (b z+cValue u z))
      ((fderiv ℝ f (b x+cValue u x)).comp (fderiv ℝ b x+cDeriv u x)) x := by
    convert! ((hf.smooth.differentiable (by simp) (b x+cValue u x)).hasFDerivAt.comp x
      ((hb x).hasFDerivAt.add (c_hasFDerivAt u x))) using 1
    all_goals try with_reducible_and_instances rfl
  rw [hd.fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (hf.norm_fderiv_le _) ((norm_add_le _ _).trans
      (add_le_add (hbB x) (c_deriv_bound u x))) (norm_nonneg _) hf.bound_nonneg)

def superpose (u : COne D E) : HMap D F :=
  ofBoundedDeriv (fun z => f (b z+cValue u z)) (superpose_differentiable hf hb u)
    hf.bound (hf.bound*(B+‖u‖)) hf.bound_nonneg
    (mul_nonneg hf.bound_nonneg (add_nonneg hB (norm_nonneg u)))
    (fun x => hf.norm_le (b x+cValue u x)) (superpose_fderiv_bound hf hb hbB u)

@[simp] lemma superpose_value (u : COne D E) (x : D) :
    valueCLM _ (superpose hf hb hB hbB u) x = f (b x+cValue u x) := rfl

include hf hb in
lemma coefficient_differentiable (u : COne D E) :
    Differentiable ℝ (fun z => fderiv ℝ f (b z+cValue u z)) :=
  (hf.fderiv_smooth.differentiable (by simp)).comp (hb.add (c_differentiable u))

include hb hbB in
lemma coefficient_fderiv_bound (u : COne D E) (x : D) :
    ‖fderiv ℝ (fun z => fderiv ℝ f (b z+cValue u z)) x‖ ≤ hf.bound * (B+‖u‖) := by
  have hd : HasFDerivAt (fun z => fderiv ℝ f (b z+cValue u z))
      ((fderiv ℝ (fderiv ℝ f) (b x+cValue u x)).comp
        (fderiv ℝ (fun z => b z+cValue u z) x)) x := by
    convert! ((hf.fderiv_smooth.differentiable (by simp) _).hasFDerivAt.comp x
      (((hb.add (c_differentiable u)) x).hasFDerivAt)) using 1
    all_goals try with_reducible_and_instances rfl
  rw [hd.fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (hf.norm_fderiv₂_le _) (base_fderiv_bound hb hbB u x)
      (norm_nonneg _) hf.bound_nonneg)

def coefficient (u : COne D E) : HMap D (E →L[ℝ] F) :=
  ofBoundedDeriv (fun z => fderiv ℝ f (b z+cValue u z))
    (coefficient_differentiable hf hb u) hf.bound (hf.bound*(B+‖u‖))
    hf.bound_nonneg (by positivity [hf.bound_nonneg])
    (fun x => hf.norm_fderiv_le _) (coefficient_fderiv_bound hf hb hbB u)

@[simp] lemma coefficient_value (u : COne D E) (x : D) :
    valueCLM _ (coefficient hf hb hB hbB u) x = fderiv ℝ f (b x+cValue u x) := rfl

def superposeDeriv (u : COne D E) : COne D E →L[ℝ] HMap D F :=
  (bilinCLM (ContinuousLinearMap.apply ℝ F).flip (coefficient hf hb hB hbB u)).comp
    (jetValueCLM _)

end Superposition
end HolderCompletion

end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
namespace HolderCompletion
variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
local instance jetCoeffInst1_rc955ba_1 : NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance jetCoeffInst3_rc955ba_1 : NormedAddCommGroup (D →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance jetCoeffInst5 : NormedAddCommGroup (D →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance jetCoeffInst2_rc955ba_1 : NormedSpace ℝ (E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
local instance jetCoeffInst4_rc955ba_1 : NormedSpace ℝ (D →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance jetCoeffInst6 : NormedSpace ℝ (D →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
local instance jetCoeffInst7 : NormedAddCommGroup (D →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance jetCoeffInst8 : NormedSpace ℝ (D →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_CompatibleStructures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HigherDimensionalBallPacking
open scoped ContDiff

noncomputable section
open scoped Topology
open Set Function Filter

namespace Rigidity

abbrev End (n : ℕ) := Phase n →L[ℝ] Phase n

def standardJ (n : ℕ) : End n :=
  (ContinuousLinearMap.lsmul ℝ ℂ) Complex.I

@[simp] theorem standardJ_apply (n : ℕ) (v : Phase n) (i : Fin n) :
    standardJ n v i = Complex.I * v i := rfl

@[simp] theorem standardJ_sq (n : ℕ) (v : Phase n) :
    standardJ n (standardJ n v) = -v := by
  funext i
  simp only [standardJ_apply, ← mul_assoc, Complex.I_mul_I, neg_one_mul, Pi.neg_apply]

@[simp] theorem standardForm_J_J {n : ℕ} (v w : Phase n) :
    standardForm (standardJ n v) (standardJ n w) = standardForm v w := by
  unfold standardForm
  apply Finset.sum_congr rfl
  intro i _
  simp [standardJ_apply, Complex.mul_re, Complex.mul_im]
  ring

@[simp] theorem standardForm_J_self {n : ℕ} (v : Phase n) :
    standardForm v (standardJ n v) = ∑ i, Complex.normSq (v i) := by
  unfold standardForm
  apply Finset.sum_congr rfl
  intro i _
  simp [standardJ_apply, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]

theorem standardForm_J_pos {n : ℕ} {v : Phase n} (hv : v ≠ 0) :
    0 < standardForm v (standardJ n v) := by
  rw [standardForm_J_self]
  have hi : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨i, hi⟩ := hi
  have hpos : 0 < Complex.normSq (v i) := Complex.normSq_pos.mpr hi
  exact hpos.trans_le (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j))
    (Finset.mem_univ i))

def Compatible {n : ℕ} (J : End n) : Prop :=
  (∀ v, J (J v) = -v) ∧
  (∀ v w, standardForm (J v) (J w) = standardForm v w) ∧
  (∀ v, v ≠ 0 → 0 < standardForm v (J v))

def conjugateJ {n : ℕ} (e : Phase n ≃L[ℝ] Phase n) : End n :=
  e.toContinuousLinearMap.comp ((standardJ n).comp e.symm.toContinuousLinearMap)

@[simp] theorem conjugateJ_apply {n : ℕ} (e : Phase n ≃L[ℝ] Phase n) (v : Phase n) :
    conjugateJ e v = e (standardJ n (e.symm v)) := rfl

def PseudoHolomorphicAt {n : ℕ} (J : Phase n → End n) (u : ℂ → Phase n) (z : ℂ) : Prop :=
  DifferentiableAt ℝ u z ∧ ∀ w : ℂ,
    fderiv ℝ u z (Complex.I * w) = J (u z) (fderiv ℝ u z w)

end Rigidity
end
end HigherDimensionalBallPacking

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity

def stdDot (n : ℕ) : Phase n →L[ℝ] Phase n →L[ℝ] ℝ :=
  ∑ i, ((ContinuousLinearMap.mul ℝ ℝ).bilinearComp
    (Complex.reCLM.comp (ContinuousLinearMap.proj i))
    (Complex.reCLM.comp (ContinuousLinearMap.proj i)) +
    (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
    (Complex.imCLM.comp (ContinuousLinearMap.proj i))
    (Complex.imCLM.comp (ContinuousLinearMap.proj i)))

@[simp] theorem stdDot_apply {n : ℕ} (v w : Phase n) :
    stdDot n v w = ∑ i, ((v i).re * (w i).re + (v i).im * (w i).im) := by
  simp [stdDot]

@[simp] theorem standardForm_J_right {n : ℕ} (v w : Phase n) :
    standardForm v (standardJ n w) = stdDot n v w := by
  simp [standardForm, stdDot_apply, standardJ_apply, Complex.mul_re, Complex.mul_im]

theorem stdDot_pos {n : ℕ} {v : Phase n} (hv : v ≠ 0) : 0 < stdDot n v v := by
  rw [← standardForm_J_right]
  exact standardForm_J_pos hv

@[simp] theorem standardForm_neg_right {n : ℕ} (v w : Phase n) :
    standardForm v (-w) = -standardForm v w := by
  unfold standardForm
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.neg_apply, Complex.neg_re, Complex.neg_im]
  ring

def relativeOperator {n : ℕ} (J : End n) : End n := -(standardJ n).comp J

@[simp] theorem relativeOperator_apply {n : ℕ} (J : End n) (v : Phase n) :
    relativeOperator J v = -standardJ n (J v) := rfl

@[simp] theorem standardJ_relativeOperator {n : ℕ} (J : End n) (v : Phase n) :
    standardJ n (relativeOperator J v) = J v := by simp

@[simp] theorem relativeOperator_J_relativeOperator {n : ℕ} {J : End n}
    (hJ : Compatible J) (v : Phase n) :
    relativeOperator J (standardJ n (relativeOperator J v)) = standardJ n v := by
  rw [standardJ_relativeOperator, relativeOperator_apply, hJ.1]
  simp

@[simp] theorem stdDot_relativeOperator {n : ℕ} (J : End n) (v w : Phase n) :
    stdDot n v (relativeOperator J w) = standardForm v (J w) := by
  rw [←standardForm_J_right, standardJ_relativeOperator]

theorem relativeOperator_positive {n : ℕ} {J : End n} (hJ : Compatible J)
    {v : Phase n} (hv : v ≠ 0) : 0 < stdDot n v (relativeOperator J v) := by
  rw [stdDot_relativeOperator]
  exact hJ.2.2 v hv

def cayleyP {n : ℕ} (J : End n) (a b : ℝ) : End n :=
  a • relativeOperator J + b • ContinuousLinearMap.id ℝ (Phase n)

@[simp] theorem cayleyP_apply {n : ℕ} (J : End n) (a b : ℝ) (v : Phase n) :
    cayleyP J a b v = a • relativeOperator J v + b • v := rfl

theorem cayleyP_invertible {n : ℕ} {J : End n} (hJ : Compatible J)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) : (cayleyP J b a).IsInvertible := by
  have hi : Injective (cayleyP J b a) := by
    apply (injective_iff_map_eq_zero (cayleyP J b a)).mpr
    intro v hv
    by_contra hne
    have hp := stdDot_pos hne
    have hA := relativeOperator_positive hJ hne
    have he : stdDot n v (cayleyP J b a v) =
        b * stdDot n v (relativeOperator J v) + a * stdDot n v v := by
      simp only [cayleyP_apply, map_add, map_smul, smul_eq_mul]
    rw [hv] at he
    simp only [map_zero] at he
    have hn := mul_nonneg hb hA.le
    have hh := mul_pos ha hp
    linarith
  have hs := (LinearMap.injective_iff_surjective (f := (cayleyP J b a).toLinearMap)).mp hi
  exact ⟨ContinuousLinearEquiv.ofBijective (cayleyP J b a)
    (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs), rfl⟩

def cayleyOperator {n : ℕ} (J : End n) (a b : ℝ) : End n :=
  (cayleyP J a b).comp (cayleyP J b a).inverse

theorem cayleyOperator_on_denominator {n : ℕ} {J : End n} {a b : ℝ}
    (hQ : (cayleyP J b a).IsInvertible) (v : Phase n) :
    cayleyOperator J a b (cayleyP J b a v) = cayleyP J a b v := by
  obtain ⟨e,he⟩ := hQ
  simp only [cayleyOperator, ←he, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

def interpolateJ {n : ℕ} (J : End n) (t : ℝ) : End n :=
  (standardJ n).comp (cayleyOperator J (1 + t) (1 - t))

@[simp] theorem interpolateJ_zero {n : ℕ} {J : End n} (hJ : Compatible J) :
    interpolateJ J 0 = standardJ n := by
  have hQ := cayleyP_invertible hJ (a := 1) (b := 1) (by norm_num) (by norm_num)
  obtain ⟨e,he⟩ := hQ
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨x,rfl⟩ := e.surjective v
  change standardJ n (cayleyOperator J (1+0) (1-0) ((e : End n) x)) = standardJ n ((e : End n) x)
  simp only [add_zero, sub_zero, he, cayleyOperator_on_denominator ⟨e,he⟩]

@[simp] theorem interpolateJ_one {n : ℕ} {J : End n} (hJ : Compatible J) :
    interpolateJ J 1 = J := by
  have hQ := cayleyP_invertible hJ (a := 2) (b := 0) (by norm_num) (by norm_num)
  obtain ⟨e,he⟩ := hQ
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨x,rfl⟩ := e.surjective v
  change standardJ n (cayleyOperator J (1+1) (1-1) ((e : End n) x)) = J ((e : End n) x)
  norm_num only [he, show (1:ℝ)+1=2 by norm_num, sub_self,
    cayleyOperator_on_denominator ⟨e,he⟩]
  simp

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_Adapted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology Manifold
open Set Function Filter


@[fun_prop]
theorem continuous_capacity (n : ℕ) : Continuous (capacity : Phase n → ℝ) := by
  unfold capacity
  fun_prop


end

section
open scoped ContDiff Topology
open Set Function Filter

def AffineLineCurve {n : ℕ} (J : Phase n → End n) (p q : Phase n)
    (u : ℂ → Phase n) : Prop :=
  ContDiff ℝ ∞ u ∧ (∀ z, PseudoHolomorphicAt J u z) ∧ u 0 = p ∧ u 1 = q ∧
    ∃ v : Phase n, v ≠ 0 ∧ Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 v)

def lineHomotopy {n : ℕ} (J : Phase n → End n) (t : ℝ) (x : Phase n) : End n :=
  interpolateJ (J x) t


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_RadialForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SymplecticBallPacking.Hamiltonian
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

abbrev Plane := ℝ × ℝ

end SymplecticBallPacking.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_MarkedJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def affine (p : E) (a : ℂ →L[ℝ] E) (z : ℂ) : E := p + a z


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_CompactFredholmAlternative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousLinearMap.FredholmPackage
open scoped _root_.ContinuousLinearMap _root_.ContinuousLinearMap.FredholmPackage
open Set Function

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {P : E →L[ℝ] F}

 def domCoords (pkg : _root_.ContinuousLinearMap.FredholmPackage P) : E ≃L[ℝ] (pkg.decDom.X₁ × pkg.decDom.X₀) :=
  (Submodule.prodEquivOfIsTopCompl _ _ pkg.decDom.isTopCompl).symm

 def codCoords (pkg : _root_.ContinuousLinearMap.FredholmPackage P) : F ≃L[ℝ] (pkg.decCodom.X₁ × pkg.decCodom.X₀) :=
  (Submodule.prodEquivOfIsTopCompl _ _ pkg.decCodom.isTopCompl).symm

 def finitePerturbation (pkg : _root_.ContinuousLinearMap.FredholmPackage P) (L : pkg.decDom.X₀ →L[ℝ] pkg.decCodom.X₀) : E →L[ℝ] F :=
  pkg.decCodom.X₀.subtypeL.comp (L.comp (pkg.decDom.X₀.projectionOntoL _ pkg.decDom.isTopCompl.symm))

 theorem finitePerturbation_coords (pkg : _root_.ContinuousLinearMap.FredholmPackage P)
    (L : pkg.decDom.X₀ →L[ℝ] pkg.decCodom.X₀) (x : E) :
    (codCoords pkg) ((P+finitePerturbation pkg L) x) =
      (pkg.equiv ((domCoords pkg) x).1,L ((domCoords pkg) x).2) := by
  apply (codCoords pkg).symm.injective
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  rw [add_apply]
  have he := congrArg (fun A : E →L[ℝ] F => A x) pkg.eq_equiv
  rw [he]
  simp only [finitePerturbation,domCoords,codCoords,ContinuousLinearEquiv.symm_symm,
    Submodule.prodEquivOfIsTopCompl_apply,Submodule.prodEquivOfIsTopCompl_symm_apply,
    ContinuousLinearMap.comp_apply,Submodule.coe_subtypeL,ContinuousLinearEquiv.coe_coe]
  rfl

end ContinuousLinearMap.FredholmPackage

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_SurjectiveParametricReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.OAI.ContinuousLinearMap.FredholmPackage

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter
open HolderCompletion
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

structure FiniteZeroGerm (F : ℝ × X → Y) (t : ℝ) (x : X) (m : ℕ) where
  kernelSpace : Submodule ℝ X
  finite_kernel : FiniteDimensional ℝ kernelSpace
  dimension : Module.finrank ℝ kernelSpace=m
  coordinate : X →L[ℝ] kernelSpace
  reconstruct : ℝ × kernelSpace → X
  base : reconstruct (t,coordinate x)=x
  smooth : ContDiffAt ℝ ∞ reconstruct (t,coordinate x)
  left_inv : ∀ v,coordinate (reconstruct v)=v.2
  zero : ∀ᶠ v in 𝓝 (t,coordinate x),F (v.1,reconstruct v)=0
  complete : ∀ᶠ v in 𝓝 (t,x),F v=0 → reconstruct (v.1,coordinate v.2)=v.2


end
open scoped Topology
open Set Function Filter



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moduli_ZeroCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

structure ZeroGraphChart (F : ℝ × X → Y) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  base : ℝ × X
  zero_base : F base=0
  coordinate : X →L[ℝ] E
  reconstruct : ℝ × E → X
  domain : Set (ℝ × E)
  ambient : Set (ℝ × X)
  domain_open : IsOpen domain
  ambient_open : IsOpen ambient
  base_domain : (base.1,coordinate base.2)∈domain
  base_ambient : base∈ambient
  smooth : ContDiffOn ℝ 2 reconstruct domain
  left_inv : ∀ v,coordinate (reconstruct v)=v.2
  zero : ∀ v∈domain,F (v.1,reconstruct v)=0
  image_ambient : ∀ v∈domain,(v.1,reconstruct v)∈ambient
  complete : ∀ v∈ambient,F v=0 → reconstruct (v.1,coordinate v.2)=v.2

omit [NormedSpace ℝ Y] in
lemma FiniteZeroGerm.graphChart [NormedSpace ℝ Y] {F : ℝ × X → Y} {t : ℝ} {x : X} {m : ℕ}
    (g : FiniteZeroGerm F t x m) (hz : F (t,x)=0) :
    ∃ c : ZeroGraphChart F g.kernelSpace,c.base=(t,x) ∧ c.coordinate=g.coordinate ∧ c.reconstruct=g.reconstruct := by
  let a : ℝ × g.kernelSpace := (t,g.coordinate x)
  let ψ : ℝ × g.kernelSpace → ℝ × X := fun q => (q.1,g.reconstruct q)
  have hψ : ContDiffAt ℝ ∞ ψ a := contDiffAt_fst.prodMk g.smooth
  obtain ⟨O,hOc,hOo,hOx⟩ := mem_nhds_iff.mp g.complete
  obtain ⟨S,hS,hSs⟩ := g.smooth.contDiffOn (m := 2) (WithTop.coe_le_coe.mpr le_top) (by norm_num)
  have hψa : ψ a=(t,x) := Prod.ext rfl g.base
  have hψO : ∀ᶠ q in 𝓝 a,ψ q∈O := hψ.continuousAt (hψa.symm ▸ hOo.mem_nhds hOx)
  obtain ⟨D,hD,hDo,hDa⟩ := mem_nhds_iff.mp (inter_mem hS (inter_mem g.zero hψO))
  refine ⟨{
    base := (t,x)
    zero_base := hz
    coordinate := g.coordinate
    reconstruct := g.reconstruct
    domain := D
    ambient := O
    domain_open := hDo
    ambient_open := hOo
    base_domain := hDa
    base_ambient := hOx
    smooth := hSs.mono (fun q hq => (hD hq).1)
    left_inv := g.left_inv
    zero := fun q hq => (hD hq).2.1
    image_ambient := fun q hq => (hD hq).2.2
    complete := fun v hv => hOc hv },rfl,rfl,rfl⟩

end
open scoped ContDiff Topology
open Set Function Filter



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end


