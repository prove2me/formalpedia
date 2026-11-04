-- Prove2me | Definitions.Def_FreeGroupFactorProof08
-- name    : FreeGroupFactorProof08
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T01:17:27.052497+00:00
-- url     : https://prove2.me/theorems/32081be6-becf-4278-b0d2-20747ccfab22
-- title:
--   Free group factors: supporting development, part 8
-- statement:
--   Part 8 of the supporting Lean development for the isomorphism of all interpolated free group factors. It contains the definitions (operators on free Fock spaces, Gaussian systems, weighted corner models, stabilization and amplification constructions, and the free-group word maps) that the statements of the published child theorems and of the main theorem's proof refer to, in source order, together with the proved lemmas their bodies rely on. No result is assumed.
--
--   **Formalization Note** Definitions of this development carry proof fields and `Classical.choose` terms, so their dependencies must be proved here rather than imported from theorems. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof07

set_option linter.all false

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15

open MeasureTheory Set CompactlySupported
open scoped ENNReal
namespace FreeGroupFactorMain.CyclicSpectral

section
variable {H : Type u_1} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
attribute [local instance] fgfLocalInst_46_0
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

end
section
open MeasureTheory
variable {H : Type u_2} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

end
section
variable {H : Type u_3} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)

end
open MeasureTheory
variable {H : Type u_4} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

end FreeGroupFactorMain.CyclicSpectral
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology ENNReal
namespace FreeGroupFactorMain.ProbabilityTransform

section
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]

end
section
open MeasureTheory ProbabilityTheory Set
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]

end
section
open MeasureTheory ProbabilityTheory Set Filter
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]

end
section
open MeasureTheory ProbabilityTheory Set Filter Function
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]

end
open MeasureTheory ProbabilityTheory Set Function Filter
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]

end FreeGroupFactorMain.ProbabilityTransform
namespace FreeGroupFactorMain.SpectralPullback
open MeasureTheory Function Filter
variable {X : Type u_5} {Y : Type u_6} [MeasurableSpace X] [MeasurableSpace Y]
variable (μ : Measure X) {f : X → Y} (e : MeasurableEmbedding f) [Nonempty X]

end FreeGroupFactorMain.SpectralPullback
namespace FreeGroupFactorMain.CyclicSpectral

section
open MeasureTheory ProbabilityTheory Set
variable {H : Type u_7} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

variable [IsProbabilityMeasure (measure A hA ξ)] [NullSingletonClass (measure A hA ξ)]

end
section
open MeasureTheory Set Function Filter
variable {H : Type u_8} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)
variable [IsProbabilityMeasure (measure A hA ξ)] [NullSingletonClass (measure A hA ξ)]

end
section
open MeasureTheory Set Function Filter
variable {H : Type u_9} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)
variable [IsProbabilityMeasure (measure A hA ξ)] [NullSingletonClass (measure A hA ξ)]

end
section
variable {H : Type u_10} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)

 theorem complexHom_composition (f : C(Space A,ℂ)) (q : C(ℂ,ℂ)) :
    complexHom A hA (q.comp f)=cfc q (complexHom A hA f) := by
  have he : cfc q f=q.comp f := by
    ext x
    have hh := (ContinuousMap.evalStarAlgHom ℂ ℂ x).map_cfc q f
      q.continuous.continuousOn (continuous_eval_const x)
    change cfc q f x=cfc q (f x) at hh
    rw [hh]
    exact cfc_algebraMap (A := ℂ) (f x) q
  rw [← he]
  exact (complexHom A hA).map_cfc q f q.continuous.continuousOn (complexHom_continuous A hA)

 theorem complexHom_composition_mem (f : C(Space A,ℂ)) (q : C(ℂ,ℂ))
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsClosed (S : Set (H →L[ℂ] H)))
    (hf : complexHom A hA f ∈ S) : complexHom A hA (q.comp f) ∈ S := by
  rw [complexHom_composition]
  apply StarSubalgebra.topologicalClosure_minimal (t := S) (by simpa) hS
    (cfc_mem_elemental _ _)

end
section
open MeasureTheory Set Function Filter

def scalarClip (R : ℝ) (z : ℂ) : ℂ := (max (-R) (min R z.re) : ℝ)
 theorem continuous_scalarClip (R : ℝ) : Continuous (scalarClip R) := by
  unfold scalarClip
  fun_prop
 theorem norm_scalarClip (R : ℝ) (hR : 0 ≤ R) (z : ℂ) : ‖scalarClip R z‖ ≤ R := by
  simp only [scalarClip,Complex.norm_real,Real.norm_eq_abs,abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
 theorem scalarClip_error (R x : ℝ) (hx : |x| ≤ R) (z : ℂ) :
    ‖scalarClip R z-(x:ℂ)‖ ≤ ‖z-(x:ℂ)‖ := by
  have hx' := abs_le.mp hx
  have he : |max (-R) (min R z.re)-x| ≤ |z.re-x| := by
    by_cases hz : z.re ≤ R
    · rw [min_eq_right hz]
      by_cases hl : -R ≤ z.re
      · rw [max_eq_right hl]
      · rw [max_eq_left (le_of_not_ge hl),abs_of_nonpos (by linarith)]
        exact (by linarith [neg_le_abs (z.re-x)])
    · rw [min_eq_left (le_of_not_ge hz),max_eq_right (by linarith),abs_of_nonneg (by linarith)]
      exact (by linarith [le_abs_self (z.re-x)])
  calc
    _ = |max (-R) (min R z.re)-x| := by
      rw [scalarClip,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    _ ≤ |z.re-x| := he
    _ ≤ _ := by simpa using Complex.abs_re_le_norm (z-(x:ℂ))

variable {H : Type u_11} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

def clipFunction (q : C(ℂ,ℂ)) : C(ℂ,ℂ) := ⟨scalarClip ‖A‖ ∘ q,(continuous_scalarClip ‖A‖).comp q.continuous⟩

 theorem clipFunction_norm (q : C(ℂ,ℂ)) (f : C(Space A,ℂ)) :
    ‖complexHom A hA ((clipFunction A q).comp f)‖ ≤ ‖A‖ := by
  apply (NonUnitalStarAlgHom.norm_apply_le _ _).trans
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro x
  exact norm_scalarClip ‖A‖ (norm_nonneg _) _
end
open MeasureTheory Set Function Filter
variable {H : Type u_12} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)
variable [IsProbabilityMeasure (measure A hA ξ)] [NullSingletonClass (measure A hA ξ)]

def coordinate : C(Space A,ℂ) := complexLift A ((ContinuousMap.id ℝ).restrict (spectrum ℝ A))
omit [Nontrivial H] in
 theorem complexHom_coordinate : complexHom A hA (coordinate A)=A := by
  rw [coordinate,complexHom_real,cfcHom_id]

omit [IsProbabilityMeasure (measure A hA ξ)] [NullSingletonClass (measure A hA ξ)] in
 theorem clip_vector_error (q : C(ℂ,ℂ)) (f : C(Space A,ℂ)) :
    ‖complexHom A hA ((clipFunction A q).comp f) ξ-A ξ‖ ≤
      ‖complexHom A hA (q.comp f) ξ-A ξ‖ := by
  have hc : A ξ=complexHom A hA (coordinate A) ξ :=
    congrArg (fun T : H →L[ℂ] H => T ξ) (complexHom_coordinate A hA).symm
  rw [hc]
  have heval (g : C(Space A,ℂ)) : complexEvaluate A hA ξ (g-coordinate A)=
      complexHom A hA g ξ-complexHom A hA (coordinate A) ξ := by
    simp [complexEvaluate]
  rw [← heval,← heval]
  rw [complexEvaluate_norm,complexEvaluate_norm]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) (measure A hA ξ)
      (((clipFunction A q).comp f)-coordinate A),
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) (measure A hA ξ) (q.comp f-coordinate A)] with x h1 h2
  rw [h1,h2]
  apply scalarClip_error
  change |(x:ℝ)| ≤ ‖A‖
  simpa only [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem x.property

 theorem bounded_haar_approx (ε : ℝ) (hε : 0 < ε) :
    ∃ T : H →L[ℂ] H,
      T ∈ StarAlgebra.elemental ℂ (haarUnitary A hA ξ : H →L[ℂ] H) ∧
      ‖T‖ ≤ ‖A‖ ∧ ‖T ξ-A ξ‖ < ε := by
  obtain ⟨v,⟨q,rfl⟩,hq⟩ := Metric.mem_closure_iff.mp
    (haar_cyclic_contains_operator A hA ξ) ε hε
  refine ⟨complexHom A hA ((clipFunction A q.toContinuousMap).comp (haarFunction A hA ξ)),?_,
    clipFunction_norm A hA _ _,?_⟩
  · apply complexHom_composition_mem
    · exact StarAlgebra.elemental.isClosed _ _
    · exact StarAlgebra.elemental.self_mem _ _
  · exact (clip_vector_error A hA ξ _ _).trans_lt (by simpa only [dist_eq_norm,norm_sub_rev] using hq)
end FreeGroupFactorMain.CyclicSpectral
namespace FreeGroupFactorMain
open Filter Topology
variable {E : Type u_13} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem strong_limit_of_bounded_total {ι : Type u_14}
    (T : ℕ → E →L[ℂ] E) (A : E →L[ℂ] E) (C : ℝ) (hbound : ∀ n, ‖T n‖ ≤ C)
    (v : ι → E) (htotal : (Submodule.span ℂ (Set.range v)).topologicalClosure=⊤)
    (hv : ∀ i, Tendsto (fun n => T n (v i)) atTop (𝓝 (A (v i))))
    (ξ : E) : Tendsto (fun n => T n ξ) atTop (𝓝 (A ξ)) := by
  have heq : Equicontinuous (fun n => (T n : E → E)) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => C*r)
      (by simpa using (tendsto_const_nhds.mul (tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0))))
    intro x y n
    rw [dist_eq_norm,← map_sub]
    exact (T n).le_opNorm (x-y) |>.trans
      (by simpa only [dist_eq_norm] using mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg (x-y)))
  let L : Submodule ℂ E := {
    carrier := {ξ | Tendsto (fun n => T n ξ) atTop (𝓝 (A ξ))}
    zero_mem' := by simp
    add_mem' := by
      intro x y hx hy
      simpa only [Set.mem_ofPred_eq,map_add] using hx.add hy
    smul_mem' := by
      intro c x hx
      simpa only [Set.mem_ofPred_eq,map_smul] using hx.const_smul c }
  have hclosed : IsClosed (L : Set E) := heq.isClosed_setOfPred_tendsto A.continuous
  have hle : Submodule.span ℂ (Set.range v) ≤ L :=
    Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact hv i)
  have hh := Submodule.topologicalClosure_minimal _ hle hclosed
  rw [htotal] at hh
  exact hh (Submodule.mem_top)
end FreeGroupFactorMain

namespace FreeGroupFactorMain.CyclicSpectral
open Filter Topology Set MeasureTheory
variable {E : Type u_15} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
variable (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (ξ : E)
variable [IsProbabilityMeasure (measure A hA ξ)] [NullSingletonClass (measure A hA ξ)]

theorem operator_mem_haar_bicommutant (M : StarSubalgebra ℂ (E →L[ℂ] E))
    (hM : IsClosed (M : Set (E →L[ℂ] E))) (hAM : A∈M)
    (htotal : (Submodule.span ℂ (Set.range (fun B : StarSubalgebra.centralizer ℂ (M : Set (E →L[ℂ] E)) =>
      (B : E →L[ℂ] E) ξ))).topologicalClosure=⊤) :
    A ∈ StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ
      ({(haarUnitary A hA ξ : E →L[ℂ] E)} : Set (E →L[ℂ] E)) : Set (E →L[ℂ] E)) := by
  have hU : (haarUnitary A hA ξ : E →L[ℂ] E)∈M := by
    exact complexHom_mem A hA M hM hAM _
  have hb (n : ℕ) := bounded_haar_approx A hA ξ (1/((n:ℝ)+1)) (by positivity)
  choose T hmem hnorm herr using hb
  have hT (n : ℕ) : T n∈M := StarAlgebra.elemental.le_of_mem hM hU (hmem n)
  have hv : Tendsto (fun n => T n ξ) atTop (𝓝 (A ξ)) := by
    have h := squeeze_zero_norm (fun n => (herr n).le)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [sub_add_cancel,zero_add] using h.add_const (A ξ)
  have hstrong : ∀ ζ, Tendsto (fun n => T n ζ) atTop (𝓝 (A ζ)) := by
    apply strong_limit_of_bounded_total T A ‖A‖ hnorm _ htotal
    intro B
    have hB (D : E →L[ℂ] E) (hD : D∈M) : D ((B : E →L[ℂ] E) ξ)=(B : E →L[ℂ] E) (D ξ) :=
      DFunLike.congr_fun (((StarSubalgebra.mem_centralizer_iff ℂ).mp B.property D hD).1) ξ
    simpa only [hB _ (hT _),hB _ hAM,Function.comp_def] using
      (B : E →L[ℂ] E).continuous.continuousAt.tendsto.comp hv
  let N := StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ
      ({(haarUnitary A hA ξ : E →L[ℂ] E)} : Set (E →L[ℂ] E)) : Set (E →L[ℂ] E))
  have hN : IsClosed (N : Set (E →L[ℂ] E)) := Set.isClosed_centralizer _
  have hUN : (haarUnitary A hA ξ : E →L[ℂ] E)∈N :=
    StarAlgebra.adjoin_le_centralizer_centralizer ℂ _ (StarAlgebra.subset_adjoin ℂ _ (Set.mem_singleton _))
  have hTN (n : ℕ) : T n∈N := StarAlgebra.elemental.le_of_mem hN hUN (hmem n)
  rw [StarSubalgebra.mem_centralizer_iff]
  intro B hB
  have hb' (D : E →L[ℂ] E) (hD : D∈StarSubalgebra.centralizer ℂ
      ({(haarUnitary A hA ξ : E →L[ℂ] E)} : Set (E →L[ℂ] E))) : D*A=A*D := by
    ext ζ
    have he n := congrArg (fun Q : E →L[ℂ] E => Q ζ)
      ((StarSubalgebra.mem_centralizer_iff ℂ).mp (hTN n) D hD).1
    exact tendsto_nhds_unique ((D.continuous.continuousAt.tendsto.comp (hstrong ζ)).congr
      (fun n => he n)) (hstrong (D ζ))
  exact ⟨hb' B hB,hb' (star B) (star_mem hB)⟩
end FreeGroupFactorMain.CyclicSpectral

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

namespace FreeGroupFactorMain.CyclicSpectral
open MeasureTheory ProbabilityTheory Set
variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (ξ : E)
variable [IsProbabilityMeasure (measure A hA ξ)] [NullSingletonClass (measure A hA ξ)]

abbrev UniformAlgebra := C(Icc (0:ℝ) 1,ℂ)

def cdfMap : C(Space A,Icc (0:ℝ) 1) :=
  ⟨fun x => ⟨cdf (realMeasure A hA ξ) x,cdf_nonneg _ _,cdf_le_one _ _⟩,
    ((ProbabilityTransform.continuous_cdf (realMeasure A hA ξ)).comp
      continuous_subtype_val).subtype_mk _⟩

def uniformHom : UniformAlgebra →⋆ₐ[ℂ] (E →L[ℂ] E) :=
  (complexHom A hA).comp (ContinuousMap.compStarAlgHom' ℂ ℂ (cdfMap A hA ξ))

def uniformState (f : UniformAlgebra) : ℂ :=
  ∫ x:ℝ, f (projIcc 0 1 (by norm_num) x) ∂volume.restrict (Icc (0:ℝ) 1)

theorem uniformHom_state (f : UniformAlgebra) :
    inner ℂ ξ (uniformHom A hA ξ f ξ)=uniformState f := by
  let g : ℝ → ℂ := fun x => f (projIcc 0 1 (by norm_num) x)
  have hg : Continuous g := f.continuous.comp continuous_projIcc
  have he (x : ℝ) : g (cdf (realMeasure A hA ξ) x)=f ⟨cdf (realMeasure A hA ξ) x,
      cdf_nonneg _ _,cdf_le_one _ _⟩ := by
    dsimp only [g]
    congr 1
    exact projIcc_of_mem (by norm_num) ⟨cdf_nonneg _ _,cdf_le_one _ _⟩
  have hi := integral_map (μ := measure A hA ξ) measurable_subtype_coe.aemeasurable
    (hg.comp (ProbabilityTransform.continuous_cdf (realMeasure A hA ξ))).aestronglyMeasurable
  have hj := integral_map (μ := realMeasure A hA ξ)
    (ProbabilityTransform.continuous_cdf (realMeasure A hA ξ)).aemeasurable hg.aestronglyMeasurable
  rw [ProbabilityTransform.map_cdf] at hj
  rw [uniformHom,StarAlgHom.comp_apply,← integral_complex]
  calc
    _ = ∫ x : Space A, g (cdf (realMeasure A hA ξ) x) ∂measure A hA ξ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (he x).symm
    _ = ∫ x : ℝ, g (cdf (realMeasure A hA ξ) x) ∂realMeasure A hA ξ := hi.symm
    _ = uniformState f := hj.symm

def uniformPhase : UniformAlgebra :=
  ⟨fun x => ProbabilityTransform.phase x,ProbabilityTransform.phase_continuous.comp continuous_subtype_val⟩

theorem uniformHom_phase : uniformHom A hA ξ uniformPhase=(haarUnitary A hA ξ : E →L[ℂ] E) := rfl

theorem uniformHom_mem (M : StarSubalgebra ℂ (E →L[ℂ] E))
    (hM : IsClosed (M : Set (E →L[ℂ] E))) (hAM : A∈M) (f : UniformAlgebra) :
    uniformHom A hA ξ f∈M := complexHom_mem A hA M hM hAM _
end FreeGroupFactorMain.CyclicSpectral

section
open scoped ENNReal

namespace FreeGroupFactorMain.CyclicSpectral

section
open MeasureTheory
variable {H : Type u_2} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance fgfLocalInst_47_8 : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

def evaluate : C(Space A,ℝ) →ₗ[ℝ] H :=
  (((ContinuousLinearMap.apply ℂ H ξ).restrictScalars ℝ).comp (cfcL hA)).toLinearMap

 theorem evaluate_norm (f : C(Space A,ℝ)) :
    ‖evaluate A hA ξ f‖=‖ContinuousMap.toLp 2 (measure A hA ξ) ℝ f‖ := by
  have hs : ‖evaluate A hA ξ f‖^2=‖ContinuousMap.toLp 2 (measure A hA ξ) ℝ f‖^2 := by
    calc
      _ = ∫ x, (f x)^2 ∂measure A hA ξ := (integral_sq A hA ξ f).symm
      _ = inner ℝ (ContinuousMap.toLp 2 (measure A hA ξ) ℝ f)
          (ContinuousMap.toLp 2 (measure A hA ξ) ℝ f) := by
        rw [MeasureTheory.ContinuousMap.inner_toLp]
        congr 1
        funext x
        simp only [pow_two,RCLike.conj_to_real]
      _ = _ := real_inner_self_eq_norm_sq _
  nlinarith [norm_nonneg (evaluate A hA ξ f),norm_nonneg (ContinuousMap.toLp 2 (measure A hA ξ) ℝ f)]

def realize : Lp ℝ 2 (measure A hA ξ) →L[ℝ] H :=
  (evaluate A hA ξ).extendOfNorm (ContinuousMap.toLp 2 (measure A hA ξ) ℝ).toLinearMap

 theorem realize_continuous (f : C(Space A,ℝ)) :
    realize A hA ξ (ContinuousMap.toLp 2 (measure A hA ξ) ℝ f)=cfcHom hA f ξ := by
  apply LinearMap.extendOfNorm_eq
  · exact ContinuousMap.toLp_denseRange ℝ (measure A hA ξ) ℝ (p := 2) (by norm_num)
  · refine ⟨1,fun g => ?_⟩
    change ‖evaluate A hA ξ g‖ ≤ 1 * ‖ContinuousMap.toLp 2 (measure A hA ξ) ℝ g‖
    rw [one_mul,evaluate_norm]

 theorem realize_norm (f : Lp ℝ 2 (measure A hA ξ)) : ‖realize A hA ξ f‖=‖f‖ := by
  have hd := ContinuousMap.toLp_denseRange ℝ (measure A hA ξ) ℝ (p := 2) (by norm_num : (2:ℝ≥0∞)≠∞)
  refine hd.induction_on (p := fun f => ‖realize A hA ξ f‖=‖f‖) f
    (isClosed_eq ((realize A hA ξ).continuous.norm) continuous_norm) ?_
  intro q
  rw [realize_continuous]
  exact evaluate_norm A hA ξ q

def isometry : Lp ℝ 2 (measure A hA ξ) →ₗᵢ[ℝ] H where
  toLinearMap := (realize A hA ξ).toLinearMap
  norm_map' := realize_norm A hA ξ

end
section
open MeasureTheory Filter
variable {H : Type u_3} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance fgfLocalInst_47_15 : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

 theorem mul_memLp (g : C(Space A,ℝ)) (f : Lp ℝ 2 (measure A hA ξ)) :
    MemLp (fun x => g x*f x) 2 (measure A hA ξ) := by
  apply (Lp.memLp f).of_le_mul (c := ‖g‖)
  · exact g.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  · exact Eventually.of_forall (fun x => by rw [norm_mul];exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm x) (norm_nonneg _))

def multiply (g : C(Space A,ℝ)) : Lp ℝ 2 (measure A hA ξ) →L[ℝ] Lp ℝ 2 (measure A hA ξ) :=
  LinearMap.mkContinuous
  { toFun := fun f => (mul_memLp A hA ξ g f).toLp (fun x => g x*f x)
    map_add' := by
      intro f k
      apply Lp.ext
      filter_upwards [(mul_memLp A hA ξ g (f+k)).coeFn_toLp,
        (mul_memLp A hA ξ g f).coeFn_toLp,(mul_memLp A hA ξ g k).coeFn_toLp,
        Lp.coeFn_add f k,Lp.coeFn_add ((mul_memLp A hA ξ g f).toLp _) ((mul_memLp A hA ξ g k).toLp _)] with x h₁ h₂ h₃ h₄ h₅
      simp only [h₁,h₅,Pi.add_apply,h₂,h₃,h₄]
      exact mul_add _ _ _
    map_smul' := by
      intro c f
      apply Lp.ext
      filter_upwards [(mul_memLp A hA ξ g (c • f)).coeFn_toLp,
        (mul_memLp A hA ξ g f).coeFn_toLp,Lp.coeFn_smul c f,
        Lp.coeFn_smul c ((mul_memLp A hA ξ g f).toLp _)] with x h₁ h₂ h₃ h₄
      simp only [RingHom.id_apply,h₁,h₄,Pi.smul_apply,smul_eq_mul,h₂,h₃]
      ring }
  ‖g‖ (by
    intro f
    change ‖(mul_memLp A hA ξ g f).toLp (fun x => g x*f x)‖ ≤ ‖g‖ * ‖f‖
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(mul_memLp A hA ξ g f).coeFn_toLp] with x hx
    rw [hx,norm_mul]
    exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm x) (norm_nonneg _))

 theorem multiply_ae (g : C(Space A,ℝ)) (f : Lp ℝ 2 (measure A hA ξ)) :
    multiply A hA ξ g f =ᵐ[measure A hA ξ] (fun x => g x*f x) :=
  (mul_memLp A hA ξ g f).coeFn_toLp

 theorem multiply_continuous (g f : C(Space A,ℝ)) :
    multiply A hA ξ g (ContinuousMap.toLp 2 (measure A hA ξ) ℝ f)=
      ContinuousMap.toLp 2 (measure A hA ξ) ℝ (g*f) := by
  apply Lp.ext
  filter_upwards [multiply_ae A hA ξ g (ContinuousMap.toLp 2 (measure A hA ξ) ℝ f),
    f.coeFn_toLp (𝕜 := ℝ) (p := 2) (measure A hA ξ),
    (g*f).coeFn_toLp (𝕜 := ℝ) (p := 2) (measure A hA ξ)] with x h₁ h₂ h₃
  rw [h₁,h₂,h₃]
  rfl

 theorem realize_multiply (g : C(Space A,ℝ)) (f : Lp ℝ 2 (measure A hA ξ)) :
    realize A hA ξ (multiply A hA ξ g f)=cfcHom hA g (realize A hA ξ f) := by
  have hd := ContinuousMap.toLp_denseRange ℝ (measure A hA ξ) ℝ (p := 2) (by norm_num : (2:ℝ≥0∞)≠∞)
  refine hd.induction_on (p := fun f => realize A hA ξ (multiply A hA ξ g f)=cfcHom hA g (realize A hA ξ f)) f (isClosed_eq ((realize A hA ξ).continuous.comp (multiply A hA ξ g).continuous)
    ((cfcHom hA g).continuous.comp (realize A hA ξ).continuous)) ?_
  intro q
  rw [multiply_continuous,realize_continuous,realize_continuous,map_mul,mul_apply_eq_comp]

 theorem realize_coordinate (f : Lp ℝ 2 (measure A hA ξ)) :
    realize A hA ξ (multiply A hA ξ ((ContinuousMap.id ℝ).restrict (spectrum ℝ A)) f)=
      A (realize A hA ξ f) := by
  rw [realize_multiply,cfcHom_id]

end
open MeasureTheory Filter
variable {H : Type u_4} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance fgfLocalInst_47_22 : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

def atom (x : Space A) : Lp ℝ 2 (measure A hA ξ) :=
  indicatorConstLp 2 (measurableSet_singleton x) (measure_ne_top _ _) (1:ℝ)

 theorem atom_ae (x : Space A) :
    atom A hA ξ x =ᵐ[measure A hA ξ] ({x} : Set (Space A)).indicator (fun _ => (1:ℝ)) :=
  indicatorConstLp_coeFn

 theorem multiply_atom (x : Space A) :
    multiply A hA ξ ((ContinuousMap.id ℝ).restrict (spectrum ℝ A)) (atom A hA ξ x)=
      (x:ℝ) • atom A hA ξ x := by
  classical
  apply Lp.ext
  filter_upwards [multiply_ae A hA ξ ((ContinuousMap.id ℝ).restrict (spectrum ℝ A)) (atom A hA ξ x),
    atom_ae A hA ξ x,Lp.coeFn_smul (x:ℝ) (atom A hA ξ x)] with y h₁ h₂ h₃
  rw [h₁,h₃]
  change (y:ℝ)*atom A hA ξ x y=(x:ℝ)*atom A hA ξ x y
  rw [h₂]
  by_cases hy : y=x
  · subst y; rfl
  · simp [Set.indicator_of_notMem,hy]

 theorem realize_atom_eigen (x : Space A) :
    A (realize A hA ξ (atom A hA ξ x))=(x:ℝ) • realize A hA ξ (atom A hA ξ x) := by
  rw [← realize_coordinate,multiply_atom,map_smul]

 theorem realize_one : realize A hA ξ (ContinuousMap.toLp 2 (measure A hA ξ) ℝ (1:C(Space A,ℝ)))=ξ := by
  rw [realize_continuous,map_one,one_apply_eq_self]

 theorem realize_atom_inner (x : Space A) :
    inner ℝ ξ (realize A hA ξ (atom A hA ξ x))=(measure A hA ξ).real {x} := by
  have hm := (isometry A hA ξ).inner_map_map
    (ContinuousMap.toLp 2 (measure A hA ξ) ℝ (1:C(Space A,ℝ))) (atom A hA ξ x)
  change inner ℝ (realize A hA ξ (ContinuousMap.toLp 2 (measure A hA ξ) ℝ (1:C(Space A,ℝ))))
    (realize A hA ξ (atom A hA ξ x))=_ at hm
  rw [realize_one] at hm
  rw [hm,real_inner_comm]
  change inner ℝ (indicatorConstLp 2 (measurableSet_singleton x) (measure_ne_top _ _) (1:ℝ))
    (ContinuousMap.toLp 2 (measure A hA ξ) ℝ (1:C(Space A,ℝ)))=_
  rw [L2.inner_indicatorConstLp_one]
  calc
    _ = ∫ _ in ({x}:Set (Space A)), (1:ℝ) ∂measure A hA ξ := by
      apply setIntegral_congr_ae (measurableSet_singleton x)
      exact ((1:C(Space A,ℝ)).coeFn_toLp (𝕜 := ℝ) (p := 2) (measure A hA ξ)).mono (fun y hy _ => hy)
    _ = _ := by simp [Measure.real]

 theorem singleton_eq_zero (x : Space A)
    (he : ∀ η : H, A η=(x:ℝ) • η → inner ℝ ξ η=0) : measure A hA ξ {x}=0 := by
  have hm : (measure A hA ξ).real {x}=0 :=
    (realize_atom_inner A hA ξ x).symm.trans (he _ (realize_atom_eigen A hA ξ x))
  exact (ENNReal.toReal_eq_zero_iff _).mp hm |>.resolve_right (measure_ne_top _ _)

 theorem noAtoms (he : ∀ (r:ℝ) (η:H), A η=r • η → inner ℝ ξ η=0) :
    NullSingletonClass (measure A hA ξ) := by
  constructor
  intro x
  exact singleton_eq_zero A hA ξ x (he x)

end FreeGroupFactorMain.CyclicSpectral

end

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock Amplification MeasureTheory CyclicSpectral

instance oldBaseOp_probability (u v : ℝ) :
    IsProbabilityMeasure (measure (oldBaseOp u v (0:ℕ) 1) (oldBaseOp_selfAdjoint u v 0 1) pRoot) :=
  probability _ _ _ pRoot_norm

theorem oldBaseOp_noAtoms (u v : ℝ) (hv : 0<v) (hvu : v<u) :
    NullSingletonClass (measure (oldBaseOp u v (0:ℕ) 1) (oldBaseOp_selfAdjoint u v 0 1) pRoot) := by
  let : InnerProductSpace ℝ (PRange ℕ) := InnerProductSpace.rclikeToReal ℂ (PRange ℕ)
  apply noAtoms
  intro r η hη
  have he : oldBaseOp u v (0:ℕ) 1 η=(r:ℂ) • η := by
    exact hη.trans (by
      apply Subtype.ext
      apply Subtype.ext
      funext w
      change r • (η:H ℕ) w=(r:ℂ)*(η:H ℕ) w
      exact Complex.real_smul)
  have hh := oldBaseOp_eigen_root_zero u v hv hvu (0:ℕ) 1 (r:ℂ) η he
  change (inner ℂ (pRoot:PRange ℕ) η).re=0
  rw [hh,Complex.zero_re]

variable (u v : ℝ)

def weightedUniform (hv : 0<v) (hvu : v<u) : UniformAlgebra →⋆ₐ[ℂ] (PRange ℕ →L[ℂ] PRange ℕ) := by
  letI := oldBaseOp_noAtoms u v hv hvu
  exact uniformHom (oldBaseOp u v (0:ℕ) 1) (oldBaseOp_selfAdjoint u v 0 1) pRoot

def representedBase : StarSubalgebra ℂ (PRange ℕ →L[ℂ] PRange ℕ) :=
  (Base u v).comap (pRepresentation (ι := ℕ)).symm.toStarAlgHom

theorem pRepresentation_symm_val (T : PRange ℕ →L[ℂ] PRange ℕ) :
    ((pRepresentation (ι := ℕ)).symm T : Operator ℕ)=
      (PRange ℕ).subtypeL.comp (T.comp pProject) := by
  apply ContinuousLinearMap.ext
  intro ξ
  have he := pRepresentation_apply ((pRepresentation (ι := ℕ)).symm T) (pProject ξ)
  rw [StarAlgEquiv.apply_symm_apply,pProject_val] at he
  have hr := DFunLike.congr_fun ((pRepresentation (ι := ℕ)).symm T).property.2 ξ
  exact hr.symm.trans he.symm

theorem pRepresentation_symm_coe_continuous :
    Continuous (fun T : PRange ℕ →L[ℂ] PRange ℕ => ((pRepresentation (ι := ℕ)).symm T : Operator ℕ)) := by
  simp_rw [pRepresentation_symm_val]
  exact continuous_const.clm_comp (continuous_id.clm_comp continuous_const)

theorem representedBase_closed : IsClosed (representedBase u v : Set (PRange ℕ →L[ℂ] PRange ℕ)) := by
  have hF : IsClosed (filledEdgeAlgebra u v (0:ℕ) 1 : Set (Operator ℕ)) := Set.isClosed_centralizer _
  exact hF.preimage pRepresentation_symm_coe_continuous

theorem oldBaseOp_mem_representedBase (hv : 0<v) (hvu : v<u) : oldBaseOp u v (0:ℕ) 1∈representedBase u v := by
  change ((pRepresentation (ι := ℕ)).symm (pRepresentation (oldBaseCorner u v 0 1)))∈Base u v
  rw [StarAlgEquiv.symm_apply_apply]
  exact diffuseBase_le_filled u v (hv.trans hvu).ne' (0:ℕ) 1 (oldBaseGenerator_mem_diffuseBase u v 0 1)

theorem weightedUniform_mem (hv : 0<v) (hvu : v<u) (a : UniformAlgebra) : weightedUniform u v hv hvu a∈representedBase u v := by
  let := oldBaseOp_noAtoms u v hv hvu
  exact uniformHom_mem _ _ _ _ (representedBase_closed u v) (oldBaseOp_mem_representedBase u v hv hvu) a

def weightedUniformBase (hv : 0<v) (hvu : v<u) : UniformAlgebra →⋆ₐ[ℂ] Base u v :=
  (((pRepresentation (ι := ℕ)).symm.toStarAlgHom).comp (weightedUniform u v hv hvu)).codRestrict
    (Base u v) (fun a => by
      simpa only [representedBase, StarSubalgebra.mem_comap, StarAlgHom.comp_apply] using
        (weightedUniform_mem u v hv hvu a))

theorem weightedUniform_state (hv : 0<v) (hvu : v<u) (a : UniformAlgebra) :
    inner ℂ (pRoot:PRange ℕ) (weightedUniform u v hv hvu a pRoot)=uniformState a := by
  let := oldBaseOp_noAtoms u v hv hvu
  exact uniformHom_state _ _ _ a

end

open FreeFock Amplification
variable {ι : Type u_5} [DecidableEq ι]

end FreeGroupFactorMain.WeightedFock

end

end OAI
end


