-- Prove2me | Definitions.Def_OAIHecke78B020
-- name    : OAIHecke78B020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T01:50:54.48538+00:00
-- url     : https://prove2.me/theorems/427621b3-3e80-4d5d-808d-4229a5a731af
-- title:
--   OpenAI Hecke 7/8 split, definitions bundle 21 of 29
-- statement:
--   Definitions bundle 21 of 29 of the split of OpenAI's proof that finite-order Hecke $L$-functions over $\mathbb{Q}(\zeta_3)$ do not vanish for $\operatorname{Re} s > 7/8$: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/NumberTheory/DirichletL` (OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $\operatorname{Re} s > 7/8$*, September 30, 2026, family 003 of [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (definitions that choose witnesses of existence theorems or build structures carrying proofs need those proofs) and the instances and attribute-tagged lemmas of the same modules.
--
--   It imports the bundles `OAIHecke78B018` of this split, and through them their definitions.
--
--   Modules: `Eisenstein.RamifiedSixBranches`, `Eisenstein.CorrespondenceAdjoint`, `Eisenstein.CorrespondenceEnergy`, `Eisenstein.CubeEigenrelation`, `Eisenstein.ResidualOrthogonality`, `Eisenstein.PrimeRecurrence`, `Eisenstein.PrimeGaussFactors`, `Eisenstein.SquarefreeCoefficients`, `GaussSum.MellinSupport`, `CubicSieve.Gauss`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission. Comments are removed; no statement of OpenAI's was changed.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B018

/-!
# OpenAI Hecke 7/8 split: definitions bundle OAIHecke78B020

OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane
Re s > 7/8*, OpenAI Math Release, September 30, 2026, https://github.com/openai/math (family 003;
Lean in `lean/OAI/NumberTheory/DirichletL`, Apache License 2.0; vendored modules of
PrimeNumberTheoremAnd and rellich-kondrachov). Carved from the port to Lean 4.33.1 / Mathlib
0df444a, comments removed. Modules:
  Eisenstein.RamifiedSixBranches
  Eisenstein.CorrespondenceAdjoint
  Eisenstein.CorrespondenceEnergy
  Eisenstein.CubeEigenrelation
  Eisenstein.ResidualOrthogonality
  Eisenstein.PrimeRecurrence
  Eisenstein.PrimeGaussFactors
  Eisenstein.SquarefreeCoefficients
  GaussSum.MellinSupport
  CubicSieve.Gauss
-/

section

namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

def arbitraryIntervalWhittaker (a b:ℝ) (ρ:BoundedContinuousFunction ℝ ℂ) (freq s:ℂ) :ℂ:=
  ∫v in Set.Icc a b,ρ v*(v:ℂ)^(-s-1)*sourceFourierKernel s (freq*v)

lemma arbitraryIntervalWhittaker_analyticAt (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq s:ℂ) (hs:1<s.re) :
    AnalyticAt ℂ (arbitraryIntervalWhittaker a b ρ freq) s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
  exact cuspWeightedWhittakerInterval_differentiableAt ρ a b ha freq w hw

lemma ramifiedSource_height_fourier_average (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side))
    (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (s:ℂ) (hs:2<s.re) :
    (∫w in cuspPeriodStrip a b,sourceEisenstein s
      (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis))•w)*
        arbitraryCuspWeightedPhase ρ (ninthCuspFrequency h) w∂hyperbolicVolume)=
      ramifiedCuspGaussSeries side h hf s*arbitraryIntervalWhittaker a b ρ (ninthCuspFrequency h) s := by
  let M:=integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis))
  let g:HyperbolicSpace→ℂ:=fun w=>sourceEisenstein s (M•w)*
    arbitraryCuspWeightedPhase ρ (ninthCuspFrequency h) w
  have hg:Continuous g:=((sourceProjection_continuous _ (hyperbolicEisenstein_continuous s hs)).comp
    (continuous_hyperbolic_action M)).mul (arbitraryCuspWeightedPhase_continuous ρ _)
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha g hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha g hg)]
  rw [arbitraryIntervalWhittaker,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hv0:0<v:=ha.trans_le hv.1
  have hvz:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv0.ne'
  have hinner:(∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
      ρ v*((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ramifiedCuspGaussSeries side h hf s:=by
    simp only [g,cuspCoordinateLift_positive v _ hv0,arbitraryCuspWeightedPhase,
      hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
    have he (z:ℂ):sourceEisenstein s (M•upperPoint z v hv0)*
        (ρ v*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ρ v*(sourceEisenstein s (M•upperPoint z v hv0)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z)):=by ring
    simp_rw [he]
    rw [integral_const_mul,ramifiedSourceEisenstein_fourier side h hf v hv0 s hs]
    ring
  have hp:(v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3:=by
    rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hvz]
    congr 1
    exact Complex.cpow_natCast _ 3
  dsimp only
  rw [hinner,hp]
  ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

abbrev RamifiedSixBranch := Unit ⊕ (Unit ⊕ (Unit ⊕ Fin 3))

def unitCuspUnramifiedIndex (u t:Eisˣ) (h:Eis) :Eis:=
  3*((↑u⁻¹:Eis)^2*(t:Eis))^2*((↑t⁻¹:Eis)*h)

def ramifiedSixIndex (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)) :RamifiedSixBranch→Eis
  | .inl _=>unitCuspUnramifiedIndex 1 (ramifiedCuspRoot side) h
  | .inr (.inl _)=>unitCuspUnramifiedIndex (-(ramifiedCuspRoot side)) (-(ramifiedCuspRoot side)) h
  | .inr (.inr (.inl _))=>unitCuspUnramifiedIndex (-(ramifiedCuspRoot side)) 1 h
  | .inr (.inr (.inr l))=>3*((↑(-(ramifiedCuspRoot side))⁻¹:Eis)^2*
      (onceCuspScale (ramifiedCuspScaleUnit side)*omega^l.val))^2*
        onceCuspFrequencyQuotient (ramifiedCuspScaleUnit side) h hf l

def ramifiedSixWeight (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)) (i:RamifiedSixBranch) (s:ℂ) :ℂ:=
  let t:=ramifiedCuspRoot side
  let phase:=ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (↑t⁻¹:Eis))
  match i with
  | .inl _=>(4:ℂ)⁻¹*ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (t:Eis))
  | .inr (.inl _)=>(4:ℂ)⁻¹*phase*ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding ((-t:Eisˣ):Eis))
  | .inr (.inr (.inl _))=>(4:ℂ)⁻¹*phase*ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding ((1:Eisˣ):Eis))
  | .inr (.inr (.inr l))=>(4:ℂ)⁻¹*phase*
      (if (3:Eis)∣onceCuspFrequencyQuotient (ramifiedCuspScaleUnit side) h hf l+
          ramifiedAffineParameter (onceCuspRayIndex (-t) (ramifiedCuspScaleUnit side) l).val 1 then
        (3:ℂ)*(3:ℂ)^(-s)*ShortDraftTrace.breveE
          (ninthCuspFrequency h/eisEmbedding (onceCuspScale (ramifiedCuspScaleUnit side)*omega^l.val)) else 0)

lemma ramifiedSixWeight_analytic (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)) (i:RamifiedSixBranch) (s:ℂ) :
    AnalyticAt ℂ (ramifiedSixWeight side h hf i) s := by
  rcases i with i|i
  · exact analyticAt_const
  rcases i with i|i
  · exact analyticAt_const
  rcases i with i|i
  · exact analyticAt_const
  unfold ramifiedSixWeight
  dsimp only
  split_ifs
  · apply analyticAt_const.mul
    apply AnalyticAt.mul _ analyticAt_const
    apply analyticAt_const.mul
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    exact Eventually.of_forall (fun z=>(differentiableAt_id.neg).const_cpow (Or.inl (by norm_num)))
  · exact analyticAt_const

lemma ramifiedCuspGaussSeries_eq_six (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)) (s:ℂ) :
    ramifiedCuspGaussSeries side h hf s=
      ∑i:RamifiedSixBranch,ramifiedSixWeight side h hf i s*
        unramifiedCubicGaussSeries s (ramifiedSixIndex side h hf i) := by
  simp only [Fintype.sum_sum_type,Fintype.sum_unique,ramifiedSixWeight,ramifiedSixIndex,
    ramifiedCuspGaussSeries,unitCuspGaussSeries,unitCuspUnramifiedIndex,onceCuspGaussSeries]
  simp only [Fin.sum_univ_three]
  split_ifs <;> ring

def ramifiedArithmeticResidue (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)) :ℂ:=
  ∑i:RamifiedSixBranch,ramifiedSixWeight side h hf i (4/3)*
    unramifiedGaussResidue (ramifiedSixIndex side h hf i)

end

open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

theorem ramifiedSource_height_residue (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side))
    (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) :
    sourceArbitraryHeightFourier
      (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis)))
      a b ha ρ (ninthCuspFrequency h) cubicEisensteinResidue=
      ramifiedArithmeticResidue side h hf*
        arbitraryIntervalWhittaker a b ρ (ninthCuspFrequency h) (4/3) := by
  let M:=integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis))
  let coeff:RamifiedSixBranch→ℂ→ℂ:=fun i s=>
    ramifiedSixWeight side h hf i s*arbitraryIntervalWhittaker a b ρ (ninthCuspFrequency h) s
  have hc:∀i s,1<s.re→AnalyticAt ℂ (coeff i) s:=fun i s hs=>
    (ramifiedSixWeight_analytic side h hf i s).mul
      (arbitraryIntervalWhittaker_analyticAt a b ha ρ (ninthCuspFrequency h) s hs)
  have he:=finite_unramified_residue (ramifiedSixIndex side h hf) coeff hc
    (sourceArbitraryHeightFamily M a b ha ρ (ninthCuspFrequency h))
    (sourceArbitraryHeightFourier M a b ha ρ (ninthCuspFrequency h) cubicEisensteinResidue)
    (sourceArbitraryHeightFamily_analyticAt M a b ha ρ (ninthCuspFrequency h))
    (sourceArbitraryHeightFamily_residue_limit M a b ha ρ (ninthCuspFrequency h)) (by
      intro s hs hi
      rw [sourceArbitraryHeightFamily_initial M a b ha ρ (ninthCuspFrequency h) s hs hi,
        ramifiedSource_height_fourier_average side h hf a b ha ρ s (by linarith),
        ramifiedCuspGaussSeries_eq_six,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi'
      dsimp only [coeff]
      ring)
  refine he.trans ?_
  rw [ramifiedArithmeticResidue,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [coeff]
  ring

theorem ramifiedSource_height_residue_integral (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side))
    (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) :
    (∫w in cuspPeriodStrip a b,
      ramifiedSourceFunction (ramifiedCuspRoot side:Eis) w*
        arbitraryCuspWeightedPhase ρ (ninthCuspFrequency h) w∂hyperbolicVolume)=
      ramifiedArithmeticResidue side h hf*
        arbitraryIntervalWhittaker a b ρ (ninthCuspFrequency h) (4/3) := by
  unfold ramifiedSourceFunction
  rw [←sourceArbitraryHeightFourier_residue_integral
    (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis))) a b ha ρ (ninthCuspFrequency h)]
  exact ramifiedSource_height_residue side h hf a b ha ρ

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O

variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)

def kernelCorrespondenceMatrix (q : IntegralCoverCosets H globalKubotaKernel) : SL(2,ℂ) :=
  g*integralComplexMatrix (((integralCoverRep H globalKubotaKernel q)⁻¹:globalKubotaKernel):SL(2,ActualEisensteinCubic.O))

lemma kernelCorrespondenceTest_field (f : kernelSmoothTests) (p : EuclideanSpatial) :
    kernelTestField (kernelCorrespondenceTest hHK hJK e g he f) p=
      letI : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
      ∑q : IntegralCoverCosets H globalKubotaKernel,
        kernelTestField f (euclideanAction (kernelCorrespondenceMatrix g q) p) := by
  let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
  change kernelCorrespondenceFunction hJK e g he f.1
    (integralOrbitProjection globalKubotaKernel (euclideanToHyperbolic p))=_
  rw [kernelCorrespondenceFunction_lift]
  apply Finset.sum_congr rfl
  intro q _
  change f.1 (integralOrbitProjection globalKubotaKernel
      (kernelCorrespondenceMatrix g q•euclideanToHyperbolic p))=
    f.1 (integralOrbitProjection globalKubotaKernel
      (euclideanToHyperbolic (euclideanAction (kernelCorrespondenceMatrix g q) p)))
  rw [euclideanAction,euclideanToHyperbolic_coordinates]

lemma kernelCorrespondenceTest_energyDensity_le (f : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelTestEnergyDensity (kernelCorrespondenceTest hHK hJK e g he f) w≤
      (H.relIndex globalKubotaKernel:ℝ)*
        (kernelCorrespondenceFunction hJK e g he (fun q=>(kernelQuotientEnergyDensity f q:ℂ))
          (integralOrbitProjection globalKubotaKernel w)).re := by
  let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
  let p := hyperbolicEuclideanCoordinates w
  let A := kernelCorrespondenceMatrix (H:=H) g
  have hFd (q : IntegralCoverCosets H globalKubotaKernel) :
      DifferentiableAt ℝ (kernelTestField f) (euclideanAction (A q) p) :=
    (kernelTestField_contDiffAt f _ (euclideanAction_positive _ _)).differentiableAt (by simp)
  have hcomp (q : IntegralCoverCosets H globalKubotaKernel) :
      DifferentiableAt ℝ (kernelTestField f ∘ euclideanAction (A q)) p := by
    obtain ⟨der,hder,_⟩ := hyperbolicDifferentialIsometry (A q) p (hyperbolicHeight_pos w)
    exact (hFd q).comp p hder.differentiableAt
  have hh := coverEnergyDensity_sum_le Finset.univ
    (fun q : IntegralCoverCosets H globalKubotaKernel=>kernelTestField f ∘ euclideanAction (A q))
    p (fun q _=>hcomp q)
  have hfield : kernelTestField (kernelCorrespondenceTest hHK hJK e g he f)=
      fun p=>∑q : IntegralCoverCosets H globalKubotaKernel,kernelTestField f (euclideanAction (A q) p) :=
    funext (kernelCorrespondenceTest_field hHK hJK e g he f)
  rw [kernelTestEnergyDensity_eq_cover,hfield]
  change coverEnergyDensity (fun p=>∑q : IntegralCoverCosets H globalKubotaKernel,
    kernelTestField f (euclideanAction (A q) p)) p≤_
  calc
    _ ≤ (Fintype.card (IntegralCoverCosets H globalKubotaKernel):ℝ)*
        ∑q : IntegralCoverCosets H globalKubotaKernel,
          coverEnergyDensity (kernelTestField f ∘ euclideanAction (A q)) p := by
      simpa only [Finset.card_univ,Function.comp_def] using hh
    _ = _ := by
      have hcard : Fintype.card (IntegralCoverCosets H globalKubotaKernel)=
          H.relIndex globalKubotaKernel := by
        rw [Subgroup.relIndex,Subgroup.index,Nat.card_eq_fintype_card]
      rw [hcard,kernelCorrespondenceFunction_lift]
      simp only [Complex.re_sum,Complex.ofReal_re]
      congr 1
      apply Finset.sum_congr rfl
      intro q _
      rw [coverEnergyDensity_comp (A q) _ p (hyperbolicHeight_pos w) (hFd q)]
      change coverEnergyDensity (kernelTestField f) (euclideanAction (A q) p)=
        kernelTestEnergyDensity f (A q•w)
      rw [kernelTestEnergyDensity_eq_cover]
      congr 1
      dsimp [p,euclideanAction]
      rw [euclideanToHyperbolic_coordinates]

lemma kernelCorrespondenceTest_energy_le (f : kernelSmoothTests) :
    kernelDirichletEnergy (kernelCorrespondenceTest hHK hJK e g he f)≤
      (H.relIndex globalKubotaKernel:ℝ)*(J.relIndex globalKubotaKernel:ℝ)*kernelDirichletEnergy f := by
  let density : KernelQuotient→ℂ := fun q=>(kernelQuotientEnergyDensity f q:ℂ)
  have hdm : Measurable density := Complex.continuous_ofReal.measurable.comp
    (kernelQuotientEnergyDensity_continuous f).measurable
  have hdi : Integrable density (integralQuotientVolume globalKubotaKernel) :=
    (kernelQuotientEnergyDensity_integrable f).ofReal
  have hTi := kernelCorrespondenceFunction_integrable hHK hJK e g he density hdm hdi
  have hint := kernelCorrespondenceFunction_integral hHK hJK e g he density hdm hdi
  have hre : (∫q,(kernelCorrespondenceFunction hJK e g he density q).re
      ∂integralQuotientVolume globalKubotaKernel)=
        (J.relIndex globalKubotaKernel:ℝ)*kernelDirichletEnergy f := by
    have htr := integral_re hTi
    have hdf := integral_re hdi
    simp only [RCLike.re_to_complex] at htr hdf
    rw [htr,hint]
    simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
    rw [←hdf]
    rfl
  unfold kernelDirichletEnergy
  calc
    _ ≤ ∫q,(H.relIndex globalKubotaKernel:ℝ)*
        (kernelCorrespondenceFunction hJK e g he density q).re
        ∂integralQuotientVolume globalKubotaKernel := by
      apply integral_mono (kernelQuotientEnergyDensity_integrable _) (hTi.re.const_mul _)
      intro q
      induction q using Quotient.inductionOn with
      | _ w => exact kernelCorrespondenceTest_energyDensity_le hHK hJK e g he f w
    _ = _ := by
      rw [integral_const_mul,hre]
      exact (mul_assoc _ _ _).symm

end

local notation "O" => ActualEisensteinCubic.O

variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)

def kernelCorrespondenceTestLinear : kernelSmoothTests→ₗ[ℂ]kernelSmoothTests where
  toFun := kernelCorrespondenceTest hHK hJK e g he
  map_add' f h := by
    apply Subtype.ext
    funext q
    induction q using Quotient.inductionOn with
    | _ w =>
      let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
      change kernelCorrespondenceFunction hJK e g he (f+h).1
        (integralOrbitProjection globalKubotaKernel w)=
          kernelCorrespondenceFunction hJK e g he f.1 (integralOrbitProjection globalKubotaKernel w)+
          kernelCorrespondenceFunction hJK e g he h.1 (integralOrbitProjection globalKubotaKernel w)
      simp only [kernelCorrespondenceFunction_lift,Submodule.coe_add,Pi.add_apply,Finset.sum_add_distrib]
  map_smul' c f := by
    apply Subtype.ext
    funext q
    induction q using Quotient.inductionOn with
    | _ w =>
      let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
      change kernelCorrespondenceFunction hJK e g he (c•f).1
        (integralOrbitProjection globalKubotaKernel w)=
          c • kernelCorrespondenceFunction hJK e g he f.1 (integralOrbitProjection globalKubotaKernel w)
      simp only [kernelCorrespondenceFunction_lift,Submodule.coe_smul,Pi.smul_apply,Finset.smul_sum]

lemma kernelCorrespondenceL2_norm_le (F : KernelQuotientL2) :
    ‖kernelCorrespondenceL2 hHK hJK e g he F‖≤
      Real.sqrt ((H.relIndex globalKubotaKernel:ℝ)*(J.relIndex globalKubotaKernel:ℝ))*‖F‖ := by
  let C := integralConjugatePullback e g he
    (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree)
  let P := integralCoverPullback hJK globalKubotaKernel_le_levelThree
  let Tr := integralCoverTrace hHK globalKubotaKernel_le_levelThree
  have hTr := integralCoverTrace_opNorm_le hHK globalKubotaKernel_le_levelThree
  have hP := integralCoverPullback_norm_le hJK globalKubotaKernel_le_levelThree F
  rw [←Real.sqrt_eq_rpow] at hTr hP
  change ‖Tr (C (P F))‖≤_
  calc
    _ ≤ ‖Tr‖*‖C (P F)‖ := Tr.le_opNorm _
    _ ≤ Real.sqrt (H.relIndex globalKubotaKernel:ℝ)*‖C (P F)‖ :=
      mul_le_mul_of_nonneg_right hTr (norm_nonneg _)
    _ = Real.sqrt (H.relIndex globalKubotaKernel:ℝ)*‖P F‖ := by rw [C.norm_map]
    _ ≤ Real.sqrt (H.relIndex globalKubotaKernel:ℝ)*
        (Real.sqrt (J.relIndex globalKubotaKernel:ℝ)*‖F‖) :=
      mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg _)]; ring

lemma kernelCorrespondenceTest_graph_norm (f : kernelSmoothTests) :
    ‖kernelEnergyGraphCore (kernelCorrespondenceTest hHK hJK e g he f)‖≤
      Real.sqrt ((H.relIndex globalKubotaKernel:ℝ)*(J.relIndex globalKubotaKernel:ℝ))*
        ‖kernelEnergyGraphCore f‖ := by
  have hm := kernelCorrespondenceL2_norm_le hHK hJK e g he (kernelSmoothTestsToL2 f)
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr hm
  rw [←kernelCorrespondenceTest_mass hHK hJK e g he,mul_pow,
    Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))] at hs
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [kernelEnergyGraphCore_norm_sq,mul_pow,
    Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),kernelEnergyGraphCore_norm_sq]
  have he := kernelCorrespondenceTest_energy_le hHK hJK e g he f
  nlinarith

def kernelCorrespondenceEnergy : KernelEnergyGraph→L[ℂ]KernelEnergyGraph :=
  (kernelEnergyGraphCore.comp (kernelCorrespondenceTestLinear hHK hJK e g he)).extendOfNorm
    kernelEnergyGraphCore

lemma kernelCorrespondenceEnergy_core (f : kernelSmoothTests) :
    kernelCorrespondenceEnergy hHK hJK e g he (kernelEnergyGraphCore f)=
      kernelEnergyGraphCore (kernelCorrespondenceTest hHK hJK e g he f) :=
  LinearMap.extendOfNorm_eq kernelEnergyGraphCore_dense
    ⟨_,kernelCorrespondenceTest_graph_norm hHK hJK e g he⟩ f

lemma kernelCorrespondenceEnergy_mass (u : KernelEnergyGraph) :
    kernelEnergyMass (kernelCorrespondenceEnergy hHK hJK e g he u)=
      kernelCorrespondenceL2 hHK hJK e g he (kernelEnergyMass u) := by
  apply congrFun (kernelEnergyGraphCore_dense.equalizer
    (kernelEnergyMass.continuous.comp (kernelCorrespondenceEnergy hHK hJK e g he).continuous)
    ((kernelCorrespondenceL2 hHK hJK e g he).continuous.comp kernelEnergyMass.continuous) ?_) u
  funext f
  change kernelEnergyMass (kernelCorrespondenceEnergy hHK hJK e g he (kernelEnergyGraphCore f))=
    kernelCorrespondenceL2 hHK hJK e g he (kernelEnergyMass (kernelEnergyGraphCore f))
  rw [kernelCorrespondenceEnergy_core,kernelEnergyMass_core,kernelEnergyMass_core,
    kernelCorrespondenceTest_mass]

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedCuspShiftNumerator (b : Bool) : Eis :=
  if b then -2-omega else omega-1

lemma ramifiedCuspShift_congr (b : Bool) :
    (3:Eis)∣ramifiedCuspShiftNumerator b-onceCuspScale (ramifiedCuspScaleUnit b) := by
  refine ⟨-1,?_⟩
  cases b
  · simp [ramifiedCuspShiftNumerator,ramifiedCuspScaleUnit,onceCuspScale,
      Units.val_neg,ramifiedOmegaUnit_val,ramifiedTraceLambda]
    linear_combination 2*ramified_omega_relation
  · simp only [ramifiedCuspShiftNumerator,ramifiedCuspScaleUnit,ite_true,onceCuspScale,
      Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val,ramifiedTraceLambda]
    linear_combination -(2*omega-1)*ramified_omega_relation

lemma ramifiedCuspShift_support (b : Bool) (h : Eis) :
    (3:Eis)∣ramifiedCuspShiftNumerator b-h ↔
      (3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b) := by
  constructor
  · intro hh
    convert (preTransparency := .instances) dvd_sub (ramifiedCuspShift_congr b) hh using 1 ; ring
  · intro hh
    convert (preTransparency := .instances) dvd_sub (ramifiedCuspShift_congr b) hh using 1 ; ring

lemma ramifiedSource_affine_shift (b : Bool) (x : Eis) (z : ℂ)
    (v : ℝ) (hv : 0<v) :
    ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint (z+3*eisEmbedding x) v hv)=
      affinePeriodChar (3:Eis) (by norm_num) (ramifiedCuspShiftNumerator b)
        (Ideal.Quotient.mk (Ideal.span {(3:Eis)}) x)*
      ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint z v hv) := by
  rw [affinePeriodChar_mk]
  cases b
  · simp only [ramifiedCuspRoot,ramifiedCuspShiftNumerator]
    simp only [Bool.false_eq_true,↓reduceIte,ramifiedOmegaUnit_val]
    rw [ramifiedSourceFunction_upper_shift10]
    congr 2
    simp only [ramifiedShift10,map_mul,map_ofNat]
    ring
  · simp only [ramifiedCuspRoot,ite_true,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val,
      ramifiedCuspShiftNumerator]
    rw [ramifiedSourceFunction_upper_shift19]
    congr 2
    simp only [ramifiedShift19,map_mul,map_ofNat]
    ring

lemma ramifiedSource_weighted_shift (b : Bool) (h x : Eis) (z : ℂ)
    (v : ℝ) (hv : 0<v) :
    ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint (z+3*eisEmbedding x) v hv)*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding x))=
    affinePeriodChar (3:Eis) (by norm_num) (ramifiedCuspShiftNumerator b-h)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)}) x)*
      (ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint z v hv)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z)) := by
  rw [ramifiedSource_affine_shift]
  have hphase : affinePeriodChar (3:Eis) (by norm_num) (ramifiedCuspShiftNumerator b)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)}) x)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding x))=
    affinePeriodChar (3:Eis) (by norm_num) (ramifiedCuspShiftNumerator b-h)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)}) x)*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
    rw [affinePeriodChar_mk,affinePeriodChar_mk,←AddChar.map_add_eq_mul,←AddChar.map_add_eq_mul]
    congr 1
    simp only [ninthCuspFrequency,cuspFrequency,map_mul,map_sub,map_ofNat]
    ring
  calc
    _ = ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint z v hv)*
        (affinePeriodChar (3:Eis) (by norm_num) (ramifiedCuspShiftNumerator b)
          (Ideal.Quotient.mk (Ideal.span {(3:Eis)}) x)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding x))) := by ring
    _ = _ := by rw [hphase];ring

theorem ramifiedSource_active_weighted_periodic (b : Bool) (h : Eis)
    (hh : (3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b)) (v : ℝ) (hv : 0<v) :
    ∀x : Eis,∀z : ℂ,
      ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint (z+3*eisEmbedding x) v hv)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding x))=
      ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint z v hv)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
  intro x z
  rw [ramifiedSource_weighted_shift]
  have hc := (affinePeriodChar_eq_one (3:Eis) (by norm_num) (ramifiedCuspShiftNumerator b-h)).mpr
    ((ramifiedCuspShift_support b h).mpr hh)
  rw [hc]
  simp

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedScaledMode (b : Bool) (h : Eis) (v : ℝ) (hv : 0<v) (z : ℂ) : ℂ :=
  ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint (3*z) v hv)*
    ShortDraftTrace.breveE (-cuspFrequency h*z)

lemma ramifiedScaledMode_shift (b : Bool) (h x : Eis) (v : ℝ) (hv : 0<v) (z : ℂ) :
    ramifiedScaledMode b h v hv (z+eisEmbedding x)=
      affinePeriodChar (3:Eis) (by norm_num) (ramifiedCuspShiftNumerator b-h)
        (Ideal.Quotient.mk (Ideal.span {(3:Eis)}) x)*ramifiedScaledMode b h v hv z := by
  unfold ramifiedScaledMode
  rw [show 3*(z+eisEmbedding x)=3*z+3*eisEmbedding x by ring]
  have h1 : -cuspFrequency h*(z+eisEmbedding x)=
      -ninthCuspFrequency h*(3*z+3*eisEmbedding x) := by rw [ninthCuspFrequency];ring
  have h2 : -cuspFrequency h*z= -ninthCuspFrequency h*(3*z) := by rw [ninthCuspFrequency];ring
  rw [h1,h2]
  exact ramifiedSource_weighted_shift b h x (3*z) v hv

lemma ramifiedScaledMode_periodic (b : Bool) (h : Eis) (v : ℝ) (hv : 0<v) :
    ∀x : Eis,∀z : ℂ,ramifiedScaledMode b h v hv (z+3*eisEmbedding x)=
      ramifiedScaledMode b h v hv z := by
  intro x z
  have hx : Ideal.Quotient.mk (Ideal.span {(3:Eis)}) (3*x)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_mul_right 3 x))
  simpa only [map_mul,map_ofNat,hx,AddChar.map_zero_eq_one,one_mul] using
    ramifiedScaledMode_shift b h (3*x) v hv z

theorem ramifiedSource_scaled_fourier_off_support (b : Bool) (h : Eis)
    (hh : ¬(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b)) (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,ramifiedSourceFunction (ramifiedCuspRoot b:Eis)
      (upperPoint (3*z) v hv)*ShortDraftTrace.breveE (-cuspFrequency h*z))=0 := by
  let χ := affinePeriodChar (3:Eis) (by norm_num) (ramifiedCuspShiftNumerator b-h)
  have hχ : χ≠1 := by
    intro he
    exact hh ((ramifiedCuspShift_support b h).mp
      ((affinePeriodChar_eq_one (3:Eis) (by norm_num) _).mp he))
  have hex : ∃x : Eis⧸Ideal.span {(3:Eis)},χ x≠1 := by
    by_contra he
    push Not at he
    apply hχ
    ext x
    simpa only [AddChar.one_apply] using he x
  obtain ⟨x,hx⟩ := hex
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective x
  change (∫z in periodDomain,ramifiedScaledMode b h v hv z)=0
  apply periodic_integral_zero_of_eigen_translation _ (ramifiedScaledMode_periodic b h v hv)
    (eisEmbedding y) (χ (Ideal.Quotient.mk (Ideal.span {(3:Eis)}) y)) hx
  intro z
  simpa only [add_comm] using ramifiedScaledMode_shift b h y v hv z

lemma ramifiedSource_height_continuous (b : Bool) (v : ℝ) (hv : 0<v) :
    Continuous (fun z : ℂ=>ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint z v hv)) := by
  let c : ℂ→UpperCoordinates := fun z=>⟨(z,v),hv⟩
  have hc : Continuous c := by
    apply Continuous.subtype_mk
    exact continuous_id.prodMk continuous_const
  have ht := continuous_upperCoordinates.comp hc
  have ht' : Continuous (fun z : ℂ=>upperPoint z v hv) := by
    simpa only [Function.comp_def,c] using ht
  exact (ramifiedSourceFunction_continuous _).comp ht'

theorem ramifiedSource_scaled_fourier_active (b : Bool) (h : Eis)
    (hh : (3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b)) (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,ramifiedSourceFunction (ramifiedCuspRoot b:Eis)
      (upperPoint (3*z) v hv)*ShortDraftTrace.breveE (-cuspFrequency h*z))=
    ∫z in periodDomain,ramifiedSourceFunction (ramifiedCuspRoot b:Eis)
      (upperPoint z v hv)*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
  have he (z : ℂ) : -ninthCuspFrequency h*(3*z)= -cuspFrequency h*z := by
    rw [ninthCuspFrequency]
    ring
  have hphase : Continuous (fun z : ℂ=>ShortDraftTrace.breveE (-ninthCuspFrequency h*z)) := by
    change Continuous (fun z : ℂ=>Complex.exp (2*Real.pi*Complex.I*
      ((-ninthCuspFrequency h*z)+starRingEnd ℂ (-ninthCuspFrequency h*z))))
    fun_prop
  have hi := period_integral_eisenstein_mul
    (fun z=>ramifiedSourceFunction (ramifiedCuspRoot b:Eis) (upperPoint z v hv)*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z))
    ((ramifiedSource_height_continuous b v hv).mul hphase).measurable
    (ramifiedSource_active_weighted_periodic b h hh v hv) (3:Eis) (by norm_num)
  simpa only [map_ofNat,he] using hi

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace

local notation "O" => ActualEisensteinCubic.O

lemma integralConjugatePullback_inverse_left {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (hH : H≤CubicKubota.levelThree) (hJ : J≤CubicKubota.levelThree)
    (F : IntegralQuotientL2 H) :
    integralConjugatePullback e g he hH hJ
      (integralConjugatePullback e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) hJ hH F)=F := by
  apply Lp.ext
  have hi := integralConjugatePullback_ae e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) hJ hH F
  have hc := (integralConjugateMap_measurePreserving e g he hH hJ).quasiMeasurePreserving.ae_eq_comp hi
  filter_upwards [integralConjugatePullback_ae e g he hH hJ
    (integralConjugatePullback e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) hJ hH F),hc]
    with q hq hqi
  dsimp only [Function.comp_def] at hqi
  rw [hq,hqi,integralConjugateMap_inverse]

lemma integralConjugatePullback_pairing {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (hH : H≤CubicKubota.levelThree) (hJ : J≤CubicKubota.levelThree)
    (F : IntegralQuotientL2 H) (G : IntegralQuotientL2 J) :
    ⟪F,integralConjugatePullback e g he hH hJ G⟫_ℂ=
      ⟪integralConjugatePullback e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) hJ hH F,G⟫_ℂ := by
  calc
    _ = ⟪integralConjugatePullback e g he hH hJ
      (integralConjugatePullback e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) hJ hH F),
      integralConjugatePullback e g he hH hJ G⟫_ℂ := by
        rw [integralConjugatePullback_inverse_left]
    _ = _ := LinearIsometry.inner_map_map _ _ _

theorem kernelCorrespondenceL2_pairing {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (F G : KernelQuotientL2) :
    ⟪F,kernelCorrespondenceL2 hHK hJK e g he G⟫_ℂ=
      ⟪kernelCorrespondenceL2 hJK hHK e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) F,G⟫_ℂ := by
  change ⟪F,integralCoverTrace hHK globalKubotaKernel_le_levelThree
    (integralConjugatePullback e g he (hHK.trans globalKubotaKernel_le_levelThree)
      (hJK.trans globalKubotaKernel_le_levelThree)
      (integralCoverPullback hJK globalKubotaKernel_le_levelThree G))⟫_ℂ=_
  rw [integralCoverTrace_pairing,integralConjugatePullback_pairing]
  exact (ContinuousLinearMap.adjoint_inner_left
    (integralCoverPullback hJK globalKubotaKernel_le_levelThree) G _).symm

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section

lemma continuous_period_integral {X:Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X]
    (f:X→ℂ→ℂ) (hf:Continuous f.uncurry) :
    Continuous (fun x=>∫z in periodDomain,f x z) := by
  rw [continuous_iff_continuousAt]
  intro x0
  obtain ⟨U,hUc,hUn⟩:=exists_compact_mem_nhds x0
  let radius:ℝ:=∑i,‖periodBasis i‖
  obtain ⟨C,hC⟩:=(hUc.prod (isCompact_closedBall (0:ℂ) radius)).bddAbove_image hf.norm.continuousOn
  apply continuousAt_of_dominated
  · filter_upwards with x using (show Continuous (f x) from hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [hUn] with x hx
    filter_upwards [ae_restrict_mem periodDomain_measurable] with z hz
    apply hC
    exact ⟨(x,z),⟨hx,by simpa only [Metric.mem_closedBall,dist_zero_right,radius] using norm_mem_periodDomain z hz⟩,rfl⟩
  · let:=periodDomain_finiteMeasure
    exact integrable_const C
  · filter_upwards with z using (show Continuous (fun x=>f x z) from hf.comp (continuous_id.prodMk continuous_const)).continuousAt

def continuousCuspSlice (f:HyperbolicSpace→ℂ) (freq:ℂ) (v:ℝ) :ℂ:=
  (∫z in periodDomain,f (cuspCoordinateLift (v,z))*ShortDraftTrace.breveE (-freq*z))/(v:ℂ)^3

lemma continuousCuspSlice_integrable (f:HyperbolicSpace→ℂ) (hf:Continuous f)
    (freq:ℂ) (a b:ℝ) (ha:0<a) :
    IntegrableOn (continuousCuspSlice f freq) (Set.Icc a b) volume := by
  let g:HyperbolicSpace→ℂ:=fun w=>f w*arbitraryCuspWeightedPhase 1 freq w
  have hg:Continuous g:=hf.mul (arbitraryCuspWeightedPhase_continuous 1 freq)
  have hi:=cuspCoordinateLift_weighted_integrable_of_pos a b ha g hg
  rw [IntegrableOn,Measure.volume_eq_prod,←Measure.prod_restrict] at hi
  apply hi.integral_prod_left.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  have hp:0<v:=ha.trans_le hv.1
  rw [integral_div,continuousCuspSlice]
  apply congrArg (fun c:ℂ=>c/(v:ℂ)^3)
  apply integral_congr_ae
  exact Eventually.of_forall (fun z=>by
    dsimp only [g]
    rw [arbitraryCuspWeightedPhase,cuspCoordinateLift_positive v z hp,
      hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
    simp)

lemma continuousCuspSlice_continuousOn (f:HyperbolicSpace→ℂ) (hf:Continuous f)
    (freq:ℂ) (a b:ℝ) (ha:0<a) :
    ContinuousOn (continuousCuspSlice f freq) (Set.Icc a b) := by
  let coord:(ℝ × ℂ)→UpperCoordinates:=fun q=>⟨(q.2,max a q.1),ha.trans_le (le_max_left _ _)⟩
  have hc:Continuous coord:=by
    apply Continuous.subtype_mk
    exact continuous_snd.prodMk (continuous_const.max continuous_fst)
  have hup:Continuous (fun q:(ℝ × ℂ)=>f (upperPoint q.2 (max a q.1) (ha.trans_le (le_max_left _ _)))):=
    hf.comp (continuous_upperCoordinates.comp hc)
  have he:Continuous (fun q:(ℝ × ℂ)=>ShortDraftTrace.breveE (-freq*q.2)):=by
    change Continuous (fun q:(ℝ × ℂ)=>Complex.exp (2*Real.pi*Complex.I*((-freq*q.2)+starRingEnd ℂ (-freq*q.2))))
    fun_prop
  have hi:=continuous_period_integral (fun v z=>f (upperPoint z (max a v) (ha.trans_le (le_max_left _ _)))*
      ShortDraftTrace.breveE (-freq*z)) (hup.mul he)
  have hnum:ContinuousOn (fun v:ℝ=>∫z in periodDomain,f (cuspCoordinateLift (v,z))*
      ShortDraftTrace.breveE (-freq*z)) (Set.Icc a b):=by
    apply hi.continuousOn.congr
    intro v hv
    have hp:0<v:=ha.trans_le hv.1
    simp only [max_eq_right hv.1,cuspCoordinateLift_positive v _ hp]
  exact hnum.div (Complex.continuous_ofReal.pow 3).continuousOn
    (fun v hv=>pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (ha.trans_le hv.1).ne'))

lemma continuousCuspSlice_test (f:HyperbolicSpace→ℂ) (hf:Continuous f) (freq:ℂ)
    (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) :
    (∫w in cuspPeriodStrip a b,f w*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume)=
      ∫v in Set.Icc a b,ρ v*continuousCuspSlice f freq v := by
  have hg:Continuous (fun w=>f w*arbitraryCuspWeightedPhase ρ freq w):=
    hf.mul (arbitraryCuspWeightedPhase_continuous ρ freq)
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha _ hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha _ hg)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hp:0<v:=ha.trans_le hv.1
  dsimp only
  rw [continuousCuspSlice,←mul_div_assoc]
  congr 1
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z=>by
    dsimp only
    rw [arbitraryCuspWeightedPhase,cuspCoordinateLift_positive v z hp,
      hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
    ring)

theorem continuousCuspSlice_eq_of_tests (f:HyperbolicSpace→ℂ) (hf:Continuous f)
    (freq:ℂ) (g:ℝ→ℂ)
    (hg:∀a b:ℝ,0<a→ ContinuousOn g (Set.Icc a b))
    (ht:∀a b:ℝ,∀_ha:0<a,∀ρ:BoundedContinuousFunction ℝ ℂ,
      (∫w in cuspPeriodStrip a b,f w*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume)=
        ∫v in Set.Icc a b,ρ v*g v) (v:ℝ) (hv:0<v) :
    continuousCuspSlice f freq v=g v := by
  have ha:0<v/2:=half_pos hv
  have hab:v/2≠2*v:=by linarith
  have he:continuousCuspSlice f freq=ᵐ[volume.restrict (Set.Icc (v/2) (2*v))]g:=by
    apply interval_ae_eq_of_boundedContinuous_height_tests (v/2) (2*v) _ _
      (continuousCuspSlice_integrable f hf freq _ _ ha) ((hg _ _ ha).integrableOn_Icc)
    intro ρ
    rw [←continuousCuspSlice_test f hf freq _ _ ha ρ]
    exact ht _ _ ha ρ
  exact Measure.eqOn_Icc_of_ae_eq volume hab he
    (continuousCuspSlice_continuousOn f hf freq _ _ ha) (hg _ _ ha)
      (by constructor <;>linarith)

local notation "Eis" => ActualEisensteinCubic.O

theorem ramifiedSource_fourier_all_heights (side:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side))
    (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,ramifiedSourceFunction (ramifiedCuspRoot side:Eis) (upperPoint z v hv)*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ramifiedArithmeticResidue side h hf*(v:ℂ)^(2/3:ℂ)*
        sourceFourierKernel (4/3) (ninthCuspFrequency h*v) := by
  let R:=ramifiedArithmeticResidue side h hf
  let g:ℝ→ℂ:=fun v=>R*(v:ℂ)^(-(4/3:ℂ)-1)*
    sourceFourierKernel (4/3) (ninthCuspFrequency h*v)
  have hg:∀a b:ℝ,0<a→ ContinuousOn g (Set.Icc a b):=by
    intro a b ha x hx
    have hp:0<x:=ha.trans_le hx.1
    exact ((continuousAt_const.mul
      (Complex.continuousAt_ofReal_cpow_const x (-(4/3:ℂ)-1) (Or.inr hp.ne'))).mul
        ((sourceFourierKernel_continuous_freq (4/3) (by norm_num)).continuousAt.comp
          ((Complex.continuous_ofReal.const_mul (ninthCuspFrequency h)).continuousAt))).continuousWithinAt
  have ht:∀a b:ℝ,∀ha:0<a,∀ρ:BoundedContinuousFunction ℝ ℂ,
      (∫w in cuspPeriodStrip a b,ramifiedSourceFunction (ramifiedCuspRoot side:Eis) w*
        arbitraryCuspWeightedPhase ρ (ninthCuspFrequency h) w∂hyperbolicVolume)=
          ∫x in Set.Icc a b,ρ x*g x:=by
    intro a b ha ρ
    rw [ramifiedSource_height_residue_integral side h hf a b ha ρ,
      arbitraryIntervalWhittaker,←integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x=>by dsimp only [g,R];ring)
  have he:=continuousCuspSlice_eq_of_tests
    (ramifiedSourceFunction (ramifiedCuspRoot side:Eis)) (ramifiedSourceFunction_continuous _)
    (ninthCuspFrequency h) g hg ht v hv
  have hvn:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv.ne'
  have hp:(v:ℂ)^(-(4/3:ℂ)-1)=(v:ℂ)^(2/3:ℂ)/(v:ℂ)^3:=by
    rw [show -(4/3:ℂ)-1=(2/3:ℂ)-3 by ring,Complex.cpow_sub _ _ hvn]
    congr 1
    exact Complex.cpow_natCast _ 3
  dsimp only [continuousCuspSlice,g,R] at he
  simp only [cuspCoordinateLift_positive v _ hv,hp] at he
  apply (div_left_inj' (pow_ne_zero 3 hvn)).mp
  convert (preTransparency := .instances) he using 1 ;ring

end

section
local notation "Eis" => ActualEisensteinCubic.O

lemma continuous_period_fourier_bound (f:ℂ→ℂ) (hf:Continuous f) :
    ∃C:ℝ,0≤C∧∀freq:ℂ,‖∫z in periodDomain,f z*ShortDraftTrace.breveE (-freq*z)‖≤C := by
  let radius:ℝ:=∑i,‖periodBasis i‖
  obtain ⟨B,hB⟩:=(isCompact_closedBall (0:ℂ) radius).bddAbove_image hf.norm.continuousOn
  refine ⟨max 0 B*(volume.restrict periodDomain).real Set.univ,mul_nonneg (le_max_left _ _) (measureReal_nonneg),?_⟩
  intro freq
  let:=periodDomain_finiteMeasure
  apply norm_integral_le_of_norm_le_const
  filter_upwards [ae_restrict_mem periodDomain_measurable] with z hz
  rw [norm_mul,breveE_norm,mul_one]
  apply le_trans _ (le_max_right _ _)
  apply hB
  exact ⟨z,by simpa only [Metric.mem_closedBall,dist_zero_right,radius] using norm_mem_periodDomain z hz,rfl⟩

theorem continuous_fourier_bessel_subexponential (f:ℝ→ℂ→ℂ) (c:Eis→ℂ)
    (hf:∀v:ℝ,0<v→ Continuous (f v))
    (hfour:∀v:ℝ,∀_hv:0<v,∀h:Eis,h≠0→
      (∫z in periodDomain,f v z*ShortDraftTrace.breveE (-cuspFrequency h*z))=
        ((9*Real.sqrt 3/2:ℝ):ℂ)*c h*(v:ℂ)*
          schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v))
    (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0≤C∧∀h:Eis,h≠0→‖c h‖≤C*Real.exp (ε*‖cuspFrequency h‖) := by
  let v:ℝ:=ε/(9*Real.pi)
  have hv:0<v:=div_pos hε (by positivity)
  let area:ℂ:=((9*Real.sqrt 3/2:ℝ):ℂ)
  have harea:0<‖area‖:=norm_pos_iff.mpr cusp_volume_ne_zero
  obtain ⟨B,hB,hbound⟩:=continuous_period_fourier_bound (f v) (hf v hv)
  let D:ℝ:=‖area‖*v*cubicBesselLowerConstant
  have hD:0<D:=mul_pos (mul_pos harea hv) cubicBesselLowerConstant_pos
  refine ⟨B/D,div_nonneg hB hD.le,?_⟩
  intro h hh
  have hx:0<4*Real.pi*‖cuspFrequency h‖*v:=by
    have hr:=norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
    positivity
  have hl: cubicBesselLowerConstant*Real.exp (-(ε*‖cuspFrequency h‖))≤
      ‖schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)‖:=by
    have hb:=(schlafliBesselK_cubic_lower (4*Real.pi*‖cuspFrequency h‖*v) hx).trans (Complex.re_le_norm _)
    convert (preTransparency := .instances) hb using 1
    congr 2
    dsimp [v]
    field_simp

  have hb:=hbound (cuspFrequency h)
  rw [hfour v hv h hh,norm_mul,norm_mul,norm_mul,Complex.norm_of_nonneg hv.le] at hb
  have hm:‖c h‖*(D*Real.exp (-(ε*‖cuspFrequency h‖)))≤B:=by
    calc
      _ = (‖area‖*‖c h‖*v)*(cubicBesselLowerConstant*Real.exp (-(ε*‖cuspFrequency h‖))) := by dsimp [D];ring
      _ ≤ (‖area‖*‖c h‖*v)*‖schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)‖ :=
        mul_le_mul_of_nonneg_left hl (by positivity)
      _ ≤ B := hb
  have hexp:0<Real.exp (-(ε*‖cuspFrequency h‖)):=Real.exp_pos _
  apply (le_div_iff₀ (mul_pos hD hexp)).mpr at hm
  calc
    _ ≤ B/(D*Real.exp (-(ε*‖cuspFrequency h‖))) := hm
    _ = (B/D)*Real.exp (ε*‖cuspFrequency h‖) := by rw [Real.exp_neg];field_simp

theorem continuous_periodic_eq_bessel (c:SubexponentialBesselCoefficients)
    (f:ℂ→ℂ) (hf:Continuous f) (v:ℝ) (hv:0<v)
    (hp:∀n:Eis,∀z:ℂ,f (z+3*ConcreteTraceCRT.eisEmbedding n)=f z)
    (hfour:∀h:Eis,(∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*c.amplitude v h) :
    ∀z:ℂ,f z=c.fullFunction 0 (upperPoint z v hv) := by
  have hc:=c.fullFunction_height_continuous 0 v hv
  have he:f=ᵐ[volume.restrict periodDomain](fun z=>c.fullFunction 0 (upperPoint z v hv)):=by
    apply periodDomain_L2_ext _ _ (periodDomain_memLp_of_continuous f hf)
      (periodDomain_memLp_of_continuous _ hc)
    intro h
    rw [hfour,c.fullFunction_fourier]
    by_cases hh:h=0
    · simp [hh,SubexponentialBesselCoefficients.amplitude]
    · simp [hh]
  have hall:=ae_eq_of_periodDomain_eq f _ hp (fun n z=>c.fullFunction_period 0 v hv z n) he
  exact congrFun (Measure.eq_of_ae_eq hall hf hc)

end

section
open ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma ninthCuspFrequency_three (h:Eis) :
    3*ninthCuspFrequency h=cuspFrequency h := by
  unfold ninthCuspFrequency cuspFrequency
  ring

lemma sourceFourierKernel_cubic_amplitude (h:Eis) (hh:h≠0) (v:ℝ) (hv:0<v) :
    (v:ℂ)^(2/3:ℂ)*sourceFourierKernel (4/3) (cuspFrequency h*v)=
      cubicBesselNormalizer h*(v:ℂ)*schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v) := by
  have hvn:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv.ne'
  have hp:(v:ℂ)^(-(4/3:ℂ)-1)=(v:ℂ)^(2/3:ℂ)/(v:ℂ)^3:=by
    rw [show -(4/3:ℂ)-1=(2/3:ℂ)-3 by ring,Complex.cpow_sub _ _ hvn]
    congr 1
    exact Complex.cpow_natCast _ 3
  have he:=sourceFourierKernel_cubic_height h hh v hv
  rw [hp] at he
  apply (div_left_inj' (pow_ne_zero 3 hvn)).mp
  calc
    _ = ((v:ℂ)^(2/3:ℂ)/(v:ℂ)^3)*sourceFourierKernel (4/3) (cuspFrequency h*v) := by ring
    _ = _ := he
    _ = _ := by field_simp

lemma ramified_kernel_scaled_bessel (h:Eis) (hh:h≠0) (v:ℝ) (hv:0<v) :
    ((3*v:ℝ):ℂ)^(2/3:ℂ)*sourceFourierKernel (4/3) (ninthCuspFrequency h*(3*v:ℝ))=
      (3:ℂ)^(2/3:ℂ)*cubicBesselNormalizer h*(v:ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v) := by
  have hfreq:ninthCuspFrequency h*((3*v:ℝ):ℂ)=cuspFrequency h*v:=by
    push_cast
    rw [←ninthCuspFrequency_three]
    ring
  have hp:((3*v:ℝ):ℂ)^(2/3:ℂ)=(3:ℂ)^(2/3:ℂ)*(v:ℂ)^(2/3:ℂ):=by
    simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using
      Complex.mul_cpow_ofReal_nonneg (a:=3) (b:=v) (by norm_num) hv.le (2/3:ℂ)
  rw [hfreq,hp,mul_assoc,sourceFourierKernel_cubic_amplitude h hh v hv]
  ring

end

section
open ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedScaledRow (side:Bool) (v:ℝ) (z:ℂ) :ℂ:=
  ramifiedSourceFunction (ramifiedCuspRoot side:Eis) (cuspCoordinateLift (3*v,3*z))

def ramifiedBesselValue (side:Bool) (h:Eis) :ℂ:=
  if hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side) then
    (3:ℂ)^(2/3:ℂ)*cubicBesselNormalizer h*ramifiedArithmeticResidue side h hf/
      ((9*Real.sqrt 3/2:ℝ):ℂ)
  else 0

lemma ramifiedScaledRow_continuous (side:Bool) (v:ℝ) (hv:0<v) :
    Continuous (ramifiedScaledRow side v) := by
  have hp:0<3*v:=by positivity
  have he:ramifiedScaledRow side v=(fun z=>ramifiedSourceFunction (ramifiedCuspRoot side:Eis)
      (upperPoint (3*z) (3*v) hp)):=by
    funext z
    exact congrArg (ramifiedSourceFunction (ramifiedCuspRoot side:Eis)) (cuspCoordinateLift_positive (3*v) (3*z) hp)
  rw [he]
  exact (ramifiedSource_height_continuous side (3*v) hp).comp (continuous_const.mul continuous_id)

lemma ramifiedScaledRow_periodic (side:Bool) (v:ℝ) (hv:0<v) (n:Eis) (z:ℂ) :
    ramifiedScaledRow side v (z+3*eisEmbedding n)=ramifiedScaledRow side v z := by
  have hp:0<3*v:=by positivity
  have he:=ramifiedScaledMode_periodic side 0 (3*v) hp n z
  simpa only [ramifiedScaledMode,cuspFrequency,map_zero,zero_div,neg_zero,zero_mul,
    AddChar.map_zero_eq_one,mul_one,ramifiedScaledRow,cuspCoordinateLift_positive (3*v) _ hp] using he

lemma ramifiedScaledRow_zero (side:Bool) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,ramifiedScaledRow side v z)=0 := by
  have hp:0<3*v:=by positivity
  simp only [ramifiedScaledRow,cuspCoordinateLift_positive (3*v) _ hp]
  cases side
  · simpa [ramifiedCuspRoot,ramifiedOmegaUnit_val] using ramifiedSource_zero_mode10 (3*v) hp
  · simpa [ramifiedCuspRoot,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val] using ramifiedSource_zero_mode19 (3*v) hp

lemma ramifiedScaledRow_fourier (side:Bool) (v:ℝ) (hv:0<v) (h:Eis) :
    (∫z in periodDomain,ramifiedScaledRow side v z*ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(if h=0 then 0 else ramifiedBesselValue side h*(v:ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)) := by
  by_cases hh:h=0
  · subst h
    simp only [cuspFrequency,map_zero,zero_div,neg_zero,zero_mul,AddChar.map_zero_eq_one,
      mul_one]
    simpa only [ite_true,mul_zero] using ramifiedScaledRow_zero side v hv
  have hp:0<3*v:=by positivity
  rw [if_neg hh]
  simp only [ramifiedScaledRow,cuspCoordinateLift_positive (3*v) _ hp]
  by_cases hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side)
  · rw [ramifiedSource_scaled_fourier_active side h hf (3*v) hp,
      ramifiedSource_fourier_all_heights side h hf (3*v) hp,
      ramifiedBesselValue,dif_pos hf,mul_assoc,ramified_kernel_scaled_bessel h hh v hv]
    field_simp [cusp_volume_ne_zero]

  · rw [ramifiedSource_scaled_fourier_off_support side h hf (3*v) hp,
      ramifiedBesselValue,dif_neg hf]
    ring

lemma ramifiedBesselValue_subexponential (side:Bool) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0≤C∧∀h:Eis,h≠0→‖ramifiedBesselValue side h‖≤C*Real.exp (ε*‖cuspFrequency h‖) := by
  apply continuous_fourier_bessel_subexponential (ramifiedScaledRow side) (ramifiedBesselValue side)
    (ramifiedScaledRow_continuous side) _ ε hε
  intro v hv h hh
  simpa only [if_neg hh,mul_assoc] using ramifiedScaledRow_fourier side v hv h

def ramifiedBesselCoefficients (side:Bool) :SubexponentialBesselCoefficients where
  value:=ramifiedBesselValue side
  growth:=ramifiedBesselValue_subexponential side

theorem ramifiedScaledRow_eq_bessel (side:Bool) (v:ℝ) (hv:0<v) (z:ℂ) :
    ramifiedScaledRow side v z=(ramifiedBesselCoefficients side).fullFunction 0 (upperPoint z v hv) := by
  apply continuous_periodic_eq_bessel (ramifiedBesselCoefficients side) (ramifiedScaledRow side v)
    (ramifiedScaledRow_continuous side v hv) v hv (ramifiedScaledRow_periodic side v hv) _ z
  intro h
  simpa only [SubexponentialBesselCoefficients.amplitude,ramifiedBesselCoefficients] using
    ramifiedScaledRow_fourier side v hv h

theorem ramifiedSource_cubic_decay (side:Bool) (a:ℝ) (ha:0<a) :
    ∃C:ℝ,0≤C∧∀v:ℝ,∀hv:0<v,∀z:ℂ,a≤v→
      ‖ramifiedSourceFunction (ramifiedCuspRoot side:Eis) (upperPoint z v hv)‖≤C/v^3 := by
  obtain ⟨C,hC,hbound⟩:=(ramifiedBesselCoefficients side).fullFunction_zero_cubic_decay
    (a/3) (by positivity)
  refine ⟨27*C,by positivity,?_⟩
  intro v hv z hav
  have hp:0<v/3:=by positivity
  have he:=ramifiedScaledRow_eq_bessel side (v/3) hp (z/3)
  have hb:=hbound (v/3) hp (z/3) (by linarith)
  rw [←he] at hb
  have hv3:3*(v/3)=v:=by ring
  have hz3:(3:ℂ)*(z/3)=z:=by ring
  simp only [ramifiedScaledRow,hv3,hz3,cuspCoordinateLift_positive v z hv] at hb
  calc
    _ ≤ C/(v/3)^3 := hb
    _ = 27*C/v^3 := by field_simp;ring

end

local notation "Eis" => ActualEisensteinCubic.O

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

lemma coverGradientAt_add (F G : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    coverGradientAt (F+G) p=coverGradientAt F p+coverGradientAt G p := by
  apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
  funext j
  simp only [coverGradientAt,fderiv_add hF hG,WithLp.equiv_apply,WithLp.ofLp_add,
    Pi.add_apply,_root_.add_apply,mul_add]

lemma coverGradientAt_sub (F G : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    coverGradientAt (F-G) p=coverGradientAt F p-coverGradientAt G p := by
  apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
  funext j
  simp only [coverGradientAt,fderiv_sub hF hG,WithLp.equiv_apply,WithLp.ofLp_sub,
    Pi.sub_apply,_root_.sub_apply,mul_sub]

lemma coverGradientAt_smul (c : ℂ) (F : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (hF : DifferentiableAt ℝ F p) :
    coverGradientAt (c•F) p=c•coverGradientAt F p := by
  apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
  funext j
  simp only [coverGradientAt,fderiv_const_smul hF,WithLp.equiv_apply,WithLp.ofLp_smul,
    Pi.smul_apply,_root_.smul_apply,smul_eq_mul,mul_left_comm]

def coverDirichletPair (F G : EuclideanSpatial→ℂ) (p : EuclideanSpatial) : ℂ :=
  inner ℂ (coverGradientAt F p) (coverGradientAt G p)

lemma coverDirichletPair_polarization (F G : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    coverDirichletPair F G p=
      ((coverEnergyDensity (F+G) p:ℂ)-(coverEnergyDensity (F-G) p:ℂ)+
        ((coverEnergyDensity (F-Complex.I•G) p:ℂ)-
          (coverEnergyDensity (F+Complex.I•G) p:ℂ))*Complex.I)/4 := by
  unfold coverDirichletPair
  rw [inner_eq_sum_norm_sq_div_four]
  simp only [RCLike.I_to_complex]
  rw [←coverGradientAt_add F G p hF hG,←coverGradientAt_sub F G p hF hG,
    ←coverGradientAt_smul Complex.I G p hG,
    ←coverGradientAt_sub F (Complex.I•G) p hF (hG.const_smul _),
    ←coverGradientAt_add F (Complex.I•G) p hF (hG.const_smul _)]
  simp only [RCLike.ofReal_eq_complex_ofReal,←Complex.ofReal_pow,
    coverGradientAt_norm_sq _ _ (hF.add hG),coverGradientAt_norm_sq _ _ (hF.sub hG),
    coverGradientAt_norm_sq _ _ (hF.sub (hG.const_smul _)),
    coverGradientAt_norm_sq _ _ (hF.add (hG.const_smul _))]

lemma coverDirichletPair_comp (g : SL(2,ℂ)) (F G : EuclideanSpatial→ℂ)
    (p : EuclideanSpatial) (hp : 0<p 2)
    (hF : DifferentiableAt ℝ F (euclideanAction g p))
    (hG : DifferentiableAt ℝ G (euclideanAction g p)) :
    coverDirichletPair (F ∘ euclideanAction g) (G ∘ euclideanAction g) p=
      coverDirichletPair F G (euclideanAction g p) := by
  obtain ⟨der,hder,_⟩ := hyperbolicDifferentialIsometry g p hp
  rw [coverDirichletPair_polarization _ _ p (hF.comp p hder.differentiableAt)
    (hG.comp p hder.differentiableAt),coverDirichletPair_polarization F G _ hF hG]
  have ha : (F ∘ euclideanAction g)+(G ∘ euclideanAction g)=(F+G) ∘ euclideanAction g := rfl
  have hs : (F ∘ euclideanAction g)-(G ∘ euclideanAction g)=(F-G) ∘ euclideanAction g := rfl
  have hai : (F ∘ euclideanAction g)+Complex.I•(G ∘ euclideanAction g)=
      (F+Complex.I•G) ∘ euclideanAction g := rfl
  have hsi : (F ∘ euclideanAction g)-Complex.I•(G ∘ euclideanAction g)=
      (F-Complex.I•G) ∘ euclideanAction g := rfl
  rw [ha,hs,hai,hsi,coverEnergyDensity_comp g _ p hp (hF.add hG),
    coverEnergyDensity_comp g _ p hp (hF.sub hG),
    coverEnergyDensity_comp g _ p hp (hF.add (hG.const_smul _)),
    coverEnergyDensity_comp g _ p hp (hF.sub (hG.const_smul _))]

lemma coverDirichletPair_sum_right {ι : Type*} (s : Finset ι)
    (F : EuclideanSpatial→ℂ) (G : ι→EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (hG : ∀i∈s,DifferentiableAt ℝ (G i) p) :
    coverDirichletPair F (fun x=>∑i∈s,G i x) p=∑i∈s,coverDirichletPair F (G i) p := by
  simp only [coverDirichletPair,coverGradientAt_sum s G p hG,inner_sum]

lemma coverDirichletPair_norm_le (F G : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    ‖coverDirichletPair F G p‖≤(coverEnergyDensity F p+coverEnergyDensity G p)/2 := by
  have hh := norm_inner_le_norm (𝕜:=ℂ) (coverGradientAt F p) (coverGradientAt G p)
  have hs := sq_nonneg (‖coverGradientAt F p‖-‖coverGradientAt G p‖)
  rw [←coverGradientAt_norm_sq F p hF,←coverGradientAt_norm_sq G p hG]
  exact le_trans hh (by nlinarith)

lemma kernelDirichletPairDensity_eq_cover (f h : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelDirichletPairDensity f h (integralOrbitProjection globalKubotaKernel w)=
      coverDirichletPair (kernelTestField f) (kernelTestField h) (hyperbolicEuclideanCoordinates w) := by
  rw [kernelDirichletPairDensity_coordinate]
  rfl

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O

lemma kernelTestField_comp_contDiffAt (f : kernelSmoothTests) (g : SL(2,ℂ))
    (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (kernelTestField f ∘ euclideanAction g) p := by
  have hd := ((((f.2.1.comp kernelProjection_contMDiff).comp (hyperbolicAction_contMDiff g))
    (euclideanToHyperbolic p)).comp p (euclideanToHyperbolic_contMDiffAt p hp)).contDiffAt
  simpa only [Function.comp_def,kernelTestField,euclideanAction,euclideanToHyperbolic_coordinates] using hd

lemma coverGradientAt_lift_continuous (F : EuclideanSpatial→ℂ)
    (hF : ∀p,0<p 2→ ContDiffAt ℝ ∞ F p) :
    Continuous (fun w : HyperbolicSpace=>coverGradientAt F (hyperbolicEuclideanCoordinates w)) := by
  apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3=>ℂ)).symm.continuous.comp
  apply continuous_pi
  intro j
  apply (Complex.continuous_ofReal.comp hyperbolicHeight_continuous).mul
  rw [continuous_iff_continuousAt]
  intro w
  exact (((hF _ (hyperbolicHeight_pos w)).continuousAt_fderiv (by simp)).clm_apply
    continuousAt_const).comp hyperbolicEuclideanCoordinates_continuous.continuousAt

def kernelCorrespondencePairLift (g : SL(2,ℂ)) (f h : kernelSmoothTests)
    (w : HyperbolicSpace) : ℂ :=
  coverDirichletPair (kernelTestField f) (kernelTestField h ∘ euclideanAction g)
    (hyperbolicEuclideanCoordinates w)

lemma kernelCorrespondencePairLift_continuous (g : SL(2,ℂ)) (f h : kernelSmoothTests) :
    Continuous (kernelCorrespondencePairLift g f h) :=
  (coverGradientAt_lift_continuous _ (kernelTestField_contDiffAt f)).inner
    (coverGradientAt_lift_continuous _ (kernelTestField_comp_contDiffAt h g))

variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)

include hHK hJK he in
omit [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondencePairLift_invariant (f h : kernelSmoothTests)
    (k : H) (w : HyperbolicSpace) :
    kernelCorrespondencePairLift g f h (k•w)=kernelCorrespondencePairLift g f h w := by
  let A := integralComplexMatrix (k:SL(2,ActualEisensteinCubic.O))
  let B := integralComplexMatrix (e k:SL(2,ActualEisensteinCubic.O))
  have hfi : kernelTestField f ∘ euclideanAction A=kernelTestField f :=
    funext (kernelTestField_invariant f ⟨(k:SL(2,ActualEisensteinCubic.O)),hHK k.property⟩)
  have hhi : (kernelTestField h ∘ euclideanAction g) ∘ euclideanAction A=
      kernelTestField h ∘ euclideanAction g := by
    rw [Function.comp_assoc,←euclideanAction_mul,he k,euclideanAction_mul,←Function.comp_assoc]
    have hh : kernelTestField h ∘ euclideanAction B=kernelTestField h :=
      funext (kernelTestField_invariant h ⟨(e k:SL(2,ActualEisensteinCubic.O)),hJK (e k).property⟩)
    rw [hh]
  have hp := hyperbolicHeight_pos w
  have hh := coverDirichletPair_comp A (kernelTestField f) (kernelTestField h ∘ euclideanAction g)
    (hyperbolicEuclideanCoordinates w) hp
    ((kernelTestField_contDiffAt f _ (euclideanAction_positive A _)).differentiableAt (by simp))
    ((kernelTestField_comp_contDiffAt h g _ (euclideanAction_positive A _)).differentiableAt (by simp))
  rw [hfi,hhi] at hh
  change _=coverDirichletPair (kernelTestField f) (kernelTestField h ∘ euclideanAction g)
    (hyperbolicEuclideanCoordinates w)
  rw [integralSubgroup_smul]
  simpa only [kernelCorrespondencePairLift,A,euclideanAction,euclideanToHyperbolic_coordinates] using hh.symm

def kernelCorrespondencePair (f h : kernelSmoothTests) : IntegralOrbitQuotient H→ℂ :=
  Quotient.lift (kernelCorrespondencePairLift g f h) (by
    rintro w v ⟨k,rfl⟩
    exact (kernelCorrespondencePairLift_invariant hHK hJK e g he f h k w).symm)

omit [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondencePair_projection (f h : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelCorrespondencePair hHK hJK e g he f h (integralOrbitProjection H w)=
      kernelCorrespondencePairLift g f h w := rfl

omit [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondencePair_measurable (f h : kernelSmoothTests) :
    Measurable (kernelCorrespondencePair hHK hJK e g he f h) :=
  measurable_from_quotient.mpr (kernelCorrespondencePairLift_continuous g f h).measurable

omit [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondencePair_norm_le (f h : kernelSmoothTests) (q : IntegralOrbitQuotient H) :
    ‖kernelCorrespondencePair hHK hJK e g he f h q‖≤
      (kernelQuotientEnergyDensity f (integralCoverMap hHK q)+
        kernelQuotientEnergyDensity h (integralCoverMap hJK (integralConjugateMap e g he q)))/2 := by
  induction q using Quotient.inductionOn with
  | _ w =>
    have hf := (kernelTestField_contDiffAt f (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)).differentiableAt (by simp)
    have hh := (kernelTestField_comp_contDiffAt h g (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)).differentiableAt (by simp)
    have hb := coverDirichletPair_norm_le (kernelTestField f) (kernelTestField h ∘ euclideanAction g)
      (hyperbolicEuclideanCoordinates w) hf hh
    rw [coverEnergyDensity_comp g _ _ (hyperbolicHeight_pos w)
      ((kernelTestField_contDiffAt h _ (euclideanAction_positive g _)).differentiableAt (by simp))] at hb
    change ‖kernelCorrespondencePairLift g f h w‖≤
      (kernelTestEnergyDensity f w+kernelTestEnergyDensity h (g•w))/2
    simpa only [kernelCorrespondencePairLift,kernelTestEnergyDensity_eq_cover,euclideanAction,
      euclideanToHyperbolic_coordinates] using hb

lemma kernelCorrespondencePair_integrable (f h : kernelSmoothTests) :
    Integrable (kernelCorrespondencePair hHK hJK e g he f h) (integralQuotientVolume H) := by
  have hf := (integralCoverMap_measurePreserving hHK globalKubotaKernel_le_levelThree).integrable_comp_of_integrable
    ((kernelQuotientEnergyDensity_integrable f).smul_measure
      (c:=(H.relIndex globalKubotaKernel:ℝ≥0∞)) (by simp))
  have hh := (integralCoverMap_measurePreserving hJK globalKubotaKernel_le_levelThree).integrable_comp_of_integrable
    ((kernelQuotientEnergyDensity_integrable h).smul_measure
      (c:=(J.relIndex globalKubotaKernel:ℝ≥0∞)) (by simp))
  have hhh := (integralConjugateMap_measurePreserving e g he
    (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree)).integrable_comp_of_integrable hh
  apply ((hf.add hhh).div_const 2).mono' (kernelCorrespondencePair_measurable hHK hJK e g he f h).aestronglyMeasurable
  exact Filter.Eventually.of_forall (kernelCorrespondencePair_norm_le hHK hJK e g he f h)

end

local notation "O" => ActualEisensteinCubic.O

lemma kernelCorrespondencePairLift_kernel (g : SL(2,ℂ)) (f h : kernelSmoothTests)
    (r : globalKubotaKernel) (w : HyperbolicSpace) :
    kernelCorrespondencePairLift g f h (r•w)=
      coverDirichletPair (kernelTestField f)
        (kernelTestField h ∘ euclideanAction (g*integralComplexMatrix (r:SL(2,ActualEisensteinCubic.O))))
        (hyperbolicEuclideanCoordinates w) := by
  have hf := (kernelTestField_contDiffAt f _ (euclideanAction_positive (integralComplexMatrix r) (hyperbolicEuclideanCoordinates w))).differentiableAt (by simp)
  have hh := (kernelTestField_comp_contDiffAt h g _ (euclideanAction_positive (integralComplexMatrix r) (hyperbolicEuclideanCoordinates w))).differentiableAt (by simp)
  have hp := coverDirichletPair_comp (integralComplexMatrix r) (kernelTestField f)
    (kernelTestField h ∘ euclideanAction g) (hyperbolicEuclideanCoordinates w)
    (hyperbolicHeight_pos w) hf hh
  have hfi : kernelTestField f ∘ euclideanAction (integralComplexMatrix r)=kernelTestField f :=
    funext (kernelTestField_invariant f r)
  rw [hfi,Function.comp_assoc,←euclideanAction_mul] at hp
  simpa only [kernelCorrespondencePairLift,integralSubgroup_smul,euclideanAction,
    euclideanToHyperbolic_coordinates] using hp.symm

lemma kernelTestField_comp_inverse (f : kernelSmoothTests) (g : SL(2,ℂ)) :
    (kernelTestField f ∘ euclideanAction g⁻¹) ∘ euclideanAction g=kernelTestField f := by
  funext p
  simp only [Function.comp_def,kernelTestField,euclideanAction,euclideanToHyperbolic_coordinates,
    inv_smul_smul]

variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)

lemma kernelCorrespondencePair_trace (f h : kernelSmoothTests) (q : KernelQuotient) :
    kernelDirichletPairDensity f (kernelCorrespondenceTest hHK hJK e g he h) q=
      integralCoverTraceFunction H globalKubotaKernel
        (kernelCorrespondencePair hHK hJK e g he f h) q := by
  let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
  induction q using Quotient.inductionOn with
  | _ w =>
    change kernelDirichletPairDensity f (kernelCorrespondenceTest hHK hJK e g he h)
      (integralOrbitProjection globalKubotaKernel w)=_
    rw [kernelDirichletPairDensity_eq_cover]
    have hfield := funext (kernelCorrespondenceTest_field hHK hJK e g he h)
    rw [hfield]
    have hd (r : IntegralCoverCosets H globalKubotaKernel) :
        DifferentiableAt ℝ (kernelTestField h ∘ euclideanAction (kernelCorrespondenceMatrix g r))
          (hyperbolicEuclideanCoordinates w) :=
      (kernelTestField_comp_contDiffAt h _ _ (hyperbolicHeight_pos w)).differentiableAt (by simp)
    have hsum := coverDirichletPair_sum_right Finset.univ (kernelTestField f)
      (fun r=>kernelTestField h ∘ euclideanAction (kernelCorrespondenceMatrix g r))
      (hyperbolicEuclideanCoordinates w) (fun r _=>hd r)
    simp only [Function.comp_apply] at hsum
    rw [hsum]
    change (∑r : IntegralCoverCosets H globalKubotaKernel,_)=
      ∑r : IntegralCoverCosets H globalKubotaKernel,
        kernelCorrespondencePair hHK hJK e g he f h (integralCoverFiberPoint H globalKubotaKernel r w)
    apply Finset.sum_congr rfl
    intro r _
    rw [integralCoverFiberPoint_rep,kernelCorrespondencePair_projection,
      kernelCorrespondencePairLift_kernel]
    rfl

lemma kernelCorrespondenceForm_integral (f h : kernelSmoothTests) :
    kernelDirichletForm f (kernelCorrespondenceTest hHK hJK e g he h)=
      ∫q,kernelCorrespondencePair hHK hJK e g he f h q∂integralQuotientVolume H := by
  unfold kernelDirichletForm
  simp_rw [kernelCorrespondencePair_trace]
  exact integralCoverTraceFunction_integral hHK globalKubotaKernel_le_levelThree _
    (kernelCorrespondencePair_measurable hHK hJK e g he f h)
    (kernelCorrespondencePair_integrable hHK hJK e g he f h)

omit [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondencePair_conjugate (f h : kernelSmoothTests) (q : IntegralOrbitQuotient H) :
    kernelCorrespondencePair hHK hJK e g he f h q=
      star (kernelCorrespondencePair hJK hHK e.symm g⁻¹
        (integralCoverIntertwines_inverse e g he) h f (integralConjugateMap e g he q)) := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change kernelCorrespondencePairLift g f h w=
      star (kernelCorrespondencePairLift g⁻¹ h f (g•w))
    have hf := (kernelTestField_contDiffAt h _ (euclideanAction_positive g (hyperbolicEuclideanCoordinates w))).differentiableAt (by simp)
    have hh := (kernelTestField_comp_contDiffAt f g⁻¹ _ (euclideanAction_positive g (hyperbolicEuclideanCoordinates w))).differentiableAt (by simp)
    have hc := coverDirichletPair_comp g (kernelTestField h) (kernelTestField f ∘ euclideanAction g⁻¹)
      (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w) hf hh
    rw [kernelTestField_comp_inverse] at hc
    have hs := congrArg star hc
    have hswap : star (inner ℂ
        (coverGradientAt (kernelTestField h ∘ euclideanAction g) (hyperbolicEuclideanCoordinates w))
        (coverGradientAt (kernelTestField f) (hyperbolicEuclideanCoordinates w)))=
        inner ℂ (coverGradientAt (kernelTestField f) (hyperbolicEuclideanCoordinates w))
          (coverGradientAt (kernelTestField h ∘ euclideanAction g) (hyperbolicEuclideanCoordinates w)) :=
      inner_conj_symm _ _
    rw [coverDirichletPair,hswap] at hs
    simpa only [kernelCorrespondencePairLift,coverDirichletPair,euclideanAction,
      euclideanToHyperbolic_coordinates] using hs

theorem kernelCorrespondenceForm_adjoint (f h : kernelSmoothTests) :
    kernelDirichletForm f (kernelCorrespondenceTest hHK hJK e g he h)=
      kernelDirichletForm (kernelCorrespondenceTest hJK hHK e.symm g⁻¹
        (integralCoverIntertwines_inverse e g he) f) h := by
  let opposite := kernelCorrespondencePair hJK hHK e.symm g⁻¹
    (integralCoverIntertwines_inverse e g he) h f
  have hom := kernelCorrespondencePair_measurable hJK hHK e.symm g⁻¹
    (integralCoverIntertwines_inverse e g he) h f
  have hm := integralConjugateMap_measurePreserving e g he
    (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree)
  rw [kernelCorrespondenceForm_integral]
  calc
    _ = ∫q,star (opposite (integralConjugateMap e g he q))∂integralQuotientVolume H := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (kernelCorrespondencePair_conjugate hHK hJK e g he f h)
    _ = ∫q,star (opposite q)∂integralQuotientVolume J := by
      have hh := integral_map («μ»:=integralQuotientVolume H) hm.measurable.aemeasurable
        (continuous_star.measurable.comp hom).aestronglyMeasurable
      rw [hm.map_eq] at hh
      exact hh.symm
    _ = star (∫q,opposite q∂integralQuotientVolume J) := by
      simp only [Complex.star_def]
      exact integral_conj
    _ = _ := by
      rw [←kernelCorrespondenceForm_integral hJK hHK e.symm g⁻¹
        (integralCoverIntertwines_inverse e g he),kernelDirichletForm_conj]

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)

lemma kernelCorrespondenceEnergy_pairing_core (f h : kernelSmoothTests) :
    inner ℂ (kernelEnergyGraphCore f)
      (kernelCorrespondenceEnergy hHK hJK e g he (kernelEnergyGraphCore h))=
    inner ℂ (kernelCorrespondenceEnergy hJK hHK e.symm g⁻¹
      (integralCoverIntertwines_inverse e g he) (kernelEnergyGraphCore f)) (kernelEnergyGraphCore h) := by
  rw [kernelCorrespondenceEnergy_core,kernelCorrespondenceEnergy_core,
    kernelEnergyGraph_inner,kernelEnergyGraph_inner]
  simp only [kernelEnergyMass_core,kernelEnergyGradient_core,kernelGradientToL2_inner]
  rw [kernelCorrespondenceTest_mass,kernelCorrespondenceTest_mass,
    kernelCorrespondenceL2_pairing,kernelCorrespondenceForm_adjoint]

theorem kernelCorrespondenceEnergy_pairing (u v : KernelEnergyGraph) :
    inner ℂ u (kernelCorrespondenceEnergy hHK hJK e g he v)=
      inner ℂ (kernelCorrespondenceEnergy hJK hHK e.symm g⁻¹
        (integralCoverIntertwines_inverse e g he) u) v := by
  apply congrFun (kernelEnergyGraphCore_dense.equalizer
    (continuous_id.inner continuous_const)
    ((kernelCorrespondenceEnergy hJK hHK e.symm g⁻¹
      (integralCoverIntertwines_inverse e g he)).continuous.inner continuous_const) ?_) u
  funext f
  apply congrFun (kernelEnergyGraphCore_dense.equalizer
    (continuous_const.inner (kernelCorrespondenceEnergy hHK hJK e g he).continuous)
    (continuous_const.inner continuous_id) ?_) v
  funext h
  exact kernelCorrespondenceEnergy_pairing_core hHK hJK e g he f h

lemma kernelCorrespondenceEnergy_pairing_left (u v : KernelEnergyGraph) :
    inner ℂ (kernelCorrespondenceEnergy hHK hJK e g he u) v=
      inner ℂ u (kernelCorrespondenceEnergy hJK hHK e.symm g⁻¹
        (integralCoverIntertwines_inverse e g he) v) := by
  exact (inner_conj_symm (𝕜 := ℂ) (E := KernelEnergyGraph) (kernelCorrespondenceEnergy hHK hJK e g he u) v).symm.trans ((congrArg (starRingEnd ℂ) (kernelCorrespondenceEnergy_pairing hHK hJK e g he v u)).trans
    (inner_conj_symm (𝕜 := ℂ) (E := KernelEnergyGraph) u (kernelCorrespondenceEnergy hJK hHK e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) v)))

lemma kernelCorrespondenceL2_pairing_left (F G : KernelQuotientL2) :
    inner ℂ (kernelCorrespondenceL2 hHK hJK e g he F) G=
      inner ℂ F (kernelCorrespondenceL2 hJK hHK e.symm g⁻¹
        (integralCoverIntertwines_inverse e g he) G) := by
  exact (inner_conj_symm (𝕜 := ℂ) (E := KernelQuotientL2) (kernelCorrespondenceL2 hHK hJK e g he F) G).symm.trans ((congrArg (starRingEnd ℂ) (kernelCorrespondenceL2_pairing hHK hJK e g he G F)).trans
    (inner_conj_symm (𝕜 := ℂ) (E := KernelQuotientL2) F (kernelCorrespondenceL2 hJK hHK e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) G)))

theorem kernelCorrespondence_variationalSolution (F : KernelQuotientL2) :
    kernelCorrespondenceEnergy hHK hJK e g he (kernelVariationalSolution F)=
      kernelVariationalSolution (kernelCorrespondenceL2 hHK hJK e g he F) := by
  apply kernelVariationalSolution_unique
  intro v
  rw [←kernelEnergyGraph_inner,kernelCorrespondenceEnergy_pairing_left,
    kernelEnergyGraph_inner,kernelVariationalSolution_equation,
    kernelCorrespondenceEnergy_mass]
  exact (kernelCorrespondenceL2_pairing_left hHK hJK e g he F (kernelEnergyMass v)).symm

theorem kernelCorrespondence_variationalResolvent (F : KernelQuotientL2) :
    kernelVariationalResolvent (kernelCorrespondenceL2 hHK hJK e g he F)=
      kernelCorrespondenceL2 hHK hJK e g he (kernelVariationalResolvent F) := by
  change kernelEnergyMass (kernelVariationalSolution (kernelCorrespondenceL2 hHK hJK e g he F))=_
  rw [←kernelCorrespondence_variationalSolution,kernelCorrespondenceEnergy_mass]
  rfl

theorem kernelCorrespondence_operatorGraph (F G : KernelQuotientL2)
    (hFG : (F,G)∈kernelEnergyLaplacian.graph) :
    (kernelCorrespondenceL2 hHK hJK e g he F,
      kernelCorrespondenceL2 hHK hJK e g he G)∈kernelEnergyLaplacian.graph := by
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph] at hFG ⊢
  rw [←map_add,kernelCorrespondence_variationalResolvent,hFG]

theorem kernelCorrespondence_eigenvector (F : KernelQuotientL2) (eigenvalue : ℂ)
    (hF : (F,eigenvalue • F)∈kernelEnergyLaplacian.graph) :
    (kernelCorrespondenceL2 hHK hJK e g he F,
      eigenvalue • kernelCorrespondenceL2 hHK hJK e g he F)∈kernelEnergyLaplacian.graph := by
  simpa only [map_smul] using kernelCorrespondence_operatorGraph hHK hJK e g he F (eigenvalue • F) hF

end

section

open MeasureTheory
open scoped Classical MatrixGroups BigOperators

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma cuspFrequency_mul_right (h c:Eis) : cuspFrequency (h*c)=cuspFrequency h*eisEmbedding c := by
  unfold cuspFrequency
  rw [map_mul]
  ring

lemma cusp_character_continuous (h:Eis) :
    Continuous (fun z:ℂ=>ShortDraftTrace.breveE (-cuspFrequency h*z)) := by
  change Continuous (fun z:ℂ=>Complex.exp (2*Real.pi*Complex.I*
    ((-cuspFrequency h*z)+starRingEnd ℂ (-cuspFrequency h*z))))
  fun_prop

lemma cusp_character_fractional_period (c:Eis) (hc:c≠0) (h q:Eis) (z:ℂ) :
    ShortDraftTrace.breveE (-cuspFrequency (h*c)*(z+3*eisEmbedding q/eisEmbedding c))=
      ShortDraftTrace.breveE (-cuspFrequency (h*c)*z) := by
  rw [mul_add,AddChar.map_add_eq_mul]
  have he:-cuspFrequency (h*c)*(3*eisEmbedding q/eisEmbedding c)=
      -cuspFrequency h*(3*eisEmbedding q):=by
    rw [cuspFrequency_mul_right]
    field_simp [eisEmbedding_ne_zero hc]
  rw [he]
  have hz:ShortDraftTrace.breveE (-cuspFrequency h*(3*eisEmbedding q))=1:=by
    simpa only [zero_add,mul_zero,AddChar.map_zero_eq_one] using cuspFrequency_negative_period h q 0
  rw [hz,mul_one]

lemma period_fourier_fractional_translation (f:ℂ→ℂ)
    (hf:∀n:Eis,∀z:ℂ,f (z+3*eisEmbedding n)=f z)
    (c:Eis) (hc:c≠0) (h q:Eis) :
    (∫z in periodDomain,f (z+3*eisEmbedding q/eisEmbedding c)*
      ShortDraftTrace.breveE (-cuspFrequency (h*c)*z))=
    ∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency (h*c)*z) := by
  let g:ℂ→ℂ:=fun z=>f z*ShortDraftTrace.breveE (-cuspFrequency (h*c)*z)
  have hg (n:Eis) (z:ℂ):g (z+3*eisEmbedding n)=g z:=by
    dsimp [g]
    rw [hf,cuspFrequency_negative_period]
  have hi:=period_integral_translation g hg (3*eisEmbedding q/eisEmbedding c)
  have hp (z:ℂ):g (3*eisEmbedding q/eisEmbedding c+z)=
      f (z+3*eisEmbedding q/eisEmbedding c)*ShortDraftTrace.breveE (-cuspFrequency (h*c)*z):=by
    dsimp [g]
    rw [add_comm (3*eisEmbedding q/eisEmbedding c) z,cusp_character_fractional_period c hc]
  simpa only [hp,g] using hi

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma cube_upperPoint_continuous (v:ℝ) (hv:0<v) : Continuous (fun z:ℂ=>upperPoint z v hv) := by
  let c:ℂ→UpperCoordinates:=fun z=>⟨(z,v),hv⟩
  have hc:Continuous c:=by
    apply Continuous.subtype_mk
    exact continuous_id.prodMk continuous_const
  simpa only [Function.comp_def,c] using continuous_upperCoordinates.comp hc

theorem cubeAverage_fourier (p:Eis) (hp:p≠0) (F:HyperbolicSpace→ℂ) (hF:Continuous F)
    (hperiod:∀n:Eis,∀w:HyperbolicSpace,F (complexTranslation (3*eisEmbedding n) • w)=F w)
    (h:Eis) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeAverage p hp F (upperPoint z v hv)*ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ∫z in periodDomain,F (upperPoint z (v/‖eisEmbedding p‖^3)
        (div_pos hv (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hp)) 3)))*
        ShortDraftTrace.breveE (-cuspFrequency (h*p^3)*z) := by
  let V:=v/‖eisEmbedding p‖^3
  have hV:0<V:=div_pos hv (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hp)) 3)
  let f:ℂ→ℂ:=fun z=>F (upperPoint z V hV)
  let H:ℂ→ℂ:=fun z=>cubeAverage p hp F (upperPoint z v hv)*ShortDraftTrace.breveE (-cuspFrequency h*z)
  have hf:Continuous f:=hF.comp (cube_upperPoint_continuous V hV)
  have hfperiod (n:Eis) (z:ℂ):f (z+3*eisEmbedding n)=f z:=by
    dsimp [f]
    rw [←complexTranslation_action]
    exact hperiod n _
  have hH:Continuous H:=
    ((cubeAverage_continuous p hp F hF).comp (cube_upperPoint_continuous v hv)).mul (cusp_character_continuous h)
  have hHperiod (n:Eis) (z:ℂ):H (z+3*eisEmbedding n)=H z:=by
    dsimp [H]
    rw [←complexTranslation_action,cubeAverage_period_three p hp F hperiod,cuspFrequency_negative_period]
  let term (r:Eis⧸Ideal.span {p^3}) (z:ℂ):=
    f (z+3*eisEmbedding (GaussianShiftedPartition.representative (p^3) r)/eisEmbedding (p^3))*
      ShortDraftTrace.breveE (-cuspFrequency (h*p^3)*z)
  have hpoint (z:ℂ):H (eisEmbedding (p^3)*z)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3*(∑' r:Eis⧸Ideal.span {p^3},term r z):=by
    have hphase:ShortDraftTrace.breveE (-cuspFrequency h*(eisEmbedding (p^3)*z))=
        ShortDraftTrace.breveE (-cuspFrequency (h*p^3)*z):=by
      rw [cuspFrequency_mul_right]
      congr 1
      ring
    dsimp only [H,cubeAverage]
    rw [hphase]
    rw [mul_assoc,←tsum_mul_right]
    congr 1
    apply tsum_congr
    intro r
    dsimp only [term,f]
    rw [cubeAverageMatrix_action]
    congr 2
    apply upperPoint_congr
    · rw [map_pow]
      field_simp [eisEmbedding_ne_zero hp]
    · rfl
  let:Finite (Eis⧸Ideal.span {p^3}):=finite_quotient_span (pow_ne_zero 3 hp)
  let:Fintype (Eis⧸Ideal.span {p^3}):=Fintype.ofFinite _
  have hi (r:Eis⧸Ideal.span {p^3}):IntegrableOn (term r) periodDomain:=by
    apply periodDomain_integrable_of_continuous
    exact (hf.comp (continuous_id.add continuous_const)).mul (cusp_character_continuous (h*p^3))
  have hint:(∫z in periodDomain,∑' r:Eis⧸Ideal.span {p^3},term r z)=
      ∑' r:Eis⧸Ideal.span {p^3},∫z in periodDomain,term r z:=by
    simp only [tsum_fintype]
    exact integral_finsetSum _ (fun r _=>hi r)
  have hterm (r:Eis⧸Ideal.span {p^3}):
      (∫z in periodDomain,term r z)=∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency (h*p^3)*z):=
    period_fourier_fractional_translation f hfperiod (p^3) (pow_ne_zero 3 hp) h _
  have hcard:(Nat.card (Eis⧸Ideal.span {p^3}):ℂ)=(Ideal.absNorm (Ideal.span {p}):ℂ)^3:=by
    change (Ideal.absNorm (Ideal.span {p^3}):ℂ)=_
    rw [←Ideal.span_singleton_pow,map_pow,Nat.cast_pow]
  have hqN:Ideal.absNorm (Ideal.span {p})≠0:=
    (Ideal.absNorm_ne_zero_iff _).mpr (finite_quotient_span hp)
  have hq:(Ideal.absNorm (Ideal.span {p}):ℂ)≠0:=by exact_mod_cast hqN
  change (∫z in periodDomain,H z)=∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency (h*p^3)*z)
  calc
    _=∫z in periodDomain,H (eisEmbedding (p^3)*z):=
      (period_integral_eisenstein_mul H hH.measurable hHperiod (p^3) (pow_ne_zero 3 hp)).symm
    _=(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3*
        (∑' r:Eis⧸Ideal.span {p^3},∫z in periodDomain,term r z):=by
      simp_rw [hpoint]
      rw [integral_const_mul,hint]
    _=(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3*
        (∑' (_:Eis⧸Ideal.span {p^3}),∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency (h*p^3)*z)):=by
      congr 1
      exact tsum_congr hterm
    _=_:=by rw [tsum_const,nsmul_eq_mul,hcard];field_simp

end

open MeasureTheory
open scoped Classical MatrixGroups BigOperators
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

theorem cubeSource_fourier (p:Eis) (hp:p≠0) (h:Eis) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeAverage p hp cubicSourceResidualFunction (upperPoint z v hv)*
      ShortDraftTrace.breveE (-cuspFrequency h*z))=
    ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceResidualFullModeAmplitude (v/‖eisEmbedding p‖^3) (h*p^3) := by
  rw [cubeAverage_fourier p hp cubicSourceResidualFunction cubicSourceResidualFunction_continuous
    cubicSource_period_three h v hv]
  simp_rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselFunction_fourier _ (div_pos hv (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hp)) 3)) _

lemma cubeSource_amplitude_of_eigenrelation (p:Eis) (hp:p≠0)
    (hU:∀w:HyperbolicSpace,cubeAverage p hp cubicSourceResidualFunction w=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction w)
    (h:Eis) (v:ℝ) (hv:0<v) :
    sourceResidualFullModeAmplitude (v/‖eisEmbedding p‖^3) (h*p^3)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceResidualFullModeAmplitude v h := by
  have hc:((9*Real.sqrt 3/2:ℝ):ℂ)≠0:=Complex.ofReal_ne_zero.mpr (by positivity)
  apply mul_left_cancel₀ hc
  calc
    _=∫z in periodDomain,cubeAverage p hp cubicSourceResidualFunction (upperPoint z v hv)*
      ShortDraftTrace.breveE (-cuspFrequency h*z):=(cubeSource_fourier p hp h v hv).symm
    _=(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*
      (∫z in periodDomain,cubicSourceResidualFunction (upperPoint z v hv)*
        ShortDraftTrace.breveE (-cuspFrequency h*z)):=by
      simp_rw [hU,mul_assoc]
      exact integral_const_mul _ _
    _=(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*
      (((9*Real.sqrt 3/2:ℝ):ℂ)*sourceResidualFullModeAmplitude v h):=by
      simp_rw [cubicSourceResidualFunction_eq_bessel]
      rw [sourceBesselFunction_fourier]
    _=_:=by ring

lemma schlafliBesselK_cubic_ne_zero (x:ℝ) (hx:0<x) : schlafliBesselK (1/3:ℂ) x≠0 := by
  have hp:0<(schlafliBesselK (1/3:ℂ) x).re:=
    lt_of_lt_of_le (mul_pos cubicBesselLowerConstant_pos (Real.exp_pos _)) (schlafliBesselK_cubic_lower x hx)
  intro he
  rw [he,Complex.zero_re] at hp
  exact (lt_irrefl 0) hp

theorem sourceResidualFourierCoefficient_cube_of_eigenrelation (p:Eis) (hp:p≠0)
    (hU:∀w:HyperbolicSpace,cubeAverage p hp cubicSourceResidualFunction w=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction w)
    (h:Eis) (hh:h≠0) :
    sourceResidualFourierCoefficient (h*p^3)=(‖eisEmbedding p‖:ℂ)*sourceResidualFourierCoefficient h := by
  have hhp:h*p^3≠0:=mul_ne_zero hh (pow_ne_zero 3 hp)
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp)
  have hrC:(‖eisEmbedding p‖:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hr.ne'
  have hf:‖cuspFrequency (h*p^3)‖=‖cuspFrequency h‖*‖eisEmbedding p‖^3:=by
    rw [cuspFrequency_mul_right,norm_mul,map_pow,norm_pow]
  have hx:0<4*Real.pi*‖cuspFrequency h‖:=by
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (norm_pos_iff.mpr (cuspFrequency_ne_zero h hh))
  have hK:=schlafliBesselK_cubic_ne_zero _ hx
  have he:=cubeSource_amplitude_of_eigenrelation p hp hU h 1 (by norm_num)
  simp only [sourceResidualFullModeAmplitude,if_neg hhp,if_neg hh,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_pow,mul_one,hf] at he
  have harg:4*Real.pi*(‖cuspFrequency h‖*‖eisEmbedding p‖^3)*(1/‖eisEmbedding p‖^3)=
      4*Real.pi*‖cuspFrequency h‖:=by field_simp
  rw [harg] at he
  have he':sourceResidualFourierCoefficient (h*p^3)/(‖eisEmbedding p‖:ℂ)^3=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceResidualFourierCoefficient h:=by
    apply mul_right_cancel₀ hK
    simpa only [div_eq_mul_inv,one_mul,mul_assoc] using he
  have hn:(Ideal.absNorm (Ideal.span {p}):ℂ)=(‖eisEmbedding p‖:ℂ)^2:=by
    exact_mod_cast (eisEmbedding_norm_sq_eq_absNorm_span p).symm
  rw [hn] at he'
  have he'' :=(div_eq_iff (pow_ne_zero 3 hrC)).mp he'
  rw [he'']
  field_simp

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CubicEisenstein

section

open scoped Classical MatrixGroups BigOperators
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma positive_cube_cpow_third (r:ℝ) (hr:0< r) :
    ((r^3:ℝ):ℂ)^(1/3:ℂ)=(r:ℂ) := by
  calc
    _=(((r^3)^(1/3:ℝ):ℝ):ℂ):=by
      simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using
        (Complex.ofReal_cpow (pow_nonneg hr.le 3) (1/3)).symm
    _=_:=by
      congr 1
      rw [←Real.rpow_natCast_mul hr.le 3]
      norm_num

lemma cubicBesselNormalizer_mul_cube (h p:Eis) (hp:p≠0) :
    cubicBesselNormalizer (h*p^3)=(‖eisEmbedding p‖:ℂ)*cubicBesselNormalizer h := by
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp)
  have hf:‖cuspFrequency (h*p^3)‖=‖cuspFrequency h‖*‖eisEmbedding p‖^3:=by
    rw [cuspFrequency_mul_right,norm_mul,map_pow,norm_pow]
  have ha:0≤2*Real.pi*‖cuspFrequency h‖:=by positivity
  have he:(2*Real.pi*‖cuspFrequency (h*p^3)‖:ℂ)=
      ((‖eisEmbedding p‖^3:ℝ):ℂ)*((2*Real.pi*‖cuspFrequency h‖:ℝ):ℂ):=by
    rw [hf]
    push_cast
    ring
  unfold cubicBesselNormalizer
  rw [he,Complex.mul_cpow_ofReal_nonneg (pow_nonneg hr.le 3) ha,
    positive_cube_cpow_third _ hr]
  push_cast
  ring

theorem sourceArithmeticResidue_cube_of_eigenrelation (p:Eis) (hp:p≠0)
    (hU:∀w:HyperbolicSpace,cubeAverage p hp cubicSourceResidualFunction w=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction w)
    (h:Eis) (hh:h≠0) : sourceArithmeticResidue (h*p^3)=sourceArithmeticResidue h := by
  have ht:=sourceResidualFourierCoefficient_cube_of_eigenrelation p hp hU h hh
  unfold sourceResidualFourierCoefficient at ht
  rw [cubicBesselNormalizer_mul_cube h p hp] at ht
  have hr:(‖eisEmbedding p‖:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp))
  apply mul_left_cancel₀ (mul_ne_zero hr (cubicBesselNormalizer_ne_zero h hh))
  simpa only [mul_assoc] using ht

end

open MeasureTheory
open scoped Classical MatrixGroups BigOperators
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

def cubeSourceDifference (p:Eis) (hp:p≠0) (w:HyperbolicSpace) : ℂ :=
  cubeAverage p hp cubicSourceResidualFunction w-
    (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction w

lemma cubeSourceDifference_continuous (p:Eis) (hp:p≠0) :
    Continuous (cubeSourceDifference p hp) :=
  (cubeAverage_continuous p hp cubicSourceResidualFunction cubicSourceResidualFunction_continuous).sub
    (continuous_const.mul cubicSourceResidualFunction_continuous)

lemma cubeSourceDifference_decay (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (K:ℝ) (hK:0≤K)
    (hrep:∀j:Fin 3,∀z:ℂ,∀v:ℝ,∀hv:0<v,(‖eisEmbedding p‖^3)⁻¹≤v→
      ‖sourceCuspRemainder (cuspRepresentative j) z v hv‖≤K/v^3)
    (M:SL(2,Eis)) (z:ℂ) (v:ℝ) (hv:0<v) (hv1:1≤v) :
    ‖cubeSourceDifference p hp.ne_zero (integralComplexMatrix M • upperPoint z v hv)‖≤
      (K*(‖eisEmbedding p‖^9+(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹))/v^3 :=
  cubeSource_difference_decay_from_representatives p hp hprimary K hK hrep M z v hv hv1

end CubicEisenstein

open scoped Classical

namespace FiniteAutomorphismCover

variable {G : Type*} [Group G] {ι : Type*}

def common (K R : Subgroup G) (a : ι → G ≃* G) : Subgroup G :=
  K ⊓ ⨅i, R.comap (a i).toMonoidHom

lemma common_le (K R : Subgroup G) (a : ι → G ≃* G) : common K R a ≤ K :=
  inf_le_left

lemma common_le_preimage (K R : Subgroup G) (a : ι → G ≃* G) (i : ι) :
    common K R a ≤ R.comap (a i).toMonoidHom :=
  inf_le_right.trans (iInf_le _ i)

instance common_finiteIndex [Finite ι] (K R : Subgroup G) (a : ι → G ≃* G)
    [K.FiniteIndex] [R.FiniteIndex] : (common K R a).FiniteIndex := by
  let : (⨅i, R.comap (a i).toMonoidHom).FiniteIndex :=
    Subgroup.finiteIndex_iInf (fun i => inferInstance)
  unfold common
  infer_instance

def toSource (K R : Subgroup G) (a : ι → G ≃* G) (i : ι) : common K R a →* R where
  toFun h := ⟨a i (h : G), common_le_preimage K R a i h.property⟩
  map_one' := Subtype.ext (map_one (a i))
  map_mul' x y := Subtype.ext (map_mul (a i) (x : G) (y : G))

@[simp] lemma toSource_coe (K R : Subgroup G) (a : ι → G ≃* G) (i : ι)
    (h : common K R a) : (toSource K R a i h : G) = a i (h : G) := rfl

lemma toSource_injective (K R : Subgroup G) (a : ι → G ≃* G) (i : ι) :
    Function.Injective (toSource K R a i) := by
  intro x y hxy
  apply Subtype.ext
  exact (a i).injective (congrArg (fun r : R => (r : G)) hxy)

lemma toSource_range (K R : Subgroup G) (a : ι → G ≃* G) (i : ι) :
    (toSource K R a i).range =
      (common K R a).comap ((a i).symm.toMonoidHom.comp R.subtype) := by
  ext r
  constructor
  · rintro ⟨h,rfl⟩
    change (a i).symm (a i (h : G)) ∈ common K R a
    simpa only [MulEquiv.symm_apply_apply] using h.property
  · intro hr
    refine ⟨⟨(a i).symm (r : G),hr⟩,?_⟩
    apply Subtype.ext
    exact (a i).apply_symm_apply (r : G)

instance toSource_range_finiteIndex [Finite ι] (K R : Subgroup G) (a : ι → G ≃* G)
    [K.FiniteIndex] [R.FiniteIndex] (i : ι) : (toSource K R a i).range.FiniteIndex := by
  rw [toSource_range]
  infer_instance

def hom (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) :
    common K R a →* G :=
  lengthScale.subtype.comp (e.toMonoidHom.comp (toSource K R a i))

@[simp] lemma hom_apply (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale)
    (i : ι) (h : common K R a) :
    hom K R lengthScale a e i h = (e (toSource K R a i h) : G) := rfl

lemma hom_injective (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) :
    Function.Injective (hom K R lengthScale a e i) :=
  lengthScale.subtype_injective.comp (e.injective.comp (toSource_injective K R a i))

def target (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) : Subgroup G :=
  (hom K R lengthScale a e i).range

lemma target_le (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) :
    target K R lengthScale a e i ≤ lengthScale := by
  rintro x ⟨h,rfl⟩
  exact (e (toSource K R a i h)).property

lemma target_le_common_ambient (K R lengthScale : Subgroup G) (a : ι → G ≃* G)
    (e : R ≃* lengthScale) (hLK : lengthScale ≤ K) (i : ι) : target K R lengthScale a e i ≤ K :=
  (target_le K R lengthScale a e i).trans hLK

lemma target_eq_map (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) :
    target K R lengthScale a e i = ((toSource K R a i).range.map e.toMonoidHom).map lengthScale.subtype := by
  rw [target,hom,MonoidHom.range_comp,MonoidHom.range_comp]

instance target_finiteIndex [Finite ι] (K R lengthScale : Subgroup G) (a : ι → G ≃* G)
    (e : R ≃* lengthScale) [K.FiniteIndex] [R.FiniteIndex] [lengthScale.FiniteIndex] (i : ι) :
    (target K R lengthScale a e i).FiniteIndex := by
  let : ((toSource K R a i).range.map e.toMonoidHom).FiniteIndex :=
    Subgroup.FiniteIndex.map_of_surjective _ e.surjective
  constructor
  rw [target_eq_map,Subgroup.index_map_subtype]
  exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.FiniteIndex.index_ne_zero

def equiv (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) :
    common K R a ≃* target K R lengthScale a e i :=
  MonoidHom.ofInjective (hom_injective K R lengthScale a e i)

@[simp] lemma equiv_coe (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale)
    (i : ι) (h : common K R a) :
    (equiv K R lengthScale a e i h : G) = (e (toSource K R a i h) : G) := rfl

end FiniteAutomorphismCover

namespace CubicKubota
open scoped BigOperators Classical MatrixGroups

open CubicEisenstein ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma literalCube_zero_pair (p : ActualEisensteinCubic.O) (hp : p≠0) (x : cubeKernelCorrespondence p) :
    cubeAverageMatrix p hp 0*integralComplexMatrix (cubeKernelRightGlobal p hp x)=
      integralComplexMatrix (cubeKernelLeftGlobal p x)*cubeAverageMatrix p hp 0 := by
  let M := cubeKernelLeftGlobal p x
  let N := cubeKernelRightGlobal p hp x
  let z := cubeDilationRoot p
  have hz : z^2=eisEmbedding p^3 := cubeDilationRoot_sq p
  have hz0 : z≠0 := cubeDilationRoot_ne_zero p hp
  have he := cubeCorrespondence_entries p x.1
  change p^3*M 0 0=N 0 0*p^3 ∧ p^3*M 0 1=N 0 1 ∧
    M 1 0=N 1 0*p^3 ∧ M 1 1=N 1 1 at he
  have h00 : eisEmbedding (M 0 0)=eisEmbedding (N 0 0) :=
    congrArg eisEmbedding (mul_left_cancel₀ (pow_ne_zero 3 hp) (he.1.trans (mul_comm _ _)))
  have h01 := congrArg eisEmbedding he.2.1
  have h10 := congrArg eisEmbedding he.2.2.1
  have h11 := congrArg eisEmbedding he.2.2.2
  simp only [map_mul,map_pow] at h01 h10
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,
      cubeAverageMatrix_entries,integralComplexMatrix_apply]
  · change z⁻¹*eisEmbedding (N 0 0)+(z⁻¹*(3*eisEmbedding 0))*eisEmbedding (N 1 0)=
      eisEmbedding (M 0 0)*z⁻¹+eisEmbedding (M 0 1)*0
    rw [h00,map_zero]
    ring
  · change z⁻¹*eisEmbedding (N 0 1)+(z⁻¹*(3*eisEmbedding 0))*eisEmbedding (N 1 1)=
      eisEmbedding (M 0 0)*(z⁻¹*(3*eisEmbedding 0))+eisEmbedding (M 0 1)*z
    rw [←h01,←hz,map_zero]
    field_simp [hz0]
    ; ring
  · change 0*eisEmbedding (N 0 0)+z*eisEmbedding (N 1 0)=
      eisEmbedding (M 1 0)*z⁻¹+eisEmbedding (M 1 1)*0
    rw [h10,←hz]
    field_simp [hz0]
    ; ring
  · change 0*eisEmbedding (N 0 1)+z*eisEmbedding (N 1 1)=
      eisEmbedding (M 1 0)*(z⁻¹*(3*eisEmbedding 0))+eisEmbedding (M 1 1)*z
    rw [h11,map_zero]
    ring

theorem literalCube_zero_intertwines (p : ActualEisensteinCubic.O) (hp : p≠0) :
    IntegralCoverIntertwines (cubeKernelRangeEquiv p hp).symm (cubeAverageMatrix p hp 0) := by
  intro r
  let x := (MonoidHom.ofInjective (cubeKernelRightGlobal_injective p hp)).symm r
  have hr : cubeKernelRightGlobal p hp x=(r:SL(2,ActualEisensteinCubic.O)) :=
    MonoidHom.apply_ofInjective_symm (cubeKernelRightGlobal_injective p hp) r
  change cubeAverageMatrix p hp 0*integralComplexMatrix (r:SL(2,ActualEisensteinCubic.O))=
    integralComplexMatrix (cubeKernelLeftGlobal p x)*cubeAverageMatrix p hp 0
  rw [←hr]
  exact literalCube_zero_pair p hp x

lemma cubeTranslation_complex (q : ActualEisensteinCubic.O) :
    integralComplexMatrix (upperTranslation q:SL(2,ActualEisensteinCubic.O))=complexTranslation (3*eisEmbedding q) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [integralComplexMatrix_apply]
  fin_cases i <;> fin_cases j <;> simp [upperTranslation, complexTranslation, map_ofNat]

lemma cubeAverageMatrix_factor_zero (p : ActualEisensteinCubic.O) (hp : p≠0) (q : ActualEisensteinCubic.O) :
    cubeAverageMatrix p hp q=cubeAverageMatrix p hp 0*
      integralComplexMatrix (upperTranslation q:SL(2,ActualEisensteinCubic.O)) := by
  rw [cubeTranslation_complex]
  have h0 : complexTranslation 0=1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [complexTranslation]
  simp only [cubeAverageMatrix,map_zero,mul_zero,h0,mul_one]

theorem literalCube_summand_intertwines (p : ActualEisensteinCubic.O) (hp : p≠0) (q : ActualEisensteinCubic.O)
    (A : SL(2,ActualEisensteinCubic.O)) (r : (cubeKernelRightGlobal p hp).range)
    (hA : (upperTranslation q:SL(2,ActualEisensteinCubic.O))*A=(r:SL(2,ActualEisensteinCubic.O))*(upperTranslation q:SL(2,ActualEisensteinCubic.O))) :
    cubeAverageMatrix p hp q*integralComplexMatrix A=
      integralComplexMatrix ((cubeKernelRangeEquiv p hp).symm r:SL(2,ActualEisensteinCubic.O))*cubeAverageMatrix p hp q := by
  have hAc := congrArg integralComplexMatrix hA
  simp only [map_mul] at hAc
  rw [cubeAverageMatrix_factor_zero,mul_assoc,hAc,←mul_assoc,
    literalCube_zero_intertwines p hp r,mul_assoc]

end CubicKubota

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma integralCoverIntertwines_trans {H J K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (f : J≃*K) (g h : SL(2,ℂ))
    (he : IntegralCoverIntertwines e g) (hf : IntegralCoverIntertwines f h) :
    IntegralCoverIntertwines (e.trans f) (h*g) := by
  intro x
  change (h*g)*integralComplexMatrix (x:SL(2,ActualEisensteinCubic.O))=
    integralComplexMatrix (f (e x):SL(2,ActualEisensteinCubic.O))*(h*g)
  rw [mul_assoc,he x,←mul_assoc,hf (e x),mul_assoc]

lemma integralConjugateMap_trans {H J K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (f : J≃*K) (g h : SL(2,ℂ))
    (he : IntegralCoverIntertwines e g) (hf : IntegralCoverIntertwines f h)
    (q : IntegralOrbitQuotient H) :
    integralConjugateMap f h hf (integralConjugateMap e g he q)=
      integralConjugateMap (e.trans f) (h*g) (integralCoverIntertwines_trans e f g h he hf) q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection K (h•(g•w))=integralOrbitProjection K ((h*g)•w)
    rw [mul_smul]

lemma integralConjugatePullback_trans {H J K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (f : J≃*K) (g h : SL(2,ℂ))
    (he : IntegralCoverIntertwines e g) (hf : IntegralCoverIntertwines f h)
    (hH : H≤CubicKubota.levelThree) (hJ : J≤CubicKubota.levelThree)
    (hK : K≤CubicKubota.levelThree) (F : IntegralQuotientL2 K) :
    integralConjugatePullback e g he hH hJ (integralConjugatePullback f h hf hJ hK F)=
      integralConjugatePullback (e.trans f) (h*g) (integralCoverIntertwines_trans e f g h he hf) hH hK F := by
  apply Lp.ext
  have hinner := (integralConjugateMap_measurePreserving e g he hH hJ).quasiMeasurePreserving.ae_eq_comp
    (integralConjugatePullback_ae f h hf hJ hK F)
  filter_upwards [integralConjugatePullback_ae e g he hH hJ (integralConjugatePullback f h hf hJ hK F),
    hinner,integralConjugatePullback_ae (e.trans f) (h*g)
      (integralCoverIntertwines_trans e f g h he hf) hH hK F] with q ho hi ht
  dsimp only [Function.comp_def] at hi
  rw [ho,hi,ht,integralConjugateMap_trans]

def kernelCoverLeg {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g) :
    KernelQuotientL2→L[ℂ]IntegralQuotientL2 H :=
  (integralConjugatePullback e g he (hHK.trans globalKubotaKernel_le_levelThree)
    (hJK.trans globalKubotaKernel_le_levelThree)).toContinuousLinearMap.comp
      (integralCoverPullback hJK globalKubotaKernel_le_levelThree)

lemma kernelCoverLeg_representative {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (F : KernelQuotientL2) (f : KernelQuotient→ℂ)
    (hrep : F=ᵐ[integralQuotientVolume globalKubotaKernel]f) :
    kernelCoverLeg hHK hJK e g he F=ᵐ[integralQuotientVolume H]
      fun q=>f (integralCoverMap hJK (integralConjugateMap e g he q)) := by
  have hc := (integralCoverPullback_ae hJK globalKubotaKernel_le_levelThree F).trans
    ((integralCoverMap_quasiMeasurePreserving hJK globalKubotaKernel_le_levelThree).ae_eq_comp hrep)
  exact (integralConjugatePullback_ae e g he
    (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree) _).trans
    ((integralConjugateMap_measurePreserving e g he
      (hHK.trans globalKubotaKernel_le_levelThree)
      (hJK.trans globalKubotaKernel_le_levelThree)).quasiMeasurePreserving.ae_eq_comp hc)

lemma kernelCoverLeg_adjoint_apply {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (F : IntegralQuotientL2 H) :
    ContinuousLinearMap.adjoint (kernelCoverLeg hHK hJK e g he) F=
      integralCoverTrace hJK globalKubotaKernel_le_levelThree
        (integralConjugatePullback e.symm g⁻¹ (integralCoverIntertwines_inverse e g he)
          (hJK.trans globalKubotaKernel_le_levelThree) (hHK.trans globalKubotaKernel_le_levelThree) F) := by
  apply ext_inner_right ℂ
  intro G
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ F (integralConjugatePullback e g he
    (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree)
    (integralCoverPullback hJK globalKubotaKernel_le_levelThree G))=_
  rw [integralConjugatePullback_pairing]
  exact (ContinuousLinearMap.adjoint_inner_left (integralCoverPullback hJK globalKubotaKernel_le_levelThree) G _).symm

theorem kernelCoverLeg_adjoint_comp {H Ji Jj : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hiK : Ji≤globalKubotaKernel) (hjK : Jj≤globalKubotaKernel)
    [Ji.IsFiniteRelIndex globalKubotaKernel] [Jj.IsFiniteRelIndex globalKubotaKernel]
    (ei : H≃*Ji) (ej : H≃*Jj) (gi gj : SL(2,ℂ))
    (hei : IntegralCoverIntertwines ei gi) (hej : IntegralCoverIntertwines ej gj) :
    (ContinuousLinearMap.adjoint (kernelCoverLeg hHK hjK ej gj hej)).comp
      (kernelCoverLeg hHK hiK ei gi hei)=
        kernelCorrespondenceL2 hjK hiK (ej.symm.trans ei) (gi*gj⁻¹)
          (integralCoverIntertwines_trans ej.symm ei gj⁻¹ gi
            (integralCoverIntertwines_inverse ej gj hej) hei) := by
  apply ContinuousLinearMap.ext
  intro F
  change ContinuousLinearMap.adjoint (kernelCoverLeg hHK hjK ej gj hej)
    (kernelCoverLeg hHK hiK ei gi hei F)=_
  rw [kernelCoverLeg_adjoint_apply]
  change integralCoverTrace hjK globalKubotaKernel_le_levelThree
    (integralConjugatePullback ej.symm gj⁻¹ (integralCoverIntertwines_inverse ej gj hej)
      (hjK.trans globalKubotaKernel_le_levelThree) (hHK.trans globalKubotaKernel_le_levelThree)
      (integralConjugatePullback ei gi hei
        (hHK.trans globalKubotaKernel_le_levelThree) (hiK.trans globalKubotaKernel_le_levelThree)
        (integralCoverPullback hiK globalKubotaKernel_le_levelThree F)))=_
  rw [integralConjugatePullback_trans]
  rfl

end CubicEisenstein

open scoped Classical MatrixGroups BigOperators

namespace CubicKubota
open CubicEisenstein ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

abbrev CubeResidues (p : ActualEisensteinCubic.O) := ActualEisensteinCubic.O ⧸ Ideal.span {p^3}

def cubeCommonAutomorphism (p : ActualEisensteinCubic.O) (r : CubeResidues p) : SL(2,ActualEisensteinCubic.O) ≃* SL(2,ActualEisensteinCubic.O) :=
  MulAut.conj (upperTranslation (GaussianShiftedPartition.representative (p^3) r):SL(2,ActualEisensteinCubic.O))

def cubeCommonCover (p : ActualEisensteinCubic.O) (hp : p≠0) : Subgroup (SL(2,ActualEisensteinCubic.O)) :=
  FiniteAutomorphismCover.common globalKubotaKernel
    (cubeKernelRightGlobal p hp).range (cubeCommonAutomorphism p)

lemma cubeCommonCover_le (p : ActualEisensteinCubic.O) (hp : p≠0) : cubeCommonCover p hp≤globalKubotaKernel :=
  FiniteAutomorphismCover.common_le _ _ _

lemma cubeCommonCover_finiteIndex (p : ActualEisensteinCubic.O) (hp : p≠0) : (cubeCommonCover p hp).FiniteIndex := by
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  let : Finite (CubeResidues p) := finite_quotient_span (pow_ne_zero 3 hp)
  let := (cubeKernelGlobal_finite_covers p hp).2
  exact FiniteAutomorphismCover.common_finiteIndex _ _ _

def cubeCommonTarget (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) : Subgroup (SL(2,ActualEisensteinCubic.O)) :=
  FiniteAutomorphismCover.target globalKubotaKernel
    (cubeKernelRightGlobal p hp).range (cubeKernelLeftGlobal p).range
    (cubeCommonAutomorphism p) (cubeKernelRangeEquiv p hp).symm r

lemma cubeCommonTarget_le (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) :
    cubeCommonTarget p hp r≤globalKubotaKernel :=
  FiniteAutomorphismCover.target_le_common_ambient _ _ _ _ _ (cubeKernelLeftGlobal_le p) r

lemma cubeCommonTarget_finiteIndex (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) :
    (cubeCommonTarget p hp r).FiniteIndex := by
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  let : Finite (CubeResidues p) := finite_quotient_span (pow_ne_zero 3 hp)
  let := (cubeKernelGlobal_finite_covers p hp).1
  let := (cubeKernelGlobal_finite_covers p hp).2
  exact FiniteAutomorphismCover.target_finiteIndex _ _ _ _ _ r

def cubeCommonEquiv (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) :
    cubeCommonCover p hp≃*cubeCommonTarget p hp r :=
  FiniteAutomorphismCover.equiv globalKubotaKernel
    (cubeKernelRightGlobal p hp).range (cubeKernelLeftGlobal p).range
    (cubeCommonAutomorphism p) (cubeKernelRangeEquiv p hp).symm r

lemma cubeCommon_intertwines (p : ActualEisensteinCubic.O) (hp : p≠0) (r : CubeResidues p) :
    IntegralCoverIntertwines (cubeCommonEquiv p hp r)
      (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r)) := by
  intro h
  let q := GaussianShiftedPartition.representative (p^3) r
  let rh := FiniteAutomorphismCover.toSource globalKubotaKernel
    (cubeKernelRightGlobal p hp).range (cubeCommonAutomorphism p) r h
  have hA : (upperTranslation q:SL(2,ActualEisensteinCubic.O))*(h:SL(2,ActualEisensteinCubic.O))=
      (rh:SL(2,ActualEisensteinCubic.O))*(upperTranslation q:SL(2,ActualEisensteinCubic.O)) := by
    change (upperTranslation q:SL(2,ActualEisensteinCubic.O))*(h:SL(2,ActualEisensteinCubic.O))=
      ((upperTranslation q:SL(2,ActualEisensteinCubic.O))*(h:SL(2,ActualEisensteinCubic.O))*(upperTranslation q:SL(2,ActualEisensteinCubic.O))⁻¹)*
        (upperTranslation q:SL(2,ActualEisensteinCubic.O))
    simp only [mul_assoc,inv_mul_cancel,mul_one]
  exact literalCube_summand_intertwines p hp q (h:SL(2,ActualEisensteinCubic.O)) rh hA

end CubicKubota

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped Classical MatrixGroups BigOperators

namespace CubicEisenstein
open CubicKubota
local notation "O" => ActualEisensteinCubic.O

lemma cubicSourceResidualFunction_kernel_invariant (M : globalKubotaKernel)
    (w : HyperbolicSpace) :
    cubicSourceResidualFunction (integralComplexMatrix (M:SL(2,ActualEisensteinCubic.O)) • w)=
      cubicSourceResidualFunction w := by
  obtain ⟨hM,hchar⟩ := (globalKubotaKernel_mem (M:SL(2,ActualEisensteinCubic.O))).mp M.property
  have h := cubicSourceResidualFunction_automorphy
    ⟨(M:SL(2,ActualEisensteinCubic.O)),levelThree_le_levelTwo hM⟩ w
  rw [levelTwoComplexCharacter_restrict ⟨(M:SL(2,ActualEisensteinCubic.O)),hM⟩,hchar,one_mul] at h
  exact h

def cubicSourceQuotientFunction : KernelQuotient→ℂ :=
  Quotient.lift cubicSourceResidualFunction (by
    rintro w u ⟨h,rfl⟩
    exact (cubicSourceResidualFunction_kernel_invariant h w).symm)

lemma cubicSourceQuotientFunction_measurable : Measurable cubicSourceQuotientFunction := by
  apply measurable_from_quotient.mpr
  exact cubicSourceResidualFunction_continuous.measurable

lemma cubicSourceQuotientFunction_represents :
    kernelSourceProjection cubicEisensteinResidue=ᵐ[integralQuotientVolume globalKubotaKernel]
      cubicSourceQuotientFunction := by
  unfold integralQuotientVolume
  apply (ae_map_iff (measurable_integralOrbitProjection _).aemeasurable
    (measurableSet_eq_fun (Lp.stronglyMeasurable _).measurable
      cubicSourceQuotientFunction_measurable)).mpr
  exact ae_restrict_of_ae cubicSourceResidualFunction_represents_projection

end CubicEisenstein

namespace CubicKubota
open CubicEisenstein ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

abbrev CubeLegIndex (p : ActualEisensteinCubic.O) := Option (CubeResidues p)

def cubeLegTarget (p : ActualEisensteinCubic.O) (hp : p≠0) : CubeLegIndex p→Subgroup (SL(2,ActualEisensteinCubic.O))
  | none => cubeCommonCover p hp
  | some r => cubeCommonTarget p hp r

lemma cubeLegTarget_le (p : ActualEisensteinCubic.O) (hp : p≠0) (i : CubeLegIndex p) :
    cubeLegTarget p hp i≤globalKubotaKernel := by
  cases i with
  | none => exact cubeCommonCover_le p hp
  | some r => exact cubeCommonTarget_le p hp r

lemma cubeLegTarget_finiteIndex (p : ActualEisensteinCubic.O) (hp : p≠0) (i : CubeLegIndex p) :
    (cubeLegTarget p hp i).FiniteIndex := by
  cases i with
  | none => exact cubeCommonCover_finiteIndex p hp
  | some r => exact cubeCommonTarget_finiteIndex p hp r

def cubeLegEquiv (p : ActualEisensteinCubic.O) (hp : p≠0) : (i : CubeLegIndex p)→
    cubeCommonCover p hp≃*cubeLegTarget p hp i
  | none => MulEquiv.refl _
  | some r => cubeCommonEquiv p hp r

def cubeLegMatrix (p : ActualEisensteinCubic.O) (hp : p≠0) : CubeLegIndex p→SL(2,ℂ)
  | none => 1
  | some r => cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r)

lemma cubeLeg_intertwines (p : ActualEisensteinCubic.O) (hp : p≠0) (i : CubeLegIndex p) :
    IntegralCoverIntertwines (cubeLegEquiv p hp i) (cubeLegMatrix p hp i) := by
  cases i with
  | none =>
    intro h
    change 1*integralComplexMatrix (h:SL(2,ActualEisensteinCubic.O))=integralComplexMatrix (h:SL(2,ActualEisensteinCubic.O))*1
    simp only [one_mul,mul_one]
  | some r => exact cubeCommon_intertwines p hp r

def cubeLeg (p : ActualEisensteinCubic.O) (hp : p≠0) (i : CubeLegIndex p) :
    KernelQuotientL2→L[ℂ]IntegralQuotientL2 (cubeCommonCover p hp) := by
  letI := cubeLegTarget_finiteIndex p hp i
  letI : (cubeLegTarget p hp i).IsFiniteRelIndex globalKubotaKernel :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  exact kernelCoverLeg (cubeCommonCover_le p hp) (cubeLegTarget_le p hp i)
    (cubeLegEquiv p hp i) (cubeLegMatrix p hp i) (cubeLeg_intertwines p hp i)

def cubeLegCoefficient (p : ActualEisensteinCubic.O) : CubeLegIndex p→ℂ
  | none => -(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹
  | some _ => (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3

def cubeLegQuotientFunction (p : ActualEisensteinCubic.O) (hp : p≠0) (i : CubeLegIndex p) :
    IntegralOrbitQuotient (cubeCommonCover p hp)→ℂ :=
  fun q=>cubicSourceQuotientFunction
    (integralCoverMap (cubeLegTarget_le p hp i)
      (integralConjugateMap (cubeLegEquiv p hp i) (cubeLegMatrix p hp i)
        (cubeLeg_intertwines p hp i) q))

lemma cubeLegQuotientFunction_projection (p : ActualEisensteinCubic.O) (hp : p≠0) (i : CubeLegIndex p)
    (w : HyperbolicSpace) :
    cubeLegQuotientFunction p hp i (integralOrbitProjection (cubeCommonCover p hp) w)=
      cubicSourceResidualFunction (cubeLegMatrix p hp i • w) := rfl

lemma cubeLegQuotientFunction_measurable (p : ActualEisensteinCubic.O) (hp : p≠0) (i : CubeLegIndex p) :
    Measurable (cubeLegQuotientFunction p hp i) :=
  cubicSourceQuotientFunction_measurable.comp
    ((integralCoverMap_measurable (cubeLegTarget_le p hp i)).comp
      (integralConjugateMap_measurable _ _ _))

lemma cubeLeg_representative (p : ActualEisensteinCubic.O) (hp : p≠0) (i : CubeLegIndex p) :
    cubeLeg p hp i (kernelSourceProjection cubicEisensteinResidue)
      =ᵐ[integralQuotientVolume (cubeCommonCover p hp)]cubeLegQuotientFunction p hp i := by
  let := cubeLegTarget_finiteIndex p hp i
  let : (cubeLegTarget p hp i).IsFiniteRelIndex globalKubotaKernel :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  exact kernelCoverLeg_representative (cubeCommonCover_le p hp) (cubeLegTarget_le p hp i)
    (cubeLegEquiv p hp i) (cubeLegMatrix p hp i) (cubeLeg_intertwines p hp i)
    _ _ cubicSourceQuotientFunction_represents

def cubeDifferenceL2 (p : ActualEisensteinCubic.O) (hp : p≠0) : IntegralQuotientL2 (cubeCommonCover p hp) :=
  ∑' i:CubeLegIndex p,cubeLegCoefficient p i •
    cubeLeg p hp i (kernelSourceProjection cubicEisensteinResidue)

def cubeDifferenceQuotientFunction (p : ActualEisensteinCubic.O) (hp : p≠0) :
    IntegralOrbitQuotient (cubeCommonCover p hp)→ℂ :=
  fun q=>∑' i:CubeLegIndex p,cubeLegCoefficient p i*cubeLegQuotientFunction p hp i q

lemma cubeDifferenceQuotientFunction_projection (p : ActualEisensteinCubic.O) (hp : p≠0)
    (w : HyperbolicSpace) :
    cubeDifferenceQuotientFunction p hp (integralOrbitProjection (cubeCommonCover p hp) w)=
      cubeSourceDifference p hp w := by
  let : Finite (CubeResidues p) := finite_quotient_span (pow_ne_zero 3 hp)
  let : Fintype (CubeResidues p) := Fintype.ofFinite _
  simp only [cubeDifferenceQuotientFunction,tsum_fintype,Fintype.sum_option,
    cubeLegCoefficient,cubeLegQuotientFunction_projection,cubeLegMatrix,one_smul,
    cubeSourceDifference,cubeAverage,Finset.mul_sum]
  ring

lemma cubeDifferenceQuotientFunction_measurable (p : ActualEisensteinCubic.O) (hp : p≠0) :
    Measurable (cubeDifferenceQuotientFunction p hp) := by
  let : Finite (CubeResidues p) := finite_quotient_span (pow_ne_zero 3 hp)
  let : Fintype (CubeResidues p) := Fintype.ofFinite _
  unfold cubeDifferenceQuotientFunction
  simp only [tsum_fintype]
  exact Finset.measurable_sum _ (fun i _=>measurable_const.mul (cubeLegQuotientFunction_measurable p hp i))

lemma cubeDifferenceL2_representative (p : ActualEisensteinCubic.O) (hp : p≠0) :
    cubeDifferenceL2 p hp=ᵐ[integralQuotientVolume (cubeCommonCover p hp)]
      cubeDifferenceQuotientFunction p hp := by
  let : Finite (CubeResidues p) := finite_quotient_span (pow_ne_zero 3 hp)
  let : Fintype (CubeResidues p) := Fintype.ofFinite _
  unfold cubeDifferenceL2 cubeDifferenceQuotientFunction
  simp only [tsum_fintype]
  apply (Lp.coeFn_finsetSum _ _).trans
  have hh (i : CubeLegIndex p) :
      ((cubeLegCoefficient p i • cubeLeg p hp i (kernelSourceProjection cubicEisensteinResidue) :
        IntegralQuotientL2 (cubeCommonCover p hp)) : IntegralOrbitQuotient (cubeCommonCover p hp)→ℂ)
      =ᵐ[integralQuotientVolume (cubeCommonCover p hp)]
      (fun q=>cubeLegCoefficient p i*cubeLegQuotientFunction p hp i q) :=
    by
      filter_upwards [Lp.coeFn_smul (cubeLegCoefficient p i)
        (cubeLeg p hp i (kernelSourceProjection cubicEisensteinResidue)),
        cubeLeg_representative p hp i] with q hq hr
      simpa only [Pi.smul_apply,smul_eq_mul,hr] using hq
  filter_upwards [eventuallyEq_sum (fun i (_ : i∈Finset.univ)=>hh i)] with q hq
  simpa only [Finset.sum_apply] using hq

end CubicKubota
end

namespace CubicEisenstein

open MeasureTheory
open scoped Classical MatrixGroups BigOperators

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceCuspLeadingCoefficient_ramified (j:Fin 3) (hj:j≠0) :
    sourceCuspLeadingCoefficient (cuspRepresentative j)=0 := by
  unfold sourceCuspLeadingCoefficient sourceCuspConstant
  rw [sourceCuspRepresentative_average]
  simp only [if_neg hj,zero_mul,zero_div]

theorem sourceCuspRemainder_representatives_decay (a:ℝ) (ha:0<a) :
    ∃K:ℝ,0≤K∧∀j:Fin 3,∀z:ℂ,∀v:ℝ,∀hv:0<v,a≤v→
      ‖sourceCuspRemainder (cuspRepresentative j) z v hv‖≤K/v^3 := by
  obtain ⟨K0,hK0,h0⟩:=sourceCuspRemainder_principal_cubic_decay a ha
  obtain ⟨K1,hK1,h1⟩:=ramifiedSource_cubic_decay false a ha
  obtain ⟨K2,hK2,h2⟩:=ramifiedSource_cubic_decay true a ha
  refine ⟨K0+K1+K2,by positivity,?_⟩
  intro j z v hv hav
  have hD:0≤v^3:=pow_nonneg hv.le 3
  fin_cases j
  · have hb:‖sourceCuspRemainder (cuspRepresentative 0) z v hv‖≤K0/v^3:=by
      simpa [cuspRepresentative,cuspParameter,lowerCuspMatrix_zero] using h0 z v hv hav
    exact hb.trans (div_le_div_of_nonneg_right (by linarith) hD)
  · have he:sourceCuspRemainder (cuspRepresentative 1) z v hv=
        ramifiedSourceFunction (ramifiedCuspRoot false:Eis) (upperPoint z v hv):=by
      rw [sourceCuspRemainder,sourceCuspLeadingCoefficient_ramified 1 (by decide),zero_mul,sub_zero]
      simp [cuspRepresentative,cuspParameter,ramifiedSourceFunction,ramifiedCuspRoot,ramifiedOmegaUnit_val]
    change ‖sourceCuspRemainder (cuspRepresentative 1) z v hv‖≤_
    rw [he]
    exact (h1 v hv z hav).trans (div_le_div_of_nonneg_right (by linarith) hD)
  · have he:sourceCuspRemainder (cuspRepresentative 2) z v hv=
        ramifiedSourceFunction (ramifiedCuspRoot true:Eis) (upperPoint z v hv):=by
      rw [sourceCuspRemainder,sourceCuspLeadingCoefficient_ramified 2 (by decide),zero_mul,sub_zero]
      simp [cuspRepresentative,cuspParameter,ramifiedSourceFunction,ramifiedCuspRoot,
        Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val]
    change ‖sourceCuspRemainder (cuspRepresentative 2) z v hv‖≤_
    rw [he]
    exact (h2 v hv z hav).trans (div_le_div_of_nonneg_right (by linarith) hD)

theorem cubeSourceDifference_cubic_decay (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) :
    ∃C:ℝ,0≤C∧∀M:SL(2,Eis),∀z:ℂ,∀v:ℝ,∀hv:0<v,1≤v→
      ‖cubeSourceDifference p hp.ne_zero (integralComplexMatrix M • upperPoint z v hv)‖≤C/v^3 := by
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp.ne_zero)
  obtain ⟨K,hK,hrep⟩:=sourceCuspRemainder_representatives_decay (‖eisEmbedding p‖^3)⁻¹ (by positivity)
  refine ⟨K*(‖eisEmbedding p‖^9+(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹),by positivity,?_⟩
  intro M z v hv hv1
  exact cubeSourceDifference_decay p hp hprimary K hK hrep M z v hv hv1

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

lemma cubeCuspTriangular_norm_sq_le {M:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData M p q) (hp:p≠0) :
    ‖cubeCuspTriangular d hp 1 1‖^2≤‖eisEmbedding p‖^3 := by
  rw [cubeCuspTriangular_norm_sq d hp,←Real.rpow_natCast ‖eisEmbedding p‖ 3]
  apply Real.rpow_le_rpow_of_exponent_le (cubePrime_norm_ge_one p hp)
  norm_num only [Nat.cast_ofNat]
  have hj:0≤(d.exponent.val:ℝ):=Nat.cast_nonneg _
  linarith

lemma cubeReducedRemainder_bound_from_height {M:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData M p q) (hp:p≠0) (a K:ℝ) (ha:0<a) (hK:0≤K)
    (hrep:∀j:Fin 3,∀z:ℂ,∀v:ℝ,∀hv:0<v,a/‖eisEmbedding p‖^3≤v→
      ‖sourceCuspRemainder (cuspRepresentative j) z v hv‖≤K/v^3)
    (z:ℂ) (v:ℝ) (hv:0<v) (hav:a≤v) :
    ‖cubeReducedRemainder d hp z v hv‖≤K*‖eisEmbedding p‖^9/v^3 := by
  let D:=‖cubeCuspTriangular d hp 1 1‖^2
  have hD:0<D:=cubeCuspTriangular_norm_sq_pos d hp
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp)
  have hd:D≤‖eisEmbedding p‖^3:=cubeCuspTriangular_norm_sq_le d hp
  have hlow:a/‖eisEmbedding p‖^3≤v/D:=by
    apply (le_div_iff₀ hD).mpr
    calc
      _≤(a/‖eisEmbedding p‖^3)*‖eisEmbedding p‖^3:=
        mul_le_mul_of_nonneg_left hd (by positivity)
      _=a:=div_mul_cancel₀ a (pow_ne_zero 3 hr.ne')
      _≤v:=hav
  have hb:=sourceCuspRemainder_bound_all K (a/‖eisEmbedding p‖^3) hrep
    d.matrix ((cubeCuspTriangular d hp 0 0*z+cubeCuspTriangular d hp 0 1)/cubeCuspTriangular d hp 1 1)
    (v/D) (div_pos hv hD) hlow
  change ‖cubeReducedRemainder d hp z v hv‖≤K/(v/D)^3 at hb
  refine hb.trans ?_
  have hd3:D^3≤‖eisEmbedding p‖^9:=by
    calc
      _≤(‖eisEmbedding p‖^3)^3:=pow_le_pow_left₀ hD.le hd 3
      _=_:=by ring
  calc
    K/(v/D)^3=K*D^3/v^3:=by field_simp
    _≤K*‖eisEmbedding p‖^9/v^3:=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd3 hK) (pow_nonneg hv.le 3)

theorem cubeSourceDifference_cubic_decay_from_height (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (a:ℝ) (ha:0<a) :
    ∃C:ℝ,0≤C∧∀M:SL(2,Eis),∀z:ℂ,∀v:ℝ,∀hv:0<v,a≤v→
      ‖cubeSourceDifference p hp.ne_zero (integralComplexMatrix M • upperPoint z v hv)‖≤C/v^3 := by
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp.ne_zero)
  have hr1:1≤‖eisEmbedding p‖:=cubePrime_norm_ge_one p hp.ne_zero
  obtain ⟨K,hK,hrep⟩:=sourceCuspRemainder_representatives_decay
    (a/‖eisEmbedding p‖^3) (by positivity)
  refine ⟨K*(‖eisEmbedding p‖^9+(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹),by positivity,?_⟩
  intro M z v hv hav
  have hlow:a/‖eisEmbedding p‖^3≤v:=by
    calc
      _≤a:=div_le_self ha.le (one_le_pow₀ hr1)
      _≤v:=hav
  have hbase:=sourceCuspRemainder_bound_all K _ hrep M z v hv hlow
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData M p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  have hsum:=cube_normalized_sum_bound p hp.ne_zero
    (fun r=>cubeReducedRemainder (d r) hp.ne_zero z v hv) (K*‖eisEmbedding p‖^9/v^3)
    (by positivity) (fun r=>cubeReducedRemainder_bound_from_height (d r) hp.ne_zero a K ha hK hrep z v hv hav)
  have hrest:‖(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspRemainder M z v hv‖≤
      (Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹*(K/v^3):=by
    rw [norm_mul,norm_inv,Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr (Nat.cast_nonneg _))
  unfold cubeSourceDifference
  rw [cubeSource_difference_eq_remainders M p hp hprimary z v hv]
  refine (norm_sub_le _ _).trans ?_
  calc
    _≤K*‖eisEmbedding p‖^9/v^3+(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹*(K/v^3):=
      add_le_add hsum hrest
    _=_:=by ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

def cubeInverseLeftMatrix (q:Eis) : SL(2,Eis) :=
  ⟨!![3*q,1;-1,0],by simp⟩

lemma cubeAverageMatrix_inverse_factor (p:Eis) (hp:p≠0) (q:Eis) :
    (cubeAverageMatrix p hp q)⁻¹=
      integralComplexMatrix (cubeInverseLeftMatrix q)*cubeAverageMatrix p hp 0*
        integralComplexMatrix (rationalEmbedding ModularGroup.S) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_mul,
    cubeAverageMatrix_entries]
  apply Matrix.ext
  intro i j
  simp only [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    integralComplexMatrix_apply, rationalEmbedding, Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;>
    simp [cubeInverseLeftMatrix, ModularGroup.S, map_ofNat]
  ring

lemma cubeAverageMatrix_inverse_cusp_factor (M:SL(2,Eis)) (p q:Eis)
    (hp:Prime p) (hprimary:lambda^2∣p-1) :
    let d:=actualCubeCuspData (rationalEmbedding ModularGroup.S*M) p 0 hp hprimary
    (cubeAverageMatrix p hp.ne_zero q)⁻¹*integralComplexMatrix M=
      integralComplexMatrix (cubeInverseLeftMatrix q*d.matrix)*cubeCuspTriangular d hp.ne_zero := by
  dsimp only
  let d:=actualCubeCuspData (rationalEmbedding ModularGroup.S*M) p 0 hp hprimary
  calc
    _=integralComplexMatrix (cubeInverseLeftMatrix q)*
        (cubeAverageMatrix p hp.ne_zero 0*integralComplexMatrix (rationalEmbedding ModularGroup.S*M)):=by
      rw [cubeAverageMatrix_inverse_factor,map_mul]
      group
    _=integralComplexMatrix (cubeInverseLeftMatrix q)*
        (integralComplexMatrix d.matrix*cubeCuspTriangular d hp.ne_zero):=by
      rw [cubeCuspTriangular_factor d hp.ne_zero]
    _=integralComplexMatrix (cubeInverseLeftMatrix q*d.matrix)*cubeCuspTriangular d hp.ne_zero:=by
      rw [map_mul,mul_assoc]

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

theorem cubeSourceDifference_inverse_cubic_decay (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) :
    ∃C:ℝ,0≤C∧∀q:Eis,∀M:SL(2,Eis),∀z:ℂ,∀v:ℝ,∀hv:0<v,1≤v→
      ‖cubeSourceDifference p hp.ne_zero ((cubeAverageMatrix p hp.ne_zero q)⁻¹ •
        (integralComplexMatrix M • upperPoint z v hv))‖≤C/v^3 := by
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp.ne_zero)
  obtain ⟨K,hK,hdecay⟩:=cubeSourceDifference_cubic_decay_from_height p hp hprimary
    (‖eisEmbedding p‖^3)⁻¹ (by positivity)
  refine ⟨K*‖eisEmbedding p‖^9,by positivity,?_⟩
  intro q M z v hv hv1
  let d:=actualCubeCuspData (rationalEmbedding ModularGroup.S*M) p 0 hp hprimary
  let T:=cubeCuspTriangular d hp.ne_zero
  let D:=‖T 1 1‖^2
  have hT:T 1 0=0:=(cubeCuspTriangular_entries d hp.ne_zero).2.1
  have hD:0<D:=cubeCuspTriangular_norm_sq_pos d hp.ne_zero
  have hDle:D≤‖eisEmbedding p‖^3:=cubeCuspTriangular_norm_sq_le d hp.ne_zero
  have hlow:(‖eisEmbedding p‖^3)⁻¹≤v/D:=by
    apply (le_div_iff₀ hD).mpr
    calc
      _≤(‖eisEmbedding p‖^3)⁻¹*‖eisEmbedding p‖^3:=
        mul_le_mul_of_nonneg_left hDle (by positivity)
      _=1:=inv_mul_cancel₀ (pow_ne_zero 3 hr.ne')
      _≤v:=hv1
  have hfactor: (cubeAverageMatrix p hp.ne_zero q)⁻¹*integralComplexMatrix M=
      integralComplexMatrix (cubeInverseLeftMatrix q*d.matrix)*T :=
    cubeAverageMatrix_inverse_cusp_factor M p q hp hprimary
  have hact: (cubeAverageMatrix p hp.ne_zero q)⁻¹ •
      (integralComplexMatrix M • upperPoint z v hv)=
      integralComplexMatrix (cubeInverseLeftMatrix q*d.matrix) •
        upperPoint ((T 0 0*z+T 0 1)/T 1 1) (v/D) (div_pos hv hD) := by
    rw [←mul_smul,hfactor,mul_smul,complex_upper_triangular_action T hT z v hv]
  rw [hact]
  refine (hdecay (cubeInverseLeftMatrix q*d.matrix) _ _ _ hlow).trans ?_
  have hd3:D^3≤‖eisEmbedding p‖^9:=by
    calc
      _≤(‖eisEmbedding p‖^3)^3:=pow_le_pow_left₀ hD.le hDle 3
      _=_:=by ring
  calc
    K/(v/D)^3=K*D^3/v^3:=by field_simp
    _≤K*‖eisEmbedding p‖^9/v^3:=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd3 hK) (pow_nonneg hv.le 3)

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

namespace CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma kernelSourcePullback_pairing_inverse (M : CubicKubota.levelTwo) (F G : KernelQuotientL2) :
    inner ℂ F (kernelSourcePullback M G)=inner ℂ (kernelSourcePullback M⁻¹ F) G := by
  calc
    _ = inner ℂ (kernelSourcePullback M (kernelSourcePullback M⁻¹ F)) (kernelSourcePullback M G) := by
      rw [kernelSourcePullback_comp,inv_mul_cancel,kernelSourcePullback_one]
    _ = _ := LinearIsometry.inner_map_map _ _ _

lemma kernelSourcePullback_integral_cusp_decay (M : CubicKubota.levelTwo)
    (f : KernelQuotient→ℂ) (C : ℝ)
    (hdec : ∀N : SL(2,ActualEisensteinCubic.O),∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
      ‖f (integralOrbitProjection globalKubotaKernel
        (integralComplexMatrix N•upperPoint z v hv))‖≤C/v^3)
    (N : SL(2,ActualEisensteinCubic.O)) (z : ℂ) (v : ℝ) (hv : 0<v) (hlarge : 1<v) :
    ‖f (kernelSourceAction M (integralOrbitProjection globalKubotaKernel
      (integralComplexMatrix N•upperPoint z v hv)))‖≤C/v^3 := by
  rw [kernelSourceAction_mk]
  change ‖f (integralOrbitProjection globalKubotaKernel
    (integralComplexMatrix (M:SL(2,ActualEisensteinCubic.O))•(integralComplexMatrix N•upperPoint z v hv)))‖≤C/v^3
  have hh := hdec ((M:SL(2,ActualEisensteinCubic.O))*N) z v hv hlarge
  simpa only [map_mul,mul_smul] using hh

lemma cubicEisensteinResidue_source_translate_orthogonal
    (F : KernelQuotientL2) (hF : (F,(8/9:ℂ)•F)∈kernelEnergyLaplacian.graph)
    (f : KernelQuotient→ℂ) (hrep : F=ᵐ[integralQuotientVolume globalKubotaKernel]f)
    (C : ℝ) (hC : 0≤C)
    (hdec : ∀N : SL(2,ActualEisensteinCubic.O),∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
      ‖f (integralOrbitProjection globalKubotaKernel
        (integralComplexMatrix N•upperPoint z v hv))‖≤C/v^3)
    (M : CubicKubota.levelTwo) :
    inner ℂ F (kernelSourcePullback M cubicEisensteinResidue)=0 := by
  rw [kernelSourcePullback_pairing_inverse]
  have hrepM : kernelSourcePullback M⁻¹ F=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q=>f (kernelSourceAction M⁻¹ q) :=
    (kernelSourcePullback_ae_eq M⁻¹ F).trans
      ((kernelSourceAction_measurePreserving M⁻¹).quasiMeasurePreserving.ae_eq_comp hrep)
  apply cubicEisensteinResidue_orthogonal_of_cusp_chart_decay _
    (kernelSource_eigenvector M⁻¹ F (8/9:ℂ) hF) _ hrepM C hC
  intro N z v hv hlarge
  exact kernelSourcePullback_integral_cusp_decay M⁻¹ f C hdec (N:SL(2,ActualEisensteinCubic.O)) z v hv hlarge

theorem cubicSourceResidue_orthogonal_of_integral_cusp_decay
    (F : KernelQuotientL2) (hF : (F,(8/9:ℂ)•F)∈kernelEnergyLaplacian.graph)
    (f : KernelQuotient→ℂ) (hrep : F=ᵐ[integralQuotientVolume globalKubotaKernel]f)
    (C : ℝ) (hC : 0≤C)
    (hdec : ∀N : SL(2,ActualEisensteinCubic.O),∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
      ‖f (integralOrbitProjection globalKubotaKernel
        (integralComplexMatrix N•upperPoint z v hv))‖≤C/v^3) :
    inner ℂ F (kernelSourceProjection cubicEisensteinResidue)=0 := by
  rw [kernelSourceProjection_apply,inner_smul_right,inner_sum]
  simp only [cubicEisensteinResidue_source_translate_orthogonal F hF f hrep C hC hdec,
    Finset.sum_const_zero,mul_zero]

theorem commonCover_source_span_vanish {H : Subgroup (SL(2,ActualEisensteinCubic.O))} {ι : Type*} [Fintype ι]
    (leg : ι→KernelQuotientL2→L[ℂ]IntegralQuotientL2 H) (c : ι→ℂ)
    (D : IntegralQuotientL2 H)
    (hD : D=∑i,c i • leg i (kernelSourceProjection cubicEisensteinResidue))
    (hEig : ∀i,(ContinuousLinearMap.adjoint (leg i) D,
      (8/9:ℂ)•ContinuousLinearMap.adjoint (leg i) D)∈kernelEnergyLaplacian.graph)
    (f : ι→KernelQuotient→ℂ)
    (hrep : ∀i,ContinuousLinearMap.adjoint (leg i) D=ᵐ[integralQuotientVolume globalKubotaKernel]f i)
    (C : ι→ℝ) (hC : ∀i,0≤C i)
    (hdec : ∀i,∀N : SL(2,ActualEisensteinCubic.O),∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
      ‖f i (integralOrbitProjection globalKubotaKernel
        (integralComplexMatrix N•upperPoint z v hv))‖≤C i/v^3) : D=0 := by
  apply (inner_self_eq_zero (𝕜:=ℂ)).mp
  calc
    inner ℂ D D=inner ℂ D (∑i,c i • leg i (kernelSourceProjection cubicEisensteinResidue)) :=
      congrArg (inner ℂ D) hD
    _ = ∑i,c i * inner ℂ D (leg i (kernelSourceProjection cubicEisensteinResidue)) := by
      simp only [inner_sum,inner_smul_right]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [←ContinuousLinearMap.adjoint_inner_left]
      rw [cubicSourceResidue_orthogonal_of_integral_cusp_decay _ (hEig i) (f i) (hrep i) (C i) (hC i) (hdec i),mul_zero]

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

namespace CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem kernelCoverLeg_adjoint_sum_eigenvector
    {H : Subgroup (SL(2,ActualEisensteinCubic.O))} {ι : Type*} [Fintype ι]
    (J : ι→Subgroup (SL(2,ActualEisensteinCubic.O)))
    (hHK : H≤globalKubotaKernel) (hJK : ∀i,J i≤globalKubotaKernel)
    [∀i,(J i).IsFiniteRelIndex globalKubotaKernel]
    (e : ∀i,H≃*J i) (g : ι→SL(2,ℂ)) (he : ∀i,IntegralCoverIntertwines (e i) (g i))
    (F : KernelQuotientL2) (eigenvalue : ℂ)
    (hF : (F,eigenvalue • F)∈kernelEnergyLaplacian.graph)
    (c : ι→ℂ) (j : ι) :
    let D := ∑i,c i • kernelCoverLeg hHK (hJK i) (e i) (g i) (he i) F
    (ContinuousLinearMap.adjoint (kernelCoverLeg hHK (hJK j) (e j) (g j) (he j)) D,
      eigenvalue • ContinuousLinearMap.adjoint (kernelCoverLeg hHK (hJK j) (e j) (g j) (he j)) D)
      ∈kernelEnergyLaplacian.graph := by
  let traced (i : ι) :=
    ContinuousLinearMap.adjoint (kernelCoverLeg hHK (hJK j) (e j) (g j) (he j))
      (kernelCoverLeg hHK (hJK i) (e i) (g i) (he i) F)
  have hi (i : ι) : (traced i,eigenvalue • traced i)∈kernelEnergyLaplacian.graph := by
    change (((ContinuousLinearMap.adjoint (kernelCoverLeg hHK (hJK j) (e j) (g j) (he j))).comp
      (kernelCoverLeg hHK (hJK i) (e i) (g i) (he i))) F,
      eigenvalue • ((ContinuousLinearMap.adjoint (kernelCoverLeg hHK (hJK j) (e j) (g j) (he j))).comp
      (kernelCoverLeg hHK (hJK i) (e i) (g i) (he i))) F)∈kernelEnergyLaplacian.graph
    rw [kernelCoverLeg_adjoint_comp]
    exact kernelCorrespondence_eigenvector _ _ _ _ _ F eigenvalue hF
  have hsum : (∑i,c i • (traced i,eigenvalue • traced i))∈kernelEnergyLaplacian.graph :=
    kernelEnergyLaplacian.graph.sum_mem (fun i _=>kernelEnergyLaplacian.graph.smul_mem (c i) (hi i))
  have hEq : (∑i,c i • (traced i,eigenvalue • traced i))=
      (∑i,c i • traced i,eigenvalue • ∑i,c i • traced i) := by
    apply Prod.ext <;> simp [Prod.fst_sum,Prod.snd_sum,Finset.smul_sum,smul_smul,mul_comm]
  rw [hEq] at hsum
  simpa only [map_sum,map_smul] using hsum

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O

theorem integralCoverTraceFunction_integral_cusp_decay (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    [H.IsFiniteRelIndex K] (f : IntegralOrbitQuotient H→ℂ) (C : ℝ)
    (hdec : ∀M : SL(2,ActualEisensteinCubic.O),∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
      ‖f (integralOrbitProjection H (integralComplexMatrix M•upperPoint z v hv))‖≤C/v^3)
    (M : SL(2,ActualEisensteinCubic.O)) (z : ℂ) (v : ℝ) (hv : 0<v) (hlarge : 1<v) :
    ‖integralCoverTraceFunction H K f
      (integralOrbitProjection K (integralComplexMatrix M•upperPoint z v hv))‖≤
        (H.relIndex K:ℝ)*C/v^3 := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  change ‖∑q : IntegralCoverCosets H K,
    f (integralCoverFiberPoint H K q (integralComplexMatrix M•upperPoint z v hv))‖≤_
  calc
    _ ≤ ∑q : IntegralCoverCosets H K,
        ‖f (integralCoverFiberPoint H K q (integralComplexMatrix M•upperPoint z v hv))‖ :=
      norm_sum_le _ _
    _ ≤ ∑_q : IntegralCoverCosets H K,C/v^3 := by
      apply Finset.sum_le_sum
      intro q _
      let r := integralCoverRep H K q
      have he : integralCoverFiberPoint H K q (integralComplexMatrix M•upperPoint z v hv)=
          integralOrbitProjection H (integralComplexMatrix ((r:SL(2,ActualEisensteinCubic.O))⁻¹*M)•upperPoint z v hv) := by
        rw [integralCoverFiberPoint_rep,integralSubgroup_smul,map_mul,mul_smul]
        rfl
      rw [he]
      exact hdec _ z v hv hlarge
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      have hc : Fintype.card (IntegralCoverCosets H K)=H.relIndex K := by
        rw [Subgroup.relIndex,Subgroup.index,Nat.card_eq_fintype_card]
      rw [hc]
      ring

variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)

def kernelCoverLegAdjointFunction (f : IntegralOrbitQuotient H→ℂ) : KernelQuotient→ℂ :=
  integralCoverTraceFunction J globalKubotaKernel
    (fun q=>f (integralConjugateMap e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) q))

theorem kernelCoverLegAdjointFunction_represents (D : IntegralQuotientL2 H)
    (f : IntegralOrbitQuotient H→ℂ) (hf : Measurable f)
    (hrep : D=ᵐ[integralQuotientVolume H]f) :
    ContinuousLinearMap.adjoint (kernelCoverLeg hHK hJK e g he) D
      =ᵐ[integralQuotientVolume globalKubotaKernel]kernelCoverLegAdjointFunction e g he f := by
  rw [kernelCoverLeg_adjoint_apply]
  have hconj := (integralConjugatePullback_ae e.symm g⁻¹
    (integralCoverIntertwines_inverse e g he)
    (hJK.trans globalKubotaKernel_le_levelThree) (hHK.trans globalKubotaKernel_le_levelThree) D).trans
    ((integralConjugateMap_measurePreserving e.symm g⁻¹
      (integralCoverIntertwines_inverse e g he)
      (hJK.trans globalKubotaKernel_le_levelThree) (hHK.trans globalKubotaKernel_le_levelThree)).quasiMeasurePreserving.ae_eq_comp hrep)
  exact integralCoverTrace_representative hJK globalKubotaKernel_le_levelThree _ _
    (hf.comp (integralConjugateMap_measurable _ _ _)) hconj

theorem kernelCoverLegAdjointFunction_cusp_decay (f : IntegralOrbitQuotient H→ℂ) (C : ℝ)
    (hdec : ∀M : SL(2,ActualEisensteinCubic.O),∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
      ‖f (integralOrbitProjection H (g⁻¹•(integralComplexMatrix M•upperPoint z v hv)))‖≤C/v^3)
    (M : SL(2,ActualEisensteinCubic.O)) (z : ℂ) (v : ℝ) (hv : 0<v) (hlarge : 1<v) :
    ‖kernelCoverLegAdjointFunction e g he f
      (integralOrbitProjection globalKubotaKernel (integralComplexMatrix M•upperPoint z v hv))‖≤
        (J.relIndex globalKubotaKernel:ℝ)*C/v^3 := by
  apply integralCoverTraceFunction_integral_cusp_decay J globalKubotaKernel _ C _ M z v hv hlarge
  intro N zz vv hvv hl
  exact hdec N zz vv hvv hl

end

local notation "O" => ActualEisensteinCubic.O

theorem commonCover_source_sum_eq_zero_of_inverse_cusp_decay
    {H : Subgroup (SL(2,ActualEisensteinCubic.O))} {ι : Type*} [Fintype ι]
    (J : ι→Subgroup (SL(2,ActualEisensteinCubic.O)))
    (hHK : H≤globalKubotaKernel) (hJK : ∀i,J i≤globalKubotaKernel)
    [∀i,(J i).IsFiniteRelIndex globalKubotaKernel]
    (e : ∀i,H≃*J i) (g : ι→SL(2,ℂ)) (he : ∀i,IntegralCoverIntertwines (e i) (g i))
    (c : ι→ℂ) (D : IntegralQuotientL2 H)
    (hD : D=∑i,c i • kernelCoverLeg hHK (hJK i) (e i) (g i) (he i)
      (kernelSourceProjection cubicEisensteinResidue))
    (f : IntegralOrbitQuotient H→ℂ) (hf : Measurable f)
    (hrep : D=ᵐ[integralQuotientVolume H]f)
    (C : ι→ℝ) (hC : ∀i,0≤C i)
    (hdec : ∀i,∀M : SL(2,ActualEisensteinCubic.O),∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
      ‖f (integralOrbitProjection H ((g i)⁻¹•(integralComplexMatrix M•upperPoint z v hv)))‖≤C i/v^3) :
    D=0 := by
  let leg (i : ι) := kernelCoverLeg hHK (hJK i) (e i) (g i) (he i)
  apply commonCover_source_span_vanish leg c D hD
    (f:=fun i=>kernelCoverLegAdjointFunction (e i) (g i) (he i) f)
    (C:=fun i=>(J i).relIndex globalKubotaKernel*C i)
  · intro i
    rw [hD]
    exact kernelCoverLeg_adjoint_sum_eigenvector J hHK hJK e g he
      (kernelSourceProjection cubicEisensteinResidue) (8/9:ℂ)
      kernelSourceProjection_cubicEisensteinResidue_eigenvector c i
  · intro i
    exact kernelCoverLegAdjointFunction_represents hHK (hJK i) (e i) (g i) (he i) D f hf hrep
  · intro i
    exact mul_nonneg (Nat.cast_nonneg _) (hC i)
  · intro i M z v hv hlarge
    exact kernelCoverLegAdjointFunction_cusp_decay (e i) (g i) (he i) f (C i) (hdec i) M z v hv hlarge

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise

local notation "Eis" => ActualEisensteinCubic.O

lemma integralProjection_quasiMeasurePreserving (H:Subgroup (SL(2,Eis)))
    (hH:H≤CubicKubota.levelThree) :
    Measure.QuasiMeasurePreserving (integralOrbitProjection H)
      hyperbolicVolume (integralQuotientVolume H) := by
  let proj:=integralOrbitProjection H
  have hp:Measurable proj:=measurable_integralOrbitProjection H
  refine ⟨hp,Measure.AbsolutelyContinuous.mk fun S hS hzero=>?_⟩
  rw [Measure.map_apply hp hS]
  have hd:hyperbolicVolume ((proj ⁻¹' S)∩hyperbolicFundamentalSet H)=0:=by
    simpa only [integralQuotientVolume,proj,
      Measure.map_apply (measurable_integralOrbitProjection _) hS,
      Measure.restrict_apply ((measurable_integralOrbitProjection _) hS)] using hzero
  have hinv:∀M:H,M • (proj ⁻¹' S)=proj ⁻¹' S:=by
    intro M
    ext w
    constructor
    · rintro ⟨u,hu,rfl⟩
      change proj (M • u)∈S
      change proj u∈S at hu
      rwa [show proj (M • u)=proj u from integralOrbitProjection_eq H M u]
    · intro hw
      refine ⟨M⁻¹ • w,?_,smul_inv_smul M w⟩
      change proj (M⁻¹ • w)∈S
      rwa [show proj (M⁻¹ • w)=proj w from integralOrbitProjection_eq H M⁻¹ w]
  exact (hyperbolicFundamentalSet_isFundamentalDomain H hH).measure_zero_of_invariant
    (proj ⁻¹' S) hinv hd

theorem integralQuotient_continuous_lifts_eq (H:Subgroup (SL(2,Eis)))
    (hH:H≤CubicKubota.levelThree) (F G:IntegralOrbitQuotient H→ℂ)
    (f g:HyperbolicSpace→ℂ) (hf:Continuous f) (hg:Continuous g)
    (hF:∀w,F (integralOrbitProjection H w)=f w)
    (hG:∀w,G (integralOrbitProjection H w)=g w)
    (he:F=ᵐ[integralQuotientVolume H]G) : f=g := by
  have hl: f=ᵐ[hyperbolicVolume]g:=by
    have hh:=(integralProjection_quasiMeasurePreserving H hH).ae_eq_comp he
    simpa only [Function.comp_def,hF,hG] using hh
  exact Measure.eq_of_ae_eq hl hf hg

theorem integralQuotient_zero_continuous_lift (H:Subgroup (SL(2,Eis)))
    (hH:H≤CubicKubota.levelThree) (F:IntegralOrbitQuotient H→ℂ)
    (f:HyperbolicSpace→ℂ) (hf:Continuous f)
    (hF:∀w,F (integralOrbitProjection H w)=f w)
    (hzero:F=ᵐ[integralQuotientVolume H]0) : ∀w,f w=0 := by
  have he:f=0:=integralQuotient_continuous_lifts_eq H hH F 0 f 0 hf
    continuous_const hF (fun _=>rfl) hzero
  intro w
  exact congrFun he w

end

section
open Filter MeasureTheory
open scoped Classical MatrixGroups BigOperators

open CubicKubota ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

theorem cubeDifferenceL2_eq_zero (p : ActualEisensteinCubic.O) (hp : Prime p)
    (hprimary : ActualEisensteinCubic.lambda^2∣p-1) :
    cubeDifferenceL2 p hp.ne_zero=0 := by
  let : Finite (CubeResidues p) := finite_quotient_span (pow_ne_zero 3 hp.ne_zero)
  let : Fintype (CubeResidues p) := Fintype.ofFinite _
  let : ∀i : CubeLegIndex p,(cubeLegTarget p hp.ne_zero i).FiniteIndex :=
    cubeLegTarget_finiteIndex p hp.ne_zero
  let : ∀i : CubeLegIndex p,(cubeLegTarget p hp.ne_zero i).IsFiniteRelIndex globalKubotaKernel :=
    fun i=>Subgroup.isFiniteRelIndex_of_finiteIndex
  obtain ⟨C0,hC0,h0⟩ := cubeSourceDifference_cubic_decay p hp hprimary
  obtain ⟨C1,hC1,h1⟩ := cubeSourceDifference_inverse_cubic_decay p hp hprimary
  let C : CubeLegIndex p→ℝ := fun i=>i.elim C0 (fun _=>C1)
  apply commonCover_source_sum_eq_zero_of_inverse_cusp_decay
    (cubeLegTarget p hp.ne_zero) (cubeCommonCover_le p hp.ne_zero)
    (cubeLegTarget_le p hp.ne_zero) (cubeLegEquiv p hp.ne_zero)
    (cubeLegMatrix p hp.ne_zero) (cubeLeg_intertwines p hp.ne_zero)
    (cubeLegCoefficient p) (cubeDifferenceL2 p hp.ne_zero) ?_
    (cubeDifferenceQuotientFunction p hp.ne_zero)
    (cubeDifferenceQuotientFunction_measurable p hp.ne_zero)
    (cubeDifferenceL2_representative p hp.ne_zero) C ?_ ?_
  · simp only [cubeDifferenceL2,tsum_fintype,cubeLeg]
  · intro i
    cases i with
    | none => exact hC0
    | some r => exact hC1
  · intro i M z v hv hlarge
    rw [cubeDifferenceQuotientFunction_projection]
    cases i with
    | none =>
      simpa only [cubeLegMatrix,inv_one,one_smul,C,Option.elim] using h0 M z v hv hlarge.le
    | some r =>
      exact h1 (GaussianShiftedPartition.representative (p^3) r) M z v hv hlarge.le

theorem cubeSourceDifference_eq_zero (p : ActualEisensteinCubic.O) (hp : Prime p)
    (hprimary : ActualEisensteinCubic.lambda^2∣p-1) (w : HyperbolicSpace) :
    cubeSourceDifference p hp.ne_zero w=0 := by
  have hz : cubeDifferenceQuotientFunction p hp.ne_zero
      =ᵐ[integralQuotientVolume (cubeCommonCover p hp.ne_zero)]0 := by
    apply (cubeDifferenceL2_representative p hp.ne_zero).symm.trans
    rw [cubeDifferenceL2_eq_zero p hp hprimary]
    exact Lp.coeFn_zero ℂ 2 _
  exact integralQuotient_zero_continuous_lift (cubeCommonCover p hp.ne_zero)
    ((cubeCommonCover_le p hp.ne_zero).trans globalKubotaKernel_le_levelThree)
    (cubeDifferenceQuotientFunction p hp.ne_zero) (cubeSourceDifference p hp.ne_zero)
    (cubeSourceDifference_continuous p hp.ne_zero)
    (cubeDifferenceQuotientFunction_projection p hp.ne_zero) hz w

theorem cubicSource_cubeAverage (p : ActualEisensteinCubic.O) (hp : Prime p)
    (hprimary : ActualEisensteinCubic.lambda^2∣p-1) (w : HyperbolicSpace) :
    cubeAverage p hp.ne_zero cubicSourceResidualFunction w=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction w :=
  sub_eq_zero.mp (cubeSourceDifference_eq_zero p hp hprimary w)

theorem sourceArithmeticResidue_prime_cube (p : ActualEisensteinCubic.O) (hp : Prime p)
    (hprimary : ActualEisensteinCubic.lambda^2∣p-1) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    sourceArithmeticResidue (h*p^3)=sourceArithmeticResidue h :=
  sourceArithmeticResidue_cube_of_eigenrelation p hp.ne_zero
    (cubicSource_cubeAverage p hp hprimary) h hh

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic
local notation "Eis" => ActualEisensteinCubic.O
local instance instFintypeUnitsO : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

abbrev PrincipalRamifiedIndex (h:Eis) := Eisˣ × Fin (ramifiedFrequencyBound h+1)

def principalRamifiedIndex (h:Eis) (i:PrincipalRamifiedIndex h) : Eis :=
  h*(9*(i.1.val*lambda^(i.2.val+2)))

def principalRamifiedWeight (h:Eis) (i:PrincipalRamifiedIndex h) (s:ℂ) : ℂ :=
  ((3^(i.2.val+2):ℕ):ℂ)^(-s)*explicitRamifiedCoefficient h i.1 (i.2.val+2)

lemma principalRamifiedWeight_analytic (h:Eis) (i:PrincipalRamifiedIndex h) (s:ℂ) :
    AnalyticAt ℂ (principalRamifiedWeight h i) s := by
  apply AnalyticAt.mul _ analyticAt_const
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  exact Eventually.of_forall fun z=>(differentiableAt_id.neg).const_cpow
    (Or.inl (by exact_mod_cast (pow_ne_zero (i.2.val+2) (by norm_num : (3:ℕ)≠0))))

lemma scatteringCoefficient_eq_principalRamified (s:ℂ) (hs:2<s.re)
    (h:Eis) (hh:h≠0) :
    scatteringCoefficient s h=
      (∑i:PrincipalRamifiedIndex h,principalRamifiedWeight h i s*
        unramifiedCubicGaussSeries s (principalRamifiedIndex h i))/
        ((9*Real.sqrt 3/2:ℝ):ℂ) := by
  rw [scatteringCoefficient_explicit_ramified s hs h hh,tsum_fintype]
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u hu
  rw [←Fin.sum_univ_eq_sum_range]
  rfl

theorem principalArithmeticResidue_eq_ramified_table (h:Eis) (hh:h≠0) :
    principalArithmeticResidue h=
      (∑i:PrincipalRamifiedIndex h,principalRamifiedWeight h i (4/3)*
        unramifiedGaussResidue (principalRamifiedIndex h i))/
        ((9*Real.sqrt 3/2:ℝ):ℂ) := by
  let coeff (i:PrincipalRamifiedIndex h) (s:ℂ) :=
    principalRamifiedWeight h i s*cuspWhittakerHeightFactor s h
  have he:=finite_unramified_residue (principalRamifiedIndex h) coeff
    (fun i s hs=>(principalRamifiedWeight_analytic h i s).mul
      (cuspWhittakerHeightFactor_analyticAt h s hs))
    (kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num))
    (kernelCuspFourier h cubicEisensteinResidue)
    (fun s hs hi=>kernelCuspFourierFamily_analyticAt_nonreal h 2 3
      (by norm_num) (by norm_num) s hs.ne' hi.ne')
    (kernelCuspFourierFamily_residue_limit h 2 3 (by norm_num) (by norm_num))
    (fun s hs hi=>by
      rw [kernelCuspFourierFamily_eq_upper h hh ⟨by linarith,hi⟩]
      dsimp only
      rw [scatteringCoefficient_eq_principalRamified s (by linarith) h hh]
      simp only [coeff]
      rw [mul_div_cancel₀ _ cusp_volume_ne_zero,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi'
      ring)
  rw [kernelCuspFourier_principal_residue] at he
  have hH:=cuspWhittakerHeightFactor_center_ne_zero h
  apply (eq_div_iff cusp_volume_ne_zero).mpr
  apply mul_right_cancel₀ hH
  calc
    principalArithmeticResidue h*((9*Real.sqrt 3/2:ℝ):ℂ)*cuspWhittakerHeightFactor (4/3) h
        = kernelCuspFourier h cubicEisensteinResidue := by
          rw [kernelCuspFourier_principal_residue]
          ring
    _ = _ := by
      rw [kernelCuspFourier_principal_residue,he]
      simp only [coeff]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem sourceArithmeticResidue_eq_ramified_table (h:Eis) (hh:h≠0) :
    sourceArithmeticResidue h=
      if ShortDraftTrace.breveE (cuspFrequency h)=1 then
        ((∑i:PrincipalRamifiedIndex h,principalRamifiedWeight h i (4/3)*
            unramifiedGaussResidue (principalRamifiedIndex h i))+
          3*unramifiedGaussResidue (9*h))/(4*((9*Real.sqrt 3/2:ℝ):ℂ))
      else 0 := by
  rw [sourceArithmeticResidue,principalArithmeticResidue_eq_ramified_table h hh]
  split_ifs
  · ring
  · rfl

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

local instance instFintypeUnitsO_1_r7efdac_1 : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
lemma arithmeticResidueSum_frequency_cube (h c p:Eis) (hc:c≠0)
    (hlevel:(3:Eis)∣c) (hprimary:lambda^2∣p-1) (hcp:IsCoprime c p) :
    arithmeticResidueSum (h*p^3) c=arithmeticResidueSum h c := by
  have ht:denominatorCondition c p:=⟨hcp,three_dvd_lambda_sq.trans hprimary⟩
  have hb:(eisEmbedding (symbol c p))^3=1:=by
    rw [←map_pow,symbol_cube_of_isCoprime c p hprimary hcp,map_one]
  have h1:=arithmeticResidueSum_frequency_twist h c p hc hlevel ht
  have h2:=arithmeticResidueSum_frequency_twist (h*p) c p hc hlevel ht
  have h3:=arithmeticResidueSum_frequency_twist (h*p*p) c p hc hlevel ht
  rw [show h*p^3=h*p*p*p by ring]
  calc
    _=eisEmbedding (symbol c p)^3*arithmeticResidueSum (h*p*p*p) c:=by rw [hb,one_mul]
    _=eisEmbedding (symbol c p)^2*arithmeticResidueSum (h*p*p) c:=by rw [pow_succ,mul_assoc,h3]
    _=eisEmbedding (symbol c p)*arithmeticResidueSum (h*p) c:=by rw [pow_two,mul_assoc,h2]
    _=arithmeticResidueSum h c:=h1

lemma ramified_prime_Gauss_cancel (h c p:Eis) (hc:c≠0) (hlevel:(3:Eis)∣c)
    (hp:Prime p) (hprimary:lambda^2∣p-1) (hcp:IsCoprime c p) :
    arithmeticResidueSum h c*primeCubicGauss p hp hprimary 1 (h*(9*c))=
      arithmeticResidueSum (h*p) c*primeCubicGauss p hp hprimary 1 (9*h) := by
  have ht:denominatorCondition c p:=⟨hcp,three_dvd_lambda_sq.trans hprimary⟩
  have hA:=arithmeticResidueSum_frequency_twist h c p hc hlevel ht
  have hG:=cubicUnitGaussSum_frequency_twist (9*h) p c hp.ne_zero hprimary hcp.symm
  rw [←primeCubicGauss_one_eq p hp hprimary,←primeCubicGauss_one_eq p hp hprimary] at hG
  rw [show (9*h)*c=h*(9*c) by ring] at hG
  have hb:eisEmbedding (symbol c p)≠0:=by
    have hcube:(eisEmbedding (symbol c p))^3=1:=by
      rw [←map_pow,symbol_cube_of_isCoprime c p hprimary hcp,map_one]
    intro hz
    simp only [hz,zero_pow (by decide : (3:ℕ)≠0)] at hcube
    exact zero_ne_one hcube
  apply mul_left_cancel₀ hb
  calc
    _=arithmeticResidueSum h c*(eisEmbedding (symbol c p)*
      primeCubicGauss p hp hprimary 1 (h*(9*c))):=by ring
    _=arithmeticResidueSum h c*primeCubicGauss p hp hprimary 1 (9*h):=by rw [hG]
    _=(eisEmbedding (symbol c p)*arithmeticResidueSum (h*p) c)*
      primeCubicGauss p hp hprimary 1 (9*h):=by rw [hA]
    _=_:=by ring

lemma ramified_prime_frequency_not_dvd (h p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (hph:¬p∣h) (u:Eisˣ) (n:ℕ) :
    ¬p∣h*(9*(u.val*lambda^n)) := by
  intro hd
  rcases hp.dvd_mul.mp hd with hh|hc
  · exact hph hh
  have hcp: IsCoprime (9*(u.val*lambda^n)) p := by
    have h3: IsCoprime (3:Eis) p:=(primary_coprime_three p hprimary).symm
    have hram: IsCoprime (u.val*lambda^n) p:=
      (ramified_primary_coprime u n p hprimary).of_mul_left_right
    convert (preTransparency := .instances) h3.pow_left (m:=2) |>.mul_left hram using 1 ; norm_num
  exact hp.not_isUnit (hcp.symm.isUnit_of_dvd hc)

lemma sourceRayPhase_mul_primary (h p:Eis) (hprimary:lambda^2∣p-1) :
    ShortDraftTrace.breveE (cuspFrequency (h*p))=
      ShortDraftTrace.breveE (cuspFrequency h) := by
  obtain ⟨d,hd⟩:=three_dvd_lambda_sq.trans hprimary
  have hp:p=1+3*d:=by linear_combination hd
  have he:cuspFrequency (h*p)=cuspFrequency h+cuspFrequency h*(3*eisEmbedding d):=by
    rw [hp,cuspFrequency,cuspFrequency,map_mul,map_add,map_mul,map_one,map_ofNat]
    ring
  rw [he,AddChar.map_add_eq_mul,cuspFrequency_period,mul_one]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance instFintypeUnitsO_2 : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def principalResidueTerm (h:Eis) (u:Eisˣ) (n:ℕ) : ℂ :=
  ((3^(n+2):ℕ):ℂ)^(-(4/3:ℂ))*arithmeticResidueSum h (u.val*lambda^(n+2))*
    unramifiedGaussResidue (h*(9*(u.val*lambda^(n+2))))

lemma principalResidueTerm_vanish (h:Eis) (hh:h≠0) (u:Eisˣ) (n:ℕ)
    (hn:ramifiedFrequencyBound h<n+2) : principalResidueTerm h u n=0 := by
  have hA:arithmeticResidueSum h (u.val*lambda^(n+2))=0:=by
    by_contra hne
    have hb:=Nat.le_log_of_pow_le (by decide : 1<3)
      (ramified_arithmetic_norm_bound h hh u (n+2) (by omega) hne)
    exact (not_le_of_gt hn) hb
  simp only [principalResidueTerm,hA,mul_zero,zero_mul]

lemma principalArithmeticResidue_eq_sum (h:Eis) (hh:h≠0) (N:ℕ)
    (hN:ramifiedFrequencyBound h+1≤N) :
    principalArithmeticResidue h=
      (∑u:Eisˣ,∑n∈Finset.range N,principalResidueTerm h u n)/
        ((9*Real.sqrt 3/2:ℝ):ℂ) := by
  rw [principalArithmeticResidue_eq_ramified_table h hh,Fintype.sum_prod_type]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  change (∑n:Fin (ramifiedFrequencyBound h+1),
    principalRamifiedWeight h (u,n) (4/3)*unramifiedGaussResidue (principalRamifiedIndex h (u,n)))=_
  have hcoeff (n:ℕ) : explicitRamifiedCoefficient h u (n+2)=
      arithmeticResidueSum h (u.val*lambda^(n+2)):=
    (arithmeticResidueSum_eq_explicitRamifiedCoefficient h u (n+2) (by omega)).symm
  simp only [principalRamifiedWeight,principalRamifiedIndex,hcoeff]
  change (∑n:Fin (ramifiedFrequencyBound h+1),principalResidueTerm h u n.val)=_
  rw [Fin.sum_univ_eq_sum_range]
  apply Finset.sum_subset (Finset.range_mono hN)
  intro n hn hn'
  exact principalResidueTerm_vanish h hh u n (by simp only [Finset.mem_range] at hn';omega)

lemma principalResidueTerm_prime_recurrence (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (u:Eisˣ) (n:ℕ) :
    principalResidueTerm (h*p^3) u n=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*principalResidueTerm h u n-
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ))*primeCubicGauss p hp hprimary 1 (9*h)*
        principalResidueTerm (h*p) u n := by
  let c:=u.val*lambda^(n+2)
  have hc:c≠0:=ramifiedElement_ne_zero u (n+2)
  have hlevel:(3:Eis)∣c:=ramifiedElement_level u (n+2) (by omega)
  have hcp:IsCoprime c p:=(ramified_primary_coprime u (n+2) p hprimary).of_mul_left_right
  have hfreq:¬p∣h*(9*c):=ramified_prime_frequency_not_dvd h p hp hprimary hph u (n+2)
  have hA:=arithmeticResidueSum_frequency_cube h c p hc hlevel hprimary hcp
  have hG:=ramified_prime_Gauss_cancel h c p hc hlevel hp hprimary hcp
  change _*arithmeticResidueSum (h*p^3) c*unramifiedGaussResidue ((h*p^3)*(9*c))=_
  rw [hA,show (h*p^3)*(9*c)=(h*(9*c))*p^3 by ring,
    unramifiedGaussResidue_prime_recurrence p hp hprimary (h*(9*c)) hfreq]
  change _=(1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*
    (((3^(n+2):ℕ):ℂ)^(-(4/3:ℂ))*arithmeticResidueSum h c*unramifiedGaussResidue (h*(9*c)))-
    (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ))*primeCubicGauss p hp hprimary 1 (9*h)*
    (((3^(n+2):ℕ):ℂ)^(-(4/3:ℂ))*arithmeticResidueSum (h*p) c*unramifiedGaussResidue ((h*p)*(9*c)))
  rw [show (h*p)*(9*c)=(h*(9*c))*p by ring]
  linear_combination -(((3^(n+2):ℕ):ℂ)^(-(4/3:ℂ)))*
    (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ))*unramifiedGaussResidue ((h*(9*c))*p)*hG

theorem principalArithmeticResidue_prime_recurrence (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    principalArithmeticResidue (h*p^3)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*principalArithmeticResidue h-
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ))*primeCubicGauss p hp hprimary 1 (9*h)*
        principalArithmeticResidue (h*p) := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  let N:=max (ramifiedFrequencyBound (h*p^3)+1)
    (max (ramifiedFrequencyBound h+1) (ramifiedFrequencyBound (h*p)+1))
  rw [principalArithmeticResidue_eq_sum (h*p^3) (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)) N (le_max_left _ _),
    principalArithmeticResidue_eq_sum h hh N (le_trans (le_max_left _ _) (le_max_right _ _)),
    principalArithmeticResidue_eq_sum (h*p) (mul_ne_zero hh hp.ne_zero) N
      (le_trans (le_max_right _ _) (le_max_right _ _))]
  simp_rw [principalResidueTerm_prime_recurrence p hp hprimary h hph,
    Finset.sum_sub_distrib,←Finset.mul_sum]
  ring

theorem sourceArithmeticResidue_prime_recurrence (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceArithmeticResidue (h*p^3)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*sourceArithmeticResidue h-
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ))*primeCubicGauss p hp hprimary 1 (9*h)*
        sourceArithmeticResidue (h*p) := by
  have hm:ShortDraftTrace.breveE (cuspFrequency (h*p^3))=
      ShortDraftTrace.breveE (cuspFrequency h):=by
    rw [show h*p^3=((h*p)*p)*p by ring]
    rw [sourceRayPhase_mul_primary _ p hprimary,sourceRayPhase_mul_primary _ p hprimary,
      sourceRayPhase_mul_primary _ p hprimary]
  have hp9:¬p∣9*h:=by
    have hh:=ramified_prime_frequency_not_dvd h p hp hprimary hph (1:Eisˣ) 0
    simpa only [Units.val_one,pow_zero,one_mul,mul_one,mul_comm 9 h] using hh
  simp only [sourceArithmeticResidue,hm,sourceRayPhase_mul_primary h p hprimary]
  split_ifs with hh
  · rw [principalArithmeticResidue_prime_recurrence p hp hprimary h hph,
      show 9*(h*p^3)=(9*h)*p^3 by ring,
      unramifiedGaussResidue_prime_recurrence p hp hprimary (9*h) hp9,
      show 9*(h*p)=(9*h)*p by ring]
    ring
  · ring

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

theorem sourceArithmeticResidue_prime_factor (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceArithmeticResidue (h*p)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ))*
        primeCubicGauss p hp hprimary 2 (9*h)*sourceArithmeticResidue h := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  have hrec:=sourceArithmeticResidue_prime_recurrence p hp hprimary h hph
  rw [sourceArithmeticResidue_prime_cube p hp hprimary h hh] at hrec
  have hrel:(Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ))*
      primeCubicGauss p hp hprimary 1 (9*h)*sourceArithmeticResidue (h*p)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceArithmeticResidue h:=by
    linear_combination hrec
  have hp9:¬p∣9*h:=by
    have ht:=ramified_prime_frequency_not_dvd h p hp hprimary hph (1:Eisˣ) 0
    simpa only [Units.val_one,pow_zero,one_mul,mul_one,mul_comm 9 h] using ht
  have hG:=primeCubicGauss_one_mul_two p hp hprimary (9*h) hp9
  let q:ℂ:=(Ideal.absNorm (Ideal.span {p}):ℂ)
  have hq:q≠0:=Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hpower:q^(-(2/3:ℂ))*q^(-(4/3:ℂ))*q^2=1:=by
    rw [←Complex.cpow_add _ _ hq,←Complex.cpow_natCast q 2,
      ←Complex.cpow_add _ _ hq]
    norm_num
  calc
    sourceArithmeticResidue (h*p)=
        (q^(-(2/3:ℂ))*q^(-(4/3:ℂ))*q^2)*sourceArithmeticResidue (h*p):=by rw [hpower,one_mul]
    _=q^(-(2/3:ℂ))*q*primeCubicGauss p hp hprimary 2 (9*h)*
        (q^(-(4/3:ℂ))*primeCubicGauss p hp hprimary 1 (9*h)*sourceArithmeticResidue (h*p)):=by
      calc
        _=q^(-(2/3:ℂ))*q^(-(4/3:ℂ))*q*
          (primeCubicGauss p hp hprimary 1 (9*h)*primeCubicGauss p hp hprimary 2 (9*h))*
          sourceArithmeticResidue (h*p):=by rw [hG];ring
        _=_:=by ring
    _=q^(-(2/3:ℂ))*q*primeCubicGauss p hp hprimary 2 (9*h)*(q⁻¹*sourceArithmeticResidue h):=by rw [hrel]
    _=_:=by
      change q^(-(2/3:ℂ))*q*primeCubicGauss p hp hprimary 2 (9*h)*(q⁻¹*sourceArithmeticResidue h)=
        q^(-(2/3:ℂ))*primeCubicGauss p hp hprimary 2 (9*h)*sourceArithmeticResidue h
      field_simp [hq]

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma primeCubicMulChar_inverse (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) :
    (primeCubicMulChar p hp hprimary)⁻¹=primeCubicMulChar p hp hprimary^2 := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [←pow_succ'] using primeCubicMulChar_cube p hp hprimary

lemma primeCubicGauss_two_eq_star (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (h:Eis) :
    primeCubicGauss p hp hprimary 2 h=star (primeCubicGauss p hp hprimary 1 h) := by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let:Field (Eis⧸Ideal.span {p}):=Ideal.Quotient.field _
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  rw [primeCubicGauss_eq_gaussSum,primeCubicGauss_eq_gaussSum,pow_one,star_gaussSum_eq,
    primeCubicMulChar_inverse]
  have he:=mul_gaussSum_inv_eq_gaussSum
    (primeCubicMulChar p hp hprimary^2) ((quotientTrace p hp.ne_zero).mulShift (Ideal.Quotient.mk _ h))
  have hm:(primeCubicMulChar p hp hprimary^2) (-1 : Eis⧸Ideal.span {p})=1:=by
    rw [MulChar.pow_apply' _ (by decide : (2:ℕ)≠0),←map_pow]
    norm_num
  rw [hm,one_mul] at he
  exact he.symm

lemma cubicBesselNormalizer_mul (h p:Eis) :
    cubicBesselNormalizer (h*p)=(‖eisEmbedding p‖:ℂ)^(1/3:ℂ)*cubicBesselNormalizer h := by
  have hfreq:‖cuspFrequency (h*p)‖=‖cuspFrequency h‖*‖eisEmbedding p‖:=by
    rw [cuspFrequency_mul_right,norm_mul]
  have he:(2*Real.pi*‖cuspFrequency (h*p)‖:ℂ)=
      (‖eisEmbedding p‖:ℂ)*((2*Real.pi*‖cuspFrequency h‖:ℝ):ℂ):=by rw [hfreq];push_cast;ring
  unfold cubicBesselNormalizer
  rw [he,Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (by positivity)]
  push_cast
  ring

lemma prime_normalizer_powers (p:Eis) (hp:p≠0) :
    (‖eisEmbedding p‖:ℂ)^(1/3:ℂ)*(Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ))=
      (‖eisEmbedding p‖:ℂ)⁻¹ := by
  have hr:(‖eisEmbedding p‖:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp))
  rw [←Complex.ofReal_natCast,←eisEmbedding_norm_sq_eq_absNorm_span,pow_two,
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _),
    ←mul_assoc,←Complex.cpow_add _ _ hr,←Complex.cpow_add _ _ hr]
  convert (preTransparency := .instances) Complex.cpow_neg_one (‖eisEmbedding p‖:ℂ) using 1 ; congr 1 ; norm_num

theorem sourceResidualFourierCoefficient_prime_factor (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceResidualFourierCoefficient (h*p)=
      (primeCubicGauss p hp hprimary 2 (9*h)/(‖eisEmbedding p‖:ℂ))*sourceResidualFourierCoefficient h := by
  rw [sourceResidualFourierCoefficient,cubicBesselNormalizer_mul,
    sourceArithmeticResidue_prime_factor p hp hprimary h hph,sourceResidualFourierCoefficient]
  calc
    _=((‖eisEmbedding p‖:ℂ)^(1/3:ℂ)*(Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ)))*
      primeCubicGauss p hp hprimary 2 (9*h)*(cubicBesselNormalizer h*sourceArithmeticResidue h):=by ring
    _=_:=by rw [prime_normalizer_powers p hp.ne_zero];ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def normalizedCubicUnitGauss (n:Eis) : ℂ :=
  cubicUnitGaussSum 1 n/(‖eisEmbedding n‖:ℂ)

@[simp] lemma normalizedCubicUnitGauss_one : normalizedCubicUnitGauss 1=1 := by
  simp [normalizedCubicUnitGauss]

lemma primary_finset_product {ι:Type*} (s:Finset ι) (p:ι→Eis)
    (hp:∀i∈s,lambda^2∣p i-1) : lambda^2∣(∏i∈s,p i)-1 := by
  classical
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert i s hi ih=>
    rw [Finset.prod_insert hi]
    exact primary_mul _ _ (hp i (Finset.mem_insert_self _ _))
      (ih (fun j hj=>hp j (Finset.mem_insert_of_mem hj)))

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

theorem sourceArithmeticResidue_primary_cube (b:Eis) (hb:b≠0)
    (hbprimary:lambda^2∣b-1) (h:Eis) (hh:h≠0) :
    sourceArithmeticResidue (h*b^3)=sourceArithmeticResidue h := by
  obtain ⟨s,hs,hpr⟩:=exists_primary_prime_factorization b hb hbprimary
  rw [←hs]
  clear hs hb hbprimary b
  induction s using Multiset.induction_on generalizing h with
  | empty=>simp
  | @cons p s ih=>
    have hp:=hpr p (Multiset.mem_cons_self _ _)
    have hs:∀q∈s,Prime q∧lambda^2∣q-1:=fun q hq=>hpr q (Multiset.mem_cons_of_mem hq)
    have hs0:s.prod≠0:=by
      intro hz
      exact (hs 0 (Multiset.prod_eq_zero_iff.mp hz)).1.ne_zero rfl
    rw [Multiset.prod_cons,show h*(p*s.prod)^3=(h*s.prod^3)*p^3 by ring,
      sourceArithmeticResidue_prime_cube p hp.1 hp.2 _ (mul_ne_zero hh (pow_ne_zero _ hs0))]
    exact ih h hh hs

theorem sourceResidualFourierCoefficient_primary_cube (b:Eis) (hb:b≠0)
    (hbprimary:lambda^2∣b-1) (h:Eis) (hh:h≠0) :
    sourceResidualFourierCoefficient (h*b^3)=
      (‖eisEmbedding b‖:ℂ)*sourceResidualFourierCoefficient h := by
  rw [sourceResidualFourierCoefficient,cubicBesselNormalizer_mul_cube h b hb,
    sourceArithmeticResidue_primary_cube b hb hbprimary h hh,sourceResidualFourierCoefficient]
  ring

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma cubicRow_eq_idealSymbol (I:Ideal Eis) (hI:primaryGenerator I≠0)
    (hsq:Squarefree I) (a:Eis) :
    cubicRow I hI (Ideal.Quotient.mk I a)=eisEmbedding (idealSymbol I a) := by
  rw [cubicRow_mk]
  simp_rw [canonicalSextic_pow_two,MulChar.ringHomComp_apply,←primeValue_eq]
  change (∏P:primeSupport I,eisEmbedding (primeValue P.val a))=eisEmbedding (idealSymbol I a)
  rw [←Finset.prod_subtype (primeSupport I) (fun _=>Iff.rfl)
    (fun P=>eisEmbedding (primeValue P a)),←map_prod]
  have hI0:=primaryGenerator_ne_zero_ideal I hI
  have hnodup: (UniqueFactorizationMonoid.normalizedFactors I).Nodup:=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI0).mp hsq
  congr 1
  rw [idealSymbol,if_neg hI0]
  change (((primeSupport I).val.map (fun P=>primeValue P a)).prod)=_
  have hv:(primeSupport I).val=UniqueFactorizationMonoid.normalizedFactors I:=by
    simpa only [primeSupport, Multiset.toFinset_val] using hnodup.dedup
  rw [hv]

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma primaryGenerator_squarefree_support (I:Ideal Eis) (hI:primaryGenerator I≠0)
    (hsq:Squarefree I) : primaryGenerator I=∏P∈primeSupport I,primaryPrime P := by
  have hI0:=primaryGenerator_ne_zero_ideal I hI
  have hn: (UniqueFactorizationMonoid.normalizedFactors I).Nodup:=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI0).mp hsq
  have hv:(primeSupport I).val=UniqueFactorizationMonoid.normalizedFactors I:=by
    simpa only [primeSupport, Multiset.toFinset_val] using hn.dedup
  unfold primaryGenerator
  rw [if_neg hI0]
  change _=((primeSupport I).val.map primaryPrime).prod
  rw [hv]

lemma primaryPrime_isPrime_of_mem (I P:Ideal Eis) (hI:primaryGenerator I≠0)
    (hP:P∈primeSupport I) : Prime (primaryPrime P) := by
  have hp0:=primaryPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP)
  have hs:=primaryPrime_spec P hp0
  let:P.IsMaximal:=hs.1
  apply (Ideal.span_singleton_prime hp0).mp
  rw [hs.2.2.1]
  infer_instance

lemma primaryPrime_support_coprime (I:Ideal Eis) (hI:primaryGenerator I≠0)
    (P:Ideal Eis) (hP:P∈primeSupport I) (Q:Ideal Eis) (hQ:Q∈primeSupport I) (hne:P≠Q) :
    IsCoprime (primaryPrime P) (primaryPrime Q) := by
  have hp:=primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))
  have hq:=primaryPrime_spec Q (primaryPrime_factor_ne_zero I Q hI (Multiset.mem_toFinset.mp hQ))
  let:P.IsMaximal:=hp.1
  let:Q.IsMaximal:=hq.1
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [hp.2.2.1,hq.2.2.1]
  exact Ideal.isCoprime_of_isMaximal hne

def infinityCoefficientScalar : ℂ := star (sourceResidualFourierCoefficient 1)

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def thetaSquarefreePart (I:Ideal Eis) : Ideal Eis :=
  ∏P∈(primeSupport I).filter (fun P=>(normalizedFactors I).count P%3=1),P

def thetaCubePart (I:Ideal Eis) : Ideal Eis :=
  ∏P∈primeSupport I,P^((normalizedFactors I).count P/3)

end

section
open Filter
open scoped BigOperators Classical Topology

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma unramifiedGaussResidue_eq_of_initial_eq (h k:Eis)
    (he:∀s:ℂ,4<s.re→0<s.im→
      unramifiedCubicGaussSeries s h=unramifiedCubicGaussSeries s k) :
    unramifiedGaussResidue h=unramifiedGaussResidue k := by
  have hh:=unramifiedGaussResidue_of_initial_relation h k 0 (fun _=>1) (fun _=>0)
    (fun _ _=>analyticAt_const) (fun _ _=>analyticAt_const)
    continuousAt_const continuousAt_const (fun s hs hi=>by simpa using he s hs hi)
  simpa only [one_mul,zero_mul,add_zero] using hh

theorem unramifiedGaussResidue_neg (h:Eis) :
    unramifiedGaussResidue (-h)=unramifiedGaussResidue h :=
  unramifiedGaussResidue_eq_of_initial_eq _ _ (fun s _ _=>unramifiedCubicGaussSeries_neg s h)

theorem unramifiedGaussResidue_lambda_pow (h:Eis) (n:ℕ) :
    unramifiedGaussResidue (h*lambda^n)=
      unramifiedGaussResidue (h*lambda^(n%3)) :=
  unramifiedGaussResidue_eq_of_initial_eq _ _ (fun s _ _=>unramifiedCubicGaussSeries_lambda_pow s h n)

theorem unramifiedGaussResidue_nine_family (h:Eis) (u:Eisˣ) (n:ℕ) :
    ∃j k:Fin 3,unramifiedGaussResidue (h*(9*((u:Eis)*lambda^n)))=
      unramifiedGaussResidue (h*omega^j.val*lambda^k.val) := by
  obtain ⟨j,k,hjk⟩:=unramifiedCubicGaussSeries_nine_family h u n
  exact ⟨j,k,unramifiedGaussResidue_eq_of_initial_eq _ _ (fun s _ _=>hjk s)⟩

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance instFintypeUnitsO_4 : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def ramifiedResidueFamilyMass (h:Eis) : ℝ :=
  ∑a:Fin 3×Fin 3,‖unramifiedGaussResidue (h*omega^a.1.val*lambda^a.2.val)‖

lemma ramifiedResidueFamilyMass_nonneg (h:Eis) : 0≤ ramifiedResidueFamilyMass h :=
  Finset.sum_nonneg (fun _ _=>norm_nonneg _)

lemma unramifiedGaussResidue_family_norm_le (h:Eis) (j k:Fin 3) :
    ‖unramifiedGaussResidue (h*omega^j.val*lambda^k.val)‖≤ ramifiedResidueFamilyMass h := by
  unfold ramifiedResidueFamilyMass
  exact Finset.single_le_sum (a:=(j,k)) (s:=Finset.univ)
    (f:=fun a:Fin 3×Fin 3=>‖unramifiedGaussResidue (h*omega^a.1.val*lambda^a.2.val)‖)
    (fun _ _=>norm_nonneg _) (Finset.mem_univ (j,k))

lemma unramifiedGaussResidue_nine_norm_le (h:Eis) (u:Eisˣ) (n:ℕ) :
    ‖unramifiedGaussResidue (h*(9*((u:Eis)*lambda^n)))‖≤ ramifiedResidueFamilyMass h := by
  obtain ⟨j,k,hjk⟩:=unramifiedGaussResidue_nine_family h u n
  rw [hjk]
  exact unramifiedGaussResidue_family_norm_le h j k

theorem unramifiedGaussResidue_unit_lambda_family (u:Eisˣ) (n:ℕ) :
    ∃j k:Fin 3,unramifiedGaussResidue ((u:Eis)*lambda^n)=
      unramifiedGaussResidue (omega^j.val*lambda^k.val) := by
  obtain ⟨j,hj⟩:=unit_eq_sign_omega u
  refine ⟨j,⟨n%3,Nat.mod_lt _ (by decide)⟩,?_⟩
  rcases hj with hj|hj
  · rw [hj,unramifiedGaussResidue_lambda_pow]
  · rw [hj,neg_mul,unramifiedGaussResidue_neg,unramifiedGaussResidue_lambda_pow]

lemma unramifiedGaussResidue_unit_lambda_norm_le (u:Eisˣ) (n:ℕ) :
    ‖unramifiedGaussResidue ((u:Eis)*lambda^n)‖≤ ramifiedResidueFamilyMass 1 := by
  obtain ⟨j,k,hjk⟩:=unramifiedGaussResidue_unit_lambda_family u n
  rw [hjk]
  simpa only [one_mul] using unramifiedGaussResidue_family_norm_le 1 j k

lemma ramifiedResidueFamilyMass_unit_lambda_le (u:Eisˣ) (n:ℕ) :
    ramifiedResidueFamilyMass ((u:Eis)*lambda^n)≤9*ramifiedResidueFamilyMass 1 := by
  calc
    _≤∑a:Fin 3×Fin 3,ramifiedResidueFamilyMass 1:=by
      apply Finset.sum_le_sum
      intro a ha
      let v:Eisˣ:=u*ramifiedOmegaUnit^a.1.val
      have he:((u:Eis)*lambda^n)*omega^a.1.val*lambda^a.2.val=
          (v:Eis)*lambda^(n+a.2.val):=by
        simp only [v,Units.val_mul,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val,pow_add]
        ring
      rw [he]
      exact unramifiedGaussResidue_unit_lambda_norm_le v _
    _=_:=by simp

theorem sourceArithmeticResidue_family_bound (h:Eis) (hh:h≠0) :
    ‖sourceArithmeticResidue h‖≤
      ((∑i:PrincipalRamifiedIndex h,‖principalRamifiedWeight h i (4/3)‖)+3)*
        ramifiedResidueFamilyMass h/(4*(9*Real.sqrt 3/2)) := by
  have hM:=ramifiedResidueFamilyMass_nonneg h
  have hden:0<4*(9*Real.sqrt 3/2):=by positivity
  rw [sourceArithmeticResidue_eq_ramified_table h hh]
  split_ifs with hphase
  · rw [norm_div,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (show 0<(9*Real.sqrt 3/2:ℝ) by positivity)]
    apply div_le_div_of_nonneg_right _ hden.le
    calc
      _≤‖∑i:PrincipalRamifiedIndex h,principalRamifiedWeight h i (4/3)*
          unramifiedGaussResidue (principalRamifiedIndex h i)‖+
          ‖(3:ℂ)*unramifiedGaussResidue (9*h)‖:=norm_add_le _ _
      _≤(∑i:PrincipalRamifiedIndex h,‖principalRamifiedWeight h i (4/3)‖)*
          ramifiedResidueFamilyMass h+3*ramifiedResidueFamilyMass h:=by
        apply add_le_add
        · calc
            _≤∑i:PrincipalRamifiedIndex h,‖principalRamifiedWeight h i (4/3)*
                unramifiedGaussResidue (principalRamifiedIndex h i)‖:=norm_sum_le _ _
            _≤∑i:PrincipalRamifiedIndex h,‖principalRamifiedWeight h i (4/3)‖*
                ramifiedResidueFamilyMass h:=by
              apply Finset.sum_le_sum
              intro i hi
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left
                (unramifiedGaussResidue_nine_norm_le h i.1 (i.2.val+2)) (norm_nonneg _)
            _=_:=by rw [Finset.sum_mul]
        · rw [norm_mul,Complex.norm_ofNat]
          have hb:=unramifiedGaussResidue_nine_norm_le h (1:Eisˣ) 0
          simp only [Units.val_one,pow_zero,mul_one] at hb
          simpa only [mul_comm 9 h] using mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤3)
      _=_:=by ring
  · rw [norm_zero]
    positivity

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance instFintypeUnitsO_5 : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def ramifiedDecayRatio : ℝ := (3:ℝ)^(-(1/3:ℝ))

lemma ramifiedDecayRatio_pos : 0< ramifiedDecayRatio :=
  Real.rpow_pos_of_pos (by norm_num) _

lemma ramifiedDecayRatio_lt_one : ramifiedDecayRatio<1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

lemma explicitRamifiedCoefficient_norm_le (h:Eis) (u:Eisˣ) (n:ℕ) :
    ‖explicitRamifiedCoefficient h u n‖≤(3^n:ℕ) := by
  unfold explicitRamifiedCoefficient
  split_ifs with hd
  · dsimp only
    split_ifs <;> simp [residueAdditive,breveE_norm]
  · simp

lemma ramifiedWeight_norm_scalar (n:ℕ) :
    ‖((3^n:ℕ):ℂ)^(-(4/3:ℂ))‖*(3^n:ℕ)=ramifiedDecayRatio^n := by
  have ha:0<(3:ℝ)^n:=pow_pos (by norm_num) _
  have hn:‖((3:ℂ)^n)^(-(4/3:ℂ))‖=((3:ℝ)^n)^(-(4/3:ℝ)):=by
    have he:=Complex.norm_cpow_eq_rpow_re_of_pos ha (-(4/3:ℂ))
    have hre:(-(4/3:ℂ)).re=-(4/3:ℝ):=by norm_num
    rw [hre] at he
    simpa only [Complex.ofReal_pow,Complex.ofReal_ofNat] using he
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  rw [hn]
  calc
    ((3:ℝ)^n)^(-(4/3:ℝ))*(3:ℝ)^n=
        ((3:ℝ)^n)^(-(4/3:ℝ))*((3:ℝ)^n)^(1:ℝ):=by rw [Real.rpow_one]
    _=((3:ℝ)^n)^(-(1/3:ℝ)):=by
      rw [←Real.rpow_add ha]
      congr 1
      norm_num
    _=(3:ℝ)^((n:ℝ)*(-(1/3:ℝ))):=(Real.rpow_natCast_mul (by norm_num) n _).symm
    _=(3:ℝ)^((-(1/3:ℝ))*(n:ℝ)):=by rw [mul_comm]
    _=ramifiedDecayRatio^n:=by
      rw [Real.rpow_mul (by norm_num),Real.rpow_natCast]
      rfl

lemma principalRamifiedWeight_norm_le (h:Eis) (i:PrincipalRamifiedIndex h) :
    ‖principalRamifiedWeight h i (4/3)‖≤ ramifiedDecayRatio^(i.2.val+2) := by
  unfold principalRamifiedWeight
  rw [norm_mul]
  calc
    _≤‖((3^(i.2.val+2):ℕ):ℂ)^(-(4/3:ℂ))‖*(3^(i.2.val+2):ℕ):=
      mul_le_mul_of_nonneg_left (explicitRamifiedCoefficient_norm_le h i.1 _) (norm_nonneg _)
    _=_:=ramifiedWeight_norm_scalar _

theorem principalRamifiedWeight_sum_norm_le (h:Eis) :
    (∑i:PrincipalRamifiedIndex h,‖principalRamifiedWeight h i (4/3)‖)≤
      6*ramifiedDecayRatio^2/(1-ramifiedDecayRatio) := by
  have ht0:=ramifiedDecayRatio_pos.le
  have ht1:=ramifiedDecayRatio_lt_one
  have hfin:(∑n:Fin (ramifiedFrequencyBound h+1),ramifiedDecayRatio^(n.val+2))≤
      ramifiedDecayRatio^2/(1-ramifiedDecayRatio):=by
    rw [Fin.sum_univ_eq_sum_range (fun n:ℕ=>ramifiedDecayRatio^(n+2))]
    simp_rw [pow_add,mul_comm _ (ramifiedDecayRatio^2)]
    rw [←Finset.mul_sum]
    have hs: (∑n∈Finset.range (ramifiedFrequencyBound h+1),ramifiedDecayRatio^n)≤
        (1-ramifiedDecayRatio)⁻¹:=by
      rw [←tsum_geometric_of_lt_one ht0 ht1]
      exact (summable_geometric_of_lt_one ht0 ht1).sum_le_tsum _ (fun n _=>pow_nonneg ht0 n)
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hs (sq_nonneg ramifiedDecayRatio)
  calc
    _≤∑i:PrincipalRamifiedIndex h,ramifiedDecayRatio^(i.2.val+2):=
      Finset.sum_le_sum (fun i _=>principalRamifiedWeight_norm_le h i)
    _=(6:ℝ)*(∑n:Fin (ramifiedFrequencyBound h+1),ramifiedDecayRatio^(n.val+2)):=by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      have hc:Fintype.card Eisˣ=6:=by
        simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six
      rw [hc]
      norm_num
    _≤6*(ramifiedDecayRatio^2/(1-ramifiedDecayRatio)):=mul_le_mul_of_nonneg_left hfin (by norm_num)
    _=_:=by ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance instFintypeUnitsO_6 : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def ramifiedSourceFamilyConstant : ℝ :=
  (6*ramifiedDecayRatio^2/(1-ramifiedDecayRatio)+3)/(4*(9*Real.sqrt 3/2))

lemma ramifiedSourceFamilyConstant_nonneg : 0≤ ramifiedSourceFamilyConstant := by
  have ht:0<1-ramifiedDecayRatio:=sub_pos.mpr ramifiedDecayRatio_lt_one
  unfold ramifiedSourceFamilyConstant
  positivity

theorem sourceArithmeticResidue_nine_family_bound (h:Eis) (hh:h≠0) :
    ‖sourceArithmeticResidue h‖≤ ramifiedSourceFamilyConstant*ramifiedResidueFamilyMass h := by
  have hm:=ramifiedResidueFamilyMass_nonneg h
  refine (sourceArithmeticResidue_family_bound h hh).trans ?_
  have hw:(∑i:PrincipalRamifiedIndex h,‖principalRamifiedWeight h i (4/3)‖)+3≤
      6*ramifiedDecayRatio^2/(1-ramifiedDecayRatio)+3:=by
    linarith [principalRamifiedWeight_sum_norm_le h]
  calc
    _≤(6*ramifiedDecayRatio^2/(1-ramifiedDecayRatio)+3)*
        ramifiedResidueFamilyMass h/(4*(9*Real.sqrt 3/2)):=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hw hm) (by positivity)
    _=ramifiedSourceFamilyConstant*ramifiedResidueFamilyMass h:=by
      unfold ramifiedSourceFamilyConstant
      ring

theorem sourceArithmeticResidue_unit_lambda_bound (u:Eisˣ) (n:ℕ) :
    ‖sourceArithmeticResidue ((u:Eis)*lambda^n)‖≤
      9*ramifiedSourceFamilyConstant*ramifiedResidueFamilyMass 1 := by
  refine (sourceArithmeticResidue_nine_family_bound _ (ramifiedElement_ne_zero u n)).trans ?_
  have he:=mul_le_mul_of_nonneg_left (ramifiedResidueFamilyMass_unit_lambda_le u n)
    ramifiedSourceFamilyConstant_nonneg
  convert (preTransparency := .instances) he using 1 ; ring

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicKubota CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def extraPeriodWitness : levelThree := by
  let M:SL(2,Eis):=⟨!![1+3*omega,3*omega^2;-3,1-3*omega],by
    rw [Matrix.det_fin_two_of]
    ring⟩
  refine ⟨M,levelThree_of_entries M ?_⟩
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨omega,by change 1+3*omega-1=3*omega;ring⟩
  · exact ⟨omega^2,by change 3*omega^2-0=3*omega^2;ring⟩
  · exact ⟨-1,by change -3-(0:Eis)=3*(-1);ring⟩
  · exact ⟨-omega,by change 1-3*omega-1=3*(-omega);ring⟩

def rationalLowerMinusThree : SL(2,ℤ):=⟨!![1,0;-3,1],by simp [Matrix.det_fin_two]⟩

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical

namespace CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def primaryCubePairToMellinIndex
    (p:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
      {J:Ideal Eis // primaryGenerator J≠0})) : CompletedMellinIndex :=
  (⟨p.1.val,p.1.property.1.ne_zero⟩,
    ⟨p.2.val,primaryGenerator_ne_zero_ideal p.2.val p.2.property⟩)

end CompletedGauss

namespace CubicEisenstein
open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology MatrixGroups

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma upper_triangular_right_cusp_ratio (g T:SL(2,ℂ)) (hT:T 1 0=0)
    (hc:(g*T) 1 0≠0) :
    g 1 0≠0 ∧ (g*T) 0 0/(g*T) 1 0=g 0 0/g 1 0 := by
  have hcol (i:Fin 2) : (g*T) i 0=g i 0*T 0 0 := by
    change (∑k:Fin 2,g i k*T k 0)=_
    rw [Fin.sum_univ_two,hT,mul_zero,add_zero]
  have hn:g 1 0*T 0 0≠0:=by rwa [hcol] at hc
  have hg: g 1 0≠0:=(mul_ne_zero_iff.mp hn).1
  have ht:T 0 0≠0:=(mul_ne_zero_iff.mp hn).2
  refine ⟨hg,?_⟩
  rw [hcol,hcol]
  field_simp

lemma exists_integral_matrix_cusp_ratio (a c:Eis) (hc:c≠0) :
    ∃M:SL(2,Eis),M 1 0≠0 ∧
      eisEmbedding (M 0 0)/eisEmbedding (M 1 0)=eisEmbedding a/eisEmbedding c := by
  let d:Eis:=IsBezout.gcd a c
  obtain ⟨a',ha⟩:=IsBezout.gcd_dvd_left a c
  obtain ⟨c',hc'⟩:=IsBezout.gcd_dvd_right a c
  change a=d*a' at ha
  change c=d*c' at hc'
  have hd:d≠0:=by
    intro hz
    exact hc (by rw [hc',hz,zero_mul])
  have hcp:c'≠0:=by
    intro hz
    exact hc (by rw [hc',hz,mul_zero])
  obtain ⟨u,v,huv⟩:=IsBezout.gcd_eq_sum a c
  change u*a+v*c=d at huv
  have hred:u*a'+v*c'=1:=by
    apply mul_left_cancel₀ hd
    calc
      d*(u*a'+v*c')=u*a+v*c:=by rw [ha,hc'];ring
      _=d:=huv
      _=d*1:=(mul_one d).symm
  let M:SL(2,Eis):=⟨!![a',-v;c',u],by
    rw [Matrix.det_fin_two_of]
    linear_combination hred⟩
  refine ⟨M,hcp,?_⟩
  change eisEmbedding a'/eisEmbedding c'=eisEmbedding a/eisEmbedding c
  rw [ha,hc',map_mul,map_mul]
  have hde:eisEmbedding d≠0:=eisEmbedding_ne_zero hd
  have hce:eisEmbedding c'≠0:=eisEmbedding_ne_zero hcp
  field_simp

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance signedOmegaUnitsFintype : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def signedOmegaUnit (s:Bool) (j:Fin 3) :Eisˣ :=
  if s then -(ramifiedOmegaUnit^j.val) else ramifiedOmegaUnit^j.val

lemma signedOmegaUnit_val (s:Bool) (j:Fin 3) :
    (signedOmegaUnit s j:Eis)=if s then -(omega^j.val) else omega^j.val := by
  cases s <;> simp [signedOmegaUnit,ramifiedOmegaUnit_val]

lemma signedOmegaUnit_surjective : Function.Surjective (fun p:Bool×Fin 3=>signedOmegaUnit p.1 p.2) := by
  intro u
  obtain ⟨j,hj|hj⟩:=unit_eq_sign_omega u
  · refine ⟨(false,j),Units.ext ?_⟩
    simpa only [signedOmegaUnit_val,Bool.false_eq_true,ite_false] using hj.symm
  · refine ⟨(true,j),Units.ext ?_⟩
    simpa only [signedOmegaUnit_val,ite_true] using hj.symm

def signedOmegaEquiv : (Bool×Fin 3)≃Eisˣ := Equiv.ofBijective
  (fun p=>signedOmegaUnit p.1 p.2)
  ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨signedOmegaUnit_surjective,by
    have hc:Fintype.card Eisˣ=6:=by
      simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six
    simp [hc]⟩)

lemma cubicSymbol_norm_one (c n:Eis) (hn:lambda^2∣n-1) (hc:IsCoprime c n) :
    ‖eisEmbedding (symbol c n)‖=1 := by
  have hcube:(eisEmbedding (symbol c n))^3=1:=by
    rw [←map_pow,symbol_cube_of_isCoprime c n hn hc,map_one]
  apply (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (3:ℕ)≠0)).mp
  simpa only [norm_pow,norm_one,one_pow] using congrArg norm hcube

lemma arithmeticResidueSum_norm_mul_primary (h n:Eis) (hn:lambda^2∣n-1)
    (u:Eisˣ) (r:ℕ) (hr:2≤ r) :
    ‖arithmeticResidueSum (h*n) (u.val*lambda^r)‖=
      ‖arithmeticResidueSum h (u.val*lambda^r)‖ := by
  have hc: IsCoprime (u.val*lambda^r) n :=
    (ramified_primary_coprime u r n hn).of_mul_left_right
  have he:=congrArg norm (arithmeticResidueSum_frequency_twist h (u.val*lambda^r) n
    (ramifiedElement_ne_zero u r) (ramifiedElement_level u r hr)
    ⟨hc,three_dvd_lambda_sq.trans hn⟩)
  simpa only [norm_mul,cubicSymbol_norm_one _ n hn hc,one_mul] using he

def lowRamifiedFrequency (a r:Fin 3) : Eis := omega^a.val*lambda^(r.val+2)

lemma lowRamifiedFrequency_ne_zero (a r:Fin 3) : lowRamifiedFrequency a r≠0 := by
  simpa only [lowRamifiedFrequency,←ramifiedOmegaUnit_val,←Units.val_pow_eq_pow_val] using
    ramifiedElement_ne_zero (ramifiedOmegaUnit^a.val) (r.val+2)

lemma lowRamifiedFrequency_absNorm (a r:Fin 3) :
    Ideal.absNorm (Ideal.span {lowRamifiedFrequency a r})=3^(r.val+2) := by
  simpa only [lowRamifiedFrequency,←ramifiedOmegaUnit_val,←Units.val_pow_eq_pow_val] using
    ramifiedElement_absNorm (ramifiedOmegaUnit^a.val) (r.val+2)

lemma lowRamifiedFrequency_arithmetic_vanish (a r:Fin 3) (u:Eisˣ) (k:ℕ) (hk:5≤k) :
    arithmeticResidueSum (lowRamifiedFrequency a r) (u.val*lambda^(k+2))=0 := by
  by_contra hA
  have hb:=ramified_arithmetic_norm_bound _ (lowRamifiedFrequency_ne_zero a r) u (k+2) (by omega) hA
  rw [lowRamifiedFrequency_absNorm] at hb
  have hlo:(3:ℕ)^7≤3^(k+2):=Nat.pow_le_pow_right (by decide) (by omega)
  have hhi:(3:ℕ)^(r.val+2)≤3^4:=Nat.pow_le_pow_right (by decide) (by omega)
  norm_num at hlo hhi
  omega

lemma lowRamifiedFrequency_primary_vanish (a r:Fin 3) (n:Eis) (hn:lambda^2∣n-1)
    (u:Eisˣ) (k:ℕ) (hk:5≤k) :
    arithmeticResidueSum (lowRamifiedFrequency a r*n) (u.val*lambda^(k+2))=0 := by
  apply norm_eq_zero.mp
  rw [arithmeticResidueSum_norm_mul_primary _ n hn u (k+2) (by omega),
    lowRamifiedFrequency_arithmetic_vanish a r u k hk,norm_zero]

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedCoordMul (x y:ℤ×ℤ) :ℤ×ℤ := (x.1*y.1-x.2*y.2,x.1*y.2+x.2*y.1-x.2*y.2)
def ramifiedCoordPow (x:ℤ×ℤ) :ℕ→ℤ×ℤ
  | 0=>(1,0)
  | n+1=>ramifiedCoordMul (ramifiedCoordPow x n) x

def lowRamifiedQuotientCoord (a r:Fin 3) (s:Bool) (j:Fin 3) (n:Fin 5) :ℤ×ℤ :=
  let z:=ramifiedCoordMul (ramifiedCoordPow (0,1) (a.val+5-j.val))
    (ramifiedCoordPow (-1,1) (r.val+2-n.val))
  if s then z else (-z.1,-z.2)

def lowRamifiedSupport (a r:Fin 3) (p:Bool×Fin 3×Fin 5) :Prop :=
  p.2.2.val≤ r.val+2 ∧
  let z:=lowRamifiedQuotientCoord a r p.1 p.2.1 p.2.2
  (3:ℤ)∣2*(p.2.1.val:ℤ)+(p.2.2.val+2:ℕ)+z.2 ∧
  (3:ℤ)∣2*(p.2.1.val:ℤ)+z.1-z.2

instance lowRamifiedSupport_decidable (a r:Fin 3) (p:Bool×Fin 3×Fin 5) :
    Decidable (lowRamifiedSupport a r p) :=
  inferInstanceAs (Decidable (p.2.2.val≤ r.val+2 ∧
    (3:ℤ)∣2*(p.2.1.val:ℤ)+(p.2.2.val+2:ℕ)+(lowRamifiedQuotientCoord a r p.1 p.2.1 p.2.2).2 ∧
    (3:ℤ)∣2*(p.2.1.val:ℤ)+(lowRamifiedQuotientCoord a r p.1 p.2.1 p.2.2).1-
      (lowRamifiedQuotientCoord a r p.1 p.2.1 p.2.2).2))

def lowRamifiedSupportSet (a r:Fin 3) :Finset (Bool×Fin 3×Fin 5) :=
  Finset.univ.filter (lowRamifiedSupport a r)

lemma lowRamifiedSupport_card (a r:Fin 3) : (lowRamifiedSupportSet a r).card≤5 := by
  decide +revert

lemma lowRamifiedSupport_exponent (a r:Fin 3) (p:Bool×Fin 3×Fin 5)
    (hp:lowRamifiedSupport a r p) : 1≤p.2.2.val := by
  decide +revert

lemma ramifiedCoordMul_eval (x y:ℤ×ℤ) :
    ActualEisensteinCoordinates.eval (ramifiedCoordMul x y).1 (ramifiedCoordMul x y).2=
      ActualEisensteinCoordinates.eval x.1 x.2*ActualEisensteinCoordinates.eval y.1 y.2 :=
  (ActualEisensteinCoordinates.eval_mul _ _ _ _).symm

lemma ramifiedCoordPow_eval (x:ℤ×ℤ) (n:ℕ) :
    ActualEisensteinCoordinates.eval (ramifiedCoordPow x n).1 (ramifiedCoordPow x n).2=
      (ActualEisensteinCoordinates.eval x.1 x.2)^n := by
  induction n with
  | zero => simp [ramifiedCoordPow,ActualEisensteinCoordinates.eval]
  | succ n ih => rw [ramifiedCoordPow,ramifiedCoordMul_eval,ih,pow_succ]

lemma lowRamifiedQuotientCoord_eval (a r:Fin 3) (s:Bool) (j:Fin 3) (n:Fin 5) :
    ActualEisensteinCoordinates.eval (lowRamifiedQuotientCoord a r s j n).1
      (lowRamifiedQuotientCoord a r s j n).2=
      if s then omega^(a.val+5-j.val)*lambda^(r.val+2-n.val)
      else -(omega^(a.val+5-j.val)*lambda^(r.val+2-n.val)) := by
  have ho:ActualEisensteinCoordinates.eval 0 1=omega:=by
    simp [ActualEisensteinCoordinates.eval]; rfl
  have hl:ActualEisensteinCoordinates.eval (-1) 1=lambda:=by
    change ActualEisensteinCoordinates.eval (-1) 1=omega-1
    have he:ActualEisensteinCoordinates.eval (-1) 1=(-1:Eis)+ActualEisensteinCoordinates.eval 0 1:=by
      simp [ActualEisensteinCoordinates.eval]
    rw [he,ho]
    ring
  have he:∀x:ℤ×ℤ,ActualEisensteinCoordinates.eval (-x.1) (-x.2)=
      -ActualEisensteinCoordinates.eval x.1 x.2:=by
    intro x
    simp only [ActualEisensteinCoordinates.eval,Int.cast_neg]
    ring
  cases s <;> simp only [lowRamifiedQuotientCoord,Bool.false_eq_true,ite_false,ite_true,
    he,ramifiedCoordMul_eval,ramifiedCoordPow_eval,ho,hl]

lemma lowRamifiedQuotientCoord_relation (a r:Fin 3) (s:Bool) (j:Fin 3) (n:Fin 5)
    (hn:n.val≤ r.val+2) :
    3*lowRamifiedFrequency a r=
      ((signedOmegaUnit s j:Eis)*lambda^(n.val+2))*
        ActualEisensteinCoordinates.eval (lowRamifiedQuotientCoord a r s j n).1
          (lowRamifiedQuotientCoord a r s j n).2 := by
  have hw:omega^2=-omega-1:=by linear_combination ramified_omega_relation
  have hl:lambda^2=-3*omega:=by
    change (omega-1)^2=-3*omega
    linear_combination hw
  have h3:(3:Eis)=-omega^2*lambda^2:=by
    rw [hl]
    calc
      (3:Eis)=3*omega^3:=by rw [omega_primitive.pow_eq_one]; ring
      _=_:=by ring
  have ho:omega^j.val*omega^(a.val+5-j.val)=omega^(a.val+2):=by
    rw [←pow_add,show j.val+(a.val+5-j.val)=a.val+5 by omega]
    rw [show a.val+5=(a.val+2)+3 by omega,pow_add,omega_primitive.pow_eq_one,mul_one]
  have hp:lambda^(n.val+2)*lambda^(r.val+2-n.val)=lambda^(r.val+4):=by
    rw [←pow_add]
    congr 1
    omega
  have he:3*lowRamifiedFrequency a r=
      -(omega^j.val*omega^(a.val+5-j.val))*(lambda^(n.val+2)*lambda^(r.val+2-n.val)):=by
    rw [ho,hp,lowRamifiedFrequency]
    conv_lhs => rw [h3]
    rw [show r.val+4=2+(r.val+2) by omega,pow_add,pow_add]
    ring
  rw [lowRamifiedQuotientCoord_eval,signedOmegaUnit_val]
  cases s <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> linear_combination he

lemma lowRamifiedSupport_of_ne_zero (a r:Fin 3) (s:Bool) (j:Fin 3) (n:Fin 5)
    (hA:arithmeticResidueSum (lowRamifiedFrequency a r)
      ((signedOmegaUnit s j:Eis)*lambda^(n.val+2))≠0) :
    lowRamifiedSupport a r (s,j,n) := by
  have hn:n.val≤ r.val+2:=by
    have hb:=ramified_arithmetic_norm_bound _ (lowRamifiedFrequency_ne_zero a r)
      (signedOmegaUnit s j) (n.val+2) (by omega) hA
    rw [lowRamifiedFrequency_absNorm] at hb
    have he:9*3^(r.val+2)=(3:ℕ)^(r.val+4):=by
      rw [show r.val+4=(r.val+2)+2 by omega,pow_add]
      ring
    rw [he] at hb
    have hh: n.val+2≤ r.val+4 := (Nat.pow_le_pow_iff_right (by decide : 1<(3:ℕ))).mp hb
    omega
  let z:=lowRamifiedQuotientCoord a r s j n
  have hu:(signedOmegaUnit s j:Eis)=omega^j.val ∨
      (signedOmegaUnit s j:Eis)=-(omega^j.val):=by
    cases s <;> simp [signedOmegaUnit_val]
  have he:=ramified_arithmetic_explicit_table (lowRamifiedFrequency a r)
    (ActualEisensteinCoordinates.eval z.1 z.2) (signedOmegaUnit s j) (n.val+2) j.val
    (by omega) hu (lowRamifiedQuotientCoord_relation a r s j n hn)
  have hz:ramifiedCongruence (ActualEisensteinCoordinates.eval z.1 z.2) j.val (n.val+2):=by
    by_contra hc
    rw [if_neg hc] at he
    exact hA he
  exact ⟨hn,by simpa only [ramifiedCongruence,ShortDraftLatticeCount.coords_eval] using hz⟩

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance ramifiedRawWeightUnitsFintype : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def ramifiedRawWeight (h:Eis) (u:Eisˣ) (k:ℕ) :ℂ :=
  ((3^(k+2):ℕ):ℂ)^(-(4/3:ℂ))*arithmeticResidueSum h (u.val*lambda^(k+2))

lemma ramifiedRawWeight_norm_le (h:Eis) (u:Eisˣ) (k:ℕ) :
    ‖ramifiedRawWeight h u k‖≤ ramifiedDecayRatio^(k+2) := by
  rw [ramifiedRawWeight,norm_mul,
    arithmeticResidueSum_eq_explicitRamifiedCoefficient h u (k+2) (by omega)]
  exact (mul_le_mul_of_nonneg_left (explicitRamifiedCoefficient_norm_le h u (k+2))
    (norm_nonneg _)).trans_eq (ramifiedWeight_norm_scalar _)

lemma ramifiedRawWeight_norm_mul_primary (h n:Eis) (hn:lambda^2∣n-1) (u:Eisˣ) (k:ℕ) :
    ‖ramifiedRawWeight (h*n) u k‖=‖ramifiedRawWeight h u k‖ := by
  simp only [ramifiedRawWeight,norm_mul,
    arithmeticResidueSum_norm_mul_primary h n hn u (k+2) (by omega)]

lemma ramifiedDecayRatio_cube : ramifiedDecayRatio^3=(1/3:ℝ) := by
  rw [ramifiedDecayRatio,←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
  norm_num

lemma lowRamifiedRawWeight_bound (a r:Fin 3) (s:Bool) (j:Fin 3) (k:Fin 5) :
    ‖ramifiedRawWeight (lowRamifiedFrequency a r) (signedOmegaUnit s j) k.val‖≤
      if lowRamifiedSupport a r (s,j,k) then (1/3:ℝ) else 0 := by
  split_ifs with hs
  · have hh:1≤k.val:=lowRamifiedSupport_exponent a r (s,j,k) hs
    have hb:ramifiedDecayRatio^(k.val+2)≤ ramifiedDecayRatio^3:=
      pow_le_pow_of_le_one ramifiedDecayRatio_pos.le ramifiedDecayRatio_lt_one.le (by omega)
    exact (ramifiedRawWeight_norm_le (lowRamifiedFrequency a r) (signedOmegaUnit s j) k.val).trans
      (hb.trans_eq ramifiedDecayRatio_cube)
  · have hz:arithmeticResidueSum (lowRamifiedFrequency a r)
        ((signedOmegaUnit s j:Eis)*lambda^(k.val+2))=0:=by
      by_contra hne
      exact hs (lowRamifiedSupport_of_ne_zero a r s j k hne)
    simp only [ramifiedRawWeight,hz,mul_zero,norm_zero,le_refl]

theorem lowRamifiedRawWeight_sum (a r:Fin 3) (n:Eis) (hn:lambda^2∣n-1) :
    (∑u:Eisˣ,∑k:Fin 5,‖ramifiedRawWeight (lowRamifiedFrequency a r*n) u k.val‖)≤5/3 := by
  simp_rw [ramifiedRawWeight_norm_mul_primary _ n hn]
  have hu:(∑u:Eisˣ,∑k:Fin 5,‖ramifiedRawWeight (lowRamifiedFrequency a r) u k.val‖)=
      ∑p:Bool×Fin 3,∑k:Fin 5,‖ramifiedRawWeight (lowRamifiedFrequency a r)
        (signedOmegaUnit p.1 p.2) k.val‖ := by
    symm
    exact Fintype.sum_equiv signedOmegaEquiv _ _ (fun _=>rfl)
  rw [hu]
  calc
    _≤∑p:Bool×Fin 3,∑k:Fin 5,
        if lowRamifiedSupport a r (p.1,p.2,k) then (1/3:ℝ) else 0:=by
      apply Finset.sum_le_sum
      intro p hp
      exact Finset.sum_le_sum (fun k hk=>lowRamifiedRawWeight_bound a r p.1 p.2 k)
    _=∑p:Bool×Fin 3×Fin 5,if lowRamifiedSupport a r p then (1/3:ℝ) else 0:=by
      simp only [Fintype.sum_prod_type]
    _=(lowRamifiedSupportSet a r).card*(1/3:ℝ):=by
      rw [←Finset.sum_filter]
      simp only [Finset.sum_const,nsmul_eq_mul,lowRamifiedSupportSet]
    _≤5/3:=by
      have hc:(lowRamifiedSupportSet a r).card≤5:=lowRamifiedSupport_card a r
      exact_mod_cast (show ((lowRamifiedSupportSet a r).card:ℝ)*(1/3:ℝ)≤5/3 by
        have hcr:((lowRamifiedSupportSet a r).card:ℝ)≤5:=by exact_mod_cast hc
        linarith)

end CubicEisenstein

end

end OAI
end

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def cubicQuotientCharacter (I : Ideal O) (hI : Admissible I) : MulChar (O ⧸ I) ℂ where
  toFun := CompletedGauss.cubicRow I hI.2
  map_one' := by simp [CompletedGauss.cubicRow]
  map_mul' x y := by simp only [CompletedGauss.cubicRow, map_mul, Finset.prod_mul_distrib]
  map_nonunit' x hx := by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [CubicEisenstein.cubicRow_eq_idealSymbol I hI.2 hI.1]
    have hcop : ¬ IsCoprime I (Ideal.span {z}) := by
      simpa only [CubicEisenstein.isUnit_quotient_iff_sup, Ideal.isCoprime_iff_sup_eq] using hx
    have hc := idealSymbol_cube_mask I z hI.2
    rw [if_neg hcop] at hc
    exact (eq_zero_of_pow_eq_zero hc)

@[simp] lemma cubicQuotientCharacter_mk (I : Ideal O) (hI : Admissible I) (z : O) :
    cubicQuotientCharacter I hI (Ideal.Quotient.mk I z) = cubicRow I z :=
  CubicEisenstein.cubicRow_eq_idealSymbol I hI.2 hI.1 z

def quotientCharacterTransport {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (χ : MulChar S ℂ) : MulChar R ℂ where
  toFun x := χ (e x)
  map_one' := by simp
  map_mul' x y := by simp only [map_mul]
  map_nonunit' x hx := MulChar.map_nonunit χ (fun h => hx (by simpa using h.map e.symm.toMonoidHom))

def principalCubicCharacter (I : Ideal O) (hI : Admissible I) :
    MulChar (O ⧸ Ideal.span {primaryGenerator I}) ℂ :=
  quotientCharacterTransport (Ideal.quotEquivOfEq (primaryGenerator_spec I hI.2).1)
    (cubicQuotientCharacter I hI)

@[simp] lemma principalCubicCharacter_mk (I : Ideal O) (hI : Admissible I) (z : O) :
    principalCubicCharacter I hI (Ideal.Quotient.mk _ z) = cubicRow I z := by
  change cubicQuotientCharacter I hI ((Ideal.quotEquivOfEq (primaryGenerator_spec I hI.2).1) (Ideal.Quotient.mk _ z)) = _
  rw [Ideal.quotEquivOfEq_mk, cubicQuotientCharacter_mk]

def cubicPairGauss (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) : ℂ := by
  let a := primaryGenerator I
  let b := primaryGenerator J
  let : Finite (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := finite_quotient_product hI.2 hJ.2
  let : Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := Fintype.ofFinite _
  exact (∑ x : O ⧸ (Ideal.span {a}) * (Ideal.span {b}),
    (principalCubicCharacter I hI)⁻¹ (Ideal.Quotient.factor Ideal.mul_le_left x) *
      principalCubicCharacter J hJ (Ideal.Quotient.factor Ideal.mul_le_right x) *
      eisTraceProdChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates a b hI.2 hJ.2 x) /
      ((‖eisEmbedding a‖ : ℂ) * (‖eisEmbedding b‖ : ℂ))

end
end SevenEighths.CubicSieve

end OAI
end


