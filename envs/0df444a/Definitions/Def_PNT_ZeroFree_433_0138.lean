-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0138
-- name    : PNT_ZeroFree_433_0138
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:47:13.907684+00:00
-- url     : https://prove2.me/theorems/fc84e01c-174f-46b4-9623-a518fe6f58a4
-- title:
--   Zero-free region foundations: QuadraticSieve.SelectedExponents [0138]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.SelectedExponents
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/SelectedExponents.lean#L78-L664

import Definitions.Def_PNT_ZeroFree_433_0136
import Definitions.Def_PNT_ZeroFree_433_0137
import Definitions.Def_PNT_ZeroFree_433_0138_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/SelectedExponents.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

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
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic IdealCoprimeSieveOperator

theorem poissonComparisonMajorant_small_power
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2≤α) (hα2 : α≤2)
    (ρ : ℝ) (hρ : 0<ρ) :
    ∃ (η : ℝ) (hη : 0<η), η≤1 ∧ 259*η≤ρ ∧
    ∃ (l A : ℕ), 4≤η*l ∧ 4≤η*A ∧
      ∀ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ),
        0≤CD → 0≤CS → 0≤CT → 0≤CP →
      ∀ (B C1 : ℝ), 1≤B → 1≤C1 → ∀ (W : 𝓢(ℝ,ℂ)),
      ∃ Cfinal : ℝ, 0<Cfinal ∧
        ∀ (C M X q : ℝ) (G : Ideal O), 4≤C → B≤C → C≤C1 →
          1≤M → 1≤X → 1≤q → q≤X → G≠0 → (Ideal.absNorm G:ℝ)=B*q →
          1≤selectedPoissonK C M X η →
        poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp η hη η hη G
          (selectedPoissonK C M X η) (X/q) M (selectedPoissonT C M X η)
          (fun _ : Unit => (1:ℂ)) W ≤
          Cfinal*(M*X)^ρ*poissonShape M X α := by
  let η := min 1 (ρ/600)
  have hη : 0<η := lt_min (by norm_num) (by positivity)
  have hη1 : η≤1 := min_le_left _ _
  have hηρ : 259*η≤ρ := by
    have hh : η≤ρ/600 := min_le_right _ _
    linarith
  obtain ⟨l,hl⟩ := exists_nat_gt (4/η)
  have horder : 4≤η*l := by
    have hh := (div_lt_iff₀ hη).mp hl
    nlinarith
  refine ⟨η,hη,hη1,hηρ,l,l,horder,horder,?_⟩
  intro sD sS sT CD CS CT CP hCD hCS hCT hCP B C1 hB hC1 W
  obtain ⟨Cfinal,hCf,hbound⟩ := poissonComparisonMajorant_selected_power hexp hα hα2
    η hη hη1 l l horder horder sD sS sT CD CS CT CP hCD hCS hCT hCP B C1 hB hC1 W
  refine ⟨Cfinal,hCf,?_⟩
  intro C M X q G hC hBC hCC hM hX hq hqX hG hGN hK
  apply (hbound C M X q G hC hBC hCC hM hX hq hqX hG hGN hK).trans
  have hP : 1≤M*X := by nlinarith
  have hshape : 0≤poissonShape M X α := by unfold poissonShape; positivity
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP hηρ) hCf.le) hshape

end CanonicalQuadraticSieve

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise

namespace CubicEisenstein

lemma hyperbolicHeight_continuous : Continuous hyperbolicHeight := by
  apply Continuous.quotient_lift
  have he (i j : Fin 2) : Continuous (fun g : SL(2,ℂ) => g i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_complexSL_coe)
  apply Continuous.inv₀
  · exact ((he 1 0).norm.pow 2).add ((he 1 1).norm.pow 2)
  · intro g
    exact (rowEnergy_pos _ (complexBottomRow_ne_zero g)).ne'

lemma matrixCross_eq_gram (g : SL(2,ℂ)) : matrixCross g=matrixGram g 0 1 := by
  simp only [matrixCross,matrixGram,Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_apply]

lemma hyperbolicGram_upperPoint (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicGram (upperPoint z v hv) 0 1=z/(v:ℂ) := by
  change matrixGram (upperSection z v hv) 0 1=_
  rw [←matrixCross_eq_gram]
  have hh := matrixCross_upperSection (1:SL(2,ℂ)) z v hv
  simpa [Matrix.one_apply] using hh

def hyperbolicHorizontal (w : HyperbolicSpace) : ℂ :=
  hyperbolicGram w 0 1*(hyperbolicHeight w:ℂ)

lemma hyperbolicHorizontal_continuous : Continuous hyperbolicHorizontal := by
  unfold hyperbolicHorizontal
  exact ((continuous_apply 1).comp ((continuous_apply 0).comp hyperbolicGram_continuous)).mul
    (Complex.continuous_ofReal.comp hyperbolicHeight_continuous)

@[simp] lemma hyperbolicHorizontal_upperPoint (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicHorizontal (upperPoint z v hv)=z := by
  simp only [hyperbolicHorizontal,hyperbolicGram_upperPoint,hyperbolicHeight_upperPoint]
  exact div_mul_cancel₀ z (Complex.ofReal_ne_zero.mpr hv.ne')

def hyperbolicCoordinates (w : HyperbolicSpace) : UpperCoordinates :=
  ⟨(hyperbolicHorizontal w,hyperbolicHeight w),hyperbolicHeight_pos w⟩

lemma hyperbolicCoordinates_continuous : Continuous hyperbolicCoordinates :=
  (hyperbolicHorizontal_continuous.prodMk hyperbolicHeight_continuous).subtype_mk _

lemma upperCoordinates_left_inverse : Function.LeftInverse hyperbolicCoordinates
    (fun p : UpperCoordinates => upperPoint p.1.1 p.1.2 p.2) := by
  intro p
  apply Subtype.ext
  exact Prod.ext (hyperbolicHorizontal_upperPoint _ _ _) (hyperbolicHeight_upperPoint _ _ _)

lemma upperCoordinates_right_inverse : Function.RightInverse hyperbolicCoordinates
    (fun p : UpperCoordinates => upperPoint p.1.1 p.1.2 p.2) := by
  intro w
  obtain ⟨z,v,hv,rfl⟩ := upperPoint_surjective w
  exact congrArg (fun p : UpperCoordinates => upperPoint p.1.1 p.1.2 p.2)
    (upperCoordinates_left_inverse ⟨(z,v),hv⟩)

def upperCoordinatesHomeomorph : UpperCoordinates ≃ₜ HyperbolicSpace where
  toFun p := upperPoint p.1.1 p.1.2 p.2
  invFun := hyperbolicCoordinates
  left_inv := upperCoordinates_left_inverse
  right_inv := upperCoordinates_right_inverse
  continuous_toFun := continuous_upperCoordinates
  continuous_invFun := hyperbolicCoordinates_continuous

lemma fundamentalSet_measure_le_cover (H : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (hH : H≤CubicKubota.levelThree) (B : Set HyperbolicSpace)
    (hB : ∀w,∃M:H,M • w∈B) :
    hyperbolicVolume (hyperbolicFundamentalSet H)≤hyperbolicVolume B := by
  rw [(hyperbolicFundamentalSet_isFundamentalDomain H hH).measure_eq_tsum B]
  apply le_trans (measure_mono ?_) (measure_iUnion_le _)
  intro w hw
  obtain ⟨M,hM⟩ := hB w
  apply Set.mem_iUnion.mpr
  refine ⟨M⁻¹,?_,hw⟩
  exact ⟨M • w,hM,inv_smul_smul M w⟩

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise ENNReal


local notation "O" => ActualEisensteinCubic.O

instance fullSLMeasurableAction : MeasurableConstSMul (SL(2,ℂ)) HyperbolicSpace :=
  ⟨fun g => (continuous_hyperbolic_action g).measurable⟩
instance fullSLVolumeInvariant : SMulInvariantMeasure (SL(2,ℂ)) HyperbolicSpace hyperbolicVolume where
  measure_preimage_smul g s hs := by
    have he := congrArg (fun ν : Measure HyperbolicSpace => ν s) (hyperbolicVolume_invariant g)
    simpa only [Measure.map_apply (continuous_hyperbolic_action g).measurable hs] using he

def hyperbolicCuspBox (a : ℝ) : Set HyperbolicSpace :=
  {w | ‖hyperbolicHorizontal w‖≤1 ∧ a<hyperbolicHeight w}

lemma hyperbolicCuspBox_measurable (a : ℝ) : MeasurableSet (hyperbolicCuspBox a) :=
  (isClosed_le hyperbolicHorizontal_continuous.norm continuous_const).measurableSet.inter
    (isOpen_lt continuous_const hyperbolicHeight_continuous).measurableSet

lemma hyperbolicCuspBox_volume_le (a : ℝ) (ha : 0<a) :
    hyperbolicVolume (hyperbolicCuspBox a)≤4*ENNReal.ofReal (1/(2*a^2)) := by
  rw [hyperbolicVolume,Measure.map_apply euclideanToHyperbolic_measurable
    (hyperbolicCuspBox_measurable a),←euclideanCuspBox_volume a ha]
  apply measure_mono_ae
  filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp hB
  change euclideanToHyperbolic p ∈ hyperbolicCuspBox a at hB
  rw [euclideanToHyperbolic_positive p hp] at hB
  change ‖hyperbolicHorizontal (upperPoint _ _ hp)‖≤1 ∧ a<hyperbolicHeight (upperPoint _ _ hp) at hB
  rw [hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint] at hB
  refine ⟨hB.2,?_⟩
  intro j hj
  fin_cases j
  · change -1≤p 0 ∧ p 0≤1
    have hh := (Complex.abs_re_le_norm ((p 0:ℂ)+Complex.I*(p 1:ℂ))).trans hB.1
    simpa using abs_le.mp hh
  · change -1≤p 1 ∧ p 1≤1
    have hh := (Complex.abs_im_le_norm ((p 0:ℂ)+Complex.I*(p 1:ℂ))).trans hB.1
    simpa using abs_le.mp hh

lemma hyperbolicCuspBox_volume_lt_top (a : ℝ) (ha : 0<a) :
    hyperbolicVolume (hyperbolicCuspBox a)<⊤ :=
  (hyperbolicCuspBox_volume_le a ha).trans_lt (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)

theorem hyperbolicFundamentalSet_volume_lt_top (H : Subgroup (SL(2,O)))
    (hH : H≤CubicKubota.levelThree) [H.FiniteIndex] :
    hyperbolicVolume (hyperbolicFundamentalSet H)<⊤ := by
  obtain ⟨S,hS⟩ := finiteIndex_ford_cover H
  let a : ℝ := Real.sqrt (2/3)/2
  have ha : 0<a := by dsimp [a]; positivity
  let B : Set HyperbolicSpace := ⋃r∈S,integralComplexMatrix r⁻¹ • hyperbolicCuspBox a
  have hcover : ∀w,∃M:H,M • w∈B := by
    intro w
    obtain ⟨M,r,hr,z,v,hv,hM,hz,hfloor⟩ := hS w
    refine ⟨M,?_⟩
    rw [integralSubgroup_smul,hM]
    apply Set.mem_iUnion.mpr
    refine ⟨r,Set.mem_iUnion.mpr ⟨hr,?_⟩⟩
    apply Set.mem_smul_set.mpr
    refine ⟨upperPoint z v hv,?_,rfl⟩
    change ‖hyperbolicHorizontal (upperPoint z v hv)‖≤1 ∧ a<hyperbolicHeight (upperPoint z v hv)
    rw [hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint]
    refine ⟨?_,?_⟩
    · rw [Complex.normSq_eq_norm_sq] at hz
      nlinarith [norm_nonneg z]
    · dsimp [a] at *
      linarith
  apply (fundamentalSet_measure_le_cover H hH B hcover).trans_lt
  apply (measure_biUnion_finset_le S (fun r => integralComplexMatrix r⁻¹ • hyperbolicCuspBox a)).trans_lt
  apply ENNReal.sum_lt_top.mpr
  intro r hr
  rw [measure_smul]
  exact hyperbolicCuspBox_volume_lt_top a ha

lemma integralQuotientVolume_univ (H : Subgroup (SL(2,O))) :
    integralQuotientVolume H Set.univ=hyperbolicVolume (hyperbolicFundamentalSet H) := by
  rw [integralQuotientVolume,Measure.map_apply (measurable_integralOrbitProjection H) MeasurableSet.univ]
  simp

theorem integralQuotientVolume_finite (H : Subgroup (SL(2,O)))
    (hH : H≤CubicKubota.levelThree) [H.FiniteIndex] : IsFiniteMeasure (integralQuotientVolume H) :=
  ⟨by rw [integralQuotientVolume_univ]; exact hyperbolicFundamentalSet_volume_lt_top H hH⟩

instance kernelQuotientVolume_finite : IsFiniteMeasure (integralQuotientVolume globalKubotaKernel) := by
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  exact integralQuotientVolume_finite globalKubotaKernel globalKubotaKernel_le_levelThree

end CubicEisenstein

namespace CanonicalQuadraticSieve

section


open ActualEisensteinCubic CompletedGauss

theorem hasSieveExponent_of_shell_threshold (β : ℝ) (hβ1 : 1≤β) (hβ2 : β≤2)
    (hshell : ∀ρ : ℝ, 0<ρ → ∃C : ℝ, 0<C ∧ ∀M X : ℝ,
      1≤M → 1≤X → X^β≤M → ∀a : idealRange X → ℂ, CoefficientOnShell X X a →
      ballQuadraticEnergy M X a≤C*(M*X)^ρ*M*∑J,‖a J‖^2) :
    HasSieveExponent β := by
  apply hasSieveExponent_of_threshold_band β hβ1 hβ2
  intro ε hε
  have hρ : 0<ε/2 := by positivity
  obtain ⟨C,hC,hbound⟩ := hshell (ε/2) hρ
  let lengthScale := 2+1/((ε/2)*Real.log 2)
  have hL : 0<lengthScale := by
    have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
    dsimp only [lengthScale]
    positivity
  refine ⟨4*C*8^(ε/2)*lengthScale,by positivity,?_⟩
  intro M N hM hN hMN hMsq
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hprod : 0<M*N := by positivity
  apply FiniteSieveOperator.squared_norm_le_of_energy (matrix M N) _ (by positivity)
  intro a
  let a' := fun j : Fin (columnDyadicLength N+1) =>
    coefficientAtScale N ((2:ℝ)^j.val)
      (dyadicColumnCoefficient N (columnDyadicLength N) (columnDyadicLength_cover N) j a)
  have hpart := ballQuadraticEnergy_column_shells_at_scale M N (columnDyadicLength N)
    (columnDyadicLength_cover N) a
  have hj (j : Fin (columnDyadicLength N+1)) :
      ballQuadraticEnergy M ((2:ℝ)^j.val) (a' j) ≤
        (4*C*8^(ε/2)*(M*N)^(ε/2)*M)*∑J,‖a' j J‖^2 := by
    let X := (2:ℝ)^j.val
    have hx := columnDyadicScale_bounds N hN j
    have hβ0 : 0≤β := by linarith
    have hXpow : X^β≤4*M := by
      calc
        _ ≤ (2*N)^β := Real.rpow_le_rpow (by positivity) hx.2 hβ0
        _ = 2^β*N^β := Real.mul_rpow (by norm_num) hN0.le
        _ ≤ 4*N^β := by
          have ht : (2:ℝ)^β≤4 := by
            have ht := Real.rpow_le_rpow_of_exponent_le
              (by norm_num : (1:ℝ)≤2) hβ2
            norm_num at ht
            exact ht
          exact mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hN0.le _)
        _ ≤ 4*M := by linarith
    have hshell' : CoefficientOnShell X X (a' j) :=
      coefficientAtScale_shell N X _ (dyadicColumnCoefficient_shell N _ _ j a)
    have hb := hbound (4*M) X (by linarith) hx.1 hXpow (a' j) hshell'
    have hp : ((4*M)*X)^(ε/2)≤8^(ε/2)*(M*N)^(ε/2) := by
      calc
        _ ≤ (8*(M*N))^(ε/2) := Real.rpow_le_rpow (by positivity) (by nlinarith [hx.2]) hρ.le
        _ = _ := Real.mul_rpow (by norm_num) hprod.le
    apply (ballQuadraticEnergy_mono (by linarith : M≤4*M) (a' j)).trans
    apply hb.trans
    calc
      _ ≤ C*(8^(ε/2)*(M*N)^(ε/2))*(4*M)*∑J,‖a' j J‖^2 := by gcongr
      _ = _ := by ring
  have he : (∑j : Fin (columnDyadicLength N+1), ∑J,‖a' j J‖^2)=∑J,‖a J‖^2 :=
    dyadicColumnCoefficient_at_scale_energy N _ _ a
  have hlen : (columnDyadicLength N+1:ℝ)≤lengthScale*(M*N)^(ε/2) := by
    apply (columnDyadicLength_small_power (ε/2) hρ N hN).trans
    change lengthScale*N^(ε/2)≤lengthScale*(M*N)^(ε/2)
    gcongr
    nlinarith
  change ballQuadraticEnergy M N a≤_
  apply hpart.trans
  calc
    _ ≤ (columnDyadicLength N+1:ℝ)*
        ∑j : Fin (columnDyadicLength N+1),
          (4*C*8^(ε/2)*(M*N)^(ε/2)*M)*∑J,‖a' j J‖^2 := by
      gcongr with j
      exact hj j
    _ = (columnDyadicLength N+1:ℝ)*(4*C*8^(ε/2)*(M*N)^(ε/2)*M)*(∑J,‖a J‖^2) := by
      rw [←Finset.mul_sum,he]
      ring
    _ ≤ (lengthScale*(M*N)^(ε/2))*(4*C*8^(ε/2)*(M*N)^(ε/2)*M)*(∑J,‖a J‖^2) := by gcongr
    _ = _ := by
      have hp : (M*N)^(ε/2)*(M*N)^(ε/2)=(M*N)^ε := by
        rw [←Real.rpow_add hprod]
        congr 1
        ring
      calc
        _ = (4*C*8^(ε/2)*lengthScale)*((M*N)^(ε/2)*(M*N)^(ε/2))*M*(∑J,‖a J‖^2) := by ring
        _ = _ := by rw [hp]

end

open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy


theorem HasSieveExponent.annular_selected_bound {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (l A : ℕ) (hl : 4≤η*l) (hA : 4≤η*A) (C1 : ℝ) (hC1 : 1≤C1) :
    ∃ C : ℝ, 0<C ∧ ∀ (c M N : ℝ),
      fixedCutoffBase≤c → c≤C1 → 1≤M → 4≤N → N^(2-1/α)≤M →
      1≤selectedPoissonK c M N η →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N N a →
      annularHighEnergy M N (selectedPoissonK c M N η) a ≤
        C*(M*N)^(260*η)*M*∑J,‖a J‖^2 := by
  have hα : 1/2≤α := by linarith
  obtain ⟨sD,sS,sT,CD,CS,CT,CP,CH,hCD,hCS,hCT,hCP,hCH,henergy⟩ :=
    hexp.annular_energy_from_scalar_cost hα η hη l A
  obtain ⟨CF,hCF,hscalar⟩ := poissonComparisonMajorant_selected_power hexp hα hα2
    η hη hη1 l A hl hA sD sS sT CD CS CT CP hCD.le hCS.le hCT.le hCP.le
    fixedBadNorm C1 fixedBadNorm_one_le hC1 QuadraticInitialBound.annularSieveCutoff
  have hdiv : 0<divisorConstant η hη := divisorConstant_pos η hη
  let SD := supportConstant η hη*divisorConstant η hη
  have hSD : 0<SD := mul_pos (supportConstant_pos η hη) (divisorConstant_pos η hη)
  let F := 16*(3*CF*divisorConstant η hη + 4*CH*2^η*SD)
  refine ⟨F,by dsimp [F]; positivity,?_⟩
  intro c M N hc hc1 hM hN hthreshold hK a ha
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hN1 : 1≤N := by linarith
  have hP : 1≤M*N := by nlinarith
  have hP0 : 0<M*N := by positivity
  have hc4 : 4≤c := fixedCutoffBase_bounds.1.trans hc
  have hcB : fixedBadNorm≤c := fixedCutoffBase_bounds.2.trans hc
  have hT : 4≤selectedPoissonT c M N η := by
    have hp := Real.one_le_rpow hP hη.le
    unfold selectedPoissonT
    nlinarith
  have hcut : N^2/M≤selectedPoissonK c M N η := by
    unfold selectedPoissonK
    rw [mul_div_assoc]
    have hp : 0≤N^2/M := by positivity
    nlinarith
  have hH := largeGcdThreshold_bounds α N hα1 hα2 hN
  have hcost : ∀D∈gcdPool (fun J : idealRange N => J.val),
      (Ideal.absNorm D:ℝ)≤largeGcdThreshold α N →
      poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp η hη η hη
        (commonMaskIdeal D) (selectedPoissonK c M N η) (N/(Ideal.absNorm D:ℝ)) M
        (selectedPoissonT c M N η) (fun _ : Unit => (1:ℂ))
        QuadraticInitialBound.annularSieveCutoff ≤ 3*CF*(M*N)^(259*η)*M := by
    intro D hD hd
    have hadm := gcdPool_admissible (fun J : idealRange N => J.val)
      (fun J => (mem_idealRange.mp J.property).1) D hD
    have hd1 : 1≤(Ideal.absNorm D:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hadm.1 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hgn : (Ideal.absNorm (commonMaskIdeal D):ℝ)=fixedBadNorm*(Ideal.absNorm D:ℝ) := by
      rw [commonMaskIdeal_norm D hadm, Nat.cast_mul]
      rfl
    have hb := hscalar c M N (Ideal.absNorm D:ℝ) (commonMaskIdeal D) hc4 hcB hc1 hM hN1 hd1
      (by linarith [hH.2]) (commonMaskIdeal_squarefree D).ne_zero hgn hK
    apply hb.trans
    have hs : poissonShape M N α≤3*M := improved_threshold_shape α N M hα1 hN1 hthreshold
    calc
      _ ≤ CF*(M*N)^(259*η)*(3*M) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  have he := henergy η hη M N (selectedPoissonK c M N η) (selectedPoissonT c M N η)
    (largeGcdThreshold α N) (3*CF*(M*N)^(259*η)*M) hM hN1 hK hT
    (by linarith [hH.1]) hH.2 (by positivity) hcost a ha
  have hhigh := chosen_large_gcd_full α η CH M N (selectedPoissonK c M N η)
    hα1 hα2 hη.le hCH.le hM0 hN (by linarith) hcut
  have hn : N^η≤(M*N)^η := Real.rpow_le_rpow hN0.le (by nlinarith) hη.le
  have hcombine1 : (M*N)^(259*η)*(M*N)^η=(M*N)^(260*η) := by
    rw [←Real.rpow_add hP0]
    congr 1
    ring
  have hcombine2 : (M*N)^η*((M*N)^η)^2=(M*N)^(3*η) := by
    rw [pow_two,←mul_assoc,←Real.rpow_add hP0,←Real.rpow_add hP0]
    congr 1
    ring
  have hpow : (M*N)^(3*η)≤(M*N)^(260*η) :=
    Real.rpow_le_rpow_of_exponent_le hP (by linarith)
  have hfirst : (3*CF*(M*N)^(259*η)*M/6)*(divisorConstant η hη*N^η) ≤
      (3*CF*divisorConstant η hη)*(M*N)^(260*η)*M := by
    calc
      _ ≤ (3*CF*(M*N)^(259*η)*M)*(divisorConstant η hη*(M*N)^η) := by
        gcongr
        nlinarith [show 0≤3*CF*(M*N)^(259*η)*M by positivity]
      _ = _ := by rw [←hcombine1]; ring
  have hsecond : (CH*((2*M)*(N/largeGcdThreshold α N))^η*
      (2*M+Real.sqrt ((2*M)/selectedPoissonK c M N η)*(N/largeGcdThreshold α N)^α))*
      SD*(N^η)^2 ≤ (4*CH*2^η*SD)*(M*N)^(260*η)*M := by
    calc
      _ ≤ ((4*CH*2^η)*(M*N)^η*M)*SD*((M*N)^η)^2 := by gcongr
      _ = (4*CH*2^η*SD)*(M*N)^(3*η)*M := by rw [←hcombine2]; ring
      _ ≤ _ := by gcongr
  apply he.trans
  change 16*(_+_*SD*(N^η)^2)*_≤_
  calc
    _ ≤ 16*((3*CF*divisorConstant η hη)*(M*N)^(260*η)*M+
      (4*CH*2^η*SD)*(M*N)^(260*η)*M)*∑J,‖a J‖^2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (by norm_num))
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := by dsimp [F]; ring

end CanonicalQuadraticSieve

end

end OAI

end


