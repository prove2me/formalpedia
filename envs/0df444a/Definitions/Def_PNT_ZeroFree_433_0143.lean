-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0143
-- name    : PNT_ZeroFree_433_0143
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:01:16.296668+00:00
-- url     : https://prove2.me/theorems/34346fb7-6f00-441e-b54e-128476e7d931
-- title:
--   Zero-free region foundations: MeanSquare.TransformedColumns [0143]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.MeanSquare.TransformedColumns
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/TransformedColumns.lean#L85-L684

import Definitions.Def_PNT_ZeroFree_433_0139
import Definitions.Def_PNT_ZeroFree_433_0142
import Definitions.Def_PNT_ZeroFree_433_0143_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/TransformedColumns.lean
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

open scoped BigOperators Classical


namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal

instance fullSLContinuousAction : ContinuousConstSMul (SL(2,ℂ)) HyperbolicSpace :=
  ⟨continuous_hyperbolic_action⟩

instance hyperbolicVolume_fullSupport : Measure.IsOpenPosMeasure hyperbolicVolume where
  open_pos U hU hne := by
    obtain ⟨u,hu⟩ := hne
    have hcover : (Set.univ : Set HyperbolicSpace) ⊆ ⋃g:SL(2,ℂ),g • U := by
      intro w hw
      obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (SL(2,ℂ)) u w
      exact Set.mem_iUnion.mpr ⟨g,u,hu,hg⟩
    obtain ⟨seq,hseq⟩ := isLindelof_univ.indexed_countable_subcover
      (fun g : SL(2,ℂ) => g • U) (fun g => isOpenMap_smul g U hU) hcover
    intro hzero
    have hz : hyperbolicVolume (⋃n:ℕ,seq n • U)=0 := by
      apply measure_iUnion_null
      intro n
      rw [measure_smul,hzero]
    have htotal : hyperbolicVolume Set.univ=0 := measure_mono_null hseq hz
    exact hyperbolicVolume_ne_zero (Measure.measure_univ_eq_zero.mp htotal)

instance kernelQuotientVolume_fullSupport :
    Measure.IsOpenPosMeasure (integralQuotientVolume globalKubotaKernel) where
  open_pos U hU hne := by
    let quotientProjection := integralOrbitProjection globalKubotaKernel
    have hp : Measurable quotientProjection := measurable_integralOrbitProjection _
    have hpre : IsOpen (quotientProjection ⁻¹' U) := hU.preimage (continuous_integralOrbitProjection _)
    have hpren : (quotientProjection ⁻¹' U).Nonempty := by
      obtain ⟨q,hq⟩ := hne
      obtain ⟨w,rfl⟩ := Quotient.mk_surjective q
      exact ⟨w,hq⟩
    intro hzero
    have hd : hyperbolicVolume ((quotientProjection ⁻¹' U)∩hyperbolicFundamentalSet globalKubotaKernel)=0 := by
      simpa only [integralQuotientVolume,quotientProjection,Measure.map_apply (measurable_integralOrbitProjection _) hU.measurableSet,
        Measure.restrict_apply ((measurable_integralOrbitProjection _) hU.measurableSet)] using hzero
    have hinv : ∀M:globalKubotaKernel,M • (quotientProjection ⁻¹' U)=quotientProjection ⁻¹' U := by
      intro M
      ext w
      constructor
      · rintro ⟨u,hu,rfl⟩
        change quotientProjection (M • u)∈U
        change quotientProjection u∈U at hu
        rwa [show quotientProjection (M • u)=quotientProjection u from integralOrbitProjection_eq _ M u]
      · intro hw
        refine ⟨M⁻¹ • w,?_,smul_inv_smul M w⟩
        change quotientProjection (M⁻¹ • w)∈U
        rwa [show quotientProjection (M⁻¹ • w)=quotientProjection w from integralOrbitProjection_eq _ M⁻¹ w]
    have hz := globalKubotaKernel_isFundamentalDomain.measure_zero_of_invariant (quotientProjection ⁻¹' U) hinv hd
    exact hpre.measure_ne_zero _ hpren hz

lemma kernel_continuous_eq_of_ae_eq (f g : IntegralOrbitQuotient globalKubotaKernel → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (he : f =ᵐ[integralQuotientVolume globalKubotaKernel] g) : f=g :=
  (MeasureTheory.Measure.eq_of_ae_eq he hf hg)

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise ENNReal

open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma integral_upper_triangular_height (M : SL(2,O)) (hc : M 1 0=0)
    (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicHeight (integralComplexMatrix M • upperPoint z v hv)=v := by
  have hdet : M 0 0*M 1 1=1 := by
    have h := M.property
    simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using h
  let u : Oˣ := ⟨M 1 1,M 0 0,by rw [mul_comm,hdet],hdet⟩
  have hn : ‖eisEmbedding (M 1 1)‖=1 := GaussGeneratorTransport.norm_eisEmbedding_unit u
  rw [hyperbolicHeight_action_upperPoint]
  simp only [integralComplexMatrix_apply,hc,map_zero,zero_mul,zero_add,norm_zero,
    hn,one_pow,]
  norm_num

lemma smoothCuspSeedDefect_high_zero (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ)
    (M : SL(2,O)) (z : ℂ) (v : ℝ) (hv : 0<v) (hvlarge : max b a⁻¹<v) :
    smoothCuspSeedDefect a b s (integralComplexMatrix M • upperPoint z v hv)=0 := by
  unfold smoothCuspSeedDefect cuspCutoffCorrection
  have hz : (fun r : CuspCosets => cuspCutoffTerm 1 (cuspSeedDefectProfile a b s) r
      (integralComplexMatrix M • upperPoint z v hv))=(fun _ => (0:ℂ)) := by
    funext r
    have hout : cosetHeight r (integralComplexMatrix M • upperPoint z v hv)<a ∨
        b<cosetHeight r (integralComplexMatrix M • upperPoint z v hv) := by
      induction r using Quotient.inductionOn with
      | _ N =>
        change cosetHeight (cosetOf N) _<a ∨ b<cosetHeight (cosetOf N) _
        rw [cosetHeight_cosetOf]
        change hyperbolicHeight (integralComplexMatrix (N:SL(2,O)) •
          (integralComplexMatrix M • upperPoint z v hv))<a ∨
          b<hyperbolicHeight (integralComplexMatrix (N:SL(2,O)) •
            (integralComplexMatrix M • upperPoint z v hv))
        simp only [←mul_smul,←map_mul]
        by_cases hc : ((N:SL(2,O))*M) 1 0=0
        · right
          rw [integral_upper_triangular_height _ hc]
          exact (le_max_left _ _).trans_lt hvlarge
        · left
          have hh := integral_hyperbolicHeight_mul_le_one ((N:SL(2,O))*M) hc (upperPoint z v hv)
          rw [hyperbolicHeight_upperPoint] at hh
          have hav : 1<a*v := by
            have hlt : a⁻¹<v := (le_max_right _ _).trans_lt hvlarge
            have hm := mul_lt_mul_of_pos_left hlt ha
            simpa only [mul_inv_cancel₀ ha.ne'] using hm
          nlinarith
    simp [cuspCutoffTerm,cuspSeedDefectProfile_zero a b s _ hab hout]
  rw [hz,tsum_zero]

theorem kernelQuotientDefect_hasCompactSupport (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    HasCompactSupport (kernelQuotientDefect a b s) := by
  obtain ⟨S,hS⟩ := globalKubotaKernel_compact_core_cusp_cover
  obtain ⟨hcompact,hcover⟩ := hS (max b a⁻¹)
  apply HasCompactSupport.of_support_subset_isCompact hcompact
  intro q hq
  have hmem : q∈compactFordCore globalKubotaKernel S (max b a⁻¹) ∪
      ⋃r∈S,fordCuspTail globalKubotaKernel r (max b a⁻¹) := by rw [←hcover]; trivial
  rcases hmem with hcore | htail
  · exact hcore
  · exfalso
    obtain ⟨r,hr⟩ := Set.mem_iUnion.mp htail
    obtain ⟨hrS,htail⟩ := Set.mem_iUnion.mp hr
    obtain ⟨p,hp,rfl⟩ := htail
    exact hq (smoothCuspSeedDefect_high_zero a b ha hab s r⁻¹ p.1.1 p.1.2 p.2 hp.2.2)

def hyperbolicSpatialCoordinates (w : HyperbolicSpace) : SpatialCoordinates :=
  ![(hyperbolicHorizontal w).re,(hyperbolicHorizontal w).im,hyperbolicHeight w]

lemma hyperbolicSpatialCoordinates_continuous : Continuous hyperbolicSpatialCoordinates := by
  apply continuous_pi
  intro j
  fin_cases j
  · exact Complex.continuous_re.comp hyperbolicHorizontal_continuous
  · exact Complex.continuous_im.comp hyperbolicHorizontal_continuous
  · exact hyperbolicHeight_continuous

lemma hyperbolicSpatialCoordinates_positive (w : HyperbolicSpace) :
    0<hyperbolicSpatialCoordinates w 2 := hyperbolicHeight_pos w

lemma hyperbolicSpatialCoordinates_reconstruct (w : HyperbolicSpace) :
    upperPoint ((hyperbolicSpatialCoordinates w 0:ℂ)+(hyperbolicSpatialCoordinates w 1:ℂ)*Complex.I)
      (hyperbolicSpatialCoordinates w 2) (hyperbolicSpatialCoordinates_positive w)=w := by
  change upperPoint (((hyperbolicHorizontal w).re:ℂ)+((hyperbolicHorizontal w).im:ℂ)*Complex.I)
    (hyperbolicHeight w) (hyperbolicHeight_pos w)=w
  rw [Complex.re_add_im]
  exact upperCoordinates_right_inverse w

lemma smoothCuspSeedDefect_continuous (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b) :
    Continuous (smoothCuspSeedDefect a b s) := by
  have heq : smoothCuspSeedDefect a b s=
      fun w => heightPoincareField (cuspSeedDefectProfile a b s) (hyperbolicSpatialCoordinates w) := by
    funext w
    nth_rw 1 [←hyperbolicSpatialCoordinates_reconstruct w]
    exact smoothCuspSeedDefect_coordinate a b s ha hab _ (hyperbolicSpatialCoordinates_positive w)
  rw [heq,continuous_iff_continuousAt]
  intro w
  exact (smoothCuspSeedDefect_contDiffAt a b s ha hab _
    (hyperbolicSpatialCoordinates_positive w)).continuousAt.comp
      hyperbolicSpatialCoordinates_continuous.continuousAt

lemma kernelQuotientDefect_continuous (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b) :
    Continuous (kernelQuotientDefect a b s) :=
  (smoothCuspSeedDefect_continuous a b s ha hab).quotient_lift _

lemma actual_smoothCuspSeedDefect_contDiffAt (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ (↑(⊤ : ℕ∞)) (smoothCuspSeedDefectField a b s) p := by
  have heq : smoothCuspSeedDefectField a b s =ᶠ[𝓝 p]
      heightPoincareField (cuspSeedDefectProfile a b s) := by
    filter_upwards [(continuous_apply 2).continuousAt.eventually_const_lt hp] with q hq
    exact smoothCuspSeedDefectField_eq a b s ha hab q hq
  exact (smoothCuspSeedDefect_contDiffAt a b s ha hab p hp).congr_of_eventuallyEq heq

end CubicEisenstein

namespace SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (firstLogDensity)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

theorem globalChildBudget_height (pool : Finset ι) (source : Finset (GlobalSecondData ι))
    (Ψ : O →* ℂ) (m : O) (windows : Fin 7 → ℝ → ℂ)
    (C ε t K ell B F M H : ℝ) (A J : ℕ) (side : Bool) :
    globalChildBudget p hp hcop hg pool source Ψ m windows C ε t t K ell B F M H A J side =
      ((1+‖t‖)^(J+2)*(1+‖t‖)^(J+2))*
        globalChildBudget p hp hcop hg pool source Ψ m windows C ε 0 0 K ell B F M H A J side := by
  simp only [globalChildBudget,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro ray hray
  apply Finset.sum_congr rfl
  intro q hq
  simp only [globalDescentWeight,norm_zero,add_zero,one_pow,mul_one]
  ring

theorem globalChildBudget_density (pool : Finset ι) (source : Finset (GlobalSecondData ι))
    (Ψ : O →* ℂ) (m : O) (windows : Fin 7 → ℝ → ℂ)
    (C ε t K ell B F M H : ℝ) (A J : ℕ) (side : Bool) :
    firstLogDensity (2*(J+2)) t*
      globalChildBudget p hp hcop hg pool source Ψ m windows C ε t t K ell B F M H A J side =
    firstLogDensity 0 t*
      globalChildBudget p hp hcop hg pool source Ψ m windows C ε 0 0 K ell B F M H A J side := by
  rw [globalChildBudget_height,← mul_assoc,FirstPassCubeLabels.firstLogDensity_pair_moment]

theorem globalChildBudget_integral (pool : Finset ι) (source : Finset (GlobalSecondData ι))
    (Ψ : O →* ℂ) (m : O) (windows : Fin 7 → ℝ → ℂ)
    (C ε K ell B F M H : ℝ) (A J : ℕ) (side : Bool) :
    (∫ t : ℝ,firstLogDensity (2*(J+2)) t*
      globalChildBudget p hp hcop hg pool source Ψ m windows C ε t t K ell B F M H A J side) =
    (∫ t : ℝ,firstLogDensity 0 t)*
      globalChildBudget p hp hcop hg pool source Ψ m windows C ε 0 0 K ell B F M H A J side := by
  simp_rw [globalChildBudget_density]
  exact integral_mul_const _ _

def globalFirstFiniteEnergy (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℝ) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (χ : RayFourExpansion.RayCharacter)
    (r : FirstCoreIndex) (T : GlobalFirstData ι → Finset O) (t : ℝ) : ℝ :=
  ∑ b∈s,w b*∑ z∈T b,‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2

theorem globalFirstFiniteEnergy_integrable (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℝ) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (χ : RayFourExpansion.RayCharacter)
    (r : FirstCoreIndex) (T : GlobalFirstData ι → Finset O) (J : ℕ) :
    Integrable (fun t => firstLogDensity J t*globalFirstFiniteEnergy p hg pool s w Ψ m g V ell side χ r T t) := by
  simp only [globalFirstFiniteEnergy,Finset.mul_sum]
  apply integrable_finsetSum
  intro b hb
  apply integrable_finsetSum
  intro z hz
  have hi := firstCoreInputRow_integrable p hg (pool\(b.cube.support∪b.common)) b.firstCommon b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
    side χ Ψ m (FirstPassCubeLabels.normalizedColumn p
      (fun A => g (FirstPassCubeLabels.columnLog p (globalFirstBlockColumnScale p ell side b) A)))
    V (FirstPassCubeLabels.columnLog p (globalFirstBlockColumnScale p ell side b))
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) r z
    (FirstPassCubeLabels.firstLogDensity_integrable J)
  simpa only [globalFirstCoreRow,mul_left_comm] using hi.const_mul (w b)

end SecondPassArithmetic

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic

theorem finite_inverse_norm_sum (S : Finset (Ideal O)) (H : ℝ)
    (hS : ∀ I∈S,I≠0) (hH : ∀I∈S,(Ideal.absNorm I:ℝ)≤H) :
    (∑I∈S,1/(Ideal.absNorm I:ℝ))≤256*(columnDyadicLength H+1:ℝ) := by
  have hpos (I : Ideal O) (hI : I∈S) : 1≤(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hS I hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hbin (j : Fin (columnDyadicLength H+1)) :
      (∑I∈divisorDyadicBin S H j,1/(Ideal.absNorm I:ℝ))≤256 := by
    have hp : 0<(2:ℝ)^j.val := by positivity
    have hone : 1≤(2:ℝ)^j.val := one_le_pow₀ (by norm_num)
    have hcount : ((divisorDyadicBin S H j).card:ℝ)≤128*(2:ℝ)^j.val := by
      apply DescentFiberCost.finite_ideal_count_real _ _ hone
      · intro I hI
        exact hS I (Finset.mem_filter.mp hI).1
      · intro I hI
        obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
        have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).2
        simpa only [hj] using hb
    have hterm (I : Ideal O) (hI : I∈divisorDyadicBin S H j) :
        1/(Ideal.absNorm I:ℝ)≤2/(2:ℝ)^j.val := by
      obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
      have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).1
      rw [hj] at hb
      apply (div_le_div_iff₀ (by linarith [hpos I hIS]) hp).mpr
      linarith
    calc
      _ ≤ ∑_I∈divisorDyadicBin S H j,2/(2:ℝ)^j.val := Finset.sum_le_sum hterm
      _ = ((divisorDyadicBin S H j).card:ℝ)*(2/(2:ℝ)^j.val) := by simp
      _ ≤ (128*(2:ℝ)^j.val)*(2/(2:ℝ)^j.val) := by gcongr
      _ = _ := by field_simp; ring
  rw [sum_divisorDyadicBins S H]
  calc
    _ ≤ ∑j : Fin (columnDyadicLength H+1),(256:ℝ) := Finset.sum_le_sum (fun j _ => hbin j)
    _ = _ := by simp; ring


open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel


open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel


theorem bounded_supported_quadratic_norm :
    ∀ε : ℝ, 0<ε → ∃C : ℝ, 0<C ∧ ∀K X lengthScale : ℝ,
      1≤K → 1≤X → 0≤lengthScale → ∀S : Finset (Ideal O),
      (∀I∈S,Supported I ∧ (Ideal.absNorm I:ℝ)≤X) →
      ∀a : Ideal O → ℂ, (∀I∈S,‖a I‖≤lengthScale) →
      (∑k : idealRange K,‖∑I∈S,quadraticRow k.val (primaryGenerator I)*a I‖^2)≤
        C*(K*X)^ε*(K+X)*X*lengthScale^2 := by
  intro ε hε
  let deltaLoss := ε/3
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  obtain ⟨C,hC,hsharp⟩ := sieveNorm_sharp deltaLoss hδ
  let D : ℝ := 256*(2+1/(deltaLoss*Real.log 2))
  have hD : 0<D := by have hlog : 0<Real.log 2 := Real.log_pos (by norm_num); dsimp [D]; positivity
  refine ⟨128*C*D^2,by positivity,?_⟩
  intro K X lengthScale hK hX hL S hS a ha
  let T := S.image squarePart
  let R : ℝ := ∑A∈T,1/(Ideal.absNorm A:ℝ)
  have hK0 : 0<K := by linarith
  have hX0 : 0<X := by linarith
  have hP0 : 0<K*X := by positivity
  have hprop (A : Ideal O) (hA : A∈T) := columnSquareParts_bounds S X hS A hA
  have hT0 : ∀A∈T,A≠0 := fun A hA => (hprop A hA).1
  have hR : 0≤R := by dsimp [R]; positivity
  have hRL : R≤D*X^deltaLoss := by
    apply (finite_inverse_norm_sum T X hT0 (fun A hA => (hprop A hA).2.2.1)).trans
    have hh := columnDyadicLength_small_power deltaLoss hδ X hX
    dsimp [D]
    nlinarith
  let F : ℝ := 128*C*(K*X)^deltaLoss*(K+X)*X*lengthScale^2
  have hF : 0≤F := by dsimp [F]; positivity
  have hf (A : Ideal O) (hA : A∈T) :
      (Ideal.absNorm A:ℝ)*(∑k : idealRange K,‖∑I∈columnSquareFiber S A,
        quadraticRow k.val (primaryGenerator I)*a I‖^2)≤F/(Ideal.absNorm A:ℝ) := by
    have hp := hprop A hA
    have hn : 0<(Ideal.absNorm A:ℝ) := by linarith [hp.2.1]
    let Y := X/(Ideal.absNorm A:ℝ)^2
    have hY : 1≤Y := hp.2.2.2
    have hYX : Y≤X := div_le_self hX0.le (one_le_pow₀ hp.2.1)
    have hb : sieveNorm Y K≤C*(K*X)^deltaLoss*(K+X) := by
      apply (hsharp Y K hY hK).trans
      have hprod : Y*K≤K*X := by nlinarith
      have hpw := Real.rpow_le_rpow (by positivity : 0≤Y*K) hprod hδ.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpw hC.le) (by linarith)
        (by positivity) (by positivity)
    have hea : (∑I∈columnSquareFiber S A,‖a I‖^2)≤128*Y*lengthScale^2 := by
      calc
        _ ≤ ∑_I∈columnSquareFiber S A,lengthScale^2 := by
          apply Finset.sum_le_sum
          intro I hI
          exact pow_le_pow_left₀ (norm_nonneg _) (ha I (Finset.mem_filter.mp hI).1) 2
        _ = ((columnSquareFiber S A).card:ℝ)*lengthScale^2 := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (columnSquareFiber_card S X hS A hY) (sq_nonneg _)
    have he := columnSquareFiber_energy S X K hS A a
    calc
      _ ≤ (Ideal.absNorm A:ℝ)*(sieveNorm Y K*(∑I∈columnSquareFiber S A,‖a I‖^2)) :=
        mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
      _ ≤ (Ideal.absNorm A:ℝ)*((C*(K*X)^deltaLoss*(K+X))*(128*Y*lengthScale^2)) := by
        gcongr
      _ = F/(Ideal.absNorm A:ℝ) := by dsimp [F,Y]; field_simp [hn.ne']
  have hsplit (k : idealRange K) :
      (∑I∈S,quadraticRow k.val (primaryGenerator I)*a I)=
      ∑A∈T,∑I∈columnSquareFiber S A,quadraticRow k.val (primaryGenerator I)*a I := by
    exact (Finset.sum_fiberwise_of_maps_to (fun I hI => Finset.mem_image_of_mem squarePart hI) _).symm
  have hcauchy (k : idealRange K) :
      ‖∑I∈S,quadraticRow k.val (primaryGenerator I)*a I‖^2≤
      R*∑A∈T,(Ideal.absNorm A:ℝ)*‖∑I∈columnSquareFiber S A,quadraticRow k.val (primaryGenerator I)*a I‖^2 := by
    rw [hsplit]
    exact ideal_reciprocal_cauchy T hT0 _
  have htotal : (∑k : idealRange K,‖∑I∈S,quadraticRow k.val (primaryGenerator I)*a I‖^2)≤F*R^2 := by
    calc
      _ ≤ ∑k : idealRange K,R*∑A∈T,(Ideal.absNorm A:ℝ)*‖∑I∈columnSquareFiber S A,
          quadraticRow k.val (primaryGenerator I)*a I‖^2 := Finset.sum_le_sum (fun k _ => hcauchy k)
      _ = R*∑A∈T,(Ideal.absNorm A:ℝ)*∑k : idealRange K,‖∑I∈columnSquareFiber S A,
          quadraticRow k.val (primaryGenerator I)*a I‖^2 := by
        rw [←Finset.mul_sum,Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro A hA
        rw [←Finset.mul_sum]
      _ ≤ R*∑A∈T,F/(Ideal.absNorm A:ℝ) := by gcongr with A hA; exact hf A hA
      _ = F*R^2 := by
        simp_rw [div_eq_mul_inv]
        rw [←Finset.mul_sum]
        dsimp [R]
        simp only [one_div]
        ring
  have hpower : (K*X)^deltaLoss*(X^deltaLoss)^2≤(K*X)^ε := by
    have hXP : X≤K*X := by nlinarith
    calc
      _ ≤ (K*X)^deltaLoss*((K*X)^deltaLoss)^2 := by gcongr
      _ = (K*X)^ε := by
        rw [pow_two,←mul_assoc,←Real.rpow_add hP0,←Real.rpow_add hP0]
        congr 1
        dsimp [deltaLoss]
        ring
  apply htotal.trans
  calc
    _ ≤ F*(D*X^deltaLoss)^2 := by gcongr
    _ = (128*C*D^2)*((K*X)^deltaLoss*(X^deltaLoss)^2)*(K+X)*X*lengthScale^2 := by dsimp [F]; ring
    _ ≤ _ := by gcongr

end CanonicalQuadraticSieve

end

end OAI

end


