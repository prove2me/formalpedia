-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0137
-- name    : PNT_ZeroFree_433_0137
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:35:29.411049+00:00
-- url     : https://prove2.me/theorems/819aa238-64f9-4493-a8f8-ef58d0897523
-- title:
--   Zero-free region foundations: QuadraticSieve.PoissonConstants [0137]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.PoissonConstants
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/PoissonConstants.lean#L80-L684

import Definitions.Def_PNT_ZeroFree_433_0133
import Definitions.Def_PNT_ZeroFree_433_0137_parallel1
import Definitions.Def_PNT_ZeroFree_433_0137_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/PoissonConstants.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

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
open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy EisensteinSchwartzPoisson


theorem poissonComparisonMajorant_selected_power
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2≤α) (hα2 : α≤2)
    (η : ℝ) (hη : 0<η) (hη1 : η≤1) (l A : ℕ)
    (hl : 4≤η*l) (hA : 4≤η*A)
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    (hCD : 0≤CD) (hCS : 0≤CS) (hCT : 0≤CT) (hCP : 0≤CP)
    (B C1 : ℝ) (hB : 1≤B) (hC1 : 1≤C1) (W : 𝓢(ℝ,ℂ)) :
    ∃ Cfinal : ℝ, 0<Cfinal ∧
      ∀ (C M X q : ℝ) (G : Ideal O), 4≤C → B≤C → C≤C1 →
        1≤M → 1≤X → 1≤q → q≤X → G≠0 → (Ideal.absNorm G:ℝ)=B*q →
        1≤selectedPoissonK C M X η →
      poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp η hη η hη G
        (selectedPoissonK C M X η) (X/q) M (selectedPoissonT C M X η)
        (fun _ : Unit => (1:ℂ)) W ≤
        Cfinal*(M*X)^(259*η)*poissonShape M X α := by
  let D := 2*C1+B
  have hD : 1≤D := by dsimp [D]; linarith only [hC1,hB]
  obtain ⟨H,hH,hconst⟩ := list_exists_positive_bound
    (poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W)
  let Cshape := poissonShapeConstant B C1
  have hC10 : 0≤C1 := le_trans zero_le_one hC1
  have hCs : 1≤Cshape := by
    dsimp [Cshape,poissonShapeConstant]
    nlinarith only [hC10,pow_nonneg hC10 3,sq_nonneg B]
  have hCsC : C1≤Cshape := by
    dsimp [Cshape,poissonShapeConstant]
    nlinarith only [pow_nonneg hC10 3,sq_nonneg B]
  have hCsB : B^2≤Cshape := by
    dsimp [Cshape,poissonShapeConstant]
    nlinarith only [hC10,pow_nonneg hC10 3]
  have hCsMid : 1+4*C1^3≤Cshape := by
    dsimp [Cshape,poissonShapeConstant]
    nlinarith only [hC10,sq_nonneg B]
  refine ⟨262144*H^64*Cshape,by positivity,?_⟩
  intro C M X q G hC hBC hCC hM hX hq hqX hG hGN hK
  have hM0 : 0<M := lt_of_lt_of_le zero_lt_one hM
  have hX0 : 0<X := lt_of_lt_of_le zero_lt_one hX
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hP : 1≤M*X := by nlinarith only [hM,hX]
  have hP0 : 0<M*X := by positivity
  have hMP : M≤M*X := by nlinarith only [hM,hX]
  have hXP : X≤M*X := by nlinarith only [hM,hX]
  have hN : 1≤X/q := (le_div_iff₀ hq0).mpr (by simpa using hqX)
  have hNX : X/q≤X := div_le_self hX0.le hq
  have hNP : X/q≤M*X := hNX.trans hXP
  obtain ⟨hT,hTP,hKP⟩ := selectedPoisson_upper C C1 M X η hC hCC hM hX hη.le hη1
  have hKg : 0≤selectedPoissonK C M X η := le_trans zero_le_one hK
  have hg : (Ideal.absNorm G:ℝ)≤B*(M*X) := by rw [hGN]; gcongr; exact hqX.trans hXP
  have hb := poissonUnitBudget_power_envelope sD sS sT CD CS CT CP hCD hCS hCT hCP
    hexp η hη G hG (selectedPoissonK C M X η) (X/q) (M*X) D H W
    hK hN hP hD hH hconst
    (poisson_seven_scale_bounds (Ideal.absNorm G:ℝ) (selectedPoissonK C M X η) (X/q)
      (M*X) B C1 hP hB hC1 (Nat.cast_nonneg _) hKg (by positivity) hg hKP hNP)
  let R := (M*X)^(3*η)
  have hR : 1≤R := Real.one_le_rpow hP (by positivity)
  let Z := X^(2*α-1)*M^(1-α)
  have hZ : 0≤Z := by dsimp [Z]; positivity
  let S := Cshape*R*poissonShape M X α
  have hshape : 1≤poissonShape M X α := by
    change 1≤M+X+Z
    linarith only [hM,hX,hZ]
  have hshape0 : 0≤poissonShape M X α := le_trans zero_le_one hshape
  have hMshape : M≤poissonShape M X α := by
    change M≤M+X+Z
    linarith only [hX,hZ]
  have hXshape : X≤poissonShape M X α := by
    change X≤M+X+Z
    linarith only [hM,hZ]
  have hZshape : Z≤poissonShape M X α := by
    change Z≤M+X+Z
    linarith only [hM,hX]
  have hRshape : 1≤R*poissonShape M X α := by nlinarith only [hR,hshape]
  have hshapeS : poissonShape M X α≤S := by
    calc
      poissonShape M X α ≤ R*poissonShape M X α := le_mul_of_one_le_left hshape0 hR
      _ ≤ Cshape*(R*poissonShape M X α) :=
        le_mul_of_one_le_left (mul_nonneg (by linarith only [hR]) hshape0) hCs
      _ = S := by dsimp [S]; ring
  have hMS : M≤S := hMshape.trans hshapeS
  have hNS : X/q≤S := hNX.trans (hXshape.trans hshapeS)
  have hMiddle : selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) ≤
      4*C1^3*R*poissonShape M X α := by
    apply (selectedPoisson_middle_bound C M X η α hC hM hX hη.le hα2).trans
    change 4*C^3*R*Z≤4*C1^3*R*poissonShape M X α
    gcongr
  have hmidS : selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2)≤S :=
    hMiddle.trans (by dsimp [S]; gcongr; linarith only [hCsMid])
  have hprS : Real.sqrt (M/selectedPoissonK C M X η)*(X/q)+
      Real.sqrt M*(selectedPoissonK C M X η)^(α-1/2)≤S := by
    apply (selectedPoisson_principal_shape C M X (X/q) η α hC hM hX (by positivity) hNX hη.le hα).trans
    calc
      M+selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2)
          ≤ poissonShape M X α+4*C1^3*R*poissonShape M X α := add_le_add hMshape hMiddle
      _ ≤ R*poissonShape M X α+4*C1^3*R*poissonShape M X α :=
        add_le_add (le_mul_of_one_le_left hshape0 hR) (le_refl _)
      _ = (1+4*C1^3)*R*poissonShape M X α := by ring
      _ ≤ S := by dsimp [S]; gcongr
  obtain ⟨hED,hES⟩ := poisson_truncation_small (M*X) (selectedPoissonT C M X η) η
    (selectedPoissonK C M X η) M (X/q) C1 l hP hTP hl hKg hM0.le (by positivity) hC10 hKP hMP hNP
  have hC1S : C1≤S := by
    calc
      C1 ≤ Cshape := hCsC
      _ ≤ Cshape*(R*poissonShape M X α) := le_mul_of_one_le_right (by positivity) hRshape
      _ = S := by dsimp [S]; ring
  have htailS : M/((min 1 (M/((Ideal.absNorm G:ℝ)*(X/q)*(X/q))))^2*
      (1+(M/((Ideal.absNorm G:ℝ)*(X/q)*(X/q)))*selectedPoissonK C M X η)^A)≤S := by
    rw [hGN]
    apply (selectedPoisson_tail_shape C B M X q η A hBC hB hM hX hq hη.le hA).trans
    calc
      B^2*M ≤ B^2*(R*poissonShape M X α) := by
        gcongr
        exact hMshape.trans (le_mul_of_one_le_left hshape0 hR)
      _ ≤ Cshape*(R*poissonShape M X α) := by gcongr
      _ = S := by dsimp [S]; ring
  have hV : 1≤H*(M*X)^(4*η) := by
    have hh := Real.one_le_rpow hP (show 0≤4*η by positivity)
    nlinarith only [hH,hh]
  have hU : 1≤(H*(M*X)^(4*η))^8 := one_le_pow₀ hV
  apply (poissonComparisonMajorant_unit_box sD sS sT CD CS CT CP l A hexp η hη η hη G
    (selectedPoissonK C M X η) (X/q) M (selectedPoissonT C M X η)
    ((H*(M*X)^(4*η))^8) S W hKg (by positivity) hM0.le (by linarith only [hT]) hU (by dsimp [S]; positivity)
    hb hMS hNS hmidS hprS (hED.trans hC1S) (hES.trans hC1S) htailS).trans_eq
  exact poisson_envelope_identity H Cshape (M*X) η (poissonShape M X α) hP0

end CanonicalQuadraticSieve

end

end OAI

end


