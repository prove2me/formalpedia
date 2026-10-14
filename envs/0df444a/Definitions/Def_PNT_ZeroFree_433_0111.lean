-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0111
-- name    : PNT_ZeroFree_433_0111
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:21:25.104388+00:00
-- url     : https://prove2.me/theorems/79230aad-9b29-4efe-aac3-b2cb307da5c0
-- title:
--   Zero-free region foundations: CubicSieve.LogarithmicTargets [0111]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.LogarithmicTargets
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/LogarithmicTargets.lean#L84-L710

import Definitions.Def_PNT_ZeroFree_433_0110

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/LogarithmicTargets.lean#L84-L710
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.CubicSieve.LogarithmicTargets
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
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def secondLogTargets (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex) :
    Finset (Ideal O × O) :=
  (secondLogSector p D F K R X M j).image (fun x =>
    (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x),
      secondSupportRow p (expansionSupportData C D x)))

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondLogTargets_mem (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex)
    (x : SecondExpansionData ι) (hx : x ∈ secondLogSector p D F K R X M j) :
    (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x),
      secondSupportRow p (expansionSupportData C D x)) ∈
      secondLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j :=
  Finset.mem_image.mpr ⟨x,hx,rfl⟩

include hp in
lemma secondLogTargets_bounds (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex)
    (q : Ideal O × O) (hq : q ∈ secondLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j) :
    q.1 ≠ ⊥ ∧ (Ideal.absNorm q.1 : ℝ) ≤ secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j ∧
      q.2 ≠ 0 ∧ ‖eisEmbedding q.2‖^2 ≤ secondLogK j * Real.exp 1 := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hx,hj⟩ := Finset.mem_filter.mp hx
  have hs := secondSupportedSector_mem p F K R X M x hx
  have hb := secondLogIndex_target_bounds p hp B C D v₁ v₂ ε₁ ε₂ x hs.2.2.2.1
  rw [hj] at hb
  exact ⟨secondSupportNewLabel_ne_bot p hp B C D v₁ v₂ ε₁ ε₂ x, hb.1,
    actualSecondRow_ne_zero p D x.divisor x.frequency hs.2.2.2.1, hb.2⟩

include hp in
lemma secondLogSector_coordinates (C D F R : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (X M : ℝ) (hX : 0 < X) (j : SecondLogIndex) (x : SecondExpansionData ι)
    (hx : x ∈ secondLogSector p D F K R X M j) :
    let y := expansionSupportData C D x
    |secondSectorZ p (secondExpansionScale p X
      (primeSubsetGenerator (fun i => Ideal.span {p i}) R) y) (secondLogX p R X j) y| ≤ 2 ∧
    |secondSectorUd p (primeProductNorm p D) y| ≤ 2 ∧
    |secondSectorUe p (secondLogE j) y| ≤ 2 ∧
    |secondSectorUv p (secondLogV j) y| ≤ 2 ∧
    |secondSectorKap p (secondLogK j) y| ≤ 2 := by
  obtain ⟨hx,hj⟩ := Finset.mem_filter.mp hx
  have hs := secondSupportedSector_mem p F K R X M x hx
  have h := secondLogIndex_coordinates p hp C D R X hX x hs.2.2.2.1
  dsimp only at h
  rw [hj] at h
  exact h

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondSupportedSector_remainder_bound (F R : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (X M : ℝ) (x : SecondExpansionData ι) (hx : x ∈ secondSupportedSector p F K R X M) :
    primeProductNorm p R ≤ X*Real.exp M := by
  obtain ⟨hG,hE,hV,hk0,hk,hr,hs⟩ := secondSupportedSector_mem p F K R X M x hx
  have h := (secondSourceSupport_bounds p hp X M x hs hE).1
  rw [← hr]
  exact (primeProductNorm_mono p hp Finset.sdiff_subset).trans h

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondSupportedSector_eq_empty (F R : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (X M : ℝ) (hR : ¬ primeProductNorm p R ≤ X*Real.exp M) :
    secondSupportedSector p F K R X M = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hR (secondSupportedSector_remainder_bound p hp F R K X M x hx)

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in

theorem truncatedSecondSource_eq_binned
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (D F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (g W : 𝓢(ℝ,ℂ))
    (X Y M Kmax : ℝ) (hX : 0 < X) (hgM : ∀ u, g u ≠ 0 → |u| ≤ M)
    (K : Finset ι → Finset ι → Finset O)
    (hK : ∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R X M,
      ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 ≤ Kmax) :
    let H := fun S => normalizedColumn p (fun A => g (columnLog p X A)) S
    truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K =
      truncatedSecondZero p hg F Ψ m c d H W Y K +
        ∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F (X*Real.exp M),
          ∑ j ∈ secondLogBinBox (X*Real.exp M) Kmax,
            secondExpansionSource p hp hcop hg F Ψ m c d z
              (secondLogSector p D F K R X M j) H H W Y := by
  dsimp only
  rw [truncatedSecondSource_eq_nonzero_add_zero, add_comm,
    truncatedSecondSource_eq_fixed_sectors p hp hcop hg hinj hc hpr]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  simp only [boundedPrimeSupports, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro R hR
  have hE : ∀ x ∈ secondExpansionSector F (fun G E => (K G E).erase 0) R,
      x.divisor ⊆ x.sourceCommon := by
    intro x hx
    exact ((mem_secondExpansionPool _ _ _).mp (Finset.mem_filter.mp hx).1).2.1
  have hs := secondExpansionSource_eq_supported p hp hcop hg hinj F Ψ m c d z
    g W X Y M hX hgM (secondExpansionSector F (fun G E => (K G E).erase 0) R) hE
  rw [hs]
  change secondExpansionSource p hp hcop hg F Ψ m c d z (secondSupportedSector p F K R X M)
      _ _ W Y = _
  by_cases hNR : primeProductNorm p R ≤ X*Real.exp M
  · rw [if_pos hNR]
    simp only [secondExpansionSource]
    exact (sum_secondLogSector p hp D F K R X M Kmax (hK R hR) _).symm
  · rw [if_neg hNR, secondSupportedSector_eq_empty p hp F R K X M hNR]
    simp only [secondExpansionSource, Finset.sum_empty]

include hinj in
theorem truncatedSecondSource_norm_le_binned
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (D F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (g W : 𝓢(ℝ,ℂ))
    (X Y M Kmax : ℝ) (hX : 0 < X) (hgM : ∀ u, g u ≠ 0 → |u| ≤ M)
    (K : Finset ι → Finset ι → Finset O)
    (hK : ∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R X M,
      ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 ≤ Kmax) :
    let H := fun S => normalizedColumn p (fun A => g (columnLog p X A)) S
    ‖truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K‖ ≤
      ‖truncatedSecondZero p hg F Ψ m c d H W Y K‖ +
        ∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F (X*Real.exp M),
          ∑ j ∈ secondLogBinBox (X*Real.exp M) Kmax,
            ‖secondExpansionSource p hp hcop hg F Ψ m c d z
              (secondLogSector p D F K R X M j) H H W Y‖ := by
  dsimp only
  rw [truncatedSecondSource_eq_binned p hp hcop hg hinj hc hpr D F Ψ m c d g W X Y M Kmax hX hgM K hK]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact le_rfl
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro z hz
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro R hR
    exact norm_sum_le _ _

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

lemma supported_cutoff_denominator (E G U : ℝ) (hE : E ≤ G) (hG : 1 ≤ G) :
    E * (U/G)^2 ≤ U^2 := by
  have hG0 : 0 < G := by linarith
  have hEG : E ≤ G^2 := by nlinarith
  have he : E/G^2 ≤ 1 := (div_le_one (sq_pos_of_pos hG0)).mpr hEG
  calc
    E*(U/G)^2 = U^2*(E/G^2) := by ring
    _ ≤ U^2*1 := mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ = _ := mul_one _

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def firstCoreSecondRowBound (D A : Finset ι) (X Y M Z : ℝ) : ℝ :=
  3 * primeProductNorm p D * ((X/primeProductNorm p A)*Real.exp M) *
    ((⌈Z*(((X/primeProductNorm p A)*Real.exp M)^2)/Y⌉₊ : ℝ)+1)^2

include hp in

theorem firstCoreSecondCutoff_supported_row_bound
    (D A F R : Finset ι) (X Y M Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 ≤ Z)
    (x : SecondExpansionData ι)
    (hx : x ∈ secondSupportedSector p F (firstCoreSecondCutoff p A X Y M Z) R
      (X/primeProductNorm p A) M) :
    ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 ≤
      firstCoreSecondRowBound p D A X Y M Z := by
  obtain ⟨hG,hE,hV,hk0,hk,hr,hs⟩ := secondSupportedSector_mem p F
    (firstCoreSecondCutoff p A X Y M Z) R (X/primeProductNorm p A) M x hx
  let U := (X/primeProductNorm p A)*Real.exp M
  have hU : 0 < U := mul_pos (div_pos hX (FirstPassCubeLabels.primeProductNorm_pos p hp A)) (Real.exp_pos _)
  have hNE := FirstPassCubeLabels.primeProductNorm_pos p hp x.divisor
  have hNG := FirstPassCubeLabels.primeProductNorm_pos p hp x.sourceCommon
  have hEupper : primeProductNorm p x.divisor ≤ U :=
    (secondSourceSupport_bounds p hp _ M x hs hE).2.1
  have hden : primeProductNorm p x.divisor *
      (((X/primeProductNorm p A)/primeProductNorm p x.sourceCommon)*Real.exp M)^2 ≤ U^2 := by
    rw [show ((X/primeProductNorm p A)/primeProductNorm p x.sourceCommon)*Real.exp M =
      U/primeProductNorm p x.sourceCommon by dsimp [U]; ring]
    exact supported_cutoff_denominator _ _ _ (primeProductNorm_mono p hp hE) (primeProductNorm_ge_one p hp _)
  have hdenpos : 0 < primeProductNorm p x.divisor *
      (((X/primeProductNorm p A)/primeProductNorm p x.sourceCommon)*Real.exp M)^2 := by
    exact mul_pos hNE (sq_pos_of_pos (mul_pos (div_pos (div_pos hX
      (FirstPassCubeLabels.primeProductNorm_pos p hp A)) hNG) (Real.exp_pos _)))
  have hratio : Z / (Y / (primeProductNorm p x.divisor *
      (((X/primeProductNorm p A)/primeProductNorm p x.sourceCommon)*Real.exp M)^2)) ≤ Z*U^2/Y := by
    rw [div_div_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hden hZ) hY.le
  have hceil : (⌈Z / (Y / (primeProductNorm p x.divisor *
      (((X/primeProductNorm p A)/primeProductNorm p x.sourceCommon)*Real.exp M)^2))⌉₊ : ℝ) ≤
      (⌈Z*U^2/Y⌉₊ : ℝ) := by exact_mod_cast Nat.ceil_mono hratio
  have hkbound := secondFrequencyCutoff_norm_sq_le _ Z x.frequency hk
  simp only [ primeSubsetGenerator_norm_eq_productNorm] at hkbound
  have hkbound' : ‖eisEmbedding x.frequency‖^2 ≤ 3*((⌈Z*U^2/Y⌉₊ : ℝ)+1)^2 := by
    apply hkbound.trans
    gcongr
  have hrow : ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 =
      primeProductNorm p D * primeProductNorm p x.divisor * ‖eisEmbedding x.frequency‖^2 := by
    simp only [actualSecondRow, map_mul, norm_mul, mul_pow, primeSubsetGenerator_norm_eq_productNorm]
  rw [hrow]
  calc
    _ ≤ (primeProductNorm p D * U) * (3*((⌈Z*U^2/Y⌉₊ : ℝ)+1)^2) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hEupper (FirstPassCubeLabels.primeProductNorm_pos p hp D).le)
        hkbound' (sq_nonneg _) (mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp D) hU).le
    _ = firstCoreSecondRowBound p D A X Y M Z := by unfold firstCoreSecondRowBound; dsimp [U]; ring

end

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm jLabel b0Label)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open JointLogSeparation (frequencyTwist frequencyTwist_apply)
open SecondPassIntegration (densityChildEnergy)

theorem normalized_binned_second_density_transfer
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ, ℂ)) (hU : ∀ t, g t ≠ 0 → U t = 1)
    (M : ℝ) (hM : 0 ≤ M) (hgM : ∀ t, g t ≠ 0 → |t| ≤ M)
    (ε : ℝ) (hε : 0 < ε) (decayOrder J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧
      ∀ (Y : ℝ), 0 < Y → ∀ θ : ℝ,
      ∀ (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (Ψ : O →* ℂ) (m : O) (X Kmax : ℝ) (K : Finset ι → Finset ι → Finset O),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X →
        (∀ G ∈ F.powerset, ∀ E ∈ G.powerset, (0 : O) ∈ K G E) →
        (∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R X M,
          ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 ≤ Kmax) →
        let c := secondBaseLabel p B C v₁ v₂ ε₁ ε₂
        let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
        let Hcol := fun S => normalizedColumn p (fun A => (frequencyTwist g θ) (columnLog p X A)) S
        ‖truncatedSecondSource p hp hg hinj F Ψ m c d Hcol W Y K‖ ≤
          |Y| * ‖paperRadialFourier W 0‖ *
            (∑ G ∈ F.powerset, ‖secondInputCoefficient p hg Ψ m c d
              (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S) G‖^2) +
          ∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F (X*Real.exp M),
            ∑ j ∈ secondLogBinBox (X*Real.exp M) Kmax,
            (Y * primeProductNorm p R / X^2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
              (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j *
                Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}))^ε) *
            (Cₛ*(1+‖θ‖)^(J+2)*(1+‖θ‖)^(J+2) /
              (1+Y*secondLogK j*(primeProductNorm p R)^2/(primeProductNorm p D*X^2))^decayOrder) *
            densityChildEnergy p hp hcop hg F (secondRayMinus Ψ z) (secondRayPlus Ψ z)
              (m * primeSubsetGenerator (fun i => Ideal.span {p i}) R)
              (secondLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j)
              (windows 5) (windows 6) (secondLogX p R X j) (secondLogX p R X j) J := by
  obtain ⟨windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,hbound⟩ :=
    normalized_twisted_second_sector_density_transfer p hp hcop hg hinj hc hpr U hUc hUs
      g g W hU hU M 2 hM (by norm_num) hgM hgM ε hε decayOrder J
  refine ⟨windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,?_⟩
  intro Y hY θ B C D F v₁ v₂ ε₁ ε₂ Ψ m X Kmax K hv hCB hD hΨ hX hzero hK
  dsimp only
  have hθ : ∀ t, (frequencyTwist g θ) t ≠ 0 → |t| ≤ M := by
    intro t ht
    exact hgM t (fun hz => ht (by simp only [frequencyTwist_apply,hz,mul_zero]))
  apply (truncatedSecondSource_norm_le_binned p hp hcop hg hinj hc hpr D F Ψ m
    (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) D)
    (frequencyTwist g θ) W X Y M Kmax hX hθ K hK).trans
  apply add_le_add
  · have hd := truncatedSecondZero_norm_le p hg hinj F Ψ m
      (secondBaseLabel p B C v₁ v₂ ε₁ ε₂) (primeSubsetGenerator (fun i => Ideal.span {p i}) D)
      (fun S => normalizedColumn p (fun A => (frequencyTwist g θ) (columnLog p X A)) S) W Y K hzero
    simpa only [secondInputCoefficient_frequencyTwist_norm] using hd
  · apply Finset.sum_le_sum
    intro z hz
    apply Finset.sum_le_sum
    intro R hR
    apply Finset.sum_le_sum
    intro j hj
    have hcoord := secondLogSector_coordinates p hp C D F R K X M hX j
    have hb := hbound (primeProductNorm p D) (secondLogE j) (secondLogV j)
      (secondLogX p R X j) (secondLogK j) Y
      (FirstPassCubeLabels.primeProductNorm_pos p hp D)
      (normLogScale_pos _) (normLogScale_pos _) (secondLogX_pos p hp R X hX j)
      (normLogScale_pos _) hY θ θ B C D R F v₁ v₂ ε₁ ε₂ Ψ m z K
      (secondLogSector p D F K R X M j) (secondLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j)
      X (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j)
      (secondLogSector_subset p D F K R X M j) hv hCB hD hΨ hX
      (zero_le_one.trans (secondLogLabelBound_ge_one p hp B C v₁ v₂ ε₁ ε₂ j))
      (fun x hx => (hcoord x hx).1) (fun x hx => (hcoord x hx).2.1)
      (fun x hx => (hcoord x hx).2.2.1) (fun x hx => (hcoord x hx).2.2.2.1)
      (fun x hx => (hcoord x hx).2.2.2.2)
      (secondLogTargets_mem p B C D F v₁ v₂ ε₁ ε₂ K R X M j)
      (fun q hq => (secondLogTargets_bounds p hp B C D F v₁ v₂ ε₁ ε₂ K R X M j q hq).1)
      (fun q hq => (secondLogTargets_bounds p hp B C D F v₁ v₂ ε₁ ε₂ K R X M j q hq).2.1)
    simpa only [secondBaseLabel, primeSubsetGenerator_norm_eq_productNorm,
      secondLogX_radial_scale p D R X Y hX.ne' j] using hb

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter)
open SecondPassIntegration (densityChildEnergy)

theorem firstCoreInputRow_binned_finite_transfer
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (hU : ∀ t, g t ≠ 0 → U t = 1)
    (M : ℝ) (hM : 0 ≤ M) (hgM : ∀ t, g t ≠ 0 → |t| ≤ M)
    (ε : ℝ) (hε : 0 < ε) (tailOrder decayOrder J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw Ctail : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧ 0 < Ctail ∧
      ∀ (Y : ℝ), 0 < Y →
      ∀ (A₀ B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (χ : RayCharacter) (Ψ : O →* ℂ) (m : O) (r₁ : FirstCoreIndex)
        (X Z t : ℝ) (Srows : Finset O),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X → 0 ≤ Z →
        (∀ z ∈ Srows, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
        (∀ z ∈ Srows, z ≠ 0) →
        let v := fun i => v₁ i + v₂ i
        let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C
        let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
        let Ψ' := firstCoreTwist negative χ Ψ r₁
        let m' := m * b0Label p B v ε₁ ε₂
        let c' := c * jLabel p B v ε₁ ε₂
        let X' := X / primeProductNorm p A₀
        let Usupp := X' * Real.exp M
        let K := firstCoreSecondCutoff p A₀ X Y M Z
        let Kmax := firstCoreSecondRowBound p D A₀ X Y M Z
        let Hbase := normalizedColumn p (fun S => firstCoreBaseProfile g V negative (columnLog p X' S))
        (∑ z ∈ Srows, ‖firstCoreInputRow p hg F A₀ B v ε₁ ε₂ negative χ Ψ m
          (normalizedColumn p (fun S => g (columnLog p X S))) V (columnLog p X) c d r₁ t z‖^2) +
          ‖firstCoreTest (normalizedColumn p (fun S => g (columnLog p X S))) V (columnLog p X)
            negative t A₀ ∅‖^2 ≤
        (primeProductNorm p A₀)⁻¹ *
          (|Y| * ‖paperRadialFourier rowMajorant 0‖ *
              (∑ G ∈ (F\A₀).powerset, ‖secondInputCoefficient p hg Ψ' m' c' d Hbase G‖^2) +
            (∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p (F\A₀) Usupp,
              ∑ j ∈ secondLogBinBox Usupp Kmax,
              (Y * primeProductNorm p R / X'^2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
                (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j *
                  Ideal.absNorm (Ideal.span {b0Label p B v ε₁ ε₂}))^ε) *
              (Cₛ*(1+‖t‖)^(J+2)*(1+‖t‖)^(J+2) /
                (1+Y*secondLogK j*(primeProductNorm p R)^2/(primeProductNorm p D*X'^2))^decayOrder) *
              densityChildEnergy p hp hcop hg (F\A₀) (secondRayMinus Ψ' z) (secondRayPlus Ψ' z)
                (m' * primeSubsetGenerator (fun i => Ideal.span {p i}) R)
                (secondLogTargets p B C D (F\A₀) v₁ v₂ ε₁ ε₂ K R X' M j)
                (windows 5) (windows 6) (secondLogX p R X' j) (secondLogX p R X' j) J) +
            Ctail*(1+Usupp)^4*Y*(1+(1+Usupp)^3/Y)^2/(1+Z)^tailOrder) := by
  have hUbase : ∀ s, firstCoreBaseProfile g V negative s ≠ 0 → U s = 1 := by
    intro s hs
    apply hU s
    intro hz
    exact hs (by simp only [firstCoreBaseProfile_apply,hz,zero_mul])
  have hMbase : ∀ s, firstCoreBaseProfile g V negative s ≠ 0 → |s| ≤ M := by
    intro s hs
    apply hgM s
    intro hz
    exact hs (by simp only [firstCoreBaseProfile_apply,hz,zero_mul])
  obtain ⟨windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,htrans⟩ :=
    normalized_binned_second_density_transfer p hp hcop hg hinj hc hpr U hUc hUs
      (firstCoreBaseProfile g V negative) rowMajorant hUbase M hM hMbase ε hε decayOrder J
  obtain ⟨Ctail,hCtail,htail⟩ :=
    firstCoreSecondCutoff_tail_fixed_source p hp hg hinj hc tailOrder g V rowMajorant negative
  refine ⟨windows,Cₐ,Cₛ,Cw,Ctail,hCₐ,hCₛ,hCw,hCtail,?_⟩
  intro Y hY A₀ B C D F v₁ v₂ ε₁ ε₂ χ Ψ m r₁ X Z t Srows hv hCB hD hΨ hX hZ hSrows hSrows0
  dsimp only
  have hX' : 0 < X / primeProductNorm p A₀ :=
    div_pos hX (FirstPassCubeLabels.primeProductNorm_pos p hp A₀)
  have hΨ' : ∀ a : O, ‖firstCoreTwist negative χ Ψ r₁ a‖ ≤ 1 :=
    fun a => (firstCoreTwist_norm_le negative χ Ψ r₁ a).trans (hΨ a)
  have hb := htrans Y hY (firstCoreModeHeight negative t) B C D (F\A₀)
    v₁ v₂ ε₁ ε₂ (firstCoreTwist negative χ Ψ r₁)
    (m * b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂) (X / primeProductNorm p A₀)
    (firstCoreSecondRowBound p D A₀ X Y M Z) (firstCoreSecondCutoff p A₀ X Y M Z)
    hv hCB hD hΨ' hX'
    (fun G hG E hE => firstCoreSecondCutoff_zero p A₀ X Y M Z G E)
    (fun R hR x hx => firstCoreSecondCutoff_supported_row_bound p hp D A₀ (F\A₀) R
      X Y M Z hX hY hZ x hx)
  simp only [firstCoreModeHeight_norm, secondBaseLabel] at hb
  have ht := htail F A₀ (firstCoreTwist negative χ Ψ r₁)
    (m * b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) C * jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) D) t X Y M Z hΨ' hX hY hZ hgM
  have hf := firstCoreInputRow_finite_le_truncated_tail p hp hg hinj hc F A₀ B
    (fun i => v₁ i+v₂ i) ε₁ ε₂ negative χ Ψ m g V X hX Y hY
    (primeSubsetGenerator (fun i => Ideal.span {p i}) C)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) D) r₁ t Srows hSrows hSrows0
    (firstCoreSecondCutoff p A₀ X Y M Z)
  simp only [firstCoreModeProfile] at hf ht ⊢
  apply hf.trans
  apply mul_le_mul_of_nonneg_left
  · apply add_le_add
    · exact hb
    · exact ht
  · exact inv_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp A₀).le

end SecondPassArithmetic

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

@[fun_prop] lemma quadraticHeightDenominator_continuous (A B C D : ℝ) :
    Continuous (fun p : SpatialCoordinates => quadraticHeightDenominator A B C D (p 0) (p 1) (p 2)) := by
  unfold quadraticHeightDenominator
  fun_prop

lemma rowSmoothPower_continuousAt (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hv : 0<p 2) : ContinuousAt (rowSmoothPower s u) p := by
  have hq := row_denominator_pos u hu p hv
  have hvc : ContinuousAt (fun q : SpatialCoordinates => q 2) p := (continuous_apply 2).continuousAt
  have hlog := (hvc.log hv.ne').sub
    ((quadraticHeightDenominator_continuous (Complex.normSq (u 0))
      (u 0*star (u 1)).re (-(u 0*star (u 1)).im) (Complex.normSq (u 1))).continuousAt.log hq.ne')
  exact Complex.continuous_exp.continuousAt.comp
    ((Complex.continuous_ofReal.continuousAt.comp hlog).const_mul s)

lemma rowLogD_continuousAt (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ContinuousAt (fun q => rowLogD u q j) p := by
  have hq := row_denominator_pos u hu p hv
  have hvn := hv.ne'
  have hqn := hq.ne'
  have hvn2 := pow_ne_zero 2 hvn
  have hqn2 := pow_ne_zero 2 hqn
  have hqc := (quadraticHeightDenominator_continuous (Complex.normSq (u 0))
    (u 0*star (u 1)).re (-(u 0*star (u 1)).im) (Complex.normSq (u 1))).continuousAt (x := p)
  have hvc : ContinuousAt (fun q : SpatialCoordinates => q 2) p := (continuous_apply 2).continuousAt
  fin_cases j
  · dsimp [rowLogD,spatialLogD,heightLogDx]
    fun_prop (disch := aesop)
  · dsimp [rowLogD,spatialLogD,heightLogDy]
    fun_prop (disch := aesop)
  · exact (continuousAt_const.div hvc hvn).sub
      ((hvc.const_mul (2*Complex.normSq (u 0))).div hqc hqn)

lemma rowLogDD_continuousAt (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ContinuousAt (fun q => rowLogDD u q j) p := by
  have hq := row_denominator_pos u hu p hv
  have hvn := hv.ne'
  have hqn := hq.ne'
  have hvn2 := pow_ne_zero 2 hvn
  have hqn2 := pow_ne_zero 2 hqn
  have hqc := (quadraticHeightDenominator_continuous (Complex.normSq (u 0))
    (u 0*star (u 1)).re (-(u 0*star (u 1)).im) (Complex.normSq (u 1))).continuousAt (x := p)
  have hvc : ContinuousAt (fun q : SpatialCoordinates => q 2) p := (continuous_apply 2).continuousAt
  fin_cases j
  · dsimp [rowLogDD,spatialLogDD,heightLogDxx]
    fun_prop (disch := aesop)
  · dsimp [rowLogDD,spatialLogDD,heightLogDyy]
    fun_prop (disch := aesop)
  · exact (continuousAt_const.div (hvc.pow 2) hvn2).neg.sub
      (((hqc.const_mul (2*Complex.normSq (u 0))).sub
        ((hvc.const_mul (2*Complex.normSq (u 0))).mul
          (hvc.const_mul (2*Complex.normSq (u 0))))).div (hqc.pow 2) hqn2)

def smoothFirstCoefficient (s : ℂ) (r : CuspCosets) (j : Fin 3) (p : SpatialCoordinates) : ℂ :=
  smoothSummand s r p*s*(rowLogD (embeddedRow r) p j:ℂ)
def smoothSecondCoefficient (s : ℂ) (r : CuspCosets) (j : Fin 3) (p : SpatialCoordinates) : ℂ :=
  smoothSummand s r p*(s^2*(rowLogD (embeddedRow r) p j:ℂ)^2+s*(rowLogDD (embeddedRow r) p j:ℂ))

lemma smoothFirstCoefficient_eq_deriv (s : ℂ) (r : CuspCosets) (j : Fin 3)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    smoothFirstCoefficient s r j p=deriv (axisSlice (smoothSummand s r) p j) (p j) := by
  unfold axisSlice smoothSummand
  rw [deriv_const_mul_field]
  have hd := (row_axis_hasDerivAt s (embeddedRow r) (embeddedRow_ne_zero r) p hv j).deriv
  unfold axisSlice at hd
  rw [hd]
  unfold smoothFirstCoefficient smoothSummand
  ring

lemma smoothSecondCoefficient_eq_deriv (s : ℂ) (r : CuspCosets) (j : Fin 3)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    smoothSecondCoefficient s r j p=deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j) := by
  unfold axisSlice smoothSummand
  rw [deriv_const_mul_field',deriv_const_mul_field]
  have hd := (row_axis_hasDerivAt_deriv s (embeddedRow r) (embeddedRow_ne_zero r) p hv j).deriv
  unfold axisSlice at hd
  rw [hd]
  unfold smoothSecondCoefficient smoothSummand
  ring

lemma smoothCoefficients_continuousAt (s : ℂ) (r : CuspCosets) (j : Fin 3)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    ContinuousAt (smoothFirstCoefficient s r j) p ∧ ContinuousAt (smoothSecondCoefficient s r j) p := by
  have hF : ContinuousAt (smoothSummand s r) p :=
    (rowSmoothPower_continuousAt s (embeddedRow r) (embeddedRow_ne_zero r) p hv).const_mul _
  have hD := Complex.continuous_ofReal.continuousAt.comp
    (rowLogD_continuousAt (embeddedRow r) (embeddedRow_ne_zero r) p hv j)
  have hDD := Complex.continuous_ofReal.continuousAt.comp
    (rowLogDD_continuousAt (embeddedRow r) (embeddedRow_ne_zero r) p hv j)
  exact ⟨(hF.mul_const s).mul hD,hF.mul ((hD.pow 2).const_mul (s^2) |>.add (hDD.const_mul s))⟩

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

lemma spatial_summable_derivative_bounds (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    ∃ U : Set SpatialCoordinates, IsOpen U ∧ p∈U ∧
      ∃ M₀ M₁ M₂ : CuspCosets → ℝ,
      Summable M₀ ∧ Summable M₁ ∧ Summable M₂ ∧
      ∀q∈U, 0<q 2 ∧ ∀r : CuspCosets,
        ‖smoothSummand s r q‖≤M₀ r ∧ ∀j : Fin 3,
        ‖smoothFirstCoefficient s r j q‖≤M₁ r ∧
        ‖smoothSecondCoefficient s r j q‖≤M₂ r := by
  let deltaLoss : ℝ := p 2/2
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  let path := clampedCoordinates deltaLoss hδ
  let C := rowBound (coordinateSection (path p))+1
  have hC : 0<C := by dsimp [C]; linarith [rowBound_pos (coordinateSection (path p))]
  let U : Set SpatialCoordinates := {q | deltaLoss<q 2 ∧ rowBound (coordinateSection (path q))<C}
  have hU : IsOpen U := (isOpen_lt continuous_const (continuous_apply 2)).inter
    (isOpen_lt (continuous_coordinate_rowBound.comp (continuous_clampedCoordinates deltaLoss hδ)) continuous_const)
  have hpU : p∈U := by constructor <;> dsimp [deltaLoss,C] <;> linarith
  obtain ⟨M,hM,hMnonneg,hbound⟩ := coordinate_summable_majorant C s.re s.re hC hs hs
  let c₁ := ‖s‖*(1/deltaLoss)
  let c₂ := ‖s‖^2*(1/deltaLoss)^2 + ‖s‖*(7/deltaLoss^2)
  refine ⟨U,hU,hpU,M,fun r => M r*c₁,fun r => M r*c₂,hM,hM.mul_right _,hM.mul_right _,?_⟩
  intro q hq
  have hpos : 0<q 2 := lt_trans hδ hq.1
  refine ⟨hpos,fun r => ?_⟩
  have hm : ‖smoothSummand s r q‖≤M r := by
    rw [smoothSummand_eq_clamped s r q deltaLoss hδ hq.1.le]
    exact hbound (path q,s) hq.2.le le_rfl le_rfl r
  have hfrac : 1 / q 2 ≤ 1/deltaLoss := one_div_le_one_div_of_le hδ hq.1.le
  have hfrac₂ : 7 / (q 2)^2 ≤ 7/deltaLoss^2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hδ)
    nlinarith [hq.1]
  refine ⟨hm,fun j => ?_⟩
  rw [smoothFirstCoefficient_eq_deriv _ _ _ _ hpos,smoothSecondCoefficient_eq_deriv _ _ _ _ hpos]
  constructor
  · apply (norm_smooth_axis_deriv s r q hpos j).trans
    apply mul_le_mul hm _ (by positivity) (hMnonneg r)
    exact mul_le_mul_of_nonneg_left hfrac (norm_nonneg s)
  · apply (norm_smooth_axis_deriv2 s r q hpos j).trans
    apply mul_le_mul hm _ (by positivity) (hMnonneg r)
    dsimp [c₂]
    gcongr

def eisensteinFirstPartial (s : ℂ) (j : Fin 3) (p : SpatialCoordinates) : ℂ :=
  deriv (axisSlice (upperEisensteinField s) p j) (p j)

def eisensteinSecondPartial (s : ℂ) (j : Fin 3) (p : SpatialCoordinates) : ℂ :=
  deriv (deriv (axisSlice (upperEisensteinField s) p j)) (p j)

lemma eisensteinPartials_eq_tsum (s : ℂ) (hs : 2<s.re) (j : Fin 3)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    eisensteinFirstPartial s j p=(∑'r,smoothFirstCoefficient s r j p) ∧
    eisensteinSecondPartial s j p=(∑'r,smoothSecondCoefficient s r j p) := by
  have ht := eisenstein_axis_termwise s hs p hv j
  have heq := axisSlice_eventuallyEq_of_positive (upperEisensteinField s) (smoothEisenstein s)
    (fun q hq => upperEisensteinField_eq_smooth s q hq) p hv j
  constructor
  · unfold eisensteinFirstPartial
    rw [heq.deriv_eq,ht.2.2.1.deriv]
    exact tsum_congr (fun r => (smoothFirstCoefficient_eq_deriv _ _ _ _ hv).symm)
  · unfold eisensteinSecondPartial
    rw [heq.deriv.deriv_eq,ht.2.2.2.deriv]
    exact tsum_congr (fun r => (smoothSecondCoefficient_eq_deriv _ _ _ _ hv).symm)

lemma actual_spatial_continuousAt (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    ContinuousAt (upperEisensteinField s) p ∧ ∀j : Fin 3,
    ContinuousAt (eisensteinFirstPartial s j) p ∧
    ContinuousAt (eisensteinSecondPartial s j) p := by
  obtain ⟨U,hU,hpU,M₀,M₁,M₂,hM₀,hM₁,hM₂,hbound⟩ := spatial_summable_derivative_bounds s hs p hv
  have hf (r : CuspCosets) : ContinuousOn (smoothSummand s r) U := by
    intro q hq
    exact ((rowSmoothPower_continuousAt s (embeddedRow r) (embeddedRow_ne_zero r) q
      (hbound q hq).1).const_mul _).continuousWithinAt
  have hsum := continuousOn_tsum hf hM₀ (fun r q hq => ((hbound q hq).2 r).1)
  have heq : (upperEisensteinField s) =ᶠ[𝓝 p] smoothEisenstein s := by
    filter_upwards [hU.mem_nhds hpU] with q hq
    exact upperEisensteinField_eq_smooth s q (hbound q hq).1
  refine ⟨(hsum.continuousAt (hU.mem_nhds hpU)).congr heq.symm,fun j => ?_⟩
  have hc₁ (r : CuspCosets) : ContinuousOn (smoothFirstCoefficient s r j) U := by
    intro q hq
    exact ((smoothCoefficients_continuousAt s r j q (hbound q hq).1).1).continuousWithinAt
  have hc₂ (r : CuspCosets) : ContinuousOn (smoothSecondCoefficient s r j) U := by
    intro q hq
    exact ((smoothCoefficients_continuousAt s r j q (hbound q hq).1).2).continuousWithinAt
  have hsum₁ := continuousOn_tsum hc₁ hM₁ (fun r q hq => (((hbound q hq).2 r).2 j).1)
  have hsum₂ := continuousOn_tsum hc₂ hM₂ (fun r q hq => (((hbound q hq).2 r).2 j).2)
  have heq₁ : eisensteinFirstPartial s j =ᶠ[𝓝 p] (fun q => ∑'r,smoothFirstCoefficient s r j q) := by
    filter_upwards [hU.mem_nhds hpU] with q hq
    exact (eisensteinPartials_eq_tsum s hs j q (hbound q hq).1).1
  have heq₂ : eisensteinSecondPartial s j =ᶠ[𝓝 p] (fun q => ∑'r,smoothSecondCoefficient s r j q) := by
    filter_upwards [hU.mem_nhds hpU] with q hq
    exact (eisensteinPartials_eq_tsum s hs j q (hbound q hq).1).2
  exact ⟨(hsum₁.continuousAt (hU.mem_nhds hpU)).congr heq₁.symm,
    (hsum₂.continuousAt (hU.mem_nhds hpU)).congr heq₂.symm⟩

end CubicEisenstein

end

end OAI

end


