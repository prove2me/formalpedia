-- Prove2me | Definitions.Def_PNT_Kadiri_HeckeBridge_433_0010
-- name    : PNT_Kadiri_HeckeBridge_433_0010
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-12T12:46:01.312567+00:00
-- url     : https://prove2.me/theorems/c29201c2-bcfb-44e7-91f6-3ff15aeede09
-- title:
--   Complete Hecke-to-zeta bridge, part 0010
-- statement:
--   Complete proved arithmetic and analytic lemmas connecting the Eisenstein Hecke L-function to ordinary Dirichlet L-functions and the Riemann zeta function. The final bridge transfers Hecke nonvanishing in Re(s) > 7/8 to zeta nonvanishing. Original hypotheses and proof bodies are retained; no unproved theorem is imported. Source modules: OAI.NumberTheory.DirichletL.IdealEuler, OAI.NumberTheory.DirichletL.Hecke.IdealBridge, OAI.NumberTheory.DirichletL.Hecke.Euler, OAI.NumberTheory.DirichletL.Hecke.Dirichlet
-- source:
--   OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, Apache-2.0; ported to Lean 4.33.1 and pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_HeckeSevenEighths
import Definitions.Def_PNT_Kadiri_HeckeBridge_433_0009

/- Complete Hecke-to-Dirichlet and zeta bridge lemmas.
Source: OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.IdealEuler
section
namespace OAI

namespace SevenEighths.IdealEuler

open ActualEisensteinCubic UniqueFactorizationMonoid
open CompletedGauss (MulFiber mulFiber_moebius_sum)

open scoped BigOperators Classical

noncomputable section

def normWeight (s : ℂ) : Ideal O →*₀ ℂ where
  toFun := CubicEisenstein.fullIdealWeight s
  map_zero' := by simp [CubicEisenstein.fullIdealWeight]
  map_one' := by simp [CubicEisenstein.fullIdealWeight]
  map_mul' I J := by
    by_cases hI : I = 0
    · simp [CubicEisenstein.fullIdealWeight, hI]
    by_cases hJ : J = 0
    · simp [CubicEisenstein.fullIdealWeight, hJ]
    simp only [CubicEisenstein.fullIdealWeight, hI, hJ, mul_ne_zero hI hJ,
      ite_false, map_mul, Nat.cast_mul]
    exact Complex.natCast_mul_natCast_cpow _ _ _

def weighted (a : Ideal O →*₀ ℂ) (s : ℂ) : Ideal O →*₀ ℂ where
  toFun I := a I * normWeight s I
  map_zero' := by rw [map_zero, map_zero, zero_mul]
  map_one' := by rw [map_one, map_one, one_mul]
  map_mul' I J := by simp only [map_mul]; ring

def series (a : Ideal O →*₀ ℂ) (s : ℂ) : ℂ := ∑' I : Ideal O, weighted a s I

def inverseSeries (a : Ideal O →*₀ ℂ) (s : ℂ) : ℂ :=
  ∑' I : Ideal O, (moebius I : ℂ) * weighted a s I

theorem weighted_summable_norm (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : Summable (fun I : Ideal O => ‖weighted a s I‖) := by
  apply (CubicEisenstein.fullIdealWeight_summable_norm s hs).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro I
  change ‖a I * CubicEisenstein.fullIdealWeight s I‖ ≤ _
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha I)


theorem inverse_summable_norm (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun I : Ideal O => ‖(moebius I : ℂ) * weighted a s I‖) := by
  apply (weighted_summable_norm a ha s hs).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro I
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (CubicEisenstein.norm_ideal_moebius_le_one I)


theorem inverseSeries_mul_series (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : inverseSeries a s * series a s = 1 := by
  let f := weighted a s
  let F : Ideal O × Ideal O → ℂ := fun p => (moebius p.1 : ℂ) * f (p.1 * p.2)
  have hprod := (inverse_summable_norm a ha s hs).mul_norm (weighted_summable_norm a ha s hs)
  have hF : Summable F := by
    apply hprod.of_norm.congr
    intro p
    dsimp only [F, f]
    rw [map_mul]
    ring
  have hfiber (B : Ideal O) : (∑' p : MulFiber B, F p.1) = if B = 1 then 1 else 0 := by
    by_cases hB : B = 0
    · subst B
      have hz (p : MulFiber 0) : F p.1 = 0 := by simp only [F, p.2, map_zero, mul_zero]
      simp only [hz, tsum_zero, zero_ne_one, ite_false]
    · calc
        _ = (∑' p : MulFiber B, (moebius p.1.1 : ℂ)) * f B := by
          rw [← tsum_mul_right]
          exact tsum_congr (fun p => by simp only [F, p.2])
        _ = _ := by
          rw [mulFiber_moebius_sum B hB]
          split_ifs with hB1
          · subst B
            simp only [map_one, one_mul]
          · exact zero_mul _
  have hsum := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1 * p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B, F p.1) (∑' p, F p) at hsum
  simp_rw [hfiber] at hsum
  have hFone : (∑' p, F p) = 1 := by simpa using hsum.tsum_eq.symm
  calc
    _ = ∑' p : Ideal O × Ideal O, ((moebius p.1 : ℂ) * f p.1) * f p.2 :=
      tsum_mul_tsum_of_summable_norm (inverse_summable_norm a ha s hs)
        (weighted_summable_norm a ha s hs)
    _ = ∑' p, F p := by
      apply tsum_congr
      intro p
      simp only [F, map_mul]
      ring
    _ = 1 := hFone


end

end SevenEighths.IdealEuler

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Hecke.IdealBridge
section
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.HeckeFamily

private instance p2mAnonymous_PNT_Kadiri_HeckeBridge_433_0010_1 : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

def idealCoeff (χ : Character) : Ideal O →*₀ ℂ :=
  IdealCharacter.ofResidue χ.modulus χ.residue χ.unit_trivial


theorem idealCoeff_span (χ : Character) {z : O} (hz : z ≠ 0) :
    idealCoeff χ (Ideal.span {z}) = elementCoeff χ z :=
  IdealCharacter.ofResidue_span χ.modulus χ.residue χ.unit_trivial hz

theorem coordinateElement_eq_baseline (a b : ℤ) :
    coordinateElement a b = ActualEisensteinCoordinates.eval a b := rfl

def coordinateEquiv : (ℤ × ℤ) ≃ O :=
  Equiv.ofBijective (fun n => coordinateElement n.1 n.2)
    ⟨fun _ _ h => Prod.ext
      (ActualEisensteinCoordinates.unique_coordinates h).1
      (ActualEisensteinCoordinates.unique_coordinates h).2,
      HeckeCoordinates.coordinateElement_surjective⟩

theorem normForm_eq_absNorm_span (n : ℤ × ℤ) :
    EisensteinTheta.normForm n.1 n.2 =
      (Ideal.absNorm (Ideal.span {coordinateElement n.1 n.2}) : ℝ) := by
  rw [coordinateElement_eq_baseline,
    ← ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    ActualEisensteinCubic.eisEmbedding_eval_norm_sq]
  simp only [EisensteinTheta.normForm, Int.cast_add, Int.cast_sub, Int.cast_mul, pow_two]

def elementTerm (χ : Character) (s : ℂ) (z : O) : ℂ :=
  elementCoeff χ z / (Ideal.absNorm (Ideal.span {z}) : ℂ) ^ s

def idealTerm (χ : Character) (s : ℂ) (I : Ideal O) : ℂ :=
  idealCoeff χ I / (Ideal.absNorm I : ℂ) ^ s

theorem elementTerm_coordinate (χ : Character) (s : ℂ) (n : ℤ × ℤ) :
    elementTerm χ s (coordinateEquiv n) =
      elementCoeff χ (coordinateElement n.1 n.2) /
        (EisensteinTheta.normForm n.1 n.2 : ℂ) ^ s := by
  change elementCoeff χ (coordinateElement n.1 n.2) /
    (Ideal.absNorm (Ideal.span {coordinateElement n.1 n.2}) : ℂ) ^ s = _
  rw [normForm_eq_absNorm_span]
  rw [Complex.ofReal_natCast]

theorem elementTerm_hasSum (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    HasSum (elementTerm χ s) (continuedLattice χ s) := by
  apply coordinateEquiv.hasSum_iff.mp
  change HasSum (fun n => elementTerm χ s (coordinateEquiv n)) _
  simpa only [elementTerm_coordinate] using continuedLattice_hasSum χ hs

theorem elementTerm_zero (χ : Character) {s : ℂ} (hs : s ≠ 0) :
    elementTerm χ s 0 = 0 := by
  simp [elementTerm, Complex.zero_cpow hs]

theorem elementTerm_unit_mul (χ : Character) (s : ℂ) (u : Oˣ) (z : O) :
    elementTerm χ s ((u : O) * z) = elementTerm χ s z := by
  unfold elementTerm
  rw [elementCoeff_unit_mul, Ideal.span_singleton_mul_left_unit u.isUnit]

theorem elementTerm_idealGenerator (χ : Character) (s : ℂ)
    (I : UnrestrictedIdealReindex.NonzeroIdeal) :
    elementTerm χ s (ConcretePrimeRowBridge.idealGenerator I.val) = idealTerm χ s I.val := by
  unfold elementTerm idealTerm
  rw [ConcretePrimeRowBridge.span_idealGenerator]
  congr 1
  exact (IdealCharacter.ofResidue_of_generator χ.modulus χ.residue χ.unit_trivial
    I.property (ConcretePrimeRowBridge.span_idealGenerator I.val)).symm

theorem continuedLattice_eq_six_ideal_tsum (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    continuedLattice χ s = 6 * ∑' I : Ideal O, idealTerm χ s I := by
  have hs₀ : s ≠ 0 := by intro h; norm_num [h] at hs
  have h := UnrestrictedIdealReindex.tsum_unit_invariant_of_zero (elementTerm χ s)
    (elementTerm_hasSum χ hs).summable (elementTerm_zero χ hs₀)
    (elementTerm_unit_mul χ s)
  rw [(elementTerm_hasSum χ hs).tsum_eq] at h
  simp_rw [elementTerm_idealGenerator] at h
  have hsum : (∑' I : UnrestrictedIdealReindex.NonzeroIdeal, idealTerm χ s I.val) =
      ∑' I : Ideal O, idealTerm χ s I := by
    apply tsum_subtype_eq_of_support_subset
    intro I hI hzero
    exact hI (by rw [hzero]; unfold idealTerm; rw [map_zero]; exact zero_div _)
  rwa [hsum] at h


theorem LFunction_eq_ideal_tsum (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = ∑' I : Ideal O, idealTerm χ s I := by
  rw [LFunction, continuedLattice_eq_six_ideal_tsum χ hs]
  ring

theorem LFunction_differentiableAt (χ : Character) {s : ℂ}
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1 ∨ χ.residue ≠ 1) :
    DifferentiableAt ℂ (LFunction χ) s := by
  apply DifferentiableAt.div_const
  rcases hs₁ with hs₁ | hχ
  · exact continuedLattice_differentiableAt χ hs₀ (Or.inl hs₁)
  · exact HeckeCharacterAnalytic.continuedLattice_differentiableAt_nonprincipal χ hχ hs₀


end SevenEighths.HeckeFamily

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Hecke.Euler
section
namespace OAI

noncomputable section
namespace SevenEighths.HeckeFamily

private instance p2mAnonymous_PNT_Kadiri_HeckeBridge_433_0010_2 : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

theorem idealCoeff_norm_le_one (χ : Character) (I : Ideal O) : ‖idealCoeff χ I‖ ≤ 1 := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  exact IdealCharacter.norm_ofResidue_le_one χ.modulus χ.residue χ.unit_trivial I

theorem idealTerm_eq_weighted (χ : Character) (s : ℂ) (I : Ideal O) :
    idealTerm χ s I = IdealEuler.weighted (idealCoeff χ) s I := by
  change idealCoeff χ I / (Ideal.absNorm I : ℂ)^s =
    idealCoeff χ I * CubicEisenstein.fullIdealWeight s I
  by_cases hI : I = 0
  · rw [hI, map_zero]
    simp
  · simp only [CubicEisenstein.fullIdealWeight, hI, ite_false,
      Complex.cpow_neg, div_eq_mul_inv]

theorem LFunction_eq_series (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = IdealEuler.series (idealCoeff χ) s := by
  rw [LFunction_eq_ideal_tsum χ hs]
  exact tsum_congr (idealTerm_eq_weighted χ s)


theorem inverseSeries_mul_LFunction (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    IdealEuler.inverseSeries (idealCoeff χ) s * LFunction χ s = 1 := by
  rw [LFunction_eq_series χ hs]
  exact IdealEuler.inverseSeries_mul_series (idealCoeff χ) (idealCoeff_norm_le_one χ) s hs


end SevenEighths.HeckeFamily

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Hecke.Dirichlet
section
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDirichlet
open HeckeFamily

variable {q : ℕ}

def modulus (q : ℕ) : Ideal O := Ideal.span {(q : O)}

theorem modulus_ne_bot [NeZero q] : modulus q ≠ ⊥ := by
  simpa only [modulus, ne_eq, Ideal.span_singleton_eq_bot] using
    (Nat.cast_ne_zero.mpr (NeZero.ne q) : (q : O) ≠ 0)

theorem quotient_modulus_zero : (q : O ⧸ modulus q) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (modulus q))]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem norm_span_dvd (z : O) :
    z ∣ (Ideal.absNorm (Ideal.span {z}) : O) := by
  have h : (Ideal.absNorm (Ideal.span {z}) : ℤ) =
      ShortDraftLatticeCount.q (ActualEisensteinCoordinates.coords z) := by
    rw [← ActualEisensteinCubic.qNat_eq_absNorm_span]
    exact Int.toNat_of_nonneg (ShortDraftLatticeCount.qO_nonneg z)
  rw [← Int.cast_natCast, h]
  exact ⟨_, ActualEisensteinCubic.coordinate_norm_eq_mul_conjO z⟩

theorem quotient_unit_of_norm_unit (z : O)
    (hz : IsUnit (Ideal.absNorm (Ideal.span {z}) : ZMod q)) :
    IsUnit (Ideal.Quotient.mk (modulus q) z) := by
  have hc := (ZMod.isUnit_iff_coprime _ _).mp hz
  have hi : IsCoprime (Ideal.absNorm (Ideal.span {z}) : O ⧸ modulus q) (q : O ⧸ modulus q) := by
    simpa only [map_natCast] using hc.isCoprime.map (Int.castRingHom (O ⧸ modulus q))
  rw [quotient_modulus_zero, isCoprime_zero_right] at hi
  obtain ⟨w, hw⟩ := norm_span_dvd z
  have hn : (Ideal.absNorm (Ideal.span {z}) : O ⧸ modulus q) =
      Ideal.Quotient.mk (modulus q) z * Ideal.Quotient.mk (modulus q) w := by
    rw [← map_mul, ← hw, map_natCast]
  rw [hn] at hi
  exact isUnit_of_mul_isUnit_left hi

def residue (χ : DirichletCharacter ℂ q) : MulChar (O ⧸ modulus q) ℂ where
  toFun x := Quotient.liftOn' x (InitialMeanSquare.normCharacter χ) (by
    intro a b hab
    exact CanonicalCoefficientClass.normCharacter_factorsModulo χ a b
      ((modulus q).quotientRel_def.mp hab))
  map_one' := (InitialMeanSquare.normCharacter χ).map_one
  map_mul' x y := by
    refine Quotient.inductionOn₂' x y ?_
    intro a b
    exact (InitialMeanSquare.normCharacter χ).map_mul a b
  map_nonunit' x hx := by
    refine Quotient.inductionOn' x (fun z hz => ?_) hx
    change χ (Ideal.absNorm (Ideal.span {z})) = 0
    apply MulChar.map_nonunit
    exact fun h => hz (quotient_unit_of_norm_unit z h)

@[simp] theorem residue_mk (χ : DirichletCharacter ℂ q) (z : O) :
    residue χ (Ideal.Quotient.mk (modulus q) z) = χ (Ideal.absNorm (Ideal.span {z})) := rfl

theorem residue_unit_trivial (χ : DirichletCharacter ℂ q) (u : Oˣ) :
    residue χ (Ideal.Quotient.mk (modulus q) (u : O)) = 1 := by
  rw [residue_mk, Ideal.span_singleton_eq_top.mpr u.isUnit, Ideal.absNorm_top]
  simp

variable [NeZero q]

def character (χ : DirichletCharacter ℂ q) : Character :=
  Character.ofResidue (modulus q) modulus_ne_bot (residue χ) (residue_unit_trivial χ)

@[simp] theorem elementCoeff_character (χ : DirichletCharacter ℂ q) (z : O) :
    elementCoeff (character χ) z = χ (Ideal.absNorm (Ideal.span {z})) := rfl

theorem idealCoeff_character (χ : DirichletCharacter ℂ q) (I : Ideal O) (hI : I ≠ 0) :
    idealCoeff (character χ) I = χ (Ideal.absNorm I) := by
  rw [← ConcretePrimeRowBridge.span_idealGenerator I]
  rw [idealCoeff_span _ (ConcretePrimeRowBridge.idealGenerator_ne_zero I hI),
    elementCoeff_character, ConcretePrimeRowBridge.span_idealGenerator]

theorem moebius_idealCoeff_character (χ : DirichletCharacter ℂ q) (I : Ideal O) :
    (UniqueFactorizationMonoid.moebius I : ℂ) * idealCoeff (character χ) I =
      ShortDraftHeckeBridge.baseChangeWeight χ I := by
  by_cases hI : I = 0
  · subst I
    unfold ShortDraftHeckeBridge.baseChangeWeight
    rw [UniqueFactorizationMonoid.moebius_zero]
    simp
  · rw [idealCoeff_character χ I hI]
    rfl

theorem inverseSeries_eq_pairInverse_LSeries (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    IdealEuler.inverseSeries (idealCoeff (character χ)) s =
      LSeries (ShortDraftHeckeBridge.pairInverseCoeff χ (ShortDraftHeckeBridge.baseChangeChar χ)) s := by
  rw [IdealEuler.inverseSeries]
  have ht (I : Ideal O) : (UniqueFactorizationMonoid.moebius I : ℂ) *
      IdealEuler.weighted (idealCoeff (character χ)) s I =
      ShortDraftHeckeBridge.baseChangeWeight χ I * CubicEisenstein.fullIdealWeight s I := by
    change (UniqueFactorizationMonoid.moebius I : ℂ) *
      (idealCoeff (character χ) I * CubicEisenstein.fullIdealWeight s I) = _
    rw [← mul_assoc, moebius_idealCoeff_character]
  simp_rw [ht]
  rw [SmoothMobiusCorrection.idealDirichlet_eq_LSeries _
    (ConcretePrimeRowBridge.baseChangeWeight_norm_le_one χ) s hs]
  exact ShortDraftHeckeBridge.normFiber_LSeries_eq_pair_inverse χ
    (ShortDraftHeckeBridge.baseChangeChar χ) _
    (ShortDraftHeckeBridge.normFiberCoeff_baseChange_eq_pairInverseCoeff χ) s

theorem LFunction_eq_dirichlet_product_right (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LFunction (character χ) s = χ.LFunction s *
      (ShortDraftHeckeBridge.baseChangeChar χ).LFunction s := by
  have hH := inverseSeries_mul_LFunction (character χ) hs
  have hD := ShortDraftHeckeBridge.pair_inverse_euler_identity χ
    (ShortDraftHeckeBridge.baseChangeChar χ) s hs
  rw [inverseSeries_eq_pairInverse_LSeries χ hs] at hH
  have hne : LSeries (ShortDraftHeckeBridge.pairInverseCoeff χ
      (ShortDraftHeckeBridge.baseChangeChar χ)) s ≠ 0 := by
    intro h
    rw [h, zero_mul] at hH
    exact zero_ne_one hH
  apply mul_left_cancel₀ hne
  rw [hH, mul_comm, hD]

theorem LFunction_eq_dirichlet_product (χ : DirichletCharacter ℂ q)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    LFunction (character χ) s = χ.LFunction s *
      (ShortDraftHeckeBridge.baseChangeChar χ).LFunction s := by
  let U : Set ℂ := {0,1}ᶜ
  have hU : IsOpen U := (Set.toFinite ({0,1} : Set ℂ)).isClosed.isOpen_compl
  have hpc : IsPreconnected U :=
    ((Set.toFinite ({0,1} : Set ℂ)).countable.isConnected_compl_of_one_lt_rank
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat)).isPreconnected
  have hmem : s ∈ U := by simp [U, h0, h1]
  have htwo : (2 : ℂ) ∈ U := by norm_num [U]
  apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    (f := LFunction (character χ))
    (g := fun z => χ.LFunction z * (ShortDraftHeckeBridge.baseChangeChar χ).LFunction z)
    _ _ hpc htwo _ hmem
  · apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    have hz' : z ≠ 0 ∧ z ≠ 1 := by simpa [U] using hz
    exact (LFunction_differentiableAt _ hz'.1 (Or.inl hz'.2)).differentiableWithinAt
  · apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    have hz' : z ≠ 1 := by simp only [U, Set.mem_compl_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hz; exact hz.2
    exact ((χ.differentiableAt_LFunction z (Or.inl hz')).mul
      ((ShortDraftHeckeBridge.baseChangeChar χ).differentiableAt_LFunction z
        (Or.inl hz'))).differentiableWithinAt
  · filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    exact LFunction_eq_dirichlet_product_right χ hz

theorem dirichlet_seven_eighths_of_hecke
    (hH : ∀ (η : Character) (s : ℂ), (7/8 : ℝ) < s.re →
      (s ≠ 1 ∨ η.residue ≠ 1) → LFunction η s ≠ 0)
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : (7/8 : ℝ) < s.re)
    (hexc : ¬ (χ = 1 ∧ s = 1)) : χ.LFunction s ≠ 0 := by
  by_cases hge : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp hexc) hge
  have hs1 : s ≠ 1 := by intro h; simp [h] at hge
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have h := hH (character χ) s hs (Or.inl hs1)
  rw [LFunction_eq_dirichlet_product χ hs0 hs1] at h
  exact (mul_ne_zero_iff.mp h).1

theorem zeta_seven_eighths_of_hecke
    (hH : ∀ (η : Character) (s : ℂ), (7/8 : ℝ) < s.re →
      (s ≠ 1 ∨ η.residue ≠ 1) → LFunction η s ≠ 0)
    (s : ℂ) (hs : (7/8 : ℝ) < s.re) : riemannZeta s ≠ 0 := by
  by_cases h1 : s = 1
  · simpa [h1] using riemannZeta_one_ne_zero
  have h := dirichlet_seven_eighths_of_hecke hH (1 : DirichletCharacter ℂ 1) s hs
    (by simp [h1])
  simpa only [DirichletCharacter.LFunction_modOne_eq] using h

end SevenEighths.HeckeDirichlet

end

end OAI

end


