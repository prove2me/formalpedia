-- Prove2me | solution 1 for AlgebraicCurve.exists_regularProlongation_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/6d38db53-d22e-579c-8f3c-9cc00b4fca00

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ValuationSubring_exists_regularProlongation_ratFunc
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_regularProlongation_of_transcendental

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_regularProlongation_of_transcendental.AlgebraicCurve IsLocalRing Polynomial"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "RegularProlongation"
namespace RegularProlongation
p2m_export "AlgebraicCurve.RegularProlongation" "isUnit_of_residue_ne_zero residue_ne_zero_of_isUnit integers residue_algebraMap residue_surjective algebraMap_mem_iff exists_smul_mem ker_residue residue"
namespace ExistsOfTranscendental
p2m_open "AlgebraicCurve.RegularProlongation AlgebraicCurve"

theorem exists_ne_map_eq_of_sum_eq_zero {K Γ₀ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {t : ι → K} (hs : s.Nonempty) (ht : ∀ i ∈ s, t i ≠ 0)
    (hsum : ∑ i ∈ s, t i = 0) : ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ v (t i) = v (t j) := by
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun i => v (t i)) hs
  by_contra hcon
  push Not at hcon
  have hlt : ∀ i ∈ s \ {j}, v (t i) < v (t j) := by
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    exact lt_of_le_of_ne (hmax i hi.1) (hcon i hi.1 j hj hi.2)
  have h := v.map_sum_eq_of_lt hj hlt
  rw [hsum, map_zero] at h
  exact ht j hj ((v.zero_iff).mp h.symm)

section Transport

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fb₀ : Type*} [Field Fb₀] [Algebra (ResidueField A) Fb₀]
variable (R₀ : RegularProlongation A (RatFunc L) Fb₀) (φ : RatFunc L →ₐ[L] F)
  (W : ValuationSubring F) (hW : ∀ x : R₀.integers, φ x ∈ W)

include hW in
theorem algebraMap_mem (a : A) : algebraMap L F a ∈ W := by
  have h : φ (algebraMap L (RatFunc L) a) ∈ W :=
    hW ⟨algebraMap L (RatFunc L) a, (R₀.algebraMap_mem_iff a).mpr a.2⟩
  rwa [φ.commutes] at h

def toW : A →+* W :=
  ((algebraMap L F).comp A.subtype).codRestrict W (fun a => algebraMap_mem R₀ φ W hW a)

@[scoped simp] theorem coe_toW (a : A) : (toW R₀ φ W hW a : F) = algebraMap L F a := rfl

def push : R₀.integers →+* W :=
  (φ.toRingHom.comp R₀.integers.subtype).codRestrict W (fun x => hW x)

@[scoped simp] theorem coe_push (x : R₀.integers) : (push R₀ φ W hW x : F) = φ x := rfl

theorem toW_eq_push (a : A) :
    toW R₀ φ W hW a =
      push R₀ φ W hW ⟨algebraMap L (RatFunc L) a, (R₀.algebraMap_mem_iff a).mpr a.2⟩ :=
  Subtype.ext (φ.commutes a).symm

include hW in

theorem exists_valuation_eq_of_mem_range {y : F} (hy : ∃ r, φ r = y) (hy0 : y ≠ 0) :
    ∃ d : L, d ≠ 0 ∧ W.valuation y = W.valuation (algebraMap L F d) := by
  obtain ⟨r, rfl⟩ := hy
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hy0 (map_zero φ)
  obtain ⟨c, hc, hres⟩ := R₀.exists_smul_mem r hr0
  have hu : IsUnit (⟨c • r, hc⟩ : R₀.integers) := R₀.isUnit_of_residue_ne_zero hres
  have hu' : IsUnit (push R₀ φ W hW ⟨c • r, hc⟩) := hu.map _
  rw [ValuationSubring.valuation_eq_one_iff] at hu'
  have h1 : W.valuation (algebraMap L F c) * W.valuation (φ r) = 1 := by
    rw [← map_mul, ← hu', coe_push]
    simp only [Algebra.smul_def, map_mul, AlgHom.commutes]
  have hc0 : W.valuation (algebraMap L F c) ≠ 0 := left_ne_zero_of_mul_eq_one h1
  refine ⟨c⁻¹, inv_ne_zero (fun h => hc0 (by rw [h, map_zero, map_zero])), ?_⟩
  rw [map_inv₀, map_inv₀]
  exact eq_inv_of_mul_eq_one_right h1

include hW in

theorem exists_smul_mem_of_isAlgebraic [IsAlgClosed L] (K : IntermediateField L F)
    (hrange : ∀ y ∈ K, ∃ r, φ r = y) [Algebra.IsAlgebraic K F] (g : F) (hg : g ≠ 0) :
    ∃ c : L, ∃ h : c • g ∈ W, IsLocalRing.residue W ⟨c • g, h⟩ ≠ 0 := by
  classical
  set v := W.valuation with hv
  obtain ⟨p, hp0, hpg⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := K) g : IsAlgebraic K g)
  have hsum : ∑ i ∈ p.support, (algebraMap K F (p.coeff i) * g ^ i) = 0 := by
    rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def] at hpg
    exact hpg
  have hs : p.support.Nonempty := Polynomial.support_nonempty.mpr hp0
  have hcoef : ∀ i ∈ p.support, algebraMap K F (p.coeff i) ≠ 0 := fun i hi =>
    (_root_.map_ne_zero _).mpr (Polynomial.mem_support_iff.mp hi)
  have ht : ∀ i ∈ p.support, algebraMap K F (p.coeff i) * g ^ i ≠ 0 := fun i hi =>
    mul_ne_zero (hcoef i hi) (pow_ne_zero _ hg)
  obtain ⟨i, hi, j, hj, hij, hvij⟩ := exists_ne_map_eq_of_sum_eq_zero v hs ht hsum
  have hvg0 : v g ≠ 0 := (v.ne_zero_iff).mpr hg
  have hmemK : ∀ c : K, algebraMap K F c ∈ K := fun c => c.2

  have key : ∀ i ∈ p.support, ∀ j ∈ p.support, i < j →
      v (algebraMap K F (p.coeff i) * g ^ i) = v (algebraMap K F (p.coeff j) * g ^ j) →
      ∃ c : L, ∃ h : c • g ∈ W, IsLocalRing.residue W ⟨c • g, h⟩ ≠ 0 := by
    intro i hi j hj hlt heq
    have ha0 := hcoef i hi
    have hb0 := hcoef j hj
    have hn : j - i ≠ 0 := (Nat.sub_pos_of_lt hlt).ne'

    have hpow : v g ^ (j - i) =
        v (algebraMap K F (p.coeff i) / algebraMap K F (p.coeff j)) := by
      rw [map_mul, map_mul, map_pow, map_pow] at heq
      have hsplit : v g ^ j = v g ^ i * v g ^ (j - i) := by
        rw [← pow_add, Nat.add_sub_cancel' hlt.le]
      rw [hsplit, ← mul_assoc] at heq
      have h2 : v (algebraMap K F (p.coeff i)) = v (algebraMap K F (p.coeff j)) * v g ^ (j - i) :=
        mul_right_cancel₀ (pow_ne_zero i hvg0) (heq.trans (mul_right_comm _ _ _))
      rw [map_div₀, eq_div_iff ((v.ne_zero_iff).mpr hb0), h2, mul_comm]
    have hab : ∃ r, φ r = algebraMap K F (p.coeff i) / algebraMap K F (p.coeff j) :=
      hrange _ (div_mem (hmemK _) (hmemK _))
    obtain ⟨d, hd0, hd⟩ :=
      exists_valuation_eq_of_mem_range R₀ φ W hW hab (div_ne_zero ha0 hb0)
    obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq d (Nat.sub_pos_of_lt hlt)
    have h1 : v (algebraMap L F (μ ^ (j - i))) = v (g ^ (j - i)) := by
      rw [hμ, ← hd, map_pow v g, ← hpow]
    simp only [map_pow] at h1
    have hvμ : v (algebraMap L F μ) = v g := (pow_left_inj hn).mp h1
    have hval : v (μ⁻¹ • g) = 1 := by
      rw [Algebra.smul_def, map_mul, map_inv₀, map_inv₀, hvμ, inv_mul_cancel₀ hvg0]
    have hmem : μ⁻¹ • g ∈ W := (W.valuation_le_one_iff _).mp hval.le
    refine ⟨μ⁻¹, hmem, ?_⟩
    rw [residue_ne_zero_iff_isUnit, ValuationSubring.valuation_eq_one_iff]
    exact hval
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact key i hi j hj hlt hvij
  · exact key j hj i hi hlt hvij.symm

variable (hloc : ∀ x : R₀.integers, IsUnit (push R₀ φ W hW x) → IsUnit x)

include hloc in
theorem isUnit_of_isUnit_toW (a : A) (ha : IsUnit (toW R₀ φ W hW a)) : IsUnit a := by
  rw [toW_eq_push] at ha
  have h1 := hloc _ ha
  have h2 := R₀.residue_ne_zero_of_isUnit h1
  rw [R₀.residue_algebraMap a] at h2
  have h3 : IsLocalRing.residue A a ≠ 0 := fun h0 => h2 (by rw [h0, map_zero])
  exact (residue_ne_zero_iff_isUnit a).mp h3

include hloc in
theorem isLocalHom_toW : IsLocalHom (toW R₀ φ W hW) :=
  ⟨isUnit_of_isUnit_toW R₀ φ W hW hloc⟩

include hloc in
private theorem _root_.AlgebraicCurve.RegularProlongation.ExistsOfTranscendental.algebraMap_mem_iff (x : L) : algebraMap L F x ∈ W ↔ x ∈ A := by
  refine ⟨fun hx => ?_, fun hx => algebraMap_mem R₀ φ W hW ⟨x, hx⟩⟩
  by_contra hxA
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxA A.zero_mem
  have hinv : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hxA
  have hu : IsUnit (toW R₀ φ W hW ⟨x⁻¹, hinv⟩) := by
    refine IsUnit.of_mul_eq_one ⟨algebraMap L F x, hx⟩ (Subtype.ext ?_)
    change algebraMap L F x⁻¹ * algebraMap L F x = 1
    rw [map_inv₀, inv_mul_cancel₀ ((_root_.map_ne_zero _).mpr hx0)]
  have hu' := isUnit_of_isUnit_toW R₀ φ W hW hloc _ hu
  rw [ValuationSubring.valuation_eq_one_iff] at hu'
  apply hxA
  rw [← A.valuation_le_one_iff]
  have h : A.valuation x⁻¹ = 1 := hu'
  rw [map_inv₀, inv_eq_one] at h
  exact h.le

p2m_export "AlgebraicCurve.RegularProlongation.ExistsOfTranscendental" "algebraMap_mem_iff"

@[reducible] def residueAlgebra : Algebra (ResidueField A) (ResidueField W) :=
  haveI := isLocalHom_toW R₀ φ W hW hloc
  (ResidueField.map (toW R₀ φ W hW)).toAlgebra

def prolongation [IsAlgClosed L] (K : IntermediateField L F)
    (hrange : ∀ y ∈ K, ∃ r, φ r = y) [Algebra.IsAlgebraic K F] :
    letI := residueAlgebra R₀ φ W hW hloc
    RegularProlongation A F (ResidueField W) := by
  letI := residueAlgebra R₀ φ W hW hloc
  exact
    { integers := W
      residue := IsLocalRing.residue W
      algebraMap_mem_iff := algebraMap_mem_iff R₀ φ W hW hloc
      residue_surjective := IsLocalRing.residue_surjective
      ker_residue := IsLocalRing.ker_residue
      residue_algebraMap := fun _ => rfl
      exists_smul_mem := exists_smul_mem_of_isAlgebraic R₀ φ W hW K hrange }

end Transport

end AlgebraicCurve.RegularProlongation.ExistsOfTranscendental
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_regularProlongation_of_transcendental.AlgebraicCurve P2MW.S_AlgebraicCurve_exists_regularProlongation_of_transcendental.AlgebraicCurve.RegularProlongation P2MW.S_AlgebraicCurve_exists_regularProlongation_of_transcendental.AlgebraicCurve.RegularProlongation.ExistsOfTranscendental"
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_regularProlongation_of_transcendental.AlgebraicCurve P2MW.S_AlgebraicCurve_exists_regularProlongation_of_transcendental.AlgebraicCurve.RegularProlongation"
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_regularProlongation_of_transcendental.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_regularProlongation_of_transcendental.AlgebraicCurve P2MW.S_AlgebraicCurve_exists_regularProlongation_of_transcendental.AlgebraicCurve.RegularProlongation P2MW.S_AlgebraicCurve_exists_regularProlongation_of_transcendental.AlgebraicCurve.RegularProlongation.ExistsOfTranscendental"

open AlgebraicCurve.RegularProlongation.ExistsOfTranscendental in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    (f : F) (htrL : Transcendental L f)
    [Algebra.IsAlgebraic (IntermediateField.adjoin L ({f} : Set F)) F] :
    ∃ (W : ValuationSubring F)
      (_ : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField W))
      (R : RegularProlongation A F (IsLocalRing.ResidueField W)),
      R.integers = W ∧ ∃ hfR : f ∈ R.integers,
        Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hfR⟩) := by
  classical
  obtain ⟨R₀, ⟨hX, -⟩, hpoly⟩ := ValuationSubring.exists_regularProlongation_ratFunc A
  set K : IntermediateField L F := IntermediateField.adjoin L ({f} : Set F) with hK

  let e : RatFunc L ≃ₐ[L] K := RatFunc.algEquivOfTranscendental f htrL
  let φ : RatFunc L →ₐ[L] F := K.val.comp e.toAlgHom
  have hφX : φ RatFunc.X = f := by
    change ((e RatFunc.X : K) : F) = f
    exact RatFunc.algEquivOfTranscendental_X f htrL
  have hrange : ∀ y ∈ K, ∃ r, φ r = y := fun y hy => ⟨e.symm ⟨y, hy⟩, by simp [φ]⟩
  have hcomp : φ.comp (IsScalarTower.toAlgHom L L[X] (RatFunc L)) = aeval f :=
    Polynomial.algHom_ext (by simp [hφX])
  have hφpoly : ∀ q : L[X], φ (algebraMap L[X] (RatFunc L) q) = aeval f q := fun q => by
    rw [← hcomp]
    rfl

  obtain ⟨W, hWmem, hWloc⟩ :=
    IsLocalRing.exists_factor_valuationRing (φ.toRingHom.comp R₀.integers.subtype)
  have hW : ∀ x : R₀.integers, φ x ∈ W := fun x => hWmem x
  have hloc : ∀ x : R₀.integers, IsUnit (push R₀ φ W hW x) → IsUnit x :=
    fun x hx => hWloc.map_nonunit x hx
  letI alg : Algebra (ResidueField A) (ResidueField W) := residueAlgebra R₀ φ W hW hloc
  have hfW : f ∈ W := by simpa [hφX] using hW ⟨RatFunc.X, hX⟩

  refine ⟨W, alg, prolongation R₀ φ W hW hloc K hrange, rfl, hfW, ?_⟩

  show Transcendental (ResidueField A) (IsLocalRing.residue W ⟨f, hfW⟩)
  rintro ⟨q, hq0, hq⟩
  obtain ⟨P, rfl⟩ :=
    Polynomial.map_surjective (IsLocalRing.residue A) IsLocalRing.residue_surjective q
  obtain ⟨hPmem, hPres⟩ := hpoly P
  set u₀ : R₀.integers := ⟨algebraMap L[X] (RatFunc L) (P.map A.subtype), hPmem⟩ with hu₀def
  have hu₀ : IsUnit u₀ := by
    apply R₀.isUnit_of_residue_ne_zero
    rw [hPres]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hq0
  have hu : IsUnit (push R₀ φ W hW u₀) := hu₀.map _
  have hWcomp : W.subtype.comp (toW R₀ φ W hW) = (algebraMap L F).comp A.subtype :=
    RingHom.ext fun _ => rfl
  have hy : push R₀ φ W hW u₀ = P.eval₂ (toW R₀ φ W hW) ⟨f, hfW⟩ := by
    apply Subtype.ext
    rw [coe_push]
    change φ (algebraMap L[X] (RatFunc L) (P.map A.subtype)) =
      W.subtype (P.eval₂ (toW R₀ φ W hW) ⟨f, hfW⟩)
    rw [Polynomial.hom_eval₂, hWcomp, hφpoly, aeval_def, Polynomial.eval₂_map]
    rfl
  rw [hy] at hu
  have hres_ne : IsLocalRing.residue W (P.eval₂ (toW R₀ φ W hW) ⟨f, hfW⟩) ≠ 0 :=
    (residue_ne_zero_iff_isUnit _).mpr hu
  have hkcomp : (IsLocalRing.residue W).comp (toW R₀ φ W hW) =
      (algebraMap (ResidueField A) (ResidueField W)).comp (IsLocalRing.residue A) :=
    RingHom.ext fun _ => rfl
  rw [Polynomial.hom_eval₂, hkcomp, ← Polynomial.eval₂_map, ← aeval_def] at hres_ne
  exact hres_ne hq

end S_AlgebraicCurve_exists_regularProlongation_of_transcendental
end P2MW
export P2MW.S_AlgebraicCurve_exists_regularProlongation_of_transcendental (solution)
