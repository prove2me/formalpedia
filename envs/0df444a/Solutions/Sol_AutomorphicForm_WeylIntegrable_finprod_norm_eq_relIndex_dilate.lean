-- Prove2me | solution 1 for AutomorphicForm.WeylIntegrable.finprod_norm_eq_relIndex_dilate
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/f47eff2a-01da-5d46-a075-30cd1fc4e3a9

import Definitions.Def_AutomorphicForm_WeylSelectors
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_WeylIntegrable_finprod_norm_eq_relIndex_dilate
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec"

set_option autoImplicit false

noncomputable section

section Lattices

open NumberField NumberField.AdelicBox IsDedekindDomain AutomorphicForm.WeylIntegrable
open scoped Classical

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F
local notation "HOS" => HeightOneSpectrum (𝓞 F)

private theorem finiteAdele_mul_apply (a b : 𝔸f) (v : HOS) : (a * b) v = a v * b v := rfl

private theorem mem_intLattice_iff_valued (t : 𝔸f) : t ∈ intLattice F ↔ ∀ v, Valued.v (t v) ≤ 1 := Iff.rfl

private theorem mem_integralFiniteAdeles_iff_valued (t : 𝔸f) :
    t ∈ integralFiniteAdeles (𝓞 F) F ↔ ∀ v, Valued.v (t v) ≤ 1 := Iff.rfl

private theorem valued_unit_apply_ne_zero (y : (𝔸f)ˣ) (v : HOS) : Valued.v ((y : 𝔸f) v) ≠ 0 := by
  intro h
  have h1 : Valued.v (((y : 𝔸f) * ((y⁻¹ : (𝔸f)ˣ) : 𝔸f)) v) = 1 := by rw [Units.mul_inv]; exact map_one _
  rw [finiteAdele_mul_apply, map_mul, h, zero_mul] at h1
  exact zero_ne_one h1

private theorem mem_dilate_iff_valued (y : (𝔸f)ˣ) (t : 𝔸f) :
    t ∈ dilate F y ↔ ∀ v, Valued.v (t v) ≤ Valued.v ((y : 𝔸f) v) := by
  rw [← SetLike.mem_coe, coe_dilate, Set.mem_smul_set]
  constructor
  · rintro ⟨s, hs, rfl⟩ v
    rw [smul_eq_mul, finiteAdele_mul_apply, map_mul]
    exact mul_le_of_le_one_right' ((mem_integralFiniteAdeles_iff_valued F s).mp hs v)
  · intro h
    refine ⟨((y⁻¹ : (𝔸f)ˣ) : 𝔸f) * t, (mem_integralFiniteAdeles_iff_valued F _).mpr fun v => ?_, ?_⟩
    · rw [finiteAdele_mul_apply, map_mul]
      have hy := valued_unit_apply_ne_zero F y v
      have hyv : (y : 𝔸f) v * ((y⁻¹ : (𝔸f)ˣ) : 𝔸f) v = 1 := by rw [← finiteAdele_mul_apply, Units.mul_inv]; rfl
      have hinv : Valued.v (((y⁻¹ : (𝔸f)ˣ) : 𝔸f) v) = (Valued.v ((y : 𝔸f) v))⁻¹ := by
        rw [← inv_eq_of_mul_eq_one_right hyv, map_inv₀]
      rw [hinv]
      calc (Valued.v ((y : 𝔸f) v))⁻¹ * Valued.v (t v) ≤ (Valued.v ((y : 𝔸f) v))⁻¹ * Valued.v ((y : 𝔸f) v) :=
            mul_le_mul' le_rfl (h v)
        _ = 1 := inv_mul_cancel₀ hy
    · show (y : 𝔸f) * (((y⁻¹ : (𝔸f)ˣ) : 𝔸f) * t) = t
      rw [← mul_assoc, Units.mul_inv, one_mul]

private theorem intLattice_le_dilate_of_one_le {y : (𝔸f)ˣ} (hy : ∀ v, 1 ≤ Valued.v ((y : 𝔸f) v)) :
    intLattice F ≤ dilate F y := fun t ht =>
  (mem_dilate_iff_valued F y t).mpr fun v => (((mem_intLattice_iff_valued F t).mp ht v).trans (hy v))

private theorem isCompact_coe_dilate (y : (𝔸f)ˣ) : IsCompact (dilate F y : Set 𝔸f) := by
  rw [coe_dilate]
  exact (isCompact_integralFiniteAdeles F).image (continuous_const.mul continuous_id)

private theorem relIndex_intLattice_dilate_ne_zero (y : (𝔸f)ˣ) : (intLattice F).relIndex (dilate F y) ≠ 0 := by
  haveI : CompactSpace (dilate F y) := isCompact_iff_compactSpace.mp (isCompact_coe_dilate F y)
  have hopen : IsOpen (((intLattice F).addSubgroupOf (dilate F y) : AddSubgroup (dilate F y)) : Set (dilate F y)) :=
    (isOpen_integralFiniteAdeles F).preimage continuous_subtype_val
  haveI := AddSubgroup.quotient_finite_of_isOpen _ hopen
  exact AddSubgroup.index_ne_zero_of_finite

end Lattices

section Slabs

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox IsDedekindDomain AutomorphicForm.WeylIntegrable

open scoped ENNReal NNReal Pointwise

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

private def fibreSlab (S : Set 𝔸∞) (T : Set 𝔸f) : Set 𝔸 := {x | x.1 ∈ S ∧ x.2 ∈ T}

private theorem mem_fibreSlab {S : Set 𝔸∞} {T : Set 𝔸f} {x : 𝔸} : x ∈ fibreSlab F S T ↔ x.1 ∈ S ∧ x.2 ∈ T := Iff.rfl

private theorem isClosed_fibreSlab {S : Set 𝔸∞} {T : Set 𝔸f} (hS : IsClosed S) (hT : IsClosed T) :
    IsClosed (fibreSlab F S T) :=
  (hS.preimage continuous_fst).inter (hT.preimage continuous_snd)

private theorem vadd_fibreSlab (S : Set 𝔸∞) (T : Set 𝔸f) (c : 𝔸f) :
    toAdele' F 0 c +ᵥ fibreSlab F S T = fibreSlab F S (c +ᵥ T) := by
  ext x
  simp only [Set.mem_vadd_set, mem_fibreSlab, vadd_eq_add]
  constructor
  · rintro ⟨z, ⟨hz1, hz2⟩, rfl⟩
    have h1 : (toAdele' F 0 c + z).1 = z.1 := show (0 : 𝔸∞) + z.1 = z.1 from zero_add _
    have h2 : (toAdele' F 0 c + z).2 = c + z.2 := rfl
    rw [h1, h2]
    exact ⟨hz1, z.2, hz2, rfl⟩
  · rintro ⟨hx1, ⟨t, ht, hxt⟩⟩
    refine ⟨toAdele' F x.1 t, ⟨hx1, ht⟩, Prod.ext ?_ ?_⟩
    · show (0 : 𝔸∞) + x.1 = x.1
      rw [zero_add]
    · show c + t = x.2
      exact hxt

private theorem measure_fibreSlab_eq_relIndex_mul (μ : Measure 𝔸) [μ.IsAddLeftInvariant] {S : Set 𝔸∞}
    (hS : IsClosed S) (A B : AddSubgroup 𝔸f) (hAB : A ≤ B) (hA : IsClosed (A : Set 𝔸f)) (hfin : A.relIndex B ≠ 0) :
    μ (fibreSlab F S B) = A.relIndex B * μ (fibreSlab F S A) := by
  classical
  set H : AddSubgroup B := A.addSubgroupOf B with hH
  haveI : H.FiniteIndex := ⟨hfin⟩
  obtain ⟨s, hs, -⟩ := H.exists_isComplement_left 0
  haveI : Finite s := hs.finite_left_iff.mpr inferInstance
  have hcard : Nat.card s = A.relIndex B := hs.card_left
  have hcover : (B : Set 𝔸f) = ⋃ c : s, ((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f) := by
    ext b
    simp only [Set.mem_iUnion, Set.mem_vadd_set, SetLike.mem_coe]
    constructor
    · intro hb
      have hmem : (⟨b, hb⟩ : B) ∈ (Set.univ : Set B) := Set.mem_univ _
      rw [← hs.add_eq] at hmem
      obtain ⟨c, hc, h, hh, hsum⟩ := Set.mem_add.mp hmem
      refine ⟨⟨c, hc⟩, (h : 𝔸f), ?_, ?_⟩
      · exact AddSubgroup.mem_addSubgroupOf.mp hh
      · exact congrArg Subtype.val hsum
    · rintro ⟨c, a, ha, rfl⟩
      exact B.add_mem (c : B).2 (hAB ha)
  have hdisj : Pairwise fun c c' : s =>
      Disjoint (((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f)) (((c' : B) : 𝔸f) +ᵥ (A : Set 𝔸f)) := by
    intro c c' hcc'
    have hd : Disjoint ((c : B) +ᵥ (H : Set B)) ((c' : B) +ᵥ (H : Set B)) :=
      hs.pairwiseDisjoint_vadd c.2 c'.2 (fun h => hcc' (Subtype.ext h))
    rw [Set.disjoint_iff_forall_ne]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩ heq
    have haB : a ∈ B := hAB ha
    have ha'B : a' ∈ B := hAB ha'
    refine hd.ne_of_mem (Set.mem_vadd_set.mpr ⟨⟨a, haB⟩, AddSubgroup.mem_addSubgroupOf.mpr ha, rfl⟩)
      (Set.mem_vadd_set.mpr ⟨⟨a', ha'B⟩, AddSubgroup.mem_addSubgroupOf.mpr ha', rfl⟩) ?_
    exact Subtype.ext heq
  have hslab : fibreSlab F S B = ⋃ c : s, fibreSlab F S (((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f)) := by
    ext x
    simp only [mem_fibreSlab, hcover, Set.mem_iUnion]
    exact ⟨fun ⟨h1, c, h2⟩ => ⟨c, h1, h2⟩, fun ⟨c, h1, h2⟩ => ⟨h1, c, h2⟩⟩
  have hmeasA : MeasurableSet (fibreSlab F S (A : Set 𝔸f)) := (isClosed_fibreSlab F hS hA).measurableSet
  have hmeas : ∀ c : s, MeasurableSet (fibreSlab F S (((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f))) := fun c => by
    rw [← vadd_fibreSlab]; exact hmeasA.const_vadd _
  have hdisj' : Pairwise fun c c' : s => Disjoint (fibreSlab F S (((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f)))
      (fibreSlab F S (((c' : B) : 𝔸f) +ᵥ (A : Set 𝔸f))) := by
    intro c c' hcc'
    rw [Set.disjoint_iff_forall_ne]
    rintro x ⟨-, hx⟩ x' ⟨-, hx'⟩ rfl
    exact Set.disjoint_iff_forall_ne.mp (hdisj hcc') hx hx' rfl
  have hconst : ∀ c : s, μ (fibreSlab F S (((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f))) = μ (fibreSlab F S A) := fun c => by
    rw [← vadd_fibreSlab, measure_vadd]
  rw [hslab, measure_iUnion hdisj' hmeas, tsum_congr hconst]
  haveI := Fintype.ofFinite s
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard, nsmul_eq_mul]

end Slabs

section Modulus

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox IsDedekindDomain AutomorphicForm.WeylIntegrable

open scoped ENNReal NNReal Pointwise

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

private def finiteIdele (y : (𝔸f)ˣ) : (𝔸)ˣ where
  val := toAdele' F 1 (y : 𝔸f)
  inv := toAdele' F 1 ((y⁻¹ : (𝔸f)ˣ) : 𝔸f)
  val_inv := Prod.ext (show (1 : 𝔸∞) * 1 = 1 from one_mul 1)
    (show (y : 𝔸f) * ((y⁻¹ : (𝔸f)ˣ) : 𝔸f) = 1 from Units.mul_inv y)
  inv_val := Prod.ext (show (1 : 𝔸∞) * 1 = 1 from one_mul 1)
    (show ((y⁻¹ : (𝔸f)ˣ) : 𝔸f) * (y : 𝔸f) = 1 from Units.inv_mul y)

private theorem finiteIdele_smul_fibreSlab (y : (𝔸f)ˣ) (S : Set 𝔸∞) (T : Set 𝔸f) :
    finiteIdele F y • fibreSlab F S T = fibreSlab F S ((y : 𝔸f) • T) := by
  ext x
  simp only [Set.mem_smul_set, mem_fibreSlab]
  constructor
  · rintro ⟨z, ⟨hz1, hz2⟩, rfl⟩
    have h1 : (finiteIdele F y • z).1 = z.1 := show (1 : 𝔸∞) * z.1 = z.1 from one_mul _
    have h2 : (finiteIdele F y • z).2 = (y : 𝔸f) * z.2 := rfl
    rw [h1, h2]
    exact ⟨hz1, z.2, hz2, rfl⟩
  · rintro ⟨hx1, ⟨t, ht, hxt⟩⟩
    refine ⟨toAdele' F x.1 t, ⟨hx1, ht⟩, Prod.ext ?_ ?_⟩
    · show (1 : 𝔸∞) * x.1 = x.1
      rw [one_mul]
    · show (y : 𝔸f) * t = x.2
      exact hxt

private theorem distribHaarChar_finiteIdele (y : (𝔸f)ˣ) (hy : intLattice F ≤ dilate F y)
    (hfin : (intLattice F).relIndex (dilate F y) ≠ 0) :
    (distribHaarChar 𝔸 (finiteIdele F y) : ℝ≥0∞) = (intLattice F).relIndex (dilate F y) := by
  obtain ⟨S, hScpt, hSnhds⟩ := exists_compact_mem_nhds (0 : 𝔸∞)
  have hSclosed : IsClosed S := hScpt.isClosed
  have hZclosed : IsClosed (integralFiniteAdeles (𝓞 F) F) := isClosed_integralFiniteAdeles F
  have hZopen : IsOpen (integralFiniteAdeles (𝓞 F) F) := isOpen_integralFiniteAdeles F
  have hZcpt : IsCompact (integralFiniteAdeles (𝓞 F) F) := isCompact_integralFiniteAdeles F
  set μ : Measure 𝔸 := adelicAddHaar (𝓞 F) F
  have hpos : 0 < μ (fibreSlab F S (integralFiniteAdeles (𝓞 F) F)) := by
    have hU : IsOpen (fibreSlab F (interior S) (integralFiniteAdeles (𝓞 F) F)) :=
      (isOpen_interior.preimage continuous_fst).inter (hZopen.preimage continuous_snd)
    have hne : (fibreSlab F (interior S) (integralFiniteAdeles (𝓞 F) F)).Nonempty :=
      ⟨((0 : 𝔸∞), (0 : 𝔸f)), mem_interior_iff_mem_nhds.mpr hSnhds, (intLattice F).zero_mem⟩
    exact (hU.measure_pos μ hne).trans_le (measure_mono fun x ⟨h1, h2⟩ => ⟨interior_subset h1, h2⟩)
  have hlt : μ (fibreSlab F S (integralFiniteAdeles (𝓞 F) F)) < ∞ := by
    have hc : IsCompact (fibreSlab F S (integralFiniteAdeles (𝓞 F) F)) := by
      have : fibreSlab F S (integralFiniteAdeles (𝓞 F) F)
          = (fun p : 𝔸∞ × 𝔸f => (p : 𝔸)) '' (S ×ˢ integralFiniteAdeles (𝓞 F) F) := by
        ext x
        simp only [mem_fibreSlab]
        exact ⟨fun ⟨h1, h2⟩ => ⟨(x.1, x.2), ⟨h1, h2⟩, rfl⟩, by rintro ⟨p, ⟨h1, h2⟩, rfl⟩; exact ⟨h1, h2⟩⟩
      rw [this]
      exact (hScpt.prod hZcpt).image continuous_id
    exact hc.measure_lt_top
  haveI : μ.Regular := by
    show (adelicAddHaar (𝓞 F) F).Regular
    unfold adelicAddHaar
    infer_instance
  have h := distribHaarChar_mul μ (finiteIdele F y) (fibreSlab F S (integralFiniteAdeles (𝓞 F) F))
  rw [finiteIdele_smul_fibreSlab, ← coe_dilate, ← coe_intLattice,
    measure_fibreSlab_eq_relIndex_mul F μ hSclosed (intLattice F) (dilate F y) hy hZclosed hfin] at h
  exact (ENNReal.mul_left_inj hpos.ne' hlt.ne).mp h

private theorem prod_norm_finiteIdele_fst (y : (𝔸f)ˣ) :
    (∏ w : InfinitePlace F, ‖((finiteIdele F y : (𝔸)ˣ) : 𝔸).1 w‖ ^ w.mult) = 1 :=
  Finset.prod_eq_one fun w _ => by
    show ‖((finiteIdele F y : (𝔸)ˣ) : 𝔸).1 w‖ ^ w.mult = 1
    have h1 : ((finiteIdele F y : (𝔸)ˣ) : 𝔸).1 w = 1 := rfl
    rw [h1, norm_one, one_pow]

private theorem coe_distribHaarChar_finiteIdele_eq_finprod (y : (𝔸f)ˣ) :
    (distribHaarChar 𝔸 (finiteIdele F y) : ℝ) = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(y : 𝔸f) v‖ :=
  calc (distribHaarChar 𝔸 (finiteIdele F y) : ℝ)
      = (∏ w : InfinitePlace F, ‖((finiteIdele F y : (𝔸)ˣ) : 𝔸).1 w‖ ^ w.mult)
          * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖((finiteIdele F y : (𝔸)ˣ) : 𝔸).2 v‖ :=
        NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm F (finiteIdele F y)
    _ = 1 * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(y : 𝔸f) v‖ :=
        congrArg (fun t : ℝ => t * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(y : 𝔸f) v‖) (prod_norm_finiteIdele_fst F y)
    _ = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(y : 𝔸f) v‖ := one_mul _

private theorem coe_distribHaarChar_finiteIdele_eq_relIndex (y : (𝔸f)ˣ) (hy : ∀ v, 1 ≤ Valued.v ((y : 𝔸f) v)) :
    (distribHaarChar 𝔸 (finiteIdele F y) : ℝ) = ((intLattice F).relIndex (dilate F y) : ℝ) := by
  have h1 : (distribHaarChar 𝔸 (finiteIdele F y) : ℝ≥0∞)
      = (((intLattice F).relIndex (dilate F y) : ℝ≥0) : ℝ≥0∞) :=
    (distribHaarChar_finiteIdele F y (intLattice_le_dilate_of_one_le F hy)
      (relIndex_intLattice_dilate_ne_zero F y)).trans (ENNReal.coe_natCast _).symm
  have h2 : distribHaarChar 𝔸 (finiteIdele F y) = ((intLattice F).relIndex (dilate F y) : ℝ≥0) := ENNReal.coe_inj.mp h1
  calc (distribHaarChar 𝔸 (finiteIdele F y) : ℝ) = (((intLattice F).relIndex (dilate F y) : ℝ≥0) : ℝ) :=
        congrArg NNReal.toReal h2
    _ = ((intLattice F).relIndex (dilate F y) : ℝ) := NNReal.coe_natCast _

end Modulus

section Solution

open AutomorphicForm.WeylIntegrable

theorem solution (F : Type) [Field F] [NumberField F]
    (y : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ)
    (hy : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      1 ≤ Valued.v ((y : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) v)) :
    ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
        ‖(y : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) v‖
      = ((intLattice F).relIndex (dilate F y) : ℝ) :=
  (coe_distribHaarChar_finiteIdele_eq_finprod F y).symm.trans (coe_distribHaarChar_finiteIdele_eq_relIndex F y hy)

end Solution

end

end S_AutomorphicForm_WeylIntegrable_finprod_norm_eq_relIndex_dilate
end P2MW
export P2MW.S_AutomorphicForm_WeylIntegrable_finprod_norm_eq_relIndex_dilate (solution)
