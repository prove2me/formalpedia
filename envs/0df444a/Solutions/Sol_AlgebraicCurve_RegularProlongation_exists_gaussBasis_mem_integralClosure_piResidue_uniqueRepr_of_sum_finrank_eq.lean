-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/0d92b7be-1ddb-5fa0-beca-27c8bf1f1240

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_finrank_adjoin_residue_le
import Theorems.Thm_AlgebraicCurve_RegularProlongation_mem_adjoin_iff_mem_integers_iff_of_transcendental_residue
import Theorems.Thm_ValuationSubring_exists_forall_mem_and_sub_mem_nonunits
import Theorems.Thm_GaussProlongation_residue_mem_adjoin_residue_of_mem_adjoin_integers
import Theorems.Thm_Algebra_exists_adjoin_ne_zero_mul_forall_valuationSubring_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq

set_option autoImplicit false
set_option maxHeartbeats 8000000

open AlgebraicCurve IsLocalRing

noncomputable section

namespace FinGeSol
namespace Generic

open IsLocalRing Submodule

section G1

variable (W : Type*) [CommRing W] [IsLocalRing W]
variable (M : Type*) [AddCommGroup M] [Module W M] [Module.Finite W M]

local notation "I" => (maximalIdeal W • ⊤ : Submodule W M)

noncomputable scoped instance : Module (ResidueField W) (M ⧸ I) :=
  inferInstanceAs (Module (W ⧸ maximalIdeal W) (M ⧸ I))

scoped instance : IsScalarTower W (ResidueField W) (M ⧸ I) :=
  inferInstanceAs (IsScalarTower W (W ⧸ maximalIdeal W) (M ⧸ I))

noncomputable scoped instance : Module.Finite (ResidueField W) (M ⧸ I) :=
  Module.Finite.of_restrictScalars_finite W _ _

theorem exists_fin_span_eq_top_of_finite :
    ∃ (m : ℕ) (v : Fin m → M),
      m = Module.finrank (ResidueField W) (M ⧸ I) ∧
      Submodule.span W (Set.range v) = ⊤ := by
  set V := M ⧸ I
  set m := Module.finrank (ResidueField W) V

  have b : Module.Basis (Fin m) (ResidueField W) V := Module.finBasis (ResidueField W) V

  choose v hv using fun i => Submodule.mkQ_surjective I (b i)
  refine ⟨m, v, rfl, ?_⟩

  rw [← IsLocalRing.map_mkQ_eq_top (N := span W (Set.range v)),
      Submodule.map_span, ← Set.range_comp]

  have hb : Submodule.mkQ I ∘ v = (b : Fin m → V) := funext hv
  rw [hb, show (⊤ : Submodule W V) = Submodule.restrictScalars W
        (⊤ : Submodule (ResidueField W) V) from rfl,
      ← b.span_eq,
      Submodule.restrictScalars_span W (ResidueField W)
        Ideal.Quotient.mk_surjective (Set.range b)]

end G1

section G2

variable {κ E : Type*} [Field κ] [Field E] (ψ : κ →+* E)

theorem finrank_le_of_forall_mem_range (d : ℕ) (b : Fin d → E)
    (S : Subfield E) (hSψ : (S : Set E) ⊆ Set.range ψ)
    (hspan : ∀ x : E, ∃ c : Fin d → E, (∀ t, c t ∈ S) ∧ x = ∑ t, c t * b t) :
    letI := ψ.toAlgebra
    Module.Finite κ E ∧ Module.finrank κ E ≤ d := by
  classical
  letI := ψ.toAlgebra

  have hspanκ : Submodule.span κ (Set.range b) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    obtain ⟨c, hcS, hx⟩ := hspan x
    choose c' hc' using fun t => hSψ (hcS t)
    have hx' : x = ∑ t, c' t • b t := by
      rw [hx]; refine Finset.sum_congr rfl fun t _ => ?_
      rw [← hc' t, Algebra.smul_def]; rfl
    rw [hx']
    exact Submodule.sum_mem _ fun t _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  refine ⟨⟨⟨Finset.image b Finset.univ, ?_⟩⟩, ?_⟩
  · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact hspanκ
  · calc Module.finrank κ E ≤ Fintype.card (Fin d) := finrank_le_of_span_eq_top hspanκ
      _ = d := Fintype.card_fin d

end G2

end FinGeSol.Generic
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq.FinGeSol P2MW.S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq.FinGeSol.Generic"
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq.FinGeSol"

namespace FinGeSol

section GaussRing

variable (L : Type*) [Field L] {F : Type*} [Field F] [Algebra L F]

abbrev KK (f : F) : IntermediateField L F :=
  IntermediateField.adjoin L ({f} : Set F)

abbrev gaussRing (f : F) (O : ValuationSubring F) : ValuationSubring (KK L f) :=
  O.comap (algebraMap (KK L f) F)

variable (f : F) (O : ValuationSubring F)

lemma mem_gaussRing_iff (x : KK L f) : x ∈ gaussRing L f O ↔ (x : F) ∈ O := ValuationSubring.mem_comap

scoped instance algebraGaussRing : Algebra (gaussRing L f O) F :=
  ((algebraMap (KK L f) F).comp (algebraMap (gaussRing L f O) (KK L f))).toAlgebra

lemma algebraMap_gaussRing_apply (w : gaussRing L f O) :
    algebraMap (gaussRing L f O) F w = ((w : KK L f) : F) :=
  rfl

scoped instance isScalarTower_gaussRing : IsScalarTower (gaussRing L f O) (KK L f) F :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

lemma gaussRing_smul_def (w : gaussRing L f O) (x : F) : w • x = ((w : KK L f) : F) * x :=
  Algebra.smul_def w x

lemma coe_gaussRing_mem (w : gaussRing L f O) : ((w : KK L f) : F) ∈ O :=
  (mem_gaussRing_iff L f O _).mp w.2

def constK (a : L) : KK L f := ⟨algebraMap L F a, IntermediateField.algebraMap_mem _ a⟩

@[scoped simp] lemma coe_constK (a : L) : ((constK L f a : KK L f) : F) = algebraMap L F a := rfl

end GaussRing
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq.FinGeSol P2MW.S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq.FinGeSol.Generic"

section Block

variable {L : Type*} [Field L] (A : ValuationSubring L)
  {F : Type*} [Field F] [Algebra L F]
  {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]
  (R : ∀ i, RegularProlongation A F (Fb i))
  (f : F) (hf : ∀ i, f ∈ (R i).integers)
  (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
  (i₀ : ι)

omit [Fintype ι] in
include hf htr in

lemma mem_integers_iff_of_mem_K {x : F} (hx : x ∈ KK L f) (i j : ι) :
    x ∈ (R i).integers ↔ x ∈ (R j).integers :=
  AlgebraicCurve.RegularProlongation.mem_adjoin_iff_mem_integers_iff_of_transcendental_residue A (R i) (R j)
    f (hf i) (hf j) (htr i) (htr j) x hx

omit [Fintype ι] in
include hf htr in

lemma coe_W_mem (w : gaussRing L f (R i₀).integers) (i : ι) : ((w : KK L f) : F) ∈ (R i).integers :=
  (mem_integers_iff_of_mem_K A Fb R f hf htr (w : KK L f).2 i₀ i).mp (coe_gaussRing_mem L f _ w)

def BB (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩)) (i₀ : ι) :
    Submodule (gaussRing L f (R i₀).integers) F where
  carrier := {b | ∀ i, b ∈ (R i).integers}
  add_mem' := fun hx hy i => add_mem (hx i) (hy i)
  zero_mem' := fun i => zero_mem _
  smul_mem' := fun w x hx i => by
    rw [gaussRing_smul_def]
    exact mul_mem (coe_W_mem A Fb R f hf htr i₀ w i) (hx i)

omit [Fintype ι] in
lemma mem_BB {b : F} : b ∈ BB A Fb R f hf htr i₀ ↔ ∀ i, b ∈ (R i).integers := Iff.rfl

variable [Nonempty ι]

lemma exists_const_smul_mem_BB (x : F) (hx : x ≠ 0) :
    ∃ c : L, c ≠ 0 ∧ ∃ h : ∀ i, c • x ∈ (R i).integers, ∃ i₁, (R i₁).residue ⟨c • x, h i₁⟩ ≠ 0 := by
  classical
  choose c hc hres using fun i => (R i).exists_smul_mem x hx
  obtain ⟨i₁, -, hmin⟩ := Finset.exists_min_image Finset.univ (fun i => A.valuation (c i))
    Finset.univ_nonempty
  have hc0 : ∀ i, c i ≠ 0 := fun i => (R i).smul_const_ne_zero (hc i) (hres i)
  have hmem : ∀ i, c i₁ • x ∈ (R i).integers := by
    intro i
    have hq : c i₁ / c i ∈ A := by
      rw [← A.valuation_le_one_iff, map_div₀]
      exact div_le_one_of_le₀ (hmin i (Finset.mem_univ i)) zero_le'
    have heq : c i₁ • x = algebraMap L F (c i₁ / c i) * (c i • x) := by
      rw [Algebra.smul_def, Algebra.smul_def, map_div₀]
      have : algebraMap L F (c i) ≠ 0 := (map_ne_zero _).mpr (hc0 i)
      field_simp
    rw [heq]
    exact mul_mem (((R i).algebraMap_mem_iff _).mpr hq) (hc i)
  exact ⟨c i₁, hc0 i₁, hmem, i₁, by convert hres i₁⟩

lemma exists_const_mul_mem_BB (x : F) :
    ∃ c : L, c ≠ 0 ∧ algebraMap L F c * x ∈ BB A Fb R f hf htr i₀ := by
  by_cases hx : x = 0
  · exact ⟨1, one_ne_zero, by simp [hx, zero_mem]⟩
  obtain ⟨c, hc0, h, -⟩ := exists_const_smul_mem_BB A Fb R x hx
  exact ⟨c, hc0, fun i => by simpa [Algebra.smul_def] using h i⟩

lemma exists_eq_const_mul_of_residue_eq_zero {b : F} (hb : ∀ i, b ∈ (R i).integers) (hb0 : b ≠ 0)
    (hres : ∀ i, (R i).residue ⟨b, hb i⟩ = 0) :
    ∃ a : L, a ∈ A ∧ a⁻¹ ∉ A ∧ ∃ b' : F, (∀ i, b' ∈ (R i).integers) ∧ b = algebraMap L F a * b' := by
  obtain ⟨c, hc0, h, i₁, hres₁⟩ := exists_const_smul_mem_BB A Fb R b hb0
  have hcA : c ∉ A := by
    intro hcA
    apply hres₁
    have hbm : (⟨b, hb i₁⟩ : (R i₁).integers) ∈ maximalIdeal (R i₁).integers := by
      rw [← (R i₁).ker_residue]; exact hres i₁
    have hcm : (⟨c • b, h i₁⟩ : (R i₁).integers) ∈ maximalIdeal (R i₁).integers := by
      have := Ideal.mul_mem_left (maximalIdeal (R i₁).integers)
        ⟨algebraMap L F c, ((R i₁).algebraMap_mem_iff c).mpr hcA⟩ hbm
      convert this using 1
      exact Subtype.ext (Algebra.smul_def c b)
    rw [← (R i₁).ker_residue] at hcm
    exact hcm
  refine ⟨c⁻¹, (A.mem_or_inv_mem c).resolve_left hcA, by simpa using hcA, c • b, h, ?_⟩
  rw [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]

omit [Fintype ι] [Nonempty ι] in

lemma constK_mem_maximalIdeal {a : L} (haA : a ∈ A) (hainv : a⁻¹ ∉ A) :
    ∃ hw : constK L f a ∈ gaussRing L f (R i₀).integers,
      (⟨constK L f a, hw⟩ : gaussRing L f (R i₀).integers) ∈
        maximalIdeal (gaussRing L f (R i₀).integers) := by
  have hw : constK L f a ∈ gaussRing L f (R i₀).integers := by
    rw [mem_gaussRing_iff, coe_constK]; exact ((R i₀).algebraMap_mem_iff a).mpr haA
  refine ⟨hw, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  apply hainv
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hu

  have hvF : ((v : KK L f) : F) ∈ (R i₀).integers := coe_gaussRing_mem L f _ v
  have hprod : algebraMap L F a * ((v : KK L f) : F) = 1 := by
    have := congrArg (fun w : gaussRing L f (R i₀).integers => ((w : KK L f) : F)) hv
    simpa using this
  have hvinv : ((v : KK L f) : F) = algebraMap L F a⁻¹ := by
    rw [map_inv₀]; exact eq_inv_of_mul_eq_one_right hprod
  rw [hvinv] at hvF
  exact ((R i₀).algebraMap_mem_iff _).mp hvF

omit [Fintype ι] [Nonempty ι] in
include hf htr in
lemma moduleFinite_BB
    (hfin : ∃ s : Finset F, (∀ x ∈ s, ∀ i, x ∈ (R i).integers) ∧
      ∀ b : F, (∀ i, b ∈ (R i).integers) →
        ∃ c : F → IntermediateField.adjoin L ({f} : Set F),
          (∀ x, (c x : F) ∈ (R i₀).integers) ∧ b = ∑ x ∈ s, (c x : F) * x) :
    Module.Finite (gaussRing L f (R i₀).integers) (BB A Fb R f hf htr i₀) := by
  classical
  obtain ⟨s, hsB, hrepr⟩ := hfin
  let u : s → BB A Fb R f hf htr i₀ := fun x => ⟨(x : F), hsB x x.2⟩
  refine ⟨(Set.finite_range u).toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset, eq_top_iff]
  rintro ⟨b, hb⟩ -
  obtain ⟨c, hc, hbeq⟩ := hrepr b hb
  have hmem : ∀ x : s, (⟨c x, (mem_gaussRing_iff L f _ _).mpr (hc x)⟩ : gaussRing L f (R i₀).integers) • u x ∈
      Submodule.span (gaussRing L f (R i₀).integers) (Set.range u) :=
    fun x => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  have hsum := Submodule.sum_mem _ (t := Finset.univ) (fun x _ => hmem x)
  have hb' : (⟨b, hb⟩ : BB A Fb R f hf htr i₀) =
      ∑ x : s, (⟨c x, (mem_gaussRing_iff L f _ _).mpr (hc x)⟩ : gaussRing L f (R i₀).integers) • u x := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, gaussRing_smul_def, u]
    rw [Finset.sum_coe_sort s (fun x => ((c x : KK L f) : F) * x)]
    exact hbeq
  rw [hb']
  exact hsum

include hf htr in

def toO (i : ι) : gaussRing L f (R i₀).integers →+* (R i).integers :=
  (algebraMap (gaussRing L f (R i₀).integers) F).codRestrict (R i).integers
    (fun w => coe_W_mem A Fb R f hf htr i₀ w i)

omit [Fintype ι] [Nonempty ι] in
@[scoped simp] lemma coe_toO (i : ι) (w : gaussRing L f (R i₀).integers) :
    ((toO A Fb R f hf htr i₀ i w : (R i).integers) : F) = ((w : KK L f) : F) := rfl

def resW (i : ι) : gaussRing L f (R i₀).integers →+* Fb i := (R i).residue.comp (toO A Fb R f hf htr i₀ i)

omit [Fintype ι] [Nonempty ι] in
lemma resW_apply (i : ι) (w : gaussRing L f (R i₀).integers) :
    resW A Fb R f hf htr i₀ i w = (R i).residue ⟨((w : KK L f) : F), coe_W_mem A Fb R f hf htr i₀ w i⟩ := rfl

omit [Fintype ι] [Nonempty ι] in
include hf htr in

lemma resW_eq_zero_of_mem_maximalIdeal (i : ι) {w : gaussRing L f (R i₀).integers}
    (hw : w ∈ maximalIdeal (gaussRing L f (R i₀).integers)) : resW A Fb R f hf htr i₀ i w = 0 := by

  have hO : toO A Fb R f hf htr i₀ i w ∈ maximalIdeal (R i).integers := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hw
    apply hw
    obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hu
    have hw0 : (w : KK L f) ≠ 0 := by
      intro h0
      have : ((toO A Fb R f hf htr i₀ i w : (R i).integers) : F) = 0 := by simp [h0]
      have h1 := congrArg (fun z : (R i).integers => (z : F)) hv
      simp [this] at h1

    have hvF : ((v : (R i).integers) : F) = (((w : KK L f)⁻¹ : KK L f) : F) := by
      have h1 := congrArg (fun z : (R i).integers => (z : F)) hv
      simp only [OneMemClass.coe_one] at h1
      rw [IntermediateField.coe_inv]
      exact (eq_inv_of_mul_eq_one_right h1)
    have hwinv : ((w : KK L f)⁻¹ : KK L f) ∈ gaussRing L f (R i₀).integers := by
      rw [mem_gaussRing_iff, ← hvF]
      exact (mem_integers_iff_of_mem_K A Fb R f hf htr
        (by rw [hvF]; exact ((w : KK L f)⁻¹).2) i i₀).mp v.2
    refine isUnit_iff_exists_inv.mpr ⟨⟨(w : KK L f)⁻¹, hwinv⟩, Subtype.ext ?_⟩
    change (w : KK L f) * (w : KK L f)⁻¹ = 1
    exact mul_inv_cancel₀ hw0
  rw [← (R i).ker_residue] at hO
  exact hO

def psi (i : ι) : ResidueField (gaussRing L f (R i₀).integers) →+* Fb i :=
  Ideal.Quotient.lift _ (resW A Fb R f hf htr i₀ i)
    (fun _ hw => resW_eq_zero_of_mem_maximalIdeal A Fb R f hf htr i₀ i hw)

omit [Fintype ι] [Nonempty ι] in
@[scoped simp] lemma psi_residue (i : ι) (w : gaussRing L f (R i₀).integers) :
    psi A Fb R f hf htr i₀ i (residue _ w) = resW A Fb R f hf htr i₀ i w := rfl

def jointRes (i : ι) :
    letI : Module (gaussRing L f (R i₀).integers) (Fb i) := Module.compHom (Fb i) (resW A Fb R f hf htr i₀ i)
    BB A Fb R f hf htr i₀ →ₗ[gaussRing L f (R i₀).integers] Fb i :=
  letI : Module (gaussRing L f (R i₀).integers) (Fb i) := Module.compHom (Fb i) (resW A Fb R f hf htr i₀ i)
  { toFun := fun b => (R i).residue ⟨(b : F), b.2 i⟩
    map_add' := fun b b' => by
      rw [← map_add]; rfl
    map_smul' := fun w b => by
      change (R i).residue ⟨((w • b : BB A Fb R f hf htr i₀) : F), _⟩ = resW A Fb R f hf htr i₀ i w * _
      rw [resW_apply, ← map_mul]
      congr 1 }

def jointResPi :
    letI : ∀ i, Module (gaussRing L f (R i₀).integers) (Fb i) :=
      fun i => Module.compHom (Fb i) (resW A Fb R f hf htr i₀ i)
    BB A Fb R f hf htr i₀ →ₗ[gaussRing L f (R i₀).integers] (∀ i, Fb i) :=
  letI : ∀ i, Module (gaussRing L f (R i₀).integers) (Fb i) :=
    fun i => Module.compHom (Fb i) (resW A Fb R f hf htr i₀ i)
  LinearMap.pi (fun i => jointRes A Fb R f hf htr i₀ i)

omit [Fintype ι] [Nonempty ι] in
lemma jointResPi_apply (b : BB A Fb R f hf htr i₀) (i : ι) :
    jointResPi A Fb R f hf htr i₀ b i = (R i).residue ⟨(b : F), b.2 i⟩ := rfl

omit [Fintype ι] [Nonempty ι] in
lemma smul_top_le_ker_jointResPi :
    letI : ∀ i, Module (gaussRing L f (R i₀).integers) (Fb i) :=
      fun i => Module.compHom (Fb i) (resW A Fb R f hf htr i₀ i)
    (maximalIdeal (gaussRing L f (R i₀).integers) • ⊤ :
        Submodule (gaussRing L f (R i₀).integers) (BB A Fb R f hf htr i₀)) ≤
      LinearMap.ker (jointResPi A Fb R f hf htr i₀) := by
  letI : ∀ i, Module (gaussRing L f (R i₀).integers) (Fb i) :=
    fun i => Module.compHom (Fb i) (resW A Fb R f hf htr i₀ i)
  refine Submodule.smul_le.mpr fun w hw b _ => ?_
  rw [LinearMap.mem_ker, map_smul]
  funext i
  change resW A Fb R f hf htr i₀ i w * jointResPi A Fb R f hf htr i₀ b i = 0
  rw [resW_eq_zero_of_mem_maximalIdeal A Fb R f hf htr i₀ i hw, zero_mul]

def jointResQW :
    letI : ∀ i, Module (gaussRing L f (R i₀).integers) (Fb i) :=
      fun i => Module.compHom (Fb i) (resW A Fb R f hf htr i₀ i)
    (BB A Fb R f hf htr i₀ ⧸ (maximalIdeal (gaussRing L f (R i₀).integers) • ⊤ :
        Submodule (gaussRing L f (R i₀).integers) (BB A Fb R f hf htr i₀))) →ₗ[gaussRing L f (R i₀).integers]
      (∀ i, Fb i) :=
  letI : ∀ i, Module (gaussRing L f (R i₀).integers) (Fb i) :=
    fun i => Module.compHom (Fb i) (resW A Fb R f hf htr i₀ i)
  Submodule.liftQ _ (jointResPi A Fb R f hf htr i₀) (smul_top_le_ker_jointResPi A Fb R f hf htr i₀)

def jointResQ [Module.Finite (gaussRing L f (R i₀).integers) (BB A Fb R f hf htr i₀)] :
    letI : ∀ i, Module (ResidueField (gaussRing L f (R i₀).integers)) (Fb i) :=
      fun i => Module.compHom (Fb i) (psi A Fb R f hf htr i₀ i)
    (BB A Fb R f hf htr i₀ ⧸ (maximalIdeal (gaussRing L f (R i₀).integers) • ⊤ :
        Submodule (gaussRing L f (R i₀).integers) (BB A Fb R f hf htr i₀))) →ₗ[
      ResidueField (gaussRing L f (R i₀).integers)] (∀ i, Fb i) :=
  letI : ∀ i, Module (ResidueField (gaussRing L f (R i₀).integers)) (Fb i) :=
    fun i => Module.compHom (Fb i) (psi A Fb R f hf htr i₀ i)
  { toFun := jointResQW A Fb R f hf htr i₀
    map_add' := fun x y => map_add _ x y
    map_smul' := fun c x => by
      obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective c
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      letI : ∀ i, Module (gaussRing L f (R i₀).integers) (Fb i) :=
        fun i => Module.compHom (Fb i) (resW A Fb R f hf htr i₀ i)
      funext i
      exact congrFun ((jointResPi A Fb R f hf htr i₀).map_smul w b) i }

omit [Fintype ι] [Nonempty ι] in
lemma jointResQ_mk [Module.Finite (gaussRing L f (R i₀).integers) (BB A Fb R f hf htr i₀)]
    (b : BB A Fb R f hf htr i₀) (i : ι) :
    jointResQ A Fb R f hf htr i₀ (Submodule.Quotient.mk b) i = (R i).residue ⟨(b : F), b.2 i⟩ := rfl

lemma jointResQ_injective [Module.Finite (gaussRing L f (R i₀).integers) (BB A Fb R f hf htr i₀)] :
    Function.Injective (jointResQ A Fb R f hf htr i₀) := by
  letI : ∀ i, Module (ResidueField (gaussRing L f (R i₀).integers)) (Fb i) :=
    fun i => Module.compHom (Fb i) (psi A Fb R f hf htr i₀ i)
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨b, hb⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  by_cases hb0 : b = 0
  · subst hb0
    rw [show (⟨0, hb⟩ : BB A Fb R f hf htr i₀) = 0 from rfl, Submodule.Quotient.mk_zero]
  have hres : ∀ i, (R i).residue ⟨b, hb i⟩ = 0 := fun i => by
    have := congrFun hx i
    rwa [jointResQ_mk] at this
  obtain ⟨a, haA, hainv, b', hb', hbeq⟩ :=
    exists_eq_const_mul_of_residue_eq_zero A Fb R hb hb0 hres
  obtain ⟨hw, hwm⟩ := constK_mem_maximalIdeal A Fb R f i₀ haA hainv
  rw [Submodule.Quotient.mk_eq_zero]
  have : (⟨b, hb⟩ : BB A Fb R f hf htr i₀) =
      (⟨constK L f a, hw⟩ : gaussRing L f (R i₀).integers) • (⟨b', hb'⟩ : BB A Fb R f hf htr i₀) :=
    Subtype.ext (by rw [Submodule.coe_smul, gaussRing_smul_def, coe_constK]; exact hbeq)
  rw [this]
  exact Submodule.smul_mem_smul hwm Submodule.mem_top

omit [Fintype ι] [Nonempty ι] in
include hf htr in
lemma exists_psi_eq_of_mem_adjoin (i : ι) {x : Fb i}
    (hx : x ∈ IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) :
    ∃ c, psi A Fb R f hf htr i₀ i c = x := by

  have hconst : ∀ c : ResidueField A,
      algebraMap (ResidueField A) (Fb i) c ∈ (psi A Fb R f hf htr i₀ i).fieldRange := by
    intro c
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    have hw : constK L f (a : L) ∈ gaussRing L f (R i₀).integers := by
      rw [mem_gaussRing_iff, coe_constK]; exact ((R i₀).algebraMap_mem_iff _).mpr a.2
    refine RingHom.mem_fieldRange.mpr ⟨residue _ ⟨constK L f (a : L), hw⟩, ?_⟩
    rw [psi_residue, resW_apply]
    exact (R i).residue_algebraMap a
  let T : IntermediateField (ResidueField A) (Fb i) :=
    (psi A Fb R f hf htr i₀ i).fieldRange.toIntermediateField hconst
  have hfbar : (R i).residue ⟨f, hf i⟩ ∈ T := by
    have hw : (⟨f, IntermediateField.mem_adjoin_simple_self L f⟩ : KK L f) ∈ gaussRing L f (R i₀).integers := by
      rw [mem_gaussRing_iff]; exact hf i₀
    change (R i).residue ⟨f, hf i⟩ ∈ (psi A Fb R f hf htr i₀ i).fieldRange
    exact RingHom.mem_fieldRange.mpr ⟨residue _ ⟨_, hw⟩, rfl⟩
  have hle : IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)) ≤ T :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hfbar)
  exact RingHom.mem_fieldRange.mp (hle hx)

omit [Fintype ι] [Nonempty ι] in

lemma finite_and_finrank_le_of_psi (i : ι)
    [FiniteDimensional (IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)))
      (Fb i)] :
    letI : Module (ResidueField (gaussRing L f (R i₀).integers)) (Fb i) :=
      Module.compHom (Fb i) (psi A Fb R f hf htr i₀ i)
    Module.Finite (ResidueField (gaussRing L f (R i₀).integers)) (Fb i) ∧
      Module.finrank (ResidueField (gaussRing L f (R i₀).integers)) (Fb i) ≤
        Module.finrank (IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)))
          (Fb i) := by
  classical
  letI : Module (ResidueField (gaussRing L f (R i₀).integers)) (Fb i) :=
    Module.compHom (Fb i) (psi A Fb R f hf htr i₀ i)
  let bi := Module.finBasis
    (IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
  have hspan : Submodule.span (ResidueField (gaussRing L f (R i₀).integers)) (Set.range bi) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    rw [← bi.sum_repr x]
    refine Submodule.sum_mem _ fun t _ => ?_
    obtain ⟨c, hc⟩ := exists_psi_eq_of_mem_adjoin A Fb R f hf htr i₀ i (bi.repr x t).2
    have hct : (bi.repr x t) • (bi t) = c • (bi t) := by
      rw [IntermediateField.smul_def, smul_eq_mul, ← hc]
      rfl
    rw [hct]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  refine ⟨⟨⟨Finset.univ.image bi, ?_⟩⟩, ?_⟩
  · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact hspan
  · exact (finrank_le_of_span_eq_top hspan).trans (Fintype.card_fin _).le

variable (hR : Function.Injective fun i => (R i).integers)

include hf htr hR in

lemma ker_jointResPi_le_smul_top :
    letI : ∀ i, Module (gaussRing L f (R i₀).integers) (Fb i) :=
      fun i => Module.compHom (Fb i) (resW A Fb R f hf htr i₀ i)
    LinearMap.ker (jointResPi A Fb R f hf htr i₀) ≤
      (maximalIdeal (gaussRing L f (R i₀).integers) • ⊤ :
        Submodule (gaussRing L f (R i₀).integers) (BB A Fb R f hf htr i₀)) := by
  letI : ∀ i, Module (gaussRing L f (R i₀).integers) (Fb i) :=
    fun i => Module.compHom (Fb i) (resW A Fb R f hf htr i₀ i)
  rintro ⟨b, hb⟩ hker
  by_cases hb0 : b = 0
  · subst hb0; exact (zero_mem _)
  have hres : ∀ i, (R i).residue ⟨b, hb i⟩ = 0 := fun i => congrFun hker i
  obtain ⟨a, haA, hainv, b', hb', hbeq⟩ :=
    exists_eq_const_mul_of_residue_eq_zero A Fb R hb hb0 hres
  obtain ⟨hw, hwm⟩ := constK_mem_maximalIdeal A Fb R f i₀ haA hainv
  have : (⟨b, hb⟩ : BB A Fb R f hf htr i₀) =
      (⟨constK L f a, hw⟩ : gaussRing L f (R i₀).integers) • (⟨b', hb'⟩ : BB A Fb R f hf htr i₀) :=
    Subtype.ext (by rw [Submodule.coe_smul, gaussRing_smul_def, coe_constK]; exact hbeq)
  rw [this]
  exact Submodule.smul_mem_smul hwm Submodule.mem_top

include hf htr in

lemma psi_mem_adjoin [IsAlgClosed L] (i : ι) (c : ResidueField (gaussRing L f (R i₀).integers)) :
    psi A Fb R f hf htr i₀ i c ∈
      IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)) := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective c

  exact GaussProlongation.residue_mem_adjoin_residue_of_mem_adjoin_integers A Fb R f hf htr i₀ i
    (w : KK L f) (coe_gaussRing_mem L f _ w) (coe_W_mem A Fb R f hf htr i₀ w i)

variable [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]

include hf htr hR in

lemma exists_coeff_mem_gaussRing_of_basis_piResidue_linearIndependent [IsAlgClosed L]
    {J : Type*} [Fintype J] (v : J → F) (hvB : ∀ τ i, v τ ∈ (R i).integers)
    (hKbasis : ∀ x : F, ∃! c : J → KK L f, x = ∑ τ, ((c τ : KK L f) : F) * v τ)

    (hResLI : ∀ g : J → ResidueField (gaussRing L f (R i₀).integers),
        (∀ i, ∑ σ, psi A Fb R f hf htr i₀ i (g σ) * (R i).residue ⟨v σ, hvB σ i⟩ = 0) →
        ∀ σ, g σ = 0)
    (b : F) (hb : ∀ i, b ∈ (R i).integers) :
    ∃ c : J → KK L f, (∀ τ, (c τ : F) ∈ (R i₀).integers) ∧
      b = ∑ τ, ((c τ : KK L f) : F) * v τ := by
  classical
  set W := gaussRing L f (R i₀).integers
  obtain ⟨c, hc, huniq⟩ := hKbasis b
  refine ⟨c, fun τ => ?_, hc⟩

  by_contra hcτ

  have hcτW : c τ ∉ W := fun h => hcτ ((mem_gaussRing_iff L f _ _).mp h)

  obtain ⟨τ₀, -, hτ₀max⟩ := Finset.exists_max_image Finset.univ (fun σ => W.valuation (c σ))
    ⟨τ, Finset.mem_univ τ⟩
  have hc0τ₀ : c τ₀ ≠ 0 := by
    intro h0
    have : W.valuation (c τ) ≤ W.valuation (c τ₀) := hτ₀max τ (Finset.mem_univ τ)
    rw [h0, map_zero] at this
    exact hcτW ((W.valuation_le_one_iff (c τ)).mp (this.trans zero_le_one))
  have hcτ₀W : c τ₀ ∉ W := by
    intro h
    have h1 : W.valuation (c τ) ≤ W.valuation (c τ₀) := hτ₀max τ (Finset.mem_univ τ)
    have h2 : W.valuation (c τ₀) ≤ 1 := (W.valuation_le_one_iff (c τ₀)).mpr h
    exact hcτW ((W.valuation_le_one_iff (c τ)).mp (h1.trans h2))

  have hcinv : (c τ₀)⁻¹ ∈ W := (W.mem_or_inv_mem (c τ₀)).resolve_left hcτ₀W
  have hcinvF : ((c τ₀)⁻¹ : F) ∈ (R i₀).integers := (mem_gaussRing_iff L f _ _).mp hcinv
  have hcinvM : (⟨(c τ₀)⁻¹, hcinv⟩ : W) ∈ maximalIdeal W := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨u, hu'⟩ := isUnit_iff_exists_inv.mp hu
    have hmul : (c τ₀)⁻¹ * ((u : W) : KK L f) = 1 := by
      have := congrArg Subtype.val hu'; simpa using this
    have hcoe : ((u : W) : KK L f) = c τ₀ :=
      mul_left_cancel₀ (inv_ne_zero hc0τ₀) (hmul.trans (inv_mul_cancel₀ hc0τ₀).symm)
    exact hcτ₀W (hcoe ▸ u.2)
  have hratio : ∀ σ, c σ * (c τ₀)⁻¹ ∈ W := fun σ => by
    rw [← W.valuation_le_one_iff, ← div_eq_mul_inv, map_div₀]
    exact div_le_one_of_le₀ (hτ₀max σ (Finset.mem_univ σ)) zero_le'

  have hcinvbB : ∀ i, ((c τ₀)⁻¹ : F) * b ∈ (R i).integers := fun i =>
    mul_mem (coe_W_mem A Fb R f hf htr i₀ ⟨(c τ₀)⁻¹, hcinv⟩ i) (hb i)
  have hmemM : (⟨((c τ₀)⁻¹ : F) * b, hcinvbB⟩ : BB A Fb R f hf htr i₀) ∈
      (maximalIdeal W • ⊤ : Submodule W (BB A Fb R f hf htr i₀)) := by
    have : (⟨((c τ₀)⁻¹ : F) * b, hcinvbB⟩ : BB A Fb R f hf htr i₀) =
        (⟨(c τ₀)⁻¹, hcinv⟩ : W) • (⟨b, hb⟩ : BB A Fb R f hf htr i₀) :=
      Subtype.ext (by rw [Submodule.coe_smul, gaussRing_smul_def]; rfl)
    rw [this]
    exact Submodule.smul_mem_smul hcinvM Submodule.mem_top

  have hres0 : ∀ i, (R i).residue ⟨((c τ₀)⁻¹ : F) * b, hcinvbB i⟩ = 0 := fun i => by
    have := smul_top_le_ker_jointResPi A Fb R f hf htr i₀ hmemM
    exact congrFun this i

  have hcexpr : ((c τ₀)⁻¹ : F) * b = ∑ σ, ((c σ * (c τ₀)⁻¹ : KK L f) : F) * v σ := by
    rw [hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    push_cast; ring

  have hcoeff0 : ∀ σ, (IsLocalRing.residue W ⟨c σ * (c τ₀)⁻¹, hratio σ⟩ : ResidueField W) = 0 := by
    refine hResLI (fun σ => residue W ⟨c σ * (c τ₀)⁻¹, hratio σ⟩) (fun i => ?_)

    have hresW : ∀ σ, (psi A Fb R f hf htr i₀ i) (residue W ⟨c σ * (c τ₀)⁻¹, hratio σ⟩) =
        (R i).residue ⟨((c σ * (c τ₀)⁻¹ : KK L f) : F), coe_W_mem A Fb R f hf htr i₀ ⟨_, hratio σ⟩ i⟩ :=
      fun σ => by rw [psi_residue, resW_apply]
    simp_rw [hresW, ← map_mul]
    rw [← map_sum, show (∑ σ, (⟨((c σ * (c τ₀)⁻¹ : KK L f) : F),
          coe_W_mem A Fb R f hf htr i₀ ⟨_, hratio σ⟩ i⟩ : (R i).integers) * ⟨v σ, hvB σ i⟩) =
        ⟨((c τ₀)⁻¹ : F) * b, hcinvbB i⟩ from Subtype.ext (by push_cast; exact hcexpr.symm)]
    exact hres0 i

  have hone : (⟨c τ₀ * (c τ₀)⁻¹, hratio τ₀⟩ : W) = 1 :=
    Subtype.ext (mul_inv_cancel₀ hc0τ₀)
  have := hcoeff0 τ₀
  rw [hone] at this
  exact one_ne_zero this

include hf htr in

lemma linearIndependent_KK_of_piResidue_linearIndependent [IsAlgClosed L]
    {J : Type*} [Fintype J] (v : J → F) (hvB : ∀ τ i, v τ ∈ (R i).integers)
    (hResLI : ∀ g : J → ResidueField (gaussRing L f (R i₀).integers),
        (∀ i, ∑ σ, psi A Fb R f hf htr i₀ i (g σ) * (R i).residue ⟨v σ, hvB σ i⟩ = 0) →
        ∀ σ, g σ = 0) :
    LinearIndependent (KK L f) v := by
  classical
  set W := gaussRing L f (R i₀).integers
  rw [Fintype.linearIndependent_iff]
  intro g hsum τ
  by_contra hgτ
  obtain ⟨τ₀, -, hτ₀max⟩ := Finset.exists_max_image Finset.univ (fun σ => W.valuation (g σ))
    ⟨τ, Finset.mem_univ τ⟩
  have hg0τ₀ : g τ₀ ≠ 0 := by
    intro h0
    have hle := hτ₀max τ (Finset.mem_univ τ)
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at hle
    exact hgτ hle
  have hratio : ∀ σ, g σ * (g τ₀)⁻¹ ∈ W := fun σ => by
    rw [← W.valuation_le_one_iff, ← div_eq_mul_inv, map_div₀]
    exact div_le_one_of_le₀ (hτ₀max σ (Finset.mem_univ σ)) zero_le'
  have hsum' : ∑ σ, ((g σ * (g τ₀)⁻¹ : KK L f) : F) * v σ = 0 := by
    have h0 : ∑ σ, ((g σ : KK L f) : F) * v σ = 0 := by
      have hh := hsum
      simp only [IntermediateField.smul_def, smul_eq_mul] at hh
      exact hh
    have h1 : (((g τ₀)⁻¹ : KK L f) : F) * ∑ σ, ((g σ : KK L f) : F) * v σ = 0 := by
      rw [h0, mul_zero]
    rw [Finset.mul_sum] at h1
    refine h1 ▸ Finset.sum_congr rfl fun σ _ => ?_
    push_cast; ring
  have hcoeff0 := hResLI (fun σ => residue W ⟨g σ * (g τ₀)⁻¹, hratio σ⟩) (fun i => ?_) τ₀
  · have hone : (⟨g τ₀ * (g τ₀)⁻¹, hratio τ₀⟩ : W) = 1 := Subtype.ext (mul_inv_cancel₀ hg0τ₀)
    rw [hone, map_one] at hcoeff0
    exact one_ne_zero hcoeff0
  · have hresW : ∀ σ, (psi A Fb R f hf htr i₀ i) (residue W ⟨g σ * (g τ₀)⁻¹, hratio σ⟩) =
        (R i).residue ⟨((g σ * (g τ₀)⁻¹ : KK L f) : F), coe_W_mem A Fb R f hf htr i₀ ⟨_, hratio σ⟩ i⟩ :=
      fun σ => by rw [psi_residue, resW_apply]
    simp_rw [hresW, ← map_mul]
    rw [← map_sum, show (∑ σ, (⟨((g σ * (g τ₀)⁻¹ : KK L f) : F),
          coe_W_mem A Fb R f hf htr i₀ ⟨_, hratio σ⟩ i⟩ : (R i).integers) * ⟨v σ, hvB σ i⟩) =
        0 from Subtype.ext (by push_cast; exact hsum'), map_zero]

section ConverseHelpers

omit [Fintype ι] [Nonempty ι] in

lemma residue_eq_zero_of_mem_nonunits (i : ι) {w : F}
    (hw : w ∈ (R i).integers) (hn : w ∈ (R i).integers.nonunits) :
    (R i).residue ⟨w, hw⟩ = 0 := by
  have hm : (⟨w, hw⟩ : (R i).integers) ∈ maximalIdeal (R i).integers :=
    ((R i).integers.valuation_lt_one_iff ⟨w, hw⟩).mpr (((R i).integers.mem_nonunits_iff).mp hn)
  rwa [← (R i).ker_residue] at hm

omit [Fintype ι] [Nonempty ι] in

lemma integers_eq_of_le {i j : ι} (h : (R i).integers ≤ (R j).integers) :
    (R i).integers = (R j).integers := by
  refine le_antisymm h fun y hy₂ => ?_
  by_contra hy₁
  have hy0 : y ≠ 0 := by rintro rfl; exact hy₁ (zero_mem _)
  obtain ⟨c, hcy, hres⟩ := (R i).exists_smul_mem y hy0
  have hc0 : c ≠ 0 := (R i).smul_const_ne_zero hcy hres
  set v₁ := (R i).integers.valuation; set v₂ := (R j).integers.valuation
  set cF : F := algebraMap L F c
  have hcF0 : cF ≠ 0 := by simp only [cF, ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]; exact hc0
  have hcy' : c • y = cF * y := Algebra.smul_def c y
  have hu : IsUnit (⟨c • y, hcy⟩ : (R i).integers) := (R i).isUnit_of_residue_ne_zero hres
  have h1 : v₁ (cF * y) = 1 := by
    have h' : v₁ (c • y) = 1 := ((R i).integers.valuation_eq_one_iff ⟨c • y, hcy⟩).mp hu
    rwa [hcy'] at h'
  have hy1 : 1 < v₁ y := by
    rw [← not_le]; intro hle; exact hy₁ (((R i).integers.valuation_le_one_iff y).mp hle)
  have hc1 : v₁ cF < 1 := by
    by_contra hge; rw [not_lt] at hge
    have h' : 1 * v₁ y ≤ v₁ cF * v₁ y := mul_le_mul' hge le_rfl
    rw [one_mul, ← map_mul, h1] at h'; exact (not_le.mpr hy1) h'
  have hcA : c ∈ A := ((R i).algebraMap_mem_iff c).mp (((R i).integers.valuation_le_one_iff cF).mp hc1.le)
  have hcinv : c⁻¹ ∉ A := by
    intro hinv
    have hmem : cF⁻¹ ∈ (R i).integers := by
      have := ((R i).algebraMap_mem_iff c⁻¹).mpr hinv; rwa [map_inv₀] at this
    have hle : v₁ cF⁻¹ ≤ 1 := ((R i).integers.valuation_le_one_iff _).mpr hmem
    have h' : v₁ cF⁻¹ * v₁ cF ≤ 1 * v₁ cF := mul_le_mul' hle le_rfl
    rw [← map_mul, inv_mul_cancel₀ hcF0, map_one, one_mul] at h'
    exact (not_lt.mpr h') hc1
  have hcF2 : v₂ cF ≤ 1 :=
    ((R j).integers.valuation_le_one_iff cF).mpr (((R j).algebraMap_mem_iff c).mpr hcA)
  have hy2 : v₂ y ≤ 1 := ((R j).integers.valuation_le_one_iff y).mpr hy₂
  have hinv1 : (cF * y)⁻¹ ∈ (R i).integers := by
    rw [← (R i).integers.valuation_le_one_iff, map_inv₀, h1, inv_one]
  have hinv2 : v₂ (cF * y)⁻¹ ≤ 1 := ((R j).integers.valuation_le_one_iff _).mpr (h hinv1)
  have hcy0 : cF * y ≠ 0 := mul_ne_zero hcF0 hy0
  have hc2 : v₂ cF = 1 := by
    refine le_antisymm hcF2 ?_
    by_contra hlt; rw [not_le] at hlt
    have hprod : v₂ (cF * y) < 1 := by
      rw [map_mul]
      calc v₂ cF * v₂ y ≤ v₂ cF * 1 := mul_le_mul' le_rfl hy2
        _ = v₂ cF := mul_one _
        _ < 1 := hlt
    have h' : v₂ (cF * y)⁻¹ * v₂ (cF * y) ≤ 1 * v₂ (cF * y) := mul_le_mul' hinv2 le_rfl
    rw [← map_mul, inv_mul_cancel₀ hcy0, map_one, one_mul] at h'
    exact (not_lt.mpr h') hprod
  have hmem2 : cF⁻¹ ∈ (R j).integers := by
    rw [← (R j).integers.valuation_le_one_iff, map_inv₀, hc2, inv_one]
  exact hcinv (((R j).algebraMap_mem_iff c⁻¹).mp (by rw [map_inv₀]; exact hmem2))

include hR in

lemma exists_lift (i : ι) (x : Fb i) :
    ∃ z : F, ∃ hz : ∀ l, z ∈ (R l).integers,
      (R i).residue ⟨z, hz i⟩ = x ∧ ∀ l, l ≠ i → (R l).residue ⟨z, hz l⟩ = 0 := by
  classical
  obtain ⟨y, hy⟩ := (R i).residue_surjective x
  let a : ι → F := fun l => if l = i then (y : F) else 0
  have ha : ∀ l, a l ∈ (R l).integers := by
    intro l; by_cases hl : l = i
    · subst hl; simp only [a, if_pos rfl]; exact y.2
    · simp only [a, if_neg hl]; exact zero_mem _
  obtain ⟨z, hz⟩ := ValuationSubring.exists_forall_mem_and_sub_mem_nonunits
    (fun l => (R l).integers) (fun l l' hle => hR (integers_eq_of_le A Fb R hle)) a ha
  refine ⟨z, fun l => (hz l).1, ?_, ?_⟩
  · have h0 := residue_eq_zero_of_mem_nonunits A Fb R i (sub_mem (hz i).1 (ha i)) (hz i).2
    have e : (⟨z - a i, sub_mem (hz i).1 (ha i)⟩ : (R i).integers) = ⟨z, (hz i).1⟩ - y := by
      apply Subtype.ext; simp [a, if_pos rfl]
    rw [e, map_sub, sub_eq_zero] at h0; rw [h0, hy]
  · intro l hl
    have h0 := residue_eq_zero_of_mem_nonunits A Fb R l (sub_mem (hz l).1 (ha l)) (hz l).2
    have e : (⟨z - a l, sub_mem (hz l).1 (ha l)⟩ : (R l).integers) = ⟨z, (hz l).1⟩ := by
      apply Subtype.ext; simp [a, if_neg hl]
    rwa [e] at h0

end ConverseHelpers
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq.FinGeSol P2MW.S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq.FinGeSol.Generic"

end Block
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq.FinGeSol P2MW.S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq.FinGeSol.Generic"

end FinGeSol
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq.FinGeSol P2MW.S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq.FinGeSol.Generic"

namespace E79PoleClear

open FinGeSol Polynomial

variable {L : Type*} [Field L] (A : ValuationSubring L)
  {F : Type*} [Field F] [Algebra L F]
  {ι : Type*} (Fb : ι → Type*) [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]
  (R : ∀ i, RegularProlongation A F (Fb i))
  (f : F) (hf : ∀ i, f ∈ (R i).integers)
  (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
  (i₀ : ι)

lemma aeval_mem_KK (P : Polynomial L) : Polynomial.aeval f P ∈ KK L f :=
  IntermediateField.algebra_adjoin_le_adjoin L {f} (Polynomial.aeval_mem_adjoin_singleton L f)

include hf in

lemma aeval_mem_of_coeff_mem (P : Polynomial L) (hP : ∀ j, P.coeff j ∈ A) :
    Polynomial.aeval f P ∈ (R i₀).integers := by
  rw [aeval_eq_sum_range]
  refine sum_mem fun j _ => ?_
  rw [Algebra.smul_def]
  exact mul_mem (((R i₀).algebraMap_mem_iff _).mpr (hP j)) (pow_mem (hf i₀) j)

include hf in

lemma subtype_aeval_eq_sum (P : Polynomial L) (hP : ∀ j, P.coeff j ∈ A) (i : ι)
    (hmem : Polynomial.aeval f P ∈ (R i).integers) :
    (⟨Polynomial.aeval f P, hmem⟩ : (R i).integers) =
      ∑ j ∈ Finset.range (P.natDegree + 1),
        ⟨algebraMap L F (P.coeff j), ((R i).algebraMap_mem_iff _).mpr (hP j)⟩ * ⟨f, hf i⟩ ^ j := by
  refine Subtype.ext ?_
  push_cast
  rw [aeval_eq_sum_range]
  exact Finset.sum_congr rfl fun j _ => Algebra.smul_def _ _

include hf htr in

lemma isUnit_aeval_of_coeff_isUnit (P : Polynomial L) (hP : ∀ j, P.coeff j ∈ A)
    {j₀ : ℕ} (hj₀ : IsUnit (⟨P.coeff j₀, hP j₀⟩ : A)) :
    IsUnit (⟨aeval f P, aeval_mem_of_coeff_mem A Fb R f hf i₀ P hP⟩ : (R i₀).integers) := by
  refine (R i₀).isUnit_of_residue_ne_zero ?_
  rw [subtype_aeval_eq_sum A Fb R f hf P hP i₀ _, map_sum]
  simp only [map_mul, map_pow, (R i₀).residue_algebraMap ⟨P.coeff _, hP _⟩]
  set fb := (R i₀).residue ⟨f, hf i₀⟩
  intro h0
  set P' : Polynomial (ResidueField A) :=
    ∑ j ∈ Finset.range (P.natDegree + 1), C (IsLocalRing.residue A ⟨P.coeff j, hP j⟩) * X ^ j with hP'
  have hP'eval : aeval fb P' = 0 := by
    rw [hP', map_sum]; simp only [map_mul, aeval_C, aeval_X_pow]; exact h0
  have hj₀ne : P.coeff j₀ ≠ 0 := fun h => hj₀.ne_zero (Subtype.ext h)
  have hj₀lt : j₀ < P.natDegree + 1 := Nat.lt_succ_of_le (le_natDegree_of_ne_zero hj₀ne)
  have hP'coeff : P'.coeff j₀ = IsLocalRing.residue A ⟨P.coeff j₀, hP j₀⟩ := by
    rw [hP', Polynomial.finset_sum_coeff]
    rw [Finset.sum_eq_single j₀ (fun j _ hj => ?_) (fun h => absurd (Finset.mem_range.mpr hj₀lt) h)]
    · simp [coeff_C_mul, coeff_X_pow]
    · simp [coeff_C_mul, coeff_X_pow, Ne.symm hj]
  have hP'0 : P' ≠ 0 := fun h => by
    have heq0 : IsLocalRing.residue A ⟨P.coeff j₀, hP j₀⟩ = 0 :=
      hP'coeff ▸ (h ▸ Polynomial.coeff_zero j₀)
    exact (IsUnit.map (IsLocalRing.residue A) hj₀).ne_zero heq0
  exact (htr i₀) ⟨P', hP'0, hP'eval⟩

include hf htr in

lemma residue_aeval_mem_adjoin (P : Polynomial L) (hP : ∀ j, P.coeff j ∈ A) (i : ι)
    (hmem : Polynomial.aeval f P ∈ (R i).integers) :
    (R i).residue ⟨_, hmem⟩ ∈
      IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)) := by
  rw [subtype_aeval_eq_sum A Fb R f hf P hP i hmem, map_sum]
  refine sum_mem fun j _ => ?_
  rw [map_mul, map_pow, (R i).residue_algebraMap ⟨P.coeff j, hP j⟩]
  exact mul_mem (IntermediateField.algebraMap_mem _ _)
    (pow_mem (IntermediateField.mem_adjoin_simple_self _ _) j)

end E79PoleClear
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq.FinGeSol P2MW.S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq.FinGeSol.Generic"

open AlgebraicCurve FinGeSol E79PoleClear IsLocalRing in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] [Nonempty ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htrL : Transcendental L f)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (i₀ : ι)
    (hcomplete : ∀ W : ValuationSubring F,
      (∀ e ∈ IntermediateField.adjoin L ({f} : Set F), e ∈ W ↔ e ∈ (R i₀).integers) →
      ∃ j, W = (R j).integers)
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) :
    ∃ (d' : ℕ) (z : Fin d' → F) (hzO : ∀ σ i, z σ ∈ (R i).integers),
      (∀ σ, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → z σ ∈ V) ∧
      (∀ q q' : Fin d' → Polynomial (IsLocalRing.ResidueField A),
        (∀ i, ∑ σ, Polynomial.aeval ((R i).residue ⟨f, hf i⟩) (q σ)
            * (R i).residue ⟨z σ, hzO σ i⟩
          = ∑ σ, Polynomial.aeval ((R i).residue ⟨f, hf i⟩) (q' σ)
            * (R i).residue ⟨z σ, hzO σ i⟩) →
        q = q') ∧
      (∀ b : F, (∀ i, b ∈ (R i).integers) →
        ∃ c : Fin d' → IntermediateField.adjoin L ({f} : Set F),
          (∀ σ, (c σ : F) ∈ (R i₀).integers) ∧ b = ∑ σ, (c σ : F) * z σ) := by
  classical
  haveI : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F := hfd
  set k := ResidueField A
  set K := IntermediateField.adjoin L ({f} : Set F)
  haveI hfin := (RegularProlongation.sum_finrank_adjoin_residue_le A Fb R hR f hf htr).1
  let d : ι → ℕ := fun i => Module.finrank
    (IntermediateField.adjoin k ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
  let yb : ∀ i, Fin (d i) → Fb i := fun i => (Module.finBasis _ (Fb i) : _)
  have hyb : ∀ i, LinearIndependent _ (yb i) := fun i => (Module.finBasis _ (Fb i)).linearIndependent

  choose z hzmem hzi hzl using fun τ : Σ i, Fin (d i) =>
    FinGeSol.exists_lift A Fb R hR τ.1 (yb τ.1 τ.2)

  have hResLI : ∀ g : (Σ i, Fin (d i)) → ResidueField (gaussRing L f (R i₀).integers),
      (∀ i, ∑ σ, psi A Fb R f hf htr i₀ i (g σ) * (R i).residue ⟨z σ, hzmem σ i⟩ = 0) →
      ∀ σ, g σ = 0 := by
    intro g hg σ
    obtain ⟨i, l⟩ := σ
    have hi := hg i
    have hred : ∑ σ : Σ i', Fin (d i'), psi A Fb R f hf htr i₀ i (g σ) *
        (R i).residue ⟨z σ, hzmem σ i⟩ =
        ∑ l' : Fin (d i), psi A Fb R f hf htr i₀ i (g ⟨i, l'⟩) * yb i l' := by
      rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
      rw [Finset.sum_eq_single i (fun i' _ hi' => ?_) (fun h => absurd (Finset.mem_univ i) h)]
      · exact Finset.sum_congr rfl fun l' _ => by congr 1; exact hzi ⟨i, l'⟩
      · exact Finset.sum_eq_zero fun l' _ => by rw [hzl ⟨i', l'⟩ i (Ne.symm hi'), mul_zero]
    rw [hred] at hi
    have hpsi_inj := (psi A Fb R f hf htr i₀ i).injective
    apply hpsi_inj; rw [map_zero]
    have hcoef : ∀ l', psi A Fb R f hf htr i₀ i (g ⟨i, l'⟩) ∈
        IntermediateField.adjoin k ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)) :=
      fun l' => psi_mem_adjoin A Fb R f hf htr i₀ i (g ⟨i, l'⟩)
    have hliapp := Fintype.linearIndependent_iff.mp (hyb i)
      (fun l' => ⟨psi A Fb R f hf htr i₀ i (g ⟨i, l'⟩), hcoef l'⟩) ?_ l
    · exact congrArg Subtype.val hliapp
    · rw [← hi]; exact Finset.sum_congr rfl fun l' _ => by
        rw [IntermediateField.smul_def, smul_eq_mul]

  have hKLI := linearIndependent_KK_of_piResidue_linearIndependent A Fb R f hf htr i₀ z hzmem hResLI
  have hcard : Fintype.card (Σ i, Fin (d i)) = Module.finrank K F := by
    rw [Fintype.card_sigma]; simp only [Fintype.card_fin]; exact heq
  haveI : Nonempty (Σ i, Fin (d i)) := by
    rw [← Fintype.card_pos_iff, hcard]; exact Module.finrank_pos
  let bK : Module.Basis (Σ i, Fin (d i)) K F :=
    basisOfLinearIndependentOfCardEqFinrank hKLI hcard
  have hBz : ∀ τ, bK τ = z τ := fun τ =>
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hKLI hcard) τ
  have hKbasis : ∀ x : F, ∃! c : (Σ i, Fin (d i)) → K, x = ∑ τ, ((c τ : K) : F) * z τ := by
    intro x
    refine ⟨fun τ => bK.repr x τ, ?_, fun c' hc' => ?_⟩
    · refine (bK.sum_repr x).symm.trans (Finset.sum_congr rfl fun τ _ => ?_)
      rw [hBz τ, IntermediateField.smul_def, smul_eq_mul]
    · have hLHS : ∑ σ, c' σ • z σ = x := by
        rw [hc']
        exact (Finset.sum_congr rfl fun σ _ => by
          rw [IntermediateField.smul_def, smul_eq_mul]).symm
      have hRHS : ∑ σ, (bK.repr x σ : K) • z σ = x := by
        refine Eq.trans (Finset.sum_congr rfl fun σ _ => ?_) (bK.sum_repr x)
        rw [← hBz σ]
      have hdiff : ∑ σ, (c' σ - bK.repr x σ) • z σ = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, hLHS, hRHS, sub_self]
      funext τ; exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hKLI _ hdiff τ)

  have hWspan := fun b hb =>
    exists_coeff_mem_gaussRing_of_basis_piResidue_linearIndependent A Fb R f hf htr i₀ hR
      z hzmem hKbasis hResLI b hb

  have hpole : ∀ σ : Σ i, Fin (d i), ∃ s : K, ∃ hs : (s : F) ∈ (R i₀).integers,
      IsUnit (⟨(s : F), hs⟩ : (R i₀).integers) ∧
      (∀ i, ∃ hsi : (s : F) ∈ (R i).integers,
        (R i).residue ⟨(s : F), hsi⟩ ∈
          IntermediateField.adjoin k ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) ∧
      (∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → (s : F) * z σ ∈ V) := by
    intro σ
    obtain ⟨⟨q₀, hq₀mem⟩, hq₀0, hq₀T⟩ :=
      Algebra.exists_adjoin_ne_zero_mul_forall_valuationSubring_mem (L := L) f (z σ)
    have hq₀F0 : q₀ ≠ 0 := fun h => hq₀0 (Subtype.ext h)

    obtain ⟨Q, hQ⟩ : ∃ Q : Polynomial L, Polynomial.aeval f Q = q₀ := by
      have hmem2 : q₀ ∈ (Polynomial.aeval f : Polynomial L →ₐ[L] F).range :=
        (Algebra.adjoin_singleton_eq_range_aeval L f) ▸ hq₀mem
      exact hmem2
    have hQ0 : Q ≠ 0 := fun h => hq₀F0 (by rw [← hQ, h, map_zero])

    obtain ⟨j₀, hj₀supp, hj₀max⟩ := Finset.exists_max_image Q.support
      (fun j => A.valuation (Q.coeff j)) (Polynomial.support_nonempty.mpr hQ0)
    have hcj₀0 : Q.coeff j₀ ≠ 0 := Polynomial.mem_support_iff.mp hj₀supp
    set P := (Polynomial.C (Q.coeff j₀)⁻¹) * Q with hPdef
    have hPcoeff : ∀ j, P.coeff j = (Q.coeff j₀)⁻¹ * Q.coeff j := fun j => by
      rw [hPdef, Polynomial.coeff_C_mul]
    have hPA : ∀ j, P.coeff j ∈ A := fun j => by
      rw [hPcoeff]
      by_cases hj : Q.coeff j = 0
      · rw [hj, mul_zero]; exact zero_mem _
      · rw [mul_comm, ← A.valuation_le_one_iff, ← div_eq_mul_inv, map_div₀]
        exact div_le_one_of_le₀ (hj₀max j (Polynomial.mem_support_iff.mpr hj)) zero_le'
    have hPj₀unit : IsUnit (⟨P.coeff j₀, hPA j₀⟩ : A) := by
      have hval : P.coeff j₀ = 1 := by rw [hPcoeff]; exact inv_mul_cancel₀ hcj₀0
      have hA1 : (⟨P.coeff j₀, hPA j₀⟩ : A) = ⟨1, one_mem _⟩ := Subtype.ext hval
      rw [hA1]; exact isUnit_one

    have hsK : Polynomial.aeval f P ∈ K := aeval_mem_KK f P
    have hsmem : Polynomial.aeval f P ∈ (R i₀).integers :=
      aeval_mem_of_coeff_mem A Fb R f hf i₀ P hPA
    have hsunit : IsUnit (⟨Polynomial.aeval f P, hsmem⟩ : (R i₀).integers) :=
      isUnit_aeval_of_coeff_isUnit A Fb R f hf htr i₀ P hPA hPj₀unit
    have haeq : Polynomial.aeval f P = algebraMap L F (Q.coeff j₀)⁻¹ * q₀ := by
      rw [hPdef, map_mul, Polynomial.aeval_C, hQ]

    have hsz : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V →
        Polynomial.aeval f P * z σ ∈ V := fun V hVL hVf => by
      rw [haeq, mul_assoc]; exact mul_mem (hVL _) (hq₀T V hVL hVf)

    have hsres : ∀ i, ∃ hsi : Polynomial.aeval f P ∈ (R i).integers,
        (R i).residue ⟨_, hsi⟩ ∈
          IntermediateField.adjoin k ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)) := fun i =>
      ⟨(mem_integers_iff_of_mem_K A Fb R f hf htr hsK i₀ i).mp hsmem,
        residue_aeval_mem_adjoin A Fb R f hf htr P hPA i _⟩
    exact ⟨⟨Polynomial.aeval f P, hsK⟩, hsmem, hsunit, hsres, hsz⟩
  choose s hsmem hsunit hsres hszT using hpole

  let z' : (Σ i, Fin (d i)) → F := fun σ => (s σ : F) * z σ
  have hsmemi : ∀ σ i, (s σ : F) ∈ (R i).integers := fun σ i => (hsres σ i).choose
  have hz'mem : ∀ σ i, z' σ ∈ (R i).integers := fun σ i => mul_mem (hsmemi σ i) (hzmem σ i)

  have hsF0 : ∀ σ, (s σ : F) ≠ 0 := fun σ he => (hsunit σ).ne_zero (Subtype.ext he)
  have hsK0 : ∀ σ, (s σ : K) ≠ 0 := fun σ h => hsF0 σ (by
    have : ((s σ : K) : F) = ((0 : K) : F) := congrArg _ h; simpa using this)
  have hsinvF : ∀ σ, ((s σ : F))⁻¹ ∈ (R i₀).integers := fun σ => by
    obtain ⟨u, hu⟩ := (hsunit σ).exists_right_inv
    have huF : (s σ : F) * (u : F) = 1 := by
      have h1 := congrArg (Subtype.val : (R i₀).integers → F) hu
      simpa using h1
    rw [← eq_inv_of_mul_eq_one_right huF]; exact u.2
  have hsinvmemi : ∀ σ i, ((s σ : F))⁻¹ ∈ (R i).integers := fun σ i =>
    (mem_integers_iff_of_mem_K A Fb R f hf htr (inv_mem (SetLike.coe_mem (s σ))) i₀ i).mp (hsinvF σ)
  have hsres0 : ∀ σ i, (R i).residue ⟨(s σ : F), hsmemi σ i⟩ ≠ 0 := fun σ i => by
    have hmul : (⟨(s σ : F), hsmemi σ i⟩ : (R i).integers) *
        ⟨((s σ : F))⁻¹, hsinvmemi σ i⟩ = 1 :=
      Subtype.ext (by push_cast; exact mul_inv_cancel₀ (hsF0 σ))
    exact (R i).residue_ne_zero_of_isUnit (isUnit_iff_exists_inv.mpr ⟨_, hmul⟩)

  let d' := Fintype.card (Σ i, Fin (d i))
  let e : (Σ i, Fin (d i)) ≃ Fin d' := Fintype.equivFin _
  refine ⟨d', fun σ => z' (e.symm σ), fun σ i => hz'mem (e.symm σ) i, ?_, ?_, ?_⟩
  ·
    exact fun σ V hVL hVf => hszT (e.symm σ) V hVL hVf
  ·
    intro q q' hqq'
    suffices h : ∀ τ : Σ i, Fin (d i), q (e τ) = q' (e τ) by
      funext σ; simpa using h (e.symm σ)
    rintro ⟨i, l⟩
    have hi := hqq' i

    have hreidx : ∀ p : Fin d' → Polynomial k,
        ∑ σ : Fin d', Polynomial.aeval ((R i).residue ⟨f, hf i⟩) (p σ) *
          (R i).residue ⟨z' (e.symm σ), hz'mem (e.symm σ) i⟩ =
        ∑ τ : Σ i', Fin (d i'), Polynomial.aeval ((R i).residue ⟨f, hf i⟩) (p (e τ)) *
          (R i).residue ⟨z' τ, hz'mem τ i⟩ := fun p =>
      Fintype.sum_equiv e.symm _ _ (fun σ => by rw [Equiv.apply_symm_apply])
    rw [hreidx q, hreidx q'] at hi

    have hz'res : ∀ τ : Σ i', Fin (d i'),
        (R i).residue ⟨z' τ, hz'mem τ i⟩ =
          (R i).residue ⟨(s τ : F), hsmemi τ i⟩ * (R i).residue ⟨z τ, hzmem τ i⟩ := fun τ => by
      have heqO : (⟨z' τ, hz'mem τ i⟩ : (R i).integers) =
          ⟨(s τ : F), hsmemi τ i⟩ * ⟨z τ, hzmem τ i⟩ := Subtype.ext rfl
      rw [heqO, map_mul]
    simp only [hz'res, ← mul_assoc] at hi

    have hredL : ∀ p : Fin d' → Polynomial k,
        ∑ τ : Σ i', Fin (d i'),
          (Polynomial.aeval ((R i).residue ⟨f, hf i⟩) (p (e τ)) *
            (R i).residue ⟨(s τ : F), hsmemi τ i⟩) * (R i).residue ⟨z τ, hzmem τ i⟩ =
        ∑ l' : Fin (d i),
          (Polynomial.aeval ((R i).residue ⟨f, hf i⟩) (p (e ⟨i, l'⟩)) *
            (R i).residue ⟨(s ⟨i,l'⟩ : F), hsmemi ⟨i,l'⟩ i⟩) * yb i l' := fun p => by
      rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
      rw [Finset.sum_eq_single i (fun i' _ hi' => ?_) (fun h => absurd (Finset.mem_univ i) h)]
      · exact Finset.sum_congr rfl fun l' _ => by rw [hzi ⟨i, l'⟩]
      · exact Finset.sum_eq_zero fun l' _ => by
          rw [hzl ⟨i', l'⟩ i (Ne.symm hi'), mul_zero]
    rw [hredL q, hredL q'] at hi

    set fbi := (R i).residue ⟨f, hf i⟩
    have hcoefadj : ∀ (p : Fin d' → Polynomial k) l',
        Polynomial.aeval fbi (p (e ⟨i, l'⟩)) *
          (R i).residue ⟨(s ⟨i,l'⟩ : F), hsmemi ⟨i,l'⟩ i⟩ ∈
        IntermediateField.adjoin k ({fbi} : Set (Fb i)) := fun p l' =>
      mul_mem (IntermediateField.algebra_adjoin_le_adjoin k {fbi}
          (Polynomial.aeval_mem_adjoin_singleton k fbi))
        (hsres ⟨i,l'⟩ i).choose_spec
    have hliapp := Fintype.linearIndependent_iff.mp (hyb i)
      (fun l' => ⟨_, hcoefadj q l'⟩ - ⟨_, hcoefadj q' l'⟩) ?_ l
    · have hsub := congrArg Subtype.val hliapp
      simp only [AddSubgroupClass.coe_sub, ZeroMemClass.coe_zero] at hsub
      have heq := sub_eq_zero.mp hsub
      have hcancel := mul_right_cancel₀ (hsres0 ⟨i,l⟩ i) heq
      exact (transcendental_iff_injective.mp (htr i)) hcancel
    ·
      have hdiff : ∑ l', ((⟨_, hcoefadj q l'⟩ : IntermediateField.adjoin k ({fbi} : Set (Fb i)))
            - ⟨_, hcoefadj q' l'⟩) • yb i l' = 0 := by
        rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at hi
        refine hi ▸ (Finset.sum_congr rfl fun l' _ => ?_).symm
        rw [sub_smul, IntermediateField.smul_def, IntermediateField.smul_def, smul_eq_mul,
          smul_eq_mul]
      exact hdiff
  ·
    intro b hb
    obtain ⟨c, hcW, hcb⟩ := hWspan b hb
    refine ⟨fun σ => c (e.symm σ) * (s (e.symm σ))⁻¹, fun σ => ?_, ?_⟩
    · show ((c (e.symm σ) * (s (e.symm σ))⁻¹ : K) : F) ∈ (R i₀).integers
      rw [IntermediateField.coe_mul, IntermediateField.coe_inv]
      exact mul_mem (hcW _) (hsinvF (e.symm σ))
    · rw [hcb]
      refine (Fintype.sum_equiv e.symm _ _ (fun τ => ?_)).symm
      simp only [Equiv.apply_symm_apply]
      show ((c (e.symm τ) * (s (e.symm τ))⁻¹ : K) : F) * z' (e.symm τ) =
        (c (e.symm τ) : F) * z (e.symm τ)
      rw [IntermediateField.coe_mul, IntermediateField.coe_inv, mul_assoc,
        show z' (e.symm τ) = (s (e.symm τ) : F) * z (e.symm τ) from rfl,
        ← mul_assoc ((s (e.symm τ) : F)⁻¹), inv_mul_cancel₀ (hsF0 _), one_mul]

end
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq.FinGeSol P2MW.S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq.FinGeSol.Generic"

end S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq (solution)
