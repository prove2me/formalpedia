-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/608ccd47-d360-5ef9-98ef-7dde72c6577a

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ValuationSubring_sum_finrank_residueField_le_finrank_of_forall_mem_iff
import Theorems.Thm_AlgebraicCurve_RegularProlongation_mem_adjoin_iff_mem_integers_iff_of_transcendental_residue
import Theorems.Thm_AlgebraicCurve_RegularProlongation_coeff_mem_of_aeval_mem_integers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq

set_option autoImplicit false

open AlgebraicCurve IsLocalRing Polynomial

namespace D342

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar] (R : RegularProlongation A F Fbar)

def constHom : A →+* R.integers where
  toFun a := ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[scoped simp] theorem coe_constHom (a : A) : ((constHom R a : R.integers) : F) = algebraMap L F a := rfl

theorem residue_constHom (a : A) : R.residue (constHom R a) = algebraMap (ResidueField A) Fbar (residue A a) :=
  R.residue_algebraMap a

theorem coe_eval₂_constHom (x : R.integers) (q : A[X]) :
    ((q.eval₂ (constHom R) x : R.integers) : F) = aeval (x : F) (q.map (algebraMap A L)) := by
  have h1 : ((q.eval₂ (constHom R) x : R.integers) : F) = q.eval₂ (R.integers.subtype.comp (constHom R)) (x : F) :=
    Polynomial.hom_eval₂ q (constHom R) R.integers.subtype x
  rw [h1, aeval_def, eval₂_map]
  congr 1

theorem residue_eval₂_constHom (x : R.integers) (q : A[X]) :
    R.residue (q.eval₂ (constHom R) x) = aeval (R.residue x) (q.map (residue A)) := by
  rw [Polynomial.hom_eval₂, aeval_def, eval₂_map]
  congr 1
  exact RingHom.ext fun a => residue_constHom R a

theorem exists_smul_coeff_mem (s : L[X]) (hs : s ≠ 0) :
    ∃ c : L, c ≠ 0 ∧ (∀ j, (c • s).coeff j ∈ A) ∧ ∃ m, A.valuation ((c • s).coeff m) = 1 := by
  classical
  obtain ⟨m, hm, hmax⟩ := s.support.exists_max_image (fun j => A.valuation (s.coeff j))
    (Polynomial.support_nonempty.mpr hs)
  have hm0 : s.coeff m ≠ 0 := Polynomial.mem_support_iff.mp hm
  refine ⟨(s.coeff m)⁻¹, inv_ne_zero hm0, fun j => ?_, m, ?_⟩
  · rw [Polynomial.coeff_smul, smul_eq_mul, ← A.valuation_le_one_iff, map_mul, map_inv₀]
    by_cases hj : j ∈ s.support
    · calc (A.valuation (s.coeff m))⁻¹ * A.valuation (s.coeff j)
          ≤ (A.valuation (s.coeff m))⁻¹ * A.valuation (s.coeff m) := by gcongr; exact hmax j hj
        _ = 1 := inv_mul_cancel₀ ((_root_.map_ne_zero _).mpr hm0)
    · rw [Polynomial.notMem_support_iff.mp hj, map_zero, mul_zero]; exact zero_le_one
  · rw [Polynomial.coeff_smul, smul_eq_mul, map_mul, map_inv₀, inv_mul_cancel₀ ((_root_.map_ne_zero _).mpr hm0)]

theorem aeval_mem_adjoin' (y : Fbar) (p : (ResidueField A)[X]) :
    aeval y p ∈ IntermediateField.adjoin (ResidueField A) ({y} : Set Fbar) :=
  IntermediateField.algebra_adjoin_le_adjoin _ _ (Polynomial.aeval_mem_adjoin_singleton _ y)

theorem residue_mem_adjoin_of_mem_adjoin (x : R.integers) (hx : Transcendental (ResidueField A) (R.residue x))
    (a : F) (ha : a ∈ IntermediateField.adjoin L ({(x : F)} : Set F)) (haO : a ∈ R.integers) :
    R.residue ⟨a, haO⟩ ∈ IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar) := by
  classical
  set K := IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar) with hK
  rw [IntermediateField.mem_adjoin_simple_iff] at ha
  obtain ⟨r, s, hrs⟩ := ha
  by_cases hs0 : aeval (x : F) s = 0
  · have : (⟨a, haO⟩ : R.integers) = 0 := Subtype.ext (show a = ((0 : R.integers) : F) by rw [hrs, hs0, div_zero]; rfl)
    rw [this, map_zero]; exact zero_mem K
  have hs : s ≠ 0 := by rintro rfl; exact hs0 (map_zero _)

  obtain ⟨c, hc0, hcs, m, hm⟩ := exists_smul_coeff_mem (A := A) s hs
  obtain ⟨sA, hsA⟩ : ∃ sA : A[X], sA.map (algebraMap A L) = c • s := by
    rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
    intro j; exact ⟨⟨_, hcs j⟩, rfl⟩
  set u : R.integers := sA.eval₂ (constHom R) x with hu
  have hu_coe : (u : F) = c • aeval (x : F) s := by
    rw [hu, coe_eval₂_constHom, hsA, map_smul]
  have hu_res : R.residue u = aeval (R.residue x) (sA.map (residue A)) := residue_eval₂_constHom R x sA
  have hsA0 : sA.map (residue A) ≠ 0 := by
    intro h0
    have hcm : (sA.map (residue A)).coeff m = 0 := by rw [h0, coeff_zero]
    rw [coeff_map] at hcm
    have hvm : A.valuation ((sA.coeff m : A) : L) = 1 := by
      have := congrArg (fun q : L[X] => q.coeff m) hsA
      simp only [coeff_map] at this
      rw [show ((sA.coeff m : A) : L) = algebraMap A L (sA.coeff m) from rfl, this]; exact hm
    have hunit : IsUnit (sA.coeff m) := (A.valuation_eq_one_iff _).mpr hvm
    exact (residue_ne_zero_iff_isUnit _ |>.mpr hunit) hcm
  have hures0 : R.residue u ≠ 0 := by
    rw [hu_res]
    intro h0
    exact hx ⟨sA.map (residue A), hsA0, h0⟩
  obtain ⟨uu, huu⟩ := R.isUnit_of_residue_ne_zero hures0

  have hv : aeval (x : F) (c • r) = a * (u : F) := by
    rw [map_smul, hu_coe, hrs, mul_smul_comm, div_mul_cancel₀ _ hs0]
  have hvO : aeval (x : F) (c • r) ∈ R.integers := by rw [hv]; exact mul_mem haO u.2
  have hcr : ∀ j, (c • r).coeff j ∈ A := fun j =>
    AlgebraicCurve.RegularProlongation.coeff_mem_of_aeval_mem_integers A R x hx (c • r) hvO j
  obtain ⟨rA, hrA⟩ : ∃ rA : A[X], rA.map (algebraMap A L) = c • r := by
    rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
    intro j; exact ⟨⟨_, hcr j⟩, rfl⟩
  have hv' : (⟨aeval (x : F) (c • r), hvO⟩ : R.integers) = rA.eval₂ (constHom R) x := by
    apply Subtype.ext; rw [coe_eval₂_constHom, hrA]

  have hprod : (⟨a, haO⟩ : R.integers) * u = ⟨aeval (x : F) (c • r), hvO⟩ := Subtype.ext hv.symm
  have hres : R.residue ⟨a, haO⟩ * R.residue u = aeval (R.residue x) (rA.map (residue A)) := by
    rw [← map_mul, hprod, hv', residue_eval₂_constHom]
  have hfinal : R.residue ⟨a, haO⟩ = aeval (R.residue x) (rA.map (residue A)) * (R.residue u)⁻¹ := by
    rw [← hres, mul_inv_cancel_right₀ hures0]
  rw [hfinal]
  refine mul_mem (aeval_mem_adjoin' _ _) (inv_mem ?_)
  rw [hu_res]; exact aeval_mem_adjoin' _ _

section ResAlg
variable {E F : Type*} [Field E] [Field F] [Algebra E F]
  (O : ValuationSubring E) (O' : ValuationSubring F) (h : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O)

def incl : O →+* O' where
  toFun x := ⟨algebraMap E F x, (h x).mpr x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[scoped simp] theorem coe_incl (x : O) : ((incl O O' h x : O') : F) = algebraMap E F x := rfl

theorem isLocalHom_incl : IsLocalHom (incl O O' h) := by
  constructor
  intro x hx

  have hx0 : (x : E) ≠ 0 := by
    intro h0
    have : incl O O' h x = 0 := Subtype.ext (by simp [h0])
    rw [this] at hx; exact not_isUnit_zero hx
  have hinv' : (algebraMap E F (x : E))⁻¹ ∈ O' := by
    obtain ⟨u, hu⟩ := hx
    have h1 : ((↑u⁻¹ : O') : F) * algebraMap E F (x : E) = 1 := by
      have h2 : ((↑u⁻¹ : O') : F) * ((u : O') : F) = 1 := by exact_mod_cast congrArg Subtype.val u.inv_mul
      rwa [hu, coe_incl] at h2
    have : (algebraMap E F (x : E))⁻¹ = ((↑u⁻¹ : O') : F) := (eq_inv_of_mul_eq_one_left h1).symm
    rw [this]; exact (↑u⁻¹ : O').2
  have hinv : (x : E)⁻¹ ∈ O := (h _).mp (by rwa [map_inv₀])
  exact ⟨⟨x, ⟨(x : E)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩

@[reducible] noncomputable def resAlg : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O') :=
  (@IsLocalRing.ResidueField.map O O' _ _ _ _ (incl O O' h) (isLocalHom_incl O O' h)).toAlgebra

theorem resAlg_compat (a : O) :
    (letI := resAlg O O' h;
      algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O') (IsLocalRing.residue O a)) =
      IsLocalRing.residue O' ⟨algebraMap E F a, (h a).mpr a.2⟩ := by
  rfl

end ResAlg

section Degree

noncomputable def resEquiv : ResidueField R.integers ≃+* Fbar :=
  (Ideal.quotEquivOfEq R.ker_residue.symm).trans (RingHom.quotientKerEquivOfSurjective R.residue_surjective)

theorem resEquiv_residue (z : R.integers) : resEquiv R (residue R.integers z) = R.residue z := by
  simp [resEquiv, RingHom.quotientKerEquivOfSurjective, Ideal.quotEquivOfEq]
  rfl

variable {E : Type*} [Field E] [Algebra E F]

theorem finrank_adjoin_le_finrank_residueField (x : R.integers) (hx : Transcendental (ResidueField A) (R.residue x))
    (O : ValuationSubring E) (h : ∀ e : E, algebraMap E F e ∈ R.integers ↔ e ∈ O)
    (hE : ∀ e : E, algebraMap E F e ∈ IntermediateField.adjoin L ({(x : F)} : Set F))
    (hfd : letI := resAlg O R.integers h; FiniteDimensional (ResidueField O) (ResidueField R.integers)) :
    letI := resAlg O R.integers h
    Module.finrank (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar ≤
      Module.finrank (ResidueField O) (ResidueField R.integers) := by
  letI := resAlg O R.integers h
  set K := IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar) with hK
  let ρ := resEquiv R
  let φ : ResidueField O →+* Fbar := ρ.toRingHom.comp (algebraMap (ResidueField O) (ResidueField R.integers))
  letI algφ : Algebra (ResidueField O) Fbar := φ.toAlgebra

  let ρₗ : ResidueField R.integers ≃ₗ[ResidueField O] Fbar :=
    { ρ.toAddEquiv with
      map_smul' := fun c z => by
        show ρ (c • z) = φ c * ρ z
        rw [Algebra.smul_def, map_mul]; rfl }
  haveI : FiniteDimensional (ResidueField O) Fbar := LinearEquiv.finiteDimensional ρₗ
  have h1 : Module.finrank (ResidueField O) (ResidueField R.integers) = Module.finrank (ResidueField O) Fbar :=
    ρₗ.finrank_eq

  have hφK : ∀ c, φ c ∈ K := by
    intro c
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    show ρ (algebraMap (ResidueField O) (ResidueField R.integers) (residue O a)) ∈ K
    rw [resAlg_compat O R.integers h a, resEquiv_residue]
    exact residue_mem_adjoin_of_mem_adjoin R x hx _ (hE a) _
  letI algK : Algebra (ResidueField O) K := (φ.codRestrict K hφK).toAlgebra
  haveI : IsScalarTower (ResidueField O) K Fbar := IsScalarTower.of_algebraMap_eq (fun c => rfl)
  haveI : FiniteDimensional (ResidueField O) K :=
    FiniteDimensional.of_injective (IsScalarTower.toAlgHom (ResidueField O) K Fbar).toLinearMap
      (fun a b hab => Subtype.ext hab)
  have hKpos : 0 < Module.finrank (ResidueField O) K := Module.finrank_pos
  have htower := Module.finrank_mul_finrank (ResidueField O) K Fbar
  rw [h1, ← htower]
  exact Nat.le_mul_of_pos_left _ hKpos

end Degree

end D342
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq.D342"

open AlgebraicCurve IsLocalRing

namespace D342

variable {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]

def gaussRing (f : F) (O : ValuationSubring F) : ValuationSubring ↥(IntermediateField.adjoin L ({f} : Set F)) :=
  O.comap (algebraMap ↥(IntermediateField.adjoin L ({f} : Set F)) F)

theorem mem_gaussRing_iff (f : F) (O : ValuationSubring F) (x : ↥(IntermediateField.adjoin L ({f} : Set F))) :
    x ∈ gaussRing (L := L) f O ↔ (x : F) ∈ O := Iff.rfl

end D342
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq.D342"

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] [Nonempty ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (i₀ : ι) (V : ValuationSubring F)
    (hV : ∀ e : F, e ∈ IntermediateField.adjoin L {f} → (e ∈ V ↔ e ∈ (R i₀).integers)) :
    ∃ j, V = (R j).integers := by
  classical
  by_contra hnot
  push Not at hnot

  set E := IntermediateField.adjoin L ({f} : Set F) with hEdef
  let O : ValuationSubring ↥E := D342.gaussRing (L := L) f (R i₀).integers

  let O' : Option ι → ValuationSubring F := fun j => j.elim V (fun i => (R i).integers)
  have hinj : Function.Injective O' := by
    intro j j' hjj'
    cases j with
    | none => cases j' with
      | none => rfl
      | some i' => exact absurd hjj' (hnot i')
    | some i => cases j' with
      | none => exact absurd hjj'.symm (hnot i)
      | some i' => exact congrArg some (hR hjj')
  have hO : ∀ (j : Option ι) (x : ↥E), algebraMap (↥E) F x ∈ O' j ↔ x ∈ O := by
    intro j x
    show (x : F) ∈ O' j ↔ (x : F) ∈ (R i₀).integers
    cases j with
    | none => exact hV x x.2
    | some i =>
      exact AlgebraicCurve.RegularProlongation.mem_adjoin_iff_mem_integers_iff_of_transcendental_residue
          A (R i) (R i₀) f (hf i) (hf i₀) (htr i) (htr i₀) x x.2

  letI hinst : ∀ j, Algebra (IsLocalRing.ResidueField ↥O) (IsLocalRing.ResidueField ↥(O' j)) :=
    fun j => D342.resAlg O (O' j) (hO j)
  have hcompat : ∀ (j : Option ι) (a : ↥O), algebraMap (IsLocalRing.ResidueField ↥O) (IsLocalRing.ResidueField ↥(O' j)) (IsLocalRing.residue ↥O a) =
      IsLocalRing.residue ↥(O' j) ⟨algebraMap (↥E) F a, (hO j a).mpr a.2⟩ := fun j a => D342.resAlg_compat O (O' j) (hO j) a
  obtain ⟨hfd, hsum⟩ := ValuationSubring.sum_finrank_residueField_le_finrank_of_forall_mem_iff O O' hinj hO hcompat

  have hGR : ∀ i, Module.finrank (IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      ≤ Module.finrank (IsLocalRing.ResidueField ↥O) (IsLocalRing.ResidueField ↥(O' (some i))) := fun i =>
    D342.finrank_adjoin_le_finrank_residueField (R i) ⟨f, hf i⟩ (htr i) O (hO (some i)) (fun e => e.2) (hfd (some i))
  have hV1 : 1 ≤ Module.finrank (IsLocalRing.ResidueField ↥O) (IsLocalRing.ResidueField ↥(O' none)) := by
    haveI := hfd none
    exact Module.finrank_pos

  have : ∑ j, Module.finrank (IsLocalRing.ResidueField ↥O) (IsLocalRing.ResidueField ↥(O' j)) ≥ Module.finrank (↥E) F + 1 := by
    rw [Fintype.sum_option, ← heq]
    have := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hGR i)
    omega
  omega

end S_AlgebraicCurve_RegularProlongation_exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq (solution)
