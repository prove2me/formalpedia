-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_prolongation_of_card_roots_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/ee971fec-c84c-5f5f-a24b-4a539be66138

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ValuationSubring_exists_sub_mem_nonunits_of_finrank_le_card
import Theorems.Thm_ValuationSubring_exists_valuation_mul_eq_one_of_finrank_le_card
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve Polynomial IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "RegularProlongation"
namespace RegularProlongation
p2m_export "AlgebraicCurve.RegularProlongation" "isUnit_of_residue_ne_zero residue_ne_zero_of_isUnit integers residue_algebraMap residue_surjective algebraMap_mem_iff exists_smul_mem ker_residue residue"
namespace KummerSplitting
p2m_open "AlgebraicCurve.RegularProlongation AlgebraicCurve"

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
variable (R : RegularProlongation A F Fbar)

private theorem _root_.AlgebraicCurve.RegularProlongation.KummerSplitting.residue_eq_zero_iff (x : R.integers) :
    R.residue x = 0 ↔ x ∈ maximalIdeal R.integers := by
  rw [← R.ker_residue]; rfl

p2m_export "AlgebraicCurve.RegularProlongation.KummerSplitting" "residue_eq_zero_iff"
theorem residue_eq_zero_iff_lt (x : R.integers) :
    R.residue x = 0 ↔ R.integers.valuation (x : F) < 1 := by
  rw [residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]

theorem residue_ne_zero_iff_isUnit (x : R.integers) : R.residue x ≠ 0 ↔ IsUnit x :=
  ⟨R.isUnit_of_residue_ne_zero, R.residue_ne_zero_of_isUnit⟩

theorem exists_residue_eq (t : Fbar) : ∃ y : R.integers, R.residue y = t :=
  R.residue_surjective t

section Numerics

variable {q : ℕ} [hq : Fact q.Prime] (f : R.integers) (S : Finset Fbar) (hS : S.card = q)
  (hSf : ∀ s ∈ S, s ^ q = R.residue f)
include hS hSf

theorem residue_f_ne_zero : R.residue f ≠ 0 := by
  intro h0
  have hsub : S ⊆ {0} := fun s hs => by
    have h := hSf s hs
    rw [h0] at h
    exact Finset.mem_singleton.mpr (pow_eq_zero_iff hq.out.ne_zero |>.mp h)
  have h := Finset.card_le_card hsub
  rw [hS, Finset.card_singleton] at h
  exact absurd h (not_le.mpr hq.out.one_lt)

theorem natCast_ne_zero_Fbar : (q : Fbar) ≠ 0 := by
  intro h0
  haveI : CharP Fbar q := (CharP.charP_iff_prime_eq_zero hq.out).mpr h0
  have hsub : ∀ s ∈ S, ∀ t ∈ S, s = t := fun s hs t ht => by
    have h : (s - t) ^ q = 0 := by rw [sub_pow_char, hSf s hs, hSf t ht, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff hq.out.ne_zero |>.mp h)
  have h := Finset.card_le_one.mpr hsub
  rw [hS] at h
  exact absurd h (not_le.mpr hq.out.one_lt)

theorem isUnit_f : IsUnit f := R.isUnit_of_residue_ne_zero (residue_f_ne_zero R f S hS hSf)

theorem coe_f_ne_zero : (f : F) ≠ 0 := by
  have h := (isUnit_f R f S hS hSf).ne_zero
  exact fun h0 => h (Subtype.ext h0)

theorem isUnit_natCast : IsUnit (q : R.integers) :=
  R.isUnit_of_residue_ne_zero (by rw [map_natCast]; exact natCast_ne_zero_Fbar R f S hS hSf)

theorem natCast_ne_zero_F : (q : F) ≠ 0 := by
  have h := (isUnit_natCast R f S hS hSf).ne_zero
  intro h0
  apply h
  exact Subtype.ext (by simpa using h0)

end Numerics

theorem isUnit_sub_of_residue_ne {x y : R.integers} (h : R.residue x ≠ R.residue y) :
    IsUnit (x - y) :=
  R.isUnit_of_residue_ne_zero (by rwa [map_sub, sub_ne_zero])

end AlgebraicCurve.RegularProlongation.KummerSplitting

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "RegularProlongation"
namespace RegularProlongation
p2m_export "AlgebraicCurve.RegularProlongation" "isUnit_of_residue_ne_zero residue_ne_zero_of_isUnit integers residue_algebraMap residue_surjective algebraMap_mem_iff exists_smul_mem ker_residue residue"
namespace KummerSplitting
p2m_open "AlgebraicCurve.RegularProlongation AlgebraicCurve"

section Kummer

variable {F : Type*} [Field F] {q : ℕ} [hq : Fact q.Prime] {f : F}
  (hf0 : f ≠ 0) (hqF : (q : F) ≠ 0)
  (F' : Type*) [Field F'] [Algebra F F'] [IsSplittingField F F' (X ^ q - C f)]
  (hdeg : Module.finrank F F' = q)
include hf0 hqF hdeg

theorem irreducible_X_pow_sub_C : Irreducible (X ^ q - C f) := by
  rw [X_pow_sub_C_irreducible_iff_of_prime hq.out]
  intro g hg
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  set P : F[X] := X ^ q - C f with hP
  have hP0 : P ≠ 0 := X_pow_sub_C_ne_zero hq.out.pos f
  have hsplit := IsSplittingField.splits F' P
  have hsep : P.Separable := separable_X_pow_sub_C f hqF hf0
  have hcard : Fintype.card (P.rootSet F') = q := by
    rw [card_rootSet_eq_natDegree hsep hsplit, hP, natDegree_X_pow_sub_C]
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hf0 (by rw [← hg, zero_pow hq.out.ne_zero])
  set g' : F' := algebraMap F F' g with hg'
  have hg'0 : g' ≠ 0 := (_root_.map_ne_zero _).mpr hg0
  have hff' : algebraMap F F' f ≠ 0 := (_root_.map_ne_zero _).mpr hf0
  have hmem : ∀ β : F', β ∈ P.rootSet F' ↔ β ^ q = algebraMap F F' f := by
    intro β
    rw [mem_rootSet, hP]
    simp only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero]
    exact ⟨fun h => h.2, fun h => ⟨hP ▸ hP0, h⟩⟩
  have hg'mem : g' ∈ P.rootSet F' := (hmem g').mpr (by rw [hg', ← map_pow, hg])
  obtain ⟨β, hβmem, hβne⟩ : ∃ β ∈ P.rootSet F', β ≠ g' := by
    by_contra! hall
    have h1 : Fintype.card (P.rootSet F') ≤ 1 :=
      Fintype.card_le_one_iff.mpr fun a b => Subtype.ext ((hall a a.2).trans (hall b b.2).symm)
    rw [hcard] at h1
    exact absurd h1 (not_le.mpr hq.out.one_lt)
  have hroot1 : ∀ β' ∈ P.rootSet F', (β' / g') ^ q = 1 := fun β' hβ' => by
    rw [div_pow, (hmem β').mp hβ', hg', ← map_pow, hg, div_self hff']
  set μ : F' := β / g' with hμdef
  have hμ1 : μ ≠ 1 := fun h => hβne (by rwa [hμdef, div_eq_one_iff_eq hg'0] at h)
  have hμ : IsPrimitiveRoot μ q := by
    have h := orderOf_eq_prime (hroot1 β hβmem) hμ1
    rw [← h]
    exact IsPrimitiveRoot.orderOf μ

  have hsub : (P.rootSet F' : Set F') ⊆ (IntermediateField.adjoin F ({μ} : Set F') : Set F') := by
    intro β' hβ'
    obtain ⟨i, -, hi⟩ := hμ.eq_pow_of_pow_eq_one (hroot1 β' hβ')
    have hβ'eq : β' = g' * μ ^ i := by rw [hi, mul_div_cancel₀ _ hg'0]
    rw [hβ'eq]
    exact mul_mem (algebraMap_mem _ g)
      (pow_mem (IntermediateField.mem_adjoin_simple_self F μ) i)
  have htop : IntermediateField.adjoin F ({μ} : Set F') = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.top_toSubalgebra, eq_top_iff, ← IsSplittingField.adjoin_rootSet F' P]
    exact Algebra.adjoin_le hsub

  have hint : IsIntegral F μ := (hμ.isIntegral hq.out.pos).tower_top
  have hdvd : minpoly F μ ∣ cyclotomic q F := by
    apply minpoly.dvd
    have h := hμ.isRoot_cyclotomic hq.out.pos
    rwa [← map_cyclotomic q (algebraMap F F'), IsRoot, eval_map, ← aeval_def] at h
  have hle : (minpoly F μ).natDegree ≤ q - 1 := by
    have h := natDegree_le_of_dvd hdvd (cyclotomic_ne_zero q F)
    rwa [natDegree_cyclotomic, Nat.totient_prime hq.out] at h
  have hfin : Module.finrank F F' ≤ q - 1 := by
    rw [← IntermediateField.finrank_top', ← htop, IntermediateField.adjoin.finrank hint]
    exact hle
  have h1 := hq.out.one_lt
  omega

theorem minpoly_eq {α : F'} (hα : α ^ q = algebraMap F F' f) : minpoly F α = X ^ q - C f :=
  (minpoly.eq_of_irreducible_of_monic (irreducible_X_pow_sub_C hf0 hqF F' hdeg)
    (by simp [hα]) (monic_X_pow_sub_C f hq.out.ne_zero)).symm

theorem dvd_of_aeval_eq_zero {O : Type*} [CommRing O] [IsDomain O] (i : O →+* F)
    (hi : Function.Injective i) (fO : O) (hfO : i fO = f)
    {α : F'} (hα : α ^ q = algebraMap F F' f)
    (p : O[X]) (hp : aeval α (p.map i) = 0) :
    (X ^ q - C fO) ∣ p := by
  set P : O[X] := X ^ q - C fO with hP
  have hPm : P.Monic := monic_X_pow_sub_C fO hq.out.ne_zero
  have hPmap : P.map i = X ^ q - C f := by
    rw [hP, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, hfO]
  have hdecomp := modByMonic_add_div p P

  set r := p %ₘ P with hr
  have hraeval : aeval α (r.map i) = 0 := by
    have h : p.map i = r.map i + (X ^ q - C f) * (p /ₘ P).map i := by
      rw [← hPmap, ← Polynomial.map_mul, ← Polynomial.map_add, hdecomp]
    rw [h, map_add, map_mul] at hp
    simpa [hα] using hp
  have hr0 : r = 0 := by
    by_contra hne
    have hne' : r.map i ≠ 0 := (Polynomial.map_ne_zero_iff hi).mpr hne
    have hle := minpoly.degree_le_of_ne_zero F α hne' hraeval
    rw [minpoly_eq hf0 hqF F' hdeg hα, degree_X_pow_sub_C hq.out.pos] at hle
    have hlt : (r.map i).degree < q := by
      refine lt_of_le_of_lt degree_map_le ?_
      have h := degree_modByMonic_lt p hPm
      rwa [degree_X_pow_sub_C hq.out.pos] at h
    exact absurd hle (not_le.mpr hlt)
  refine ⟨p /ₘ P, ?_⟩
  have h := hdecomp
  rw [hr0, zero_add] at h
  exact h.symm

end Kummer

end AlgebraicCurve.RegularProlongation.KummerSplitting

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "RegularProlongation"
namespace RegularProlongation
p2m_export "AlgebraicCurve.RegularProlongation" "isUnit_of_residue_ne_zero residue_ne_zero_of_isUnit integers residue_algebraMap residue_surjective algebraMap_mem_iff exists_smul_mem ker_residue residue"
namespace KummerSplitting
p2m_open "AlgebraicCurve.RegularProlongation AlgebraicCurve"

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
variable (R : RegularProlongation A F Fbar)
variable {F' : Type*} [Field F'] [Algebra F F']

def evalAt (α : F') : R.integers[X] →+* F' :=
  (aeval α : F[X] →ₐ[F] F').toRingHom.comp (mapRingHom R.integers.subtype)

theorem evalAt_apply (α : F') (p : R.integers[X]) :
    evalAt R α p = aeval α (p.map R.integers.subtype) := rfl

@[scoped simp] theorem evalAt_C (α : F') (y : R.integers) :
    evalAt R α (C y) = algebraMap F F' (y : F) := by
  simp [evalAt_apply]

@[scoped simp] theorem evalAt_X (α : F') : evalAt R α X = α := by simp [evalAt_apply]

def resEval (s : Fbar) : R.integers[X] →+* Fbar := eval₂RingHom R.residue s

@[scoped simp] theorem resEval_C (s : Fbar) (y : R.integers) : resEval R s (C y) = R.residue y :=
  eval₂_C _ _

@[scoped simp] theorem resEval_X (s : Fbar) : resEval R s X = s := eval₂_X _ _

structure CentredAt (α : F') (s : Fbar) (V : ValuationSubring F') : Prop where
  mem : ∀ p : R.integers[X], evalAt R α p ∈ V
  lt_one : ∀ p : R.integers[X], resEval R s p = 0 → V.valuation (evalAt R α p) < 1

namespace CentredAt

variable {R} {α : F'} {s : Fbar} {V : ValuationSubring F'} (hV : CentredAt R α s V)
include hV

theorem algebraMap_mem (y : R.integers) : algebraMap F F' (y : F) ∈ V := by
  simpa using hV.mem (C y)

theorem root_mem : α ∈ V := by simpa using hV.mem X

theorem valuation_lt_one_of_residue_eq_zero {y : R.integers} (hy : R.residue y = 0) :
    V.valuation (algebraMap F F' (y : F)) < 1 := by
  simpa using hV.lt_one (C y) (by simpa using hy)

theorem valuation_eq_one_of_isUnit {y : R.integers} (hy : IsUnit y) :
    V.valuation (algebraMap F F' (y : F)) = 1 := by
  obtain ⟨u, rfl⟩ := hy
  apply le_antisymm (V.valuation_le_one_iff _ |>.mpr (hV.algebraMap_mem _))
  have h1 : V.valuation (algebraMap F F' ((↑u⁻¹ : R.integers) : F)) ≤ 1 :=
    (V.valuation_le_one_iff _).mpr (hV.algebraMap_mem _)
  have hmul : V.valuation (algebraMap F F' ((u : R.integers) : F)) *
      V.valuation (algebraMap F F' ((↑u⁻¹ : R.integers) : F)) = 1 := by
    rw [← map_mul, ← map_mul, ← Subring.coe_mul, Units.mul_inv]
    simp
  calc (1 : _) = _ := hmul.symm
    _ ≤ V.valuation (algebraMap F F' ((u : R.integers) : F)) * 1 := mul_le_mul_right h1 _
    _ = _ := mul_one _

theorem comap_eq : V.comap (algebraMap F F') = R.integers := by
  ext x
  rw [ValuationSubring.mem_comap]
  refine ⟨fun hx => ?_, fun hx => hV.algebraMap_mem ⟨x, hx⟩⟩
  by_contra hxO
  have hxinv : x⁻¹ ∈ R.integers := (R.integers.mem_or_inv_mem x).resolve_left hxO
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxO (zero_mem _)

  have hres : R.residue ⟨x⁻¹, hxinv⟩ = 0 := by
    by_contra hne
    obtain ⟨u, hu⟩ := R.isUnit_of_residue_ne_zero hne
    have hmul : (x⁻¹ : F) * ((↑u⁻¹ : R.integers) : F) = 1 := by
      have h := congrArg (fun z : R.integers => (z : F)) u.mul_inv
      simpa [hu] using h
    have hxeq : x = ((↑u⁻¹ : R.integers) : F) := (inv_mul_eq_one₀ hx0).mp hmul
    exact hxO (hxeq ▸ (↑u⁻¹ : R.integers).2)
  have hlt := hV.valuation_lt_one_of_residue_eq_zero hres
  have hle : V.valuation (algebraMap F F' x) ≤ 1 := (V.valuation_le_one_iff _).mpr hx
  have hmul : V.valuation (algebraMap F F' x⁻¹) * V.valuation (algebraMap F F' x) = 1 := by
    rw [← map_mul, ← map_mul, inv_mul_cancel₀ hx0, map_one, map_one]
  have : V.valuation (algebraMap F F' x⁻¹) * V.valuation (algebraMap F F' x) < 1 :=
    calc _ ≤ V.valuation (algebraMap F F' x⁻¹) * 1 := mul_le_mul_right hle _
      _ = _ := mul_one _
      _ < 1 := hlt
  exact absurd hmul this.ne

theorem valuation_root_sub_lt_one {y : R.integers} (hy : R.residue y = s) :
    V.valuation (α - algebraMap F F' (y : F)) < 1 := by
  have h := hV.lt_one (X - C y) (by simp [hy])
  rwa [map_sub, evalAt_X, evalAt_C] at h

end CentredAt

variable {R} in

theorem CentredAt.ne {α : F'} {s t : Fbar} {V W : ValuationSubring F'}
    (hV : CentredAt R α s V) (hW : CentredAt R α t W) (hst : s ≠ t) : V ≠ W := by
  obtain ⟨ys, hys⟩ := R.residue_surjective s
  obtain ⟨yt, hyt⟩ := R.residue_surjective t
  intro hVW
  have hunit : IsUnit (ys - yt) :=
    isUnit_sub_of_residue_ne R (by rw [hys, hyt]; exact hst)
  have h1 : V.valuation (algebraMap F F' ((ys : F) - (yt : F))) = 1 := by
    have h := hV.valuation_eq_one_of_isUnit hunit
    rwa [show ((ys - yt : R.integers) : F) = (ys : F) - (yt : F) from rfl] at h
  have hlt : V.valuation (α - algebraMap F F' (ys : F)) < 1 := hV.valuation_root_sub_lt_one hys
  have heq : V.valuation (α - algebraMap F F' (yt : F)) = 1 := by
    have hsum : α - algebraMap F F' (yt : F) =
        (α - algebraMap F F' (ys : F)) + algebraMap F F' ((ys : F) - (yt : F)) := by
      rw [map_sub]
      ring
    rw [hsum, Valuation.map_add_eq_of_lt_right V.valuation (lt_of_lt_of_eq hlt h1.symm), h1]
  have hlt' : W.valuation (α - algebraMap F F' (yt : F)) < 1 := hW.valuation_root_sub_lt_one hyt
  rw [hVW] at heq
  exact absurd heq hlt'.ne

section Existence

variable {q : ℕ} [hq : Fact q.Prime] (f : R.integers) (S : Finset Fbar) (hS : S.card = q)
  (hSf : ∀ s ∈ S, s ^ q = R.residue f)
  [IsSplittingField F F' (X ^ q - C (f : F))] (hdeg : Module.finrank F F' = q)
  {α : F'} (hα : α ^ q = algebraMap F F' (f : F))
include hS hSf hdeg hα

theorem resEval_eq_zero_of_evalAt_eq_zero {s : Fbar} (hs : s ^ q = R.residue f)
    (p : R.integers[X]) (hp : evalAt R α p = 0) : resEval R s p = 0 := by
  obtain ⟨g, hg⟩ := dvd_of_aeval_eq_zero (coe_f_ne_zero R f S hS hSf)
    (natCast_ne_zero_F R f S hS hSf) F' hdeg R.integers.subtype
    (fun a b h => Subtype.ext h) f rfl hα p hp
  rw [hg, map_mul, map_sub, map_pow, resEval_X, resEval_C, hs, sub_self, zero_mul]

theorem exists_centredAt {s : Fbar} (hs : s ^ q = R.residue f) :
    ∃ V : ValuationSubring F', CentredAt R α s V := by
  set e := evalAt R α with he
  have hsurj : Function.Surjective e.rangeRestrict := e.rangeRestrict_surjective
  have hker : RingHom.ker e.rangeRestrict ≤ RingHom.ker (resEval R s) := by
    intro p hp
    rw [RingHom.mem_ker] at hp ⊢
    apply resEval_eq_zero_of_evalAt_eq_zero R f S hS hSf hdeg hα hs
    have h := congrArg Subtype.val hp
    rwa [RingHom.coe_rangeRestrict] at h
  set φ : e.range →+* Fbar := e.rangeRestrict.liftOfSurjective hsurj ⟨resEval R s, hker⟩ with hφdef
  have hφ : ∀ p, φ (e.rangeRestrict p) = resEval R s p := fun p =>
    e.rangeRestrict.liftOfRightInverse_comp_apply _ _ ⟨resEval R s, hker⟩ p
  have hI : RingHom.ker φ ≠ ⊤ := by
    rw [Ne, Ideal.eq_top_iff_one, RingHom.mem_ker, map_one]
    exact one_ne_zero
  obtain ⟨V, hBV, hIV⟩ := Ideal.image_subset_nonunits_valuationSubring (RingHom.ker φ) hI
  refine ⟨V, ⟨fun p => hBV ⟨p, rfl⟩, fun p hp => ?_⟩⟩
  have hmem : e.rangeRestrict p ∈ RingHom.ker φ := by rw [RingHom.mem_ker, hφ, hp]
  have h : (e.rangeRestrict p : F') ∈ V.nonunits := hIV ⟨_, hmem, rfl⟩
  rw [RingHom.coe_rangeRestrict] at h
  exact h

end Existence

end AlgebraicCurve.RegularProlongation.KummerSplitting
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve.RegularProlongation P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve.RegularProlongation.KummerSplitting"
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve.RegularProlongation"
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "RegularProlongation"
namespace RegularProlongation
p2m_export "AlgebraicCurve.RegularProlongation" "isUnit_of_residue_ne_zero residue_ne_zero_of_isUnit integers residue_algebraMap residue_surjective algebraMap_mem_iff exists_smul_mem ker_residue residue"
namespace KummerSplitting
p2m_open "AlgebraicCurve.RegularProlongation AlgebraicCurve"

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
variable (R : RegularProlongation A F Fbar)
variable {F' : Type*} [Field F'] [Algebra F F']

section Lift

variable (V : ValuationSubring F') (hcomap : V.comap (algebraMap F F') = R.integers)

section Comap
include hcomap

theorem mem_of_mem_integers (y : R.integers) : algebraMap F F' (y : F) ∈ V := by
  have h : (y : F) ∈ V.comap (algebraMap F F') := by rw [hcomap]; exact y.2
  exact ValuationSubring.mem_comap.mp h

def incl : R.integers →+* V :=
  ((algebraMap F F').comp R.integers.subtype).codRestrict V
    (fun y => mem_of_mem_integers R V hcomap y)

@[scoped simp] theorem coe_incl (y : R.integers) :
    (incl R V hcomap y : F') = algebraMap F F' (y : F) := rfl

theorem valuation_map_lt_one_iff (x : F) :
    V.valuation (algebraMap F F' x) < 1 ↔ R.integers.valuation x < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, map_eq_zero,
    ← map_inv₀, ← ValuationSubring.mem_comap (A := V) (f := algebraMap F F'), hcomap]

theorem residue_eq_zero_iff_incl_mem (y : R.integers) :
    R.residue y = 0 ↔ incl R V hcomap y ∈ maximalIdeal V := by
  rw [residue_eq_zero_iff_lt, ValuationSubring.valuation_lt_one_iff, coe_incl,
    valuation_map_lt_one_iff R V hcomap]

def theta : R.integers →+* ResidueField V := (IsLocalRing.residue V).comp (incl R V hcomap)

theorem theta_apply (y : R.integers) :
    theta R V hcomap y = IsLocalRing.residue V (incl R V hcomap y) := rfl

theorem theta_eq_zero_iff (y : R.integers) : theta R V hcomap y = 0 ↔ R.residue y = 0 := by
  rw [theta_apply, IsLocalRing.residue_eq_zero_iff, residue_eq_zero_iff_incl_mem R V hcomap]

def thetaBar : ResidueField R.integers →+* ResidueField V :=
  Ideal.Quotient.lift (maximalIdeal R.integers) (theta R V hcomap)
    (fun y hy => (theta_eq_zero_iff R V hcomap y).mpr ((residue_eq_zero_iff R y).mpr hy))

@[scoped simp] theorem thetaBar_residue (y : R.integers) :
    thetaBar R V hcomap (IsLocalRing.residue R.integers y) = theta R V hcomap y :=
  Ideal.Quotient.lift_mk _ _ _

def resBar : ResidueField R.integers →+* Fbar :=
  Ideal.Quotient.lift (maximalIdeal R.integers) R.residue
    (fun y hy => (residue_eq_zero_iff R y).mpr hy)

omit hcomap in
@[scoped simp] theorem resBar_residue (y : R.integers) :
    resBar R (IsLocalRing.residue R.integers y) = R.residue y :=
  Ideal.Quotient.lift_mk _ _ _

end Comap
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve.RegularProlongation P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve.RegularProlongation.KummerSplitting"

section ResidueDegreeOne

variable (hf1 : ∀ x ∈ V, ∃ y ∈ R.integers, x - algebraMap F F' y ∈ V.nonunits)
include hf1

theorem theta_surjective : Function.Surjective (theta R V hcomap) := by
  intro z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨y, hy, hxy⟩ := hf1 x x.2
  refine ⟨⟨y, hy⟩, ?_⟩
  rw [theta_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    ValuationSubring.valuation_lt_one_iff]
  have h : V.valuation (x - algebraMap F F' y) < 1 := hxy
  rw [← Valuation.map_neg] at h
  convert h using 2
  simp

theorem thetaBar_bijective : Function.Bijective (thetaBar R V hcomap) := by
  refine ⟨(thetaBar R V hcomap).injective, fun z => ?_⟩
  obtain ⟨y, rfl⟩ := theta_surjective R V hcomap hf1 z
  exact ⟨IsLocalRing.residue R.integers y, thetaBar_residue R V hcomap y⟩

def thetaEquiv : ResidueField R.integers ≃+* ResidueField V :=
  RingEquiv.ofBijective (thetaBar R V hcomap) (thetaBar_bijective R V hcomap hf1)

theorem thetaEquiv_apply (z : ResidueField R.integers) :
    thetaEquiv R V hcomap hf1 z = thetaBar R V hcomap z := rfl

def liftResidue : V →+* Fbar :=
  (resBar R).comp ((thetaEquiv R V hcomap hf1).symm.toRingHom.comp (IsLocalRing.residue V))

theorem liftResidue_apply (x : V) :
    liftResidue R V hcomap hf1 x =
      resBar R ((thetaEquiv R V hcomap hf1).symm (IsLocalRing.residue V x)) := rfl

theorem liftResidue_incl (y : R.integers) :
    liftResidue R V hcomap hf1 (incl R V hcomap y) = R.residue y := by
  rw [liftResidue_apply]
  have h : thetaEquiv R V hcomap hf1 (IsLocalRing.residue R.integers y) =
      IsLocalRing.residue V (incl R V hcomap y) := by
    rw [thetaEquiv_apply, thetaBar_residue, theta_apply]
  rw [← h, RingEquiv.symm_apply_apply, resBar_residue]

theorem liftResidue_eq_zero_iff (x : V) :
    liftResidue R V hcomap hf1 x = 0 ↔ x ∈ maximalIdeal V := by
  rw [liftResidue_apply, map_eq_zero_iff _ (resBar R).injective,
    EmbeddingLike.map_eq_zero_iff, IsLocalRing.residue_eq_zero_iff]

theorem ker_liftResidue : RingHom.ker (liftResidue R V hcomap hf1) = maximalIdeal V := by
  ext x
  rw [RingHom.mem_ker, liftResidue_eq_zero_iff]

theorem liftResidue_surjective : Function.Surjective (liftResidue R V hcomap hf1) := fun t => by
  obtain ⟨y, hy⟩ := R.residue_surjective t
  exact ⟨incl R V hcomap y, by rw [liftResidue_incl, hy]⟩

variable [Algebra L F'] [IsScalarTower L F F']
  (he1 : ∀ g : F', g ≠ 0 → ∃ h : F, V.valuation (algebraMap F F' h * g) = 1)
include he1

private def _root_.AlgebraicCurve.RegularProlongation.KummerSplitting.lift : RegularProlongation A F' Fbar where
  integers := V
  residue := liftResidue R V hcomap hf1
  algebraMap_mem_iff x := by
    rw [IsScalarTower.algebraMap_apply L F F' x,
      ← ValuationSubring.mem_comap (A := V) (f := algebraMap F F'), hcomap]
    exact R.algebraMap_mem_iff x
  residue_surjective := liftResidue_surjective R V hcomap hf1
  ker_residue := ker_liftResidue R V hcomap hf1
  residue_algebraMap a := by
    have h : ∀ hm : algebraMap L F' (a : L) ∈ V, (⟨algebraMap L F' a, hm⟩ : V) =
        incl R V hcomap ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩ :=
      fun hm => Subtype.ext (IsScalarTower.algebraMap_apply L F F' (a : L))
    rw [h, liftResidue_incl, R.residue_algebraMap]
  exists_smul_mem g hg := by
    obtain ⟨h, hh⟩ := he1 g hg
    have hh0 : h ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_mul, map_zero] at hh
      exact zero_ne_one hh
    obtain ⟨c, hc, hres⟩ := R.exists_smul_mem h⁻¹ (inv_ne_zero hh0)
    have hunit : IsUnit (⟨c • h⁻¹, hc⟩ : R.integers) := R.isUnit_of_residue_ne_zero hres
    have hv1 : V.valuation (algebraMap F F' (c • h⁻¹)) = 1 := by
      have hu : IsUnit (incl R V hcomap ⟨c • h⁻¹, hc⟩) := hunit.map _
      exact (V.valuation_eq_one_iff _).mp hu
    have hcg : c • g = algebraMap F F' (c • h⁻¹) * (algebraMap F F' h * g) := by
      have hh' : algebraMap F F' h ≠ 0 := (_root_.map_ne_zero _).mpr hh0
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
        map_inv₀, mul_assoc, ← mul_assoc (algebraMap F F' h)⁻¹, inv_mul_cancel₀ hh', one_mul]
    have hv : V.valuation (c • g) = 1 := by rw [hcg, map_mul, hv1, hh, one_mul]
    have hmem : c • g ∈ V := (V.valuation_le_one_iff _).mp hv.le
    refine ⟨c, hmem, ?_⟩
    rw [Ne, liftResidue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    exact fun hlt => absurd hv (ne_of_lt hlt)

p2m_export "AlgebraicCurve.RegularProlongation.KummerSplitting" "lift"
@[scoped simp] theorem lift_integers : (lift R V hcomap hf1 he1).integers = V := rfl

theorem lift_residue_incl (y : R.integers) :
    (lift R V hcomap hf1 he1).residue (incl R V hcomap y) = R.residue y :=
  liftResidue_incl R V hcomap hf1 y

end ResidueDegreeOne
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve.RegularProlongation P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve.RegularProlongation.KummerSplitting"

end Lift
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve.RegularProlongation P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve.RegularProlongation.KummerSplitting"

end AlgebraicCurve.RegularProlongation.KummerSplitting
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve.RegularProlongation P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve.RegularProlongation.KummerSplitting"
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve.RegularProlongation P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve.RegularProlongation.KummerSplitting"
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve.RegularProlongation P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve.RegularProlongation.KummerSplitting"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve.RegularProlongation P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve.RegularProlongation.KummerSplitting"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.AlgebraicCurve Polynomial"

open AlgebraicCurve.RegularProlongation.KummerSplitting in
theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    {q : ℕ} [Fact q.Prime] (f : R.integers)
    (S : Finset Fbar) (hS : S.card = q) (hSf : ∀ s ∈ S, s ^ q = R.residue f)
    (F' : Type*) [Field F'] [Algebra F F'] [Algebra L F'] [IsScalarTower L F F']
    [IsSplittingField F F' (X ^ q - C (f : F))] (hdeg : Module.finrank F F' = q) :
    ∃ R' : Fin q → RegularProlongation A F' Fbar,
      Function.Injective (fun i => (R' i).integers) ∧
      ∀ i, (R' i).integers.comap (algebraMap F F') = R.integers ∧
        ∀ (x : (R' i).integers) (y : R.integers), algebraMap F F' y = x →
          (R' i).residue x = R.residue y := by
  classical
  have hqp : q.Prime := Fact.out
  haveI : NeZero q := ⟨hqp.ne_zero⟩

  set α : F' := rootOfSplitsXPowSubC (NeZero.pos q) (f : F) F' with hαdef
  have hα : α ^ q = algebraMap F F' (f : F) := rootOfSplitsXPowSubC_pow (f : F) F'

  have hex : ∀ s : S, ∃ V : ValuationSubring F', CentredAt R α (s : Fbar) V := fun s =>
    exists_centredAt R f S hS hSf hdeg hα (hSf s s.2)
  choose V hV using hex

  have hcardS : Fintype.card S = q := (Fintype.card_coe S).trans hS
  let e : S ≃ Fin q := Fintype.equivFinOfCardEq hcardS
  let O' : Fin q → ValuationSubring F' := fun i => V (e.symm i)
  have hO'inj : Function.Injective O' := by
    intro i j hij
    by_contra hne
    have hst : ((e.symm i : S) : Fbar) ≠ ((e.symm j : S) : Fbar) := fun h =>
      hne (e.symm.injective (Subtype.ext h))
    exact (hV (e.symm i)).ne (hV (e.symm j)) hst hij
  have hO'comap : ∀ i, (O' i).comap (algebraMap F F') = R.integers := fun i =>
    (hV (e.symm i)).comap_eq

  haveI : FiniteDimensional F F' := Module.finite_of_finrank_pos (by rw [hdeg]; exact hqp.pos)
  have hcard : Module.finrank F F' ≤ Fintype.card (Fin q) := by rw [Fintype.card_fin, hdeg]
  have hf1 : ∀ i, ∀ x ∈ O' i, ∃ y ∈ R.integers, x - algebraMap F F' y ∈ (O' i).nonunits :=
    fun i x hx => ValuationSubring.exists_sub_mem_nonunits_of_finrank_le_card R.integers O'
      hO'inj hO'comap hcard i x hx
  have he1 : ∀ i, ∀ g : F', g ≠ 0 → ∃ h : F, (O' i).valuation (algebraMap F F' h * g) = 1 :=
    fun i g hg => ValuationSubring.exists_valuation_mul_eq_one_of_finrank_le_card R.integers O'
      hO'inj hO'comap hcard i g hg
  refine ⟨fun i => lift R (O' i) (hO'comap i) (hf1 i) (he1 i), hO'inj, fun i => ⟨hO'comap i, ?_⟩⟩
  intro x y hxy
  have h : x = incl R (O' i) (hO'comap i) y := Subtype.ext hxy.symm
  rw [h]
  exact lift_residue_incl R (O' i) (hO'comap i) (hf1 i) (he1 i) y

end S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq (solution)
