-- Prove2me | solution 1 for AlgebraicGeometry.finrank_eq_finsum_length_stalk_of_isFinite_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/9d2e434f-1b37-5a37-8171-a92d94de68c6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_finrank_eq_finsum_length_stalk_of_isFinite_of_isAlgClosed

set_option autoImplicit false

universe u v w

open CategoryTheory AlgebraicGeometry

namespace RankSumAux

theorem finrank_eq_length_aux {k : Type u} [Field k] [IsAlgClosed k] (L : Type v) [CommRing L] [Algebra k L] [IsLocalRing L]
    [Module.Finite k L] (n : ℕ) :
    ∀ (M : Type w) [AddCommGroup M] [Module L M] [Module k M] [IsScalarTower k L M] [Module.Finite k M],
      Module.finrank k M = n → (Module.finrank k M : ℕ∞) = Module.length L M := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ _ _ _ _ hn
  by_cases hM : Subsingleton M
  · rw [Module.length_eq_zero, Module.finrank_zero_of_subsingleton, Nat.cast_zero]
  · haveI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
    haveI : IsArtinian L M := isArtinian_of_tower k (inferInstance : IsArtinian k M)
    haveI : IsAtomic (Submodule L M) :=
      isAtomic_of_orderBot_wellFounded_lt (wellFounded_lt : WellFounded ((· < ·) : Submodule L M → Submodule L M → Prop))
    obtain ⟨N, hNat⟩ := IsAtomic.exists_atom (Submodule L M)
    haveI hN : IsSimpleModule L N := isSimpleModule_iff_isAtom.mpr hNat

    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hN
    have hIm : I = IsLocalRing.maximalIdeal L := IsLocalRing.eq_maximalIdeal hI
    have hN1 : Module.finrank k N = 1 := by
      letI : Field (L ⧸ I) := Ideal.Quotient.field I
      haveI : Module.Finite k (L ⧸ I) :=
        Module.Finite.of_surjective (Ideal.Quotient.mkₐ k I).toLinearMap (Ideal.Quotient.mkₐ_surjective k I)
      haveI : Algebra.IsIntegral k (L ⧸ I) := Algebra.IsIntegral.of_finite k (L ⧸ I)
      have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := L ⧸ I)
      have h1 : Module.finrank k (L ⧸ I) = 1 := by
        rw [← (AlgEquiv.ofBijective (Algebra.ofId k (L ⧸ I)) hb).toLinearEquiv.finrank_eq, Module.finrank_self]
      rw [← h1]
      exact (e.restrictScalars k).finrank_eq
    have hNlen : Module.length L N = 1 := Module.length_eq_one L N

    have hq : Module.finrank k (M ⧸ N) = Module.finrank k M - Module.finrank k N := Submodule.finrank_quotient N
    have hpos : 0 < Module.finrank k M := Module.finrank_pos
    have hlt : Module.finrank k (M ⧸ N) < n := by rw [hq, hN1, ← hn]; omega
    have ihq := ih _ hlt (M ⧸ N) rfl

    have hadd : Module.length L M = Module.length L N + Module.length L (M ⧸ N) :=
      Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N)
    rw [hadd, hNlen, ← ihq, hq, hN1]
    have : (Module.finrank k M : ℕ∞) = ((1 + (Module.finrank k M - 1) : ℕ) : ℕ∞) := by congr 1; omega
    rw [this, Nat.cast_add, Nat.cast_one]

theorem finrank_eq_length {k : Type u} [Field k] [IsAlgClosed k] (L : Type v) [CommRing L] [Algebra k L] [IsLocalRing L]
    [Module.Finite k L] : (Module.finrank k L : ℕ∞) = Module.length L L :=
  finrank_eq_length_aux L (Module.finrank k L) L rfl

theorem finrank_eq_sum_length_localization {k : Type u} [Field k] [IsAlgClosed k] (S : Type v) [CommRing S] [Algebra k S]
    [Module.Finite k S] [Fintype (PrimeSpectrum S)] :
    (Module.finrank k S : ℕ∞) =
      ∑ p : PrimeSpectrum S, Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) := by
  haveI : IsArtinianRing S := isArtinian_of_tower k inferInstance
  rw [IsArtinianRing.finrank_eq_sum_primeSpectrum S k, Nat.cast_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  haveI : Module.Finite k (Localization.AtPrime p.asIdeal) :=
    Module.Finite.of_surjective (Algebra.algHom k S (Localization.AtPrime p.asIdeal)).toLinearMap
      (IsArtinianRing.localization_surjective p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal))
  exact finrank_eq_length (Localization.AtPrime p.asIdeal)

theorem length_self_eq_of_ringEquiv {A : Type v} {B : Type w} [CommRing A] [CommRing B] (e : A ≃+* B) :
    Module.length A A = Module.length B B := by
  letI : Algebra A B := e.toRingHom.toAlgebra
  have h1 : Module.length A B = Module.length B B :=
    Module.length_eq_of_surjective (S := A) (R := B) (M := B) e.surjective
  rw [← h1]

  let l : B ≃ₗ[A] A :=
    { toFun := e.symm, invFun := e, map_add' := fun x y => by simp,
      map_smul' := fun a x => by
        show e.symm (e a * x) = a * e.symm x
        rw [map_mul, RingEquiv.symm_apply_apply],
      left_inv := fun x => by simp, right_inv := fun x => by simp }
  exact (LinearEquiv.length_eq l).symm

end RankSumAux

namespace RankSumBridge

variable {k : Type u} [Field k]

theorem finrank_sections_eq {C : Scheme.{u}} (z : C ⟶ Spec (CommRingCat.of k)) [IsFinite z] [Flat z] [IsAffine C]
    (n : ℕ) (hrank : ∀ s : ↥(Spec (CommRingCat.of k)), z.finrank s = n) :
    letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
    Module.Finite k Γ(C, ⊤) ∧ Module.finrank k Γ(C, ⊤) = n := by
  set φ : CommRingCat.of k ⟶ Γ(C, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop with hφ
  letI alg : Algebra k Γ(C, ⊤) := φ.hom.toAlgebra
  have hbij : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv
  have hFin : φ.hom.Finite := by
    show (z.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).Finite
    exact z.finite_appTop.comp (RingHom.Finite.of_surjective _ hbij.surjective)
  have hFlat : φ.hom.Flat := by
    show (z.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).Flat
    exact (RingHom.Flat.of_bijective hbij).comp z.flat_appTop
  have hfin : Module.Finite k Γ(C, ⊤) := hFin
  refine ⟨hfin, ?_⟩
  have hz : z = C.isoSpec.hom ≫ Spec.map φ := by
    rw [hφ, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  haveI : IsFinite (Spec.map φ) := (IsFinite.SpecMap_iff φ).2 hFin
  haveI : Flat (Spec.map φ) := Flat.SpecMap_iff.2 hFlat
  obtain ⟨s⟩ := (inferInstance : Nonempty ↥(Spec (CommRingCat.of k)))
  have h1 := hrank s
  rw [hz, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_eq_finrank hFin hFlat] at h1
  have h2 : φ.hom.finrank s = Module.finrank k Γ(C, ⊤) := by
    have : φ.hom = algebraMap k Γ(C, ⊤) := rfl
    rw [this, RingHom.finrank_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
    rfl
  rw [← h2, h1]

theorem flat_of_field {C : Scheme.{u}} (z : C ⟶ Spec (CommRingCat.of k)) [IsFinite z] : Flat z := by
  haveI : IsAffine C := isAffine_of_isAffineHom z
  set φ : CommRingCat.of k ⟶ Γ(C, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop with hφ
  have hFlat : φ.hom.Flat := by
    letI : Algebra k Γ(C, ⊤) := φ.hom.toAlgebra
    have : Module.Flat k Γ(C, ⊤) := inferInstance
    exact this
  have hz : z = C.isoSpec.hom ≫ Spec.map φ := by
    rw [hφ, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  haveI : Flat (Spec.map φ) := Flat.SpecMap_iff.2 hFlat
  rw [hz]; infer_instance

end RankSumBridge

open RankSumAux RankSumBridge in
theorem solution
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsFinite f]
    (s : ↥(Spec (CommRingCat.of k))) :
    (f.finrank s : ℕ∞) =
      ∑ᶠ x : {x : Spec (CommRingCat.of k) ⟶ X // x ≫ f = 𝟙 (Spec (CommRingCat.of k))},
        Module.length (X.presheaf.stalk (x.1.base (IsLocalRing.closedPoint k)))
          (X.presheaf.stalk (x.1.base (IsLocalRing.closedPoint k))) := by
  classical
  haveI : IsAffine X := isAffine_of_isAffineHom f
  haveI : Flat f := flat_of_field f

  haveI : Subsingleton ↥(Spec (CommRingCat.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  obtain ⟨hfinS, hrank⟩ := finrank_sections_eq f (f.finrank s) (fun s' => by rw [Subsingleton.elim s' s])
  letI alg : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom.toAlgebra
  haveI : Module.Finite k Γ(X, ⊤) := hfinS
  haveI : IsArtinianRing Γ(X, ⊤) := isArtinian_of_tower k inferInstance
  haveI : Fintype (PrimeSpectrum Γ(X, ⊤)) := Fintype.ofFinite _

  rw [← hrank, finrank_eq_sum_length_localization (k := k) Γ(X, ⊤)]

  haveI : IsLocallyArtinian X := IsLocallyArtinian.of_locallyQuasiFinite f
  have hcl : closedPoints X = Set.univ := closedPoints_eq_univ

  have hU : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  let E₁ : {x : Spec (CommRingCat.of k) ⟶ X // x ≫ f = 𝟙 (Spec (CommRingCat.of k))} ≃ ↥(⊤ : X.Opens) :=
    (pointEquivClosedPoint f).trans
      ⟨fun x => ⟨x.1, trivial⟩, fun x => ⟨x.1, hcl.symm ▸ Set.mem_univ _⟩, fun x => rfl, fun x => rfl⟩
  let E₂ : ↥(⊤ : X.Opens) ≃ PrimeSpectrum Γ(X, ⊤) := (Scheme.homeoOfIso hU.isoSpec).toEquiv
  let E := E₁.trans E₂
  haveI : Fintype {x : Spec (CommRingCat.of k) ⟶ X // x ≫ f = 𝟙 (Spec (CommRingCat.of k))} := Fintype.ofEquiv _ E.symm
  rw [finsum_eq_sum_of_fintype, ← Equiv.sum_comp E]
  refine Finset.sum_congr rfl fun y _ => ?_

  have hEy : y.1.base (IsLocalRing.closedPoint k) = (E₁ y).1 := rfl
  have hpy : E y = hU.primeIdealOf (E₁ y) := rfl
  haveI := hU.isLocalization_stalk (E₁ y)
  rw [hEy, hpy]
  exact length_self_eq_of_ringEquiv (IsLocalization.algEquiv (hU.primeIdealOf (E₁ y)).asIdeal.primeCompl
      (Localization.AtPrime (hU.primeIdealOf (E₁ y)).asIdeal) (X.presheaf.stalk (E₁ y).1)).toRingEquiv

end S_AlgebraicGeometry_finrank_eq_finsum_length_stalk_of_isFinite_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicGeometry_finrank_eq_finsum_length_stalk_of_isFinite_of_isAlgClosed (solution)
