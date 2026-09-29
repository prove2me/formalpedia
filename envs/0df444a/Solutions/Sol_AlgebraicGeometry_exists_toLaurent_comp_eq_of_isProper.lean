-- Prove2me | solution 1 for AlgebraicGeometry.exists_toLaurent_comp_eq_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/a6adef03-5e92-5d28-91af-94408037a416

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_toLaurent_comp_eq_of_isProper

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_toLaurent_comp_eq_of_isProper.AlgebraicGeometry Polynomial AlgebraicGeometry.Polynomial"

universe u

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp spread_out_of_isGermInjective' Spec.fromSpecStalk_eq' IsProper IsOpenImmersion.of_isLocalization StructureSheaf.stalkAlgebra_map IsProper.eq_valuativeCriterion ValuativeCommSq LocallyOfFiniteType Spec StructureSheaf.toStalk StructureSheaf.stalkIso Spec.map Scheme Scheme.Opens.fromSpecStalkOfMem_ι ValuativeCommSq.mk ext_of_isDominant_of_isSeparated IsOpenImmersion ValuativeCriterion.existence IsReduced Spec.map_id Scheme.Cover.mkOfCovers Scheme.Cover.glueMorphisms Scheme.Cover.ι_glueMorphisms_assoc IsDominant Scheme.Opens Scheme.Cover.ι_glueMorphisms Scheme.Cover.hom_ext ValuativeCriterion isReduced_of_isOpenImmersion Scheme.Cover"
namespace ExtGm
p2m_open "AlgebraicGeometry"

variable (k : Type u) [Field k]

abbrev P0 : Ideal (Polynomial k) := Ideal.span {(X : Polynomial k)}

scoped instance isPrime_P0 : (P0 k).IsPrime :=
  (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X

theorem P0_ne_bot : P0 k ≠ ⊥ := by
  simp [P0, Polynomial.X_ne_zero]

abbrev O : Type u := Localization (P0 k).primeCompl

scoped instance isDomain_O : IsDomain (O k) :=
  IsLocalization.isDomain_localization (P0 k).primeCompl_le_nonZeroDivisors

scoped instance isDVR_O : IsDiscreteValuationRing (O k) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (Polynomial k) (P0_ne_bot k) (O k)

example : ValuationRing (O k) := inferInstance

abbrev Kx : Type u := FractionRing (Polynomial k)

theorem isUnit_algebraMap_Kx (y : (P0 k).primeCompl) : IsUnit (algebraMap (Polynomial k) (Kx k) y) := by
  refine isUnit_iff_ne_zero.mpr fun h => ?_
  have hy : (y : Polynomial k) ≠ 0 := fun h0 => y.2 (by rw [h0]; exact (P0 k).zero_mem)
  exact hy (IsFractionRing.injective (Polynomial k) (Kx k) (by rw [h, map_zero]))

scoped instance algebra_O_Kx : Algebra (O k) (Kx k) :=
  (IsLocalization.lift (M := (P0 k).primeCompl) (S := O k) (g := algebraMap (Polynomial k) (Kx k))
    (isUnit_algebraMap_Kx k)).toAlgebra

scoped instance isScalarTower_O_Kx : IsScalarTower (Polynomial k) (O k) (Kx k) :=
  IsScalarTower.of_algebraMap_eq (R := Polynomial k) (S := O k) (A := Kx k) fun x => by
    rw [RingHom.algebraMap_toAlgebra]
    exact (IsLocalization.lift_eq (M := (P0 k).primeCompl) (isUnit_algebraMap_Kx k) x).symm

scoped instance isFractionRing_O_Kx : IsFractionRing (O k) (Kx k) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (P0 k).primeCompl (O k) (Kx k)

def lam : LaurentPolynomial k →+* Kx k :=
  IsLocalization.Away.lift (X : Polynomial k) (g := algebraMap (Polynomial k) (Kx k))
    (isUnit_iff_ne_zero.mpr fun h => Polynomial.X_ne_zero
      (IsFractionRing.injective (Polynomial k) (Kx k) (by rw [h, map_zero])))

private theorem _root_.AlgebraicGeometry.ExtGm.algebraMap_eq_toLaurent : algebraMap (Polynomial k) (LaurentPolynomial k) = Polynomial.toLaurent := by
  ext <;> simp [LaurentPolynomial.algebraMap_eq_toLaurent]

p2m_export "AlgebraicGeometry.ExtGm" "algebraMap_eq_toLaurent"
theorem lam_comp_toLaurent : (lam k).comp Polynomial.toLaurent = algebraMap (Polynomial k) (Kx k) := by
  rw [← algebraMap_eq_toLaurent]
  exact IsLocalization.Away.lift_comp (x := (X : Polynomial k)) _

theorem lam_comp_algebraMap :
    (lam k).comp (algebraMap k (LaurentPolynomial k)) = (algebraMap (O k) (Kx k)).comp (algebraMap k (O k)) := by
  ext c
  have h1 : algebraMap k (LaurentPolynomial k) c = Polynomial.toLaurent (Polynomial.C c) := by
    simp [Polynomial.toLaurent_C, LaurentPolynomial.algebraMap_apply]
  have h2 : (algebraMap (O k) (Kx k)) (algebraMap k (O k) c) = algebraMap (Polynomial k) (Kx k) (Polynomial.C c) := by
    rw [IsScalarTower.algebraMap_apply k (Polynomial k) (O k) c,
      ← IsScalarTower.algebraMap_apply (Polynomial k) (O k) (Kx k), Polynomial.algebraMap_eq]
  simp only [RingHom.coe_comp, Function.comp_apply, h1, h2]
  exact congrArg (fun f : Polynomial k →+* Kx k => f (Polynomial.C c)) (lam_comp_toLaurent k)

variable {k}
variable {Z : Scheme.{u}} (fZ : Z ⟶ Spec (CommRingCat.of k))

theorem exists_lift [IsProper fZ] (φ : Spec (CommRingCat.of (LaurentPolynomial k)) ⟶ Z)
    (hφ : φ ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k)))) :
    ∃ l : Spec (CommRingCat.of (O k)) ⟶ Z,
      Spec.map (CommRingCat.ofHom (algebraMap (O k) (Kx k))) ≫ l =
        Spec.map (CommRingCat.ofHom (lam k)) ≫ φ ∧
      l ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap k (O k))) := by
  have hV : ValuativeCriterion fZ := by
    have h := (inferInstance : IsProper fZ)
    rw [AlgebraicGeometry.IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  have hsq : CommSq (Spec.map (CommRingCat.ofHom (lam k)) ≫ φ)
      (Spec.map (CommRingCat.ofHom (algebraMap (O k) (Kx k)))) fZ
      (Spec.map (CommRingCat.ofHom (algebraMap k (O k)))) := ⟨by
    rw [Category.assoc, hφ, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      lam_comp_algebraMap]⟩
  haveI : hsq.HasLift := ValuativeCriterion.existence hV (ValuativeCommSq.mk (O k) (Kx k) _ _ hsq)
  exact ⟨hsq.lift, hsq.fac_left, hsq.fac_right⟩

variable (k)

abbrev 𝔸 : Scheme.{u} := Spec (CommRingCat.of (Polynomial k))

def x₀ : 𝔸 k := ⟨P0 k, inferInstance⟩

theorem x₀_asIdeal : (x₀ k).asIdeal = P0 k := rfl

abbrev sA : 𝔸 k ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))

def eO : O k ≃+* ((𝔸 k).presheaf.stalk (x₀ k)) :=
  (StructureSheaf.stalkIso (Polynomial k) (x₀ k)).toRingEquiv

theorem eO_algebraMap (p : Polynomial k) :
    eO k (algebraMap (Polynomial k) (O k) p) = StructureSheaf.toStalk (Polynomial k) (x₀ k) p := by
  change (StructureSheaf.stalkIso (Polynomial k) (x₀ k)) (algebraMap (Polynomial k) _ p) = _
  rw [AlgEquiv.commutes]
  exact StructureSheaf.stalkAlgebra_map (Polynomial k) (x₀ k) p

theorem exists_lift_stalk [IsProper fZ] (φ : Spec (CommRingCat.of (LaurentPolynomial k)) ⟶ Z)
    (hφ : φ ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k)))) :
    ∃ l : Spec (CommRingCat.of (O k)) ⟶ Z,
      Spec.map (CommRingCat.ofHom (algebraMap (O k) (Kx k))) ≫ l =
        Spec.map (CommRingCat.ofHom (lam k)) ≫ φ ∧
      l ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap k (O k))) ∧
      (Spec.map (CommRingCat.ofHom (eO k).toRingHom) ≫ l :
          Spec ((𝔸 k).presheaf.stalk (x₀ k)) ⟶ Z) ≫ fZ = (𝔸 k).fromSpecStalk (x₀ k) ≫ sA k := by
  obtain ⟨l, hl₁, hl₂⟩ := exists_lift fZ φ hφ
  refine ⟨l, hl₁, hl₂, ?_⟩
  rw [Category.assoc, hl₂, Spec.fromSpecStalk_eq']
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  change eO k (algebraMap k (O k) r) = StructureSheaf.toStalk (Polynomial k) (x₀ k) (algebraMap k (Polynomial k) r)
  rw [IsScalarTower.algebraMap_apply k (Polynomial k) (O k), eO_algebraMap]

theorem exists_spread [IsProper fZ] (φ : Spec (CommRingCat.of (LaurentPolynomial k)) ⟶ Z)
    (hφ : φ ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k)))) :
    ∃ (l : Spec (CommRingCat.of (O k)) ⟶ Z) (U : (𝔸 k).Opens) (hx : x₀ k ∈ U) (f : (U : Scheme.{u}) ⟶ Z),
      Spec.map (CommRingCat.ofHom (algebraMap (O k) (Kx k))) ≫ l =
        Spec.map (CommRingCat.ofHom (lam k)) ≫ φ ∧
      (Spec.map (CommRingCat.ofHom (eO k).toRingHom) ≫ l :
          Spec ((𝔸 k).presheaf.stalk (x₀ k)) ⟶ Z) = U.fromSpecStalkOfMem (x₀ k) hx ≫ f ∧
      f ≫ fZ = U.ι ≫ sA k := by
  obtain ⟨l, hl₁, hl₂, hl₃⟩ := exists_lift_stalk k fZ φ hφ
  haveI : LocallyOfFiniteType fZ := by
    have h := (inferInstance : IsProper fZ)
    rw [AlgebraicGeometry.IsProper.eq_valuativeCriterion] at h
    exact h.2
  obtain ⟨U, hx, f, hf₁, hf₂⟩ := spread_out_of_isGermInjective' (sA k) fZ
    (Spec.map (CommRingCat.ofHom (eO k).toRingHom) ≫ l) hl₃
  exact ⟨l, U, hx, f, hl₁, hf₁, hf₂⟩

abbrev ιG : Spec (CommRingCat.of (LaurentPolynomial k)) ⟶ 𝔸 k :=
  Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial k →+* LaurentPolynomial k))

scoped instance isOpenImmersion_ιG : IsOpenImmersion (ιG k) := by
  rw [ιG, ← algebraMap_eq_toLaurent]
  exact IsOpenImmersion.of_isLocalization (X : Polynomial k)

theorem ιG_sA : ιG k ≫ sA k = Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k))) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext c
  simp [Polynomial.toLaurent_C, LaurentPolynomial.algebraMap_apply]

abbrev η : Spec (CommRingCat.of (Kx k)) ⟶ 𝔸 k :=
  Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (Kx k)))

theorem isDominant_of_comp_eq_η {P : Scheme.{u}} (j : P ⟶ 𝔸 k) [IsOpenImmersion j]
    (w : Spec (CommRingCat.of (Kx k)) ⟶ P) (hw : w ≫ j = η k) : IsDominant w := by
  let pt : Spec (CommRingCat.of (Kx k)) := IsLocalRing.closedPoint (Kx k)

  have hg : ((η k).base pt).asIdeal = ⊥ := by
    have hpt : pt.asIdeal = ⊥ := (Ideal.eq_bot_or_top pt.asIdeal).resolve_right pt.2.ne_top
    change (PrimeSpectrum.comap (algebraMap (Polynomial k) (Kx k)) pt).asIdeal = ⊥
    rw [PrimeSpectrum.comap_asIdeal, hpt]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (Polynomial k) (Kx k))

  have hmem : ∀ W : Set (𝔸 k), IsOpen W → W.Nonempty → (η k).base pt ∈ W := by
    intro W hW hne
    by_contra h
    have hcl : closure {(η k).base pt} ⊆ Wᶜ :=
      closure_minimal (Set.singleton_subset_iff.mpr h) hW.isClosed_compl
    have huniv : closure {(η k).base pt} = Set.univ := by
      refine Set.eq_univ_of_forall fun y => specializes_iff_mem_closure.mp ?_
      refine (PrimeSpectrum.le_iff_specializes _ _).mp ?_
      change ((η k).base pt).asIdeal ≤ y.asIdeal
      rw [hg]
      exact bot_le
    rw [huniv] at hcl
    obtain ⟨x, hx⟩ := hne
    exact hcl (Set.mem_univ x) hx

  refine ⟨dense_iff_inter_open.mpr fun V hV hVne => ?_⟩
  have hjV : IsOpen (j.base '' V) := j.isOpenEmbedding.isOpenMap V hV
  obtain ⟨v, hvV, hv⟩ : (η k).base pt ∈ j.base '' V := hmem _ hjV (hVne.image _)
  refine ⟨v, hvV, ⟨pt, j.isOpenEmbedding.injective ?_⟩⟩
  have hcomp : j.base (w.base pt) = (η k).base pt := by
    rw [← hw]
    rfl
  rw [hv]
  exact hcomp

theorem exists_extension [IsProper fZ] (φ : Spec (CommRingCat.of (LaurentPolynomial k)) ⟶ Z)
    (hφ : φ ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k)))) :
    ∃ ψ : 𝔸 k ⟶ Z, ιG k ≫ ψ = φ ∧ ψ ≫ fZ = sA k := by
  obtain ⟨l, U, hx, fU, hl₁, hlU, hfU⟩ := exists_spread k fZ φ hφ

  have hcov : ∀ x : 𝔸 k, ∃ (b : Bool) (y : (fun b => cond b (U : Scheme.{u}) (Spec (CommRingCat.of (LaurentPolynomial k)))) b),
      ((fun b => show (cond b (U : Scheme.{u}) (Spec (CommRingCat.of (LaurentPolynomial k)))) ⟶ 𝔸 k from
        Bool.rec (ιG k) U.ι b) b).base y = x := by
    intro x
    by_cases hxX : (X : Polynomial k) ∈ x.asIdeal
    ·
      have hxeq : x = x₀ k := by
        apply PrimeSpectrum.ext
        have hle : P0 k ≤ x.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hxX
        haveI : (P0 k).IsMaximal := Ideal.IsPrime.isMaximal inferInstance (P0_ne_bot k)
        exact ((Ideal.IsMaximal.eq_of_le inferInstance x.2.ne_top hle)).symm
      exact ⟨true, ⟨x, hxeq ▸ hx⟩, rfl⟩
    ·
      have : x ∈ Set.range (ιG k).base := by
        rw [ιG, ← algebraMap_eq_toLaurent]
        change x ∈ Set.range (PrimeSpectrum.comap (algebraMap (Polynomial k) (LaurentPolynomial k)))
        rw [PrimeSpectrum.localization_away_comap_range (LaurentPolynomial k) (X : Polynomial k)]
        exact hxX
      obtain ⟨y, hy⟩ := this
      exact ⟨false, y, hy⟩
  let 𝒰 : (𝔸 k).OpenCover := Scheme.Cover.mkOfCovers Bool
    (fun b => cond b (U : Scheme.{u}) (Spec (CommRingCat.of (LaurentPolynomial k))))
    (fun b => Bool.rec (ιG k) U.ι b) hcov (by rintro (_ | _) <;> dsimp <;> infer_instance)
  let g : ∀ b : Bool, 𝒰.X b ⟶ Z := fun b => Bool.rec (motive := fun b => 𝒰.X b ⟶ Z) φ fU b

  have hagree : pullback.fst U.ι (ιG k) ≫ fU = pullback.snd U.ι (ιG k) ≫ φ := by

    let a : Spec (CommRingCat.of (Kx k)) ⟶ (U : Scheme.{u}) :=
      Spec.map (CommRingCat.ofHom (algebraMap (O k) (Kx k))) ≫
        Spec.map (CommRingCat.ofHom (eO k).symm.toRingHom) ≫ U.fromSpecStalkOfMem (x₀ k) hx
    let b : Spec (CommRingCat.of (Kx k)) ⟶ Spec (CommRingCat.of (LaurentPolynomial k)) :=
      Spec.map (CommRingCat.ofHom (lam k))
    have heO : Spec.map (CommRingCat.ofHom (eO k).symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom (eO k).toRingHom) =
        𝟙 (Spec (CommRingCat.of (O k))) := by
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 1
      ext r
      exact (eO k).symm_apply_apply r
    have ha_ι : a ≫ U.ι = η k := by
      simp only [a, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, Spec.fromSpecStalk_eq']
      change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      refine RingHom.ext fun r => ?_
      change algebraMap (O k) (Kx k) ((eO k).symm (StructureSheaf.toStalk (Polynomial k) (x₀ k) r)) = algebraMap (Polynomial k) (Kx k) r
      rw [← eO_algebraMap, RingEquiv.symm_apply_apply, ← IsScalarTower.algebraMap_apply]
    have hb_ι : b ≫ ιG k = η k := by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, lam_comp_toLaurent]
    have hab : a ≫ U.ι = b ≫ ιG k := by rw [ha_ι, hb_ι]
    let w : Spec (CommRingCat.of (Kx k)) ⟶ pullback U.ι (ιG k) := pullback.lift a b hab
    haveI : IsDominant w :=
      isDominant_of_comp_eq_η k (pullback.fst U.ι (ιG k) ≫ U.ι) w (by rw [pullback.lift_fst_assoc, ha_ι])
    haveI : IsReduced (pullback U.ι (ιG k)) := isReduced_of_isOpenImmersion (pullback.fst U.ι (ιG k) ≫ U.ι)
    refine ext_of_isDominant_of_isSeparated fZ ?_ w ?_
    · rw [Category.assoc, hfU, Category.assoc, hφ, ← ιG_sA, pullback.condition_assoc]
    ·
      rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc]
      change (Spec.map _ ≫ Spec.map _ ≫ U.fromSpecStalkOfMem (x₀ k) hx) ≫ fU = Spec.map _ ≫ φ
      rw [← hl₁, Category.assoc, Category.assoc, ← hlU]
      congr 1
      rw [← Category.assoc]
      erw [heO]
      exact Category.id_comp _
  have hg : ∀ b₁ b₂ : Bool, pullback.fst (𝒰.f b₁) (𝒰.f b₂) ≫ g b₁ = pullback.snd (𝒰.f b₁) (𝒰.f b₂) ≫ g b₂ := by
    rintro (_ | _) (_ | _)
    ·
      change pullback.fst (ιG k) (ιG k) ≫ φ = pullback.snd (ιG k) (ιG k) ≫ φ
      rw [fst_eq_snd_of_mono_eq]
    ·
      change pullback.fst (ιG k) U.ι ≫ φ = pullback.snd (ιG k) U.ι ≫ fU
      have := congrArg (fun t => (pullbackSymmetry (ιG k) U.ι).hom ≫ t) hagree
      simp only [pullbackSymmetry_hom_comp_fst_assoc, pullbackSymmetry_hom_comp_snd_assoc] at this
      exact this.symm
    ·
      exact hagree
    · change pullback.fst U.ι U.ι ≫ fU = pullback.snd U.ι U.ι ≫ fU
      rw [fst_eq_snd_of_mono_eq]
  refine ⟨Scheme.Cover.glueMorphisms 𝒰 g hg, ?_, ?_⟩
  · exact Scheme.Cover.ι_glueMorphisms 𝒰 g hg false
  · apply Scheme.Cover.hom_ext 𝒰
    rintro (_ | _)
    · rw [Scheme.Cover.ι_glueMorphisms_assoc]
      change φ ≫ fZ = ιG k ≫ sA k
      rw [hφ, ιG_sA]
    · rw [Scheme.Cover.ι_glueMorphisms_assoc]
      exact hfU

end AlgebraicGeometry.ExtGm
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_toLaurent_comp_eq_of_isProper.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_toLaurent_comp_eq_of_isProper.AlgebraicGeometry.ExtGm"
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_toLaurent_comp_eq_of_isProper.AlgebraicGeometry"

open AlgebraicGeometry.ExtGm in
theorem solution {k : Type u} [Field k] {Z : Scheme.{u}}
    (fZ : Z ⟶ Spec (CommRingCat.of k)) [IsProper fZ]
    (φ : Spec (CommRingCat.of (LaurentPolynomial k)) ⟶ Z)
    (hφ : φ ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k)))) :
    ∃ ψ : Spec (CommRingCat.of (Polynomial k)) ⟶ Z,
      Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial k →+* LaurentPolynomial k)) ≫ ψ = φ ∧
      ψ ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) :=
  AlgebraicGeometry.ExtGm.exists_extension k fZ φ hφ

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_toLaurent_comp_eq_of_isProper.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_toLaurent_comp_eq_of_isProper.AlgebraicGeometry.ExtGm"

end S_AlgebraicGeometry_exists_toLaurent_comp_eq_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_exists_toLaurent_comp_eq_of_isProper (solution)
