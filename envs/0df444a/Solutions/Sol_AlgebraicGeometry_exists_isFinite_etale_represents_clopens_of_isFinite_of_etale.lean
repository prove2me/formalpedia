-- Prove2me | solution 1 for AlgebraicGeometry.exists_isFinite_etale_represents_clopens_of_isFinite_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/20214920-d37a-5092-9867-ce5e2a5c90ad

import Mathlib
import Theorems.Thm_Algebra_exists_etale_algHom_equiv_isIdempotentElem_tensorProduct_of_projective
import Theorems.Thm_Module_Finite_of_algHom_equiv_isIdempotentElem_tensorProduct_of_etale_of_rankAtStalk_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isFinite_etale_represents_clopens_of_isFinite_of_etale

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

noncomputable section

namespace ClopenRep22

theorem mul_one_sub_eq_zero_of_basicOpen_le {R : Type*} [CommRing R] {a b : R}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (hab : PrimeSpectrum.basicOpen a ≤ PrimeSpectrum.basicOpen b) : a * (1 - b) = 0 := by
  have hidem : IsIdempotentElem (a * (1 - b)) := ha.mul hb.one_sub
  have hnil : IsNilpotent (a * (1 - b)) := by
    rw [← PrimeSpectrum.basicOpen_eq_bot_iff, PrimeSpectrum.basicOpen_mul, eq_bot_iff]
    intro x hx
    obtain ⟨hxa, hxb⟩ := hx
    have hxb' : b ∉ x.asIdeal := hab hxa
    have h1b : (1 - b) ∉ x.asIdeal := hxb
    have : b * (1 - b) ∈ x.asIdeal := by
      rw [mul_sub, mul_one, hb.eq, sub_self]; exact x.asIdeal.zero_mem
    rcases x.isPrime.mem_or_mem this with h | h
    · exact (hxb' h).elim
    · exact (h1b h).elim
  obtain ⟨n, hn⟩ := hnil
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    rw [pow_zero] at hn
    exact (subsingleton_of_zero_eq_one hn.symm).elim _ _
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hnpos
    rwa [hidem.pow_succ_eq k] at hn

theorem idem_eq_of_basicOpen_eq {R : Type*} [CommRing R] {e e' : R}
    (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (h : PrimeSpectrum.basicOpen e = PrimeSpectrum.basicOpen e') : e = e' := by
  have h1 := mul_one_sub_eq_zero_of_basicOpen_le he he' h.le
  have h2 := mul_one_sub_eq_zero_of_basicOpen_le he' he h.ge
  rw [mul_sub, mul_one, sub_eq_zero] at h1 h2
  rw [h1, mul_comm, ← h2]

def idemOf {A : Type} [CommRing A] (V : (Spec (CommRingCat.of A)).Opens)
    (hV : IsClosed (V : Set ↥(Spec (CommRingCat.of A)))) : A :=
  (PrimeSpectrum.isClopen_iff.mp (⟨hV, V.isOpen⟩ : IsClopen (V : Set ↥(Spec (CommRingCat.of A))))).choose

theorem idemOf_isIdempotentElem {A : Type} [CommRing A] (V : (Spec (CommRingCat.of A)).Opens)
    (hV : IsClosed (V : Set ↥(Spec (CommRingCat.of A)))) : IsIdempotentElem (idemOf V hV) :=
  (PrimeSpectrum.isClopen_iff.mp (⟨hV, V.isOpen⟩ : IsClopen (V : Set ↥(Spec (CommRingCat.of A))))).choose_spec.1

theorem coe_eq_basicOpen_idemOf {A : Type} [CommRing A] (V : (Spec (CommRingCat.of A)).Opens)
    (hV : IsClosed (V : Set ↥(Spec (CommRingCat.of A)))) :
    (V : Set ↥(Spec (CommRingCat.of A))) =
      ((PrimeSpectrum.basicOpen (idemOf V hV) : TopologicalSpace.Opens (PrimeSpectrum A)) : Set (PrimeSpectrum A)) :=
  (PrimeSpectrum.isClopen_iff.mp (⟨hV, V.isOpen⟩ : IsClopen (V : Set ↥(Spec (CommRingCat.of A))))).choose_spec.2

theorem mem_iff_idemOf_notMem {A : Type} [CommRing A] (V : (Spec (CommRingCat.of A)).Opens)
    (hV : IsClosed (V : Set ↥(Spec (CommRingCat.of A)))) (x : ↥(Spec (CommRingCat.of A))) :
    x ∈ V ↔ idemOf V hV ∉ x.asIdeal := by
  have := Set.ext_iff.mp (coe_eq_basicOpen_idemOf V hV) x
  exact this

theorem eq_basicOpen_idemOf {A : Type} [CommRing A] (V : (Spec (CommRingCat.of A)).Opens)
    (hV : IsClosed (V : Set ↥(Spec (CommRingCat.of A)))) :
    V = (PrimeSpectrum.basicOpen (idemOf V hV) : TopologicalSpace.Opens (PrimeSpectrum A)) :=
  TopologicalSpace.Opens.ext (coe_eq_basicOpen_idemOf V hV)

theorem idemOf_unique {A : Type} [CommRing A] (V : (Spec (CommRingCat.of A)).Opens)
    (hV : IsClosed (V : Set ↥(Spec (CommRingCat.of A)))) (e : A) (he : IsIdempotentElem e)
    (heV : V = (PrimeSpectrum.basicOpen e : TopologicalSpace.Opens (PrimeSpectrum A))) : idemOf V hV = e := by
  apply idem_eq_of_basicOpen_eq (idemOf_isIdempotentElem V hV) he
  rw [← eq_basicOpen_idemOf V hV, ← heV]

theorem idemOf_eq_iff {A : Type} [CommRing A] (V W : (Spec (CommRingCat.of A)).Opens)
    (hV : IsClosed (V : Set ↥(Spec (CommRingCat.of A)))) (hW : IsClosed (W : Set ↥(Spec (CommRingCat.of A)))) :
    idemOf V hV = idemOf W hW ↔ V = W := by
  constructor
  · intro h
    rw [eq_basicOpen_idemOf V hV, eq_basicOpen_idemOf W hW, h]
  · rintro rfl; rfl

theorem preimage_basicOpen {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (e : A) :
    Spec.map (CommRingCat.ofHom f) ⁻¹ᵁ (PrimeSpectrum.basicOpen e : TopologicalSpace.Opens (PrimeSpectrum A)) =
      (PrimeSpectrum.basicOpen (f e) : TopologicalSpace.Opens (PrimeSpectrum B)) := by
  ext x
  show (Spec.map (CommRingCat.ofHom f)) x ∈ PrimeSpectrum.basicOpen e ↔ x ∈ PrimeSpectrum.basicOpen (f e)
  rw [Spec.map_apply]
  exact Iff.rfl

theorem idemOf_preimage {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (V : (Spec (CommRingCat.of A)).Opens) (hV : IsClosed (V : Set ↥(Spec (CommRingCat.of A))))
    (hV' : IsClosed ((Spec.map (CommRingCat.ofHom f) ⁻¹ᵁ V : (Spec (CommRingCat.of B)).Opens) :
      Set ↥(Spec (CommRingCat.of B)))) :
    idemOf (Spec.map (CommRingCat.ofHom f) ⁻¹ᵁ V) hV' = f (idemOf V hV) := by
  apply idemOf_unique _ _ _ ((idemOf_isIdempotentElem V hV).map f)
  conv_lhs => rw [eq_basicOpen_idemOf V hV]
  exact preimage_basicOpen f _

variable {S : Type} [CommRing S] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of S))

def Q (_p : X ⟶ Spec (CommRingCat.of S)) : Type := ↑Γ(X, ⊤)

scoped instance : CommRing (Q p) := inferInstanceAs (CommRing ↑Γ(X, ⊤))

def algHomQ : S →+* Q p := ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ p.appTop).hom

scoped instance : Algebra S (Q p) := (algHomQ p).toAlgebra

theorem algebraMap_Q : algebraMap S (Q p) = algHomQ p := rfl

def pQ : Spec (CommRingCat.of (Q p)) ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S (Q p)))

def eX [IsAffine X] : X ≅ Spec (CommRingCat.of (Q p)) := X.isoSpec

theorem eX_hom_pQ [IsAffine X] : (eX p).hom ≫ pQ p = p := by
  have h := Scheme.isoSpec_hom_naturality p
  rw [Scheme.isoSpec_Spec_hom] at h
  calc (eX p).hom ≫ pQ p
      = X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algHomQ p)) := rfl
    _ = X.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ p.appTop) := by
        rw [algHomQ, CommRingCat.ofHom_hom]
    _ = (X.isoSpec.hom ≫ Spec.map p.appTop) ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of S)).inv := by
        rw [Spec.map_comp, Category.assoc]
    _ = p := by
        rw [h, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

theorem pQ_eq [IsAffine X] : pQ p = (eX p).inv ≫ p :=
  (Iso.eq_inv_comp _).mpr (eX_hom_pQ p)

section insts
variable [IsAffine X] [IsFinite p] [Etale p]

scoped instance isFinite_pQ : IsFinite (pQ p) := by rw [pQ_eq]; infer_instance
scoped instance etale_pQ : Etale (pQ p) := by rw [pQ_eq]; infer_instance

scoped instance moduleFinite_Q : Module.Finite S (Q p) := by
  have := (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap S (Q p)))).mp (isFinite_pQ p)
  exact (RingHom.finite_algebraMap).mp this

scoped instance etale_Q : Algebra.Etale S (Q p) := by
  have : (CommRingCat.ofHom (algebraMap S (Q p))).hom.Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp (etale_pQ p)
  exact RingHom.etale_algebraMap.mp this

scoped instance flat_Q : Module.Flat S (Q p) := inferInstance
scoped instance fp_Q : Module.FinitePresentation S (Q p) :=
  Module.FinitePresentation.of_finite_of_finitePresentation S (Q p)
scoped instance proj_Q : Module.Projective S (Q p) := Module.Flat.projective_of_finitePresentation

theorem rankAtStalk_Q (r : ℕ) (hr : ∀ s : ↥(Spec (CommRingCat.of S)), p.finrank s = r)
    (x : PrimeSpectrum S) : Module.rankAtStalk (R := S) (Q p) x = r := by
  rw [← Scheme.Hom.finrank_SpecMap_algebraMap S (Q p) x]
  change (pQ p).finrank x = r
  rw [pQ_eq, Scheme.Hom.finrank_comp_left_of_isIso]
  exact hr x

end insts

section iota
variable {T : Type} [CommRing T] (φ : S →+* T) {X' : Scheme.{0}} (p' : X' ⟶ Spec (CommRingCat.of T))
  (g : X' ⟶ X) [IsAffine X]

def tfst : Spec (CommRingCat.of (letI := φ.toAlgebra; T ⊗[S] Q p)) ⟶ Spec (CommRingCat.of T) :=
  letI := φ.toAlgebra
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : T →+* T ⊗[S] Q p))

def tsnd : Spec (CommRingCat.of (letI := φ.toAlgebra; T ⊗[S] Q p)) ⟶ Spec (CommRingCat.of (Q p)) :=
  letI := φ.toAlgebra
  Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : Q p →ₐ[S] T ⊗[S] Q p).toRingHom))

omit [IsAffine X] in
theorem isPullback_tensor :
    IsPullback (tfst p φ) (tsnd p φ) (Spec.map (CommRingCat.ofHom φ)) (pQ p) := by
  letI := φ.toAlgebra
  have := isPullback_SpecMap_of_isPushout _ _ _ _
    (IsPushout.of_isColimit (CommRingCat.pushoutCoconeIsColimit S T (Q p)))
  exact this

theorem isPullback_h' (h : IsPullback g p' p (Spec.map (CommRingCat.ofHom φ))) :
    IsPullback p' (g ≫ (eX p).hom) (Spec.map (CommRingCat.ofHom φ)) (pQ p) := by
  refine IsPullback.of_iso h.flip (Iso.refl _) (Iso.refl _) (eX p) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · simp [eX_hom_pQ]

def ι (h : IsPullback g p' p (Spec.map (CommRingCat.ofHom φ))) :
    X' ≅ Spec (CommRingCat.of (letI := φ.toAlgebra; T ⊗[S] Q p)) :=
  IsPullback.isoIsPullback _ _ (isPullback_h' p φ p' g h) (isPullback_tensor p φ)

theorem ι_hom_tfst (h : IsPullback g p' p (Spec.map (CommRingCat.ofHom φ))) :
    (ι p φ p' g h).hom ≫ tfst p φ = p' := by
  simp [ι]

theorem ι_hom_tsnd (h : IsPullback g p' p (Spec.map (CommRingCat.ofHom φ))) :
    (ι p φ p' g h).hom ≫ tsnd p φ = g ≫ (eX p).hom := by
  simp [ι]

end iota

section pt
variable (C : Type) [CommRing C] [Algebra S C]
  (η : ∀ (T : Type) [CommRing T] [Algebra S T], (C →ₐ[S] T) ≃ {e : T ⊗[S] Q p // IsIdempotentElem e})
variable {T : Type} [CommRing T] (φ : S →+* T) {X' : Scheme.{0}} (p' : X' ⟶ Spec (CommRingCat.of T))
  (g : X' ⟶ X) [IsAffine X]

def clopenT (h : IsPullback g p' p (Spec.map (CommRingCat.ofHom φ))) (U : X'.Opens) :
    (Spec (CommRingCat.of (letI := φ.toAlgebra; T ⊗[S] Q p))).Opens :=
  (ι p φ p' g h).inv ⁻¹ᵁ U

theorem isClosed_clopenT (h : IsPullback g p' p (Spec.map (CommRingCat.ofHom φ))) (U : X'.Opens)
    (hU : IsClosed (U : Set ↥X')) :
    IsClosed (clopenT p φ p' g h U : Set ↥(Spec (CommRingCat.of (letI := φ.toAlgebra; T ⊗[S] Q p)))) :=
  hU.preimage (ι p φ p' g h).inv.continuous

def idemU (h : IsPullback g p' p (Spec.map (CommRingCat.ofHom φ))) (U : X'.Opens)
    (hU : IsClosed (U : Set ↥X')) : (letI := φ.toAlgebra; T ⊗[S] Q p) :=
  idemOf (clopenT p φ p' g h U) (isClosed_clopenT p φ p' g h U hU)

def ptZ (h : IsPullback g p' p (Spec.map (CommRingCat.ofHom φ))) (U : X'.Opens)
    (hU : IsClosed (U : Set ↥X')) : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of C) :=
  letI := φ.toAlgebra
  Spec.map (CommRingCat.ofHom
    ((η T).symm ⟨idemU p φ p' g h U hU, idemOf_isIdempotentElem _ _⟩ : C →ₐ[S] T).toRingHom)

theorem ptZ_over (h : IsPullback g p' p (Spec.map (CommRingCat.ofHom φ))) (U : X'.Opens)
    (hU : IsClosed (U : Set ↥X')) :
    ptZ p C η φ p' g h U hU ≫ Spec.map (CommRingCat.ofHom (algebraMap S C)) = Spec.map (CommRingCat.ofHom φ) := by
  letI := φ.toAlgebra
  have hc : ((η T).symm ⟨idemU p φ p' g h U hU, idemOf_isIdempotentElem _ _⟩ : C →ₐ[S] T).toRingHom.comp
      (algebraMap S C) = φ := RingHom.ext fun s => AlgHom.commutes _ s
  rw [ptZ, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]

end pt

end ClopenRep22
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isFinite_etale_represents_clopens_of_isFinite_of_etale.ClopenRep22"

open ClopenRep22 in
theorem solution
    (S : Type) [CommRing S] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of S)) [IsFinite p] [Etale p]
    (r : ℕ) (hr : ∀ s : ↥(Spec (CommRingCat.of S)), p.finrank s = r) :
    ∃ (Z : Scheme.{0}) (ζ : Z ⟶ Spec (CommRingCat.of S)) (_ : IsFinite ζ) (_ : Etale ζ)
      (ptZ : ∀ (T : Type) [CommRing T] (φ : S →+* T) (X' : Scheme.{0}) (p' : X' ⟶ Spec (CommRingCat.of T))
        (g : X' ⟶ X), IsPullback g p' p (Spec.map (CommRingCat.ofHom φ)) →
        ∀ U : X'.Opens, IsClosed (U : Set ↥X') → (Spec (CommRingCat.of T) ⟶ Z)),

      (∀ (T : Type) [CommRing T] (φ : S →+* T) (X' : Scheme.{0}) (p' : X' ⟶ Spec (CommRingCat.of T))
          (g : X' ⟶ X) (h : IsPullback g p' p (Spec.map (CommRingCat.ofHom φ)))
          (U : X'.Opens) (hU : IsClosed (U : Set ↥X')),
          ptZ T φ X' p' g h U hU ≫ ζ = Spec.map (CommRingCat.ofHom φ)) ∧

      (∀ (T T' : Type) [CommRing T] [CommRing T'] (φ : S →+* T) (ψ : T →+* T')
          (X' : Scheme.{0}) (p' : X' ⟶ Spec (CommRingCat.of T)) (g : X' ⟶ X)
          (h : IsPullback g p' p (Spec.map (CommRingCat.ofHom φ)))
          (X'' : Scheme.{0}) (p'' : X'' ⟶ Spec (CommRingCat.of T')) (g' : X'' ⟶ X)
          (h' : IsPullback g' p'' p (Spec.map (CommRingCat.ofHom (ψ.comp φ))))
          (k : X'' ⟶ X'), k ≫ p' = p'' ≫ Spec.map (CommRingCat.ofHom ψ) → k ≫ g = g' →
          ∀ (U : X'.Opens) (hU : IsClosed (U : Set ↥X')) (U' : X''.Opens) (hU' : IsClosed (U' : Set ↥X'')),
            k ⁻¹ᵁ U = U' →
            ptZ T' (ψ.comp φ) X'' p'' g' h' U' hU' = Spec.map (CommRingCat.ofHom ψ) ≫ ptZ T φ X' p' g h U hU) ∧

      (∀ (T : Type) [CommRing T] (φ : S →+* T) (X' : Scheme.{0}) (p' : X' ⟶ Spec (CommRingCat.of T))
          (g : X' ⟶ X) (h : IsPullback g p' p (Spec.map (CommRingCat.ofHom φ)))
          (z : Spec (CommRingCat.of T) ⟶ Z), z ≫ ζ = Spec.map (CommRingCat.ofHom φ) →
          ∃ (U : X'.Opens) (hU : IsClosed (U : Set ↥X')), ptZ T φ X' p' g h U hU = z) ∧

      (∀ (T : Type) [CommRing T] (φ : S →+* T) (X' : Scheme.{0}) (p' : X' ⟶ Spec (CommRingCat.of T))
          (g : X' ⟶ X) (h : IsPullback g p' p (Spec.map (CommRingCat.ofHom φ)))
          (U U' : X'.Opens) (hU : IsClosed (U : Set ↥X')) (hU' : IsClosed (U' : Set ↥X')),
          ptZ T φ X' p' g h U hU = ptZ T φ X' p' g h U' hU' → U = U') := by
  classical
  haveI : IsAffine X := isAffine_of_isAffineHom p
  obtain ⟨C, _, _, _, η, hη⟩ :=
    Algebra.exists_etale_algHom_equiv_isIdempotentElem_tensorProduct_of_projective S (Q p)
  haveI : Module.Finite S C :=
    Module.Finite.of_algHom_equiv_isIdempotentElem_tensorProduct_of_etale_of_rankAtStalk_eq S (Q p) r
      (rankAtStalk_Q p r hr) C η hη
  refine ⟨Spec (CommRingCat.of C), Spec.map (CommRingCat.ofHom (algebraMap S C)), ?_, ?_,
    fun T _ φ X' p' g h U hU => ClopenRep22.ptZ p C η φ p' g h U hU, ?_, ?_, ?_, ?_⟩
  · exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  · exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)
  · intro T _ φ X' p' g h U hU
    exact ptZ_over p C η φ p' g h U hU
  ·
    intro T T' _ _ φ ψ X' p' g h X'' p'' g' h' k hk1 hk2 U hU U' hU' hUU'
    letI algT : Algebra S T := φ.toAlgebra
    letI algT' : Algebra S T' := (ψ.comp φ).toAlgebra
    let ψa : T →ₐ[S] T' := { toRingHom := ψ, commutes' := fun _ => rfl }
    let Mr : T ⊗[S] Q p →+* T' ⊗[S] Q p :=
      (Algebra.TensorProduct.map ψa (AlgHom.id S (Q p))).toRingHom
    have hM1 : Mr.comp (Algebra.TensorProduct.includeLeftRingHom) =
        (Algebra.TensorProduct.includeLeftRingHom).comp ψ := by
      ext t
      simp [Mr, ψa, Algebra.TensorProduct.includeLeftRingHom]
    have hM2 : Mr.comp (Algebra.TensorProduct.includeRight : Q p →ₐ[S] T ⊗[S] Q p).toRingHom =
        (Algebra.TensorProduct.includeRight : Q p →ₐ[S] T' ⊗[S] Q p).toRingHom := by
      ext q
      simp [Mr]
    have hMfst : Spec.map (CommRingCat.ofHom Mr) ≫ tfst p φ =
        tfst p (ψ.comp φ) ≫ Spec.map (CommRingCat.ofHom ψ) := by
      simp only [tfst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hM1
    have hMsnd : Spec.map (CommRingCat.ofHom Mr) ≫ tsnd p φ = tsnd p (ψ.comp φ) := by
      simp only [tsnd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hM2
    have hk : k ≫ (ι p φ p' g h).hom =
        (ι p (ψ.comp φ) p'' g' h').hom ≫ Spec.map (CommRingCat.ofHom Mr) := by
      apply (isPullback_tensor p φ).hom_ext
      · rw [Category.assoc, ι_hom_tfst, hk1, Category.assoc, hMfst, ← Category.assoc, ι_hom_tfst]
      · rw [Category.assoc, ι_hom_tsnd, ← Category.assoc, hk2, Category.assoc, hMsnd, ι_hom_tsnd]
    have hcl : clopenT p (ψ.comp φ) p'' g' h' U' =
        Spec.map (CommRingCat.ofHom Mr) ⁻¹ᵁ (clopenT p φ p' g h U) := by
      show (ι p (ψ.comp φ) p'' g' h').inv ⁻¹ᵁ U' =
        Spec.map (CommRingCat.ofHom Mr) ⁻¹ᵁ ((ι p φ p' g h).inv ⁻¹ᵁ U)
      have hk' : (ι p (ψ.comp φ) p'' g' h').inv ≫ k =
          Spec.map (CommRingCat.ofHom Mr) ≫ (ι p φ p' g h).inv := by
        rw [Iso.inv_comp_eq, ← Category.assoc, ← hk, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [← hUU', ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hk']
    have hid : idemU p (ψ.comp φ) p'' g' h' U' hU' = Mr (idemU p φ p' g h U hU) := by
      unfold idemU
      apply idemOf_unique
      · exact (idemOf_isIdempotentElem _ _).map Mr
      · rw [hcl]
        conv_lhs => rw [eq_basicOpen_idemOf (clopenT p φ p' g h U) (isClosed_clopenT p φ p' g h U hU)]
        exact preimage_basicOpen Mr _
    have hθ : ((η T').symm ⟨idemU p (ψ.comp φ) p'' g' h' U' hU', idemOf_isIdempotentElem _ _⟩ : C →ₐ[S] T') =
        ψa.comp ((η T).symm ⟨idemU p φ p' g h U hU, idemOf_isIdempotentElem _ _⟩) := by
      apply (η T').injective
      rw [Equiv.apply_symm_apply]
      apply Subtype.ext
      rw [hη T T' ψa, Equiv.apply_symm_apply]
      exact hid
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    exact congrArg (fun f : C →ₐ[S] T' => Spec.map (CommRingCat.ofHom f.toRingHom)) hθ
  ·
    intro T _ φ X' p' g h z hz
    letI := φ.toAlgebra
    obtain ⟨θ', rfl⟩ := Spec.map_surjective z
    have hθ' : CommRingCat.ofHom (algebraMap S C) ≫ θ' = CommRingCat.ofHom φ := by
      apply Spec.map_injective
      rw [Spec.map_comp]; exact hz
    let θ : C →ₐ[S] T :=
      { toRingHom := θ'.hom
        commutes' := fun s => by
          show θ'.hom (algebraMap S C s) = φ s
          have := congrArg (fun f => (CommRingCat.Hom.hom f) s) hθ'
          simpa using this }
    let e := η T θ
    let V : (Spec (CommRingCat.of (T ⊗[S] Q p))).Opens :=
      (PrimeSpectrum.basicOpen e.1 : TopologicalSpace.Opens (PrimeSpectrum (T ⊗[S] Q p)))
    have hV : IsClosed (V : Set ↥(Spec (CommRingCat.of (T ⊗[S] Q p)))) :=
      (PrimeSpectrum.isClopen_iff.mpr ⟨e.1, e.2, rfl⟩).1
    refine ⟨(ι p φ p' g h).hom ⁻¹ᵁ V, hV.preimage (ι p φ p' g h).hom.continuous, ?_⟩
    have hcl : clopenT p φ p' g h ((ι p φ p' g h).hom ⁻¹ᵁ V) = V := by
      show (ι p φ p' g h).inv ⁻¹ᵁ ((ι p φ p' g h).hom ⁻¹ᵁ V) = V
      rw [← Scheme.Hom.comp_preimage, Iso.inv_hom_id]
      rfl
    have hid : idemU p φ p' g h ((ι p φ p' g h).hom ⁻¹ᵁ V) (hV.preimage (ι p φ p' g h).hom.continuous) = e.1 := by
      unfold idemU
      rw [show ∀ hV', idemOf (clopenT p φ p' g h ((ι p φ p' g h).hom ⁻¹ᵁ V)) hV' = idemOf V hV from
        fun hV' => by congr 1]
      exact idemOf_unique V hV e.1 e.2 rfl
    show Spec.map _ = Spec.map θ'
    congr 1
    have : (⟨idemU p φ p' g h ((ι p φ p' g h).hom ⁻¹ᵁ V) (hV.preimage (ι p φ p' g h).hom.continuous),
        idemOf_isIdempotentElem _ _⟩ : {e : T ⊗[S] Q p // IsIdempotentElem e}) = e := Subtype.ext hid
    rw [this, show e = η T θ from rfl, Equiv.symm_apply_apply]
    rfl
  ·
    intro T _ φ X' p' g h U U' hU hU' hUU'
    letI := φ.toAlgebra
    have h1 := Spec.map_injective hUU'
    have h2 : ((η T).symm ⟨idemU p φ p' g h U hU, idemOf_isIdempotentElem _ _⟩ : C →ₐ[S] T) =
        (η T).symm ⟨idemU p φ p' g h U' hU', idemOf_isIdempotentElem _ _⟩ := by
      apply AlgHom.ext; intro c
      exact congrArg (fun f => (CommRingCat.Hom.hom f) c) h1
    have h3 := congrArg Subtype.val ((η T).symm.injective h2)
    have h4 : clopenT p φ p' g h U = clopenT p φ p' g h U' :=
      (idemOf_eq_iff _ _ (isClosed_clopenT p φ p' g h U hU) (isClosed_clopenT p φ p' g h U' hU')).mp h3
    have : ∀ W : X'.Opens, W = (ι p φ p' g h).hom ⁻¹ᵁ (clopenT p φ p' g h W) := fun W => by
      show W = (ι p φ p' g h).hom ⁻¹ᵁ ((ι p φ p' g h).inv ⁻¹ᵁ W)
      rw [← Scheme.Hom.comp_preimage, Iso.hom_inv_id]; rfl
    rw [this U, this U', h4]

end
end S_AlgebraicGeometry_exists_isFinite_etale_represents_clopens_of_isFinite_of_etale
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isFinite_etale_represents_clopens_of_isFinite_of_etale (solution)
