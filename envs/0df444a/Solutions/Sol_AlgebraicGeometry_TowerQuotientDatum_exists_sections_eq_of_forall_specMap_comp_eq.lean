-- Prove2me | solution 1 for AlgebraicGeometry.TowerQuotientDatum.exists_sections_eq_of_forall_specMap_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/37e9c381-4286-5d18-9fd2-5ba4d3bb36cf

import Mathlib
import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TowerQuotientDatum_exists_sections_eq_of_forall_specMap_comp_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace TQD7

noncomputable def homSpecOf (S : Scheme.{0}) (B : CommRingCat.{0}) (φ : B ⟶ Γ(S, ⊤)) : S ⟶ Spec B :=
  S.toSpecΓ ≫ Spec.map φ

theorem homSpecOf_appTop (S : Scheme.{0}) (B : CommRingCat.{0}) (φ : B ⟶ Γ(S, ⊤)) :
    (homSpecOf S B φ).appTop = (Scheme.ΓSpecIso B).hom ≫ φ := by
  rw [homSpecOf, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
  exact Scheme.ΓSpecIso_naturality φ

theorem hom_Spec_ext (S : Scheme.{0}) (B : CommRingCat.{0}) (f g : S ⟶ Spec B)
    (h : (Scheme.ΓSpecIso B).inv ≫ f.appTop = (Scheme.ΓSpecIso B).inv ≫ g.appTop) : f = g :=
  ext_of_isAffine ((cancel_epi (Scheme.ΓSpecIso B).inv).mp h)

theorem eq_homSpecOf (S : Scheme.{0}) (B : CommRingCat.{0}) (f : S ⟶ Spec B) :
    f = homSpecOf S B ((Scheme.ΓSpecIso B).inv ≫ f.appTop) := by
  apply ext_of_isAffine
  rw [homSpecOf_appTop, Iso.hom_inv_id_assoc]

noncomputable def secOf {Z : Scheme.{0}} (V : Z.Opens) (B : CommRingCat.{0}) (w : (↑V : Scheme.{0}) ⟶ Spec B) :
    B →+* Γ(Z, V) :=
  ((Scheme.ΓSpecIso B).inv ≫ w.appTop ≫ V.topIso.hom).hom

theorem secOf_resLE {Z Z' : Scheme.{0}} (q : Z ⟶ Z') (V : Z.Opens) (V' : Z'.Opens) (e : V ≤ q ⁻¹ᵁ V')
    (B : CommRingCat.{0}) (w : (↑V' : Scheme.{0}) ⟶ Spec B) (b : B) :
    secOf V B (q.resLE V' V e ≫ w) b = q.appLE V' V e (secOf V' B w b) := by
  simp only [secOf, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  have key := Scheme.Hom.resLE_app_top q e
  rw [← Scheme.Hom.appTop] at key
  rw [key]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  exact Iso.inv_hom_id_apply V.topIso _

theorem eq_of_secOf_eq {Z : Scheme.{0}} (V : Z.Opens) (B : CommRingCat.{0}) (w w' : (↑V : Scheme.{0}) ⟶ Spec B)
    (h : ∀ b : B, secOf V B w b = secOf V B w' b) : w = w' := by
  apply hom_Spec_ext
  rw [← cancel_mono V.topIso.hom]
  ext b
  simpa only [secOf, Category.assoc] using h b

theorem secOf_homSpecOf {Z : Scheme.{0}} (V : Z.Opens) (B : CommRingCat.{0}) (χ : B →+* Γ(Z, V)) (b : B) :
    secOf V B (homSpecOf (↑V) B (CommRingCat.ofHom χ ≫ V.topIso.inv)) b = χ b := by
  simp only [secOf, homSpecOf_appTop, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id,
    CommRingCat.hom_ofHom]

theorem TowerQuotientDatum.exists_smul_eq_of_apply_eq
    {𝒪 : Type} [CommRing 𝒪] {π : 𝒪}
    {X : ℕ → Scheme.{0}} {xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))}
    {xt : ∀ n : ℕ, X n ⟶ X (n + 1)}
    {G : Type} [Group G] {a : ∀ n : ℕ, G →* Aut (X n)}
    (D : TowerQuotientDatum 𝒪 π X xb xt G a) (n : ℕ) (x x' : X n) (hxx : (D.p n).base x = (D.p n).base x') :
    ∃ g : G, (a n g).hom.base x = x' := by
  classical
  let k₀ : CommRingCat := (D.Y n).residueField ((D.p n).base x)
  let k₁ : CommRingCat := (X n).residueField x
  let k₂ : CommRingCat := (X n).residueField x'
  let i₁ : k₀ ⟶ k₁ := (D.p n).residueFieldMap x
  let i₂ : k₀ ⟶ k₂ := ((D.Y n).residueFieldCongr hxx).hom ≫ (D.p n).residueFieldMap x'
  letI alg₁ : Algebra k₀ k₁ := i₁.hom.toAlgebra
  letI alg₂ : Algebra k₀ k₂ := i₂.hom.toAlgebra
  haveI : Nontrivial (TensorProduct k₀ k₁ k₂) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k₀ k₁ k₂ i₁.hom.injective i₂.hom.injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct k₀ k₁ k₂)
  letI : Field (TensorProduct k₀ k₁ k₂ ⧸ m) := Ideal.Quotient.field m
  let K : Type := AlgebraicClosure (TensorProduct k₀ k₁ k₂ ⧸ m)
  let j : TensorProduct k₀ k₁ k₂ →+* K := (algebraMap _ K).comp (Ideal.Quotient.mk m)
  let j₁ : k₁ →+* K := j.comp (Algebra.TensorProduct.includeLeft (R := k₀) (S := k₀) (A := k₁) (B := k₂)).toRingHom
  let j₂ : k₂ →+* K := j.comp (Algebra.TensorProduct.includeRight (R := k₀) (A := k₁) (B := k₂)).toRingHom
  have hj : j₁.comp i₁.hom = j₂.comp i₂.hom := by
    ext c
    show j (Algebra.TensorProduct.includeLeft (R := k₀) (S := k₀) (A := k₁) (B := k₂) (algebraMap k₀ k₁ c)) =
      j (Algebra.TensorProduct.includeRight (R := k₀) (A := k₁) (B := k₂) (algebraMap k₀ k₂ c))
    rw [AlgHom.commutes, AlgHom.commutes]
  let ξ₁ : Spec (CommRingCat.of K) ⟶ X n := Spec.map (CommRingCat.ofHom j₁) ≫ (X n).fromSpecResidueField x
  let ξ₂ : Spec (CommRingCat.of K) ⟶ X n := Spec.map (CommRingCat.ofHom j₂) ≫ (X n).fromSpecResidueField x'
  have hξp : ξ₁ ≫ D.p n = ξ₂ ≫ D.p n := by
    show (Spec.map (CommRingCat.ofHom j₁) ≫ (X n).fromSpecResidueField x) ≫ D.p n =
      (Spec.map (CommRingCat.ofHom j₂) ≫ (X n).fromSpecResidueField x') ≫ D.p n
    rw [Category.assoc, Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← (D.Y n).residueFieldCongr_fromSpecResidueField hxx, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc]
    congr 2
    show i₁ ≫ CommRingCat.ofHom j₁ = (((D.Y n).residueFieldCongr hxx).hom ≫ (D.p n).residueFieldMap x') ≫ CommRingCat.ofHom j₂
    ext c
    exact congrArg (fun φ : (k₀ : Type) →+* K => φ c) hj
  obtain ⟨g, hg⟩ := ((D.fib n K (ξ₁ ≫ D.p n)).2 ξ₁ ξ₂ rfl).mp hξp.symm
  refine ⟨g, ?_⟩
  have hb := congrArg (fun φ => φ.base (default : Spec (CommRingCat.of K))) hg
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hb
  have h1 : ξ₁.base default = x := by
    show ((X n).fromSpecResidueField x).base ((Spec.map (CommRingCat.ofHom j₁)).base default) = x
    exact (X n).fromSpecResidueField_apply x _
  have h2 : ξ₂.base default = x' := by
    show ((X n).fromSpecResidueField x').base ((Spec.map (CommRingCat.ofHom j₂)).base default) = x'
    exact (X n).fromSpecResidueField_apply x' _
  rw [h1, h2] at hb
  exact hb.symm

theorem app_injective_of_epi {X Y : Scheme.{0}} (p : X ⟶ Y) (U : Y.Opens) [Epi (p ∣_ U)] :
    Function.Injective (p.app U).hom := by
  classical
  intro t t' htt
  let B : CommRingCat.{0} := CommRingCat.of (Polynomial ℤ)
  let χ : ∀ s : Γ(Y, U), B →+* Γ(Y, U) := fun s => (Polynomial.aeval (R := ℤ) s).toRingHom
  have hχ : ∀ s, χ s Polynomial.X = s := fun s => Polynomial.aeval_X s
  let v : ∀ s : Γ(Y, U), (↑U : Scheme.{0}) ⟶ Spec B := fun s => homSpecOf (↑U) B (CommRingCat.ofHom (χ s) ≫ U.topIso.inv)
  have hv : ∀ s b, secOf U B (v s) b = χ s b := fun s b => secOf_homSpecOf U B (χ s) b
  have key : (p ∣_ U) ≫ v t = (p ∣_ U) ≫ v t' := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict]
    apply eq_of_secOf_eq
    intro b
    rw [secOf_resLE, secOf_resLE, hv, hv, Scheme.Hom.appLE_eq_app]
    show (p.app U).hom.toIntAlgHom (Polynomial.aeval (R := ℤ) t b) = (p.app U).hom.toIntAlgHom (Polynomial.aeval (R := ℤ) t' b)
    rw [← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply]
    show Polynomial.aeval (R := ℤ) ((p.app U).hom t) b = Polynomial.aeval (R := ℤ) ((p.app U).hom t') b
    rw [htt]
  have hvv : v t = v t' := (cancel_epi (p ∣_ U)).mp key
  have := congrArg (fun w => secOf U B w Polynomial.X) hvv
  simp only [hv, hχ] at this
  exact this

theorem appLE_top_top {T Y : Scheme.{0}} (f : T ⟶ Y) (h : (⊤ : T.Opens) ≤ f ⁻¹ᵁ ⊤) : f.appLE ⊤ ⊤ h = f.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem appLE_congr_hom {T Y : Scheme.{0}} {f g : T ⟶ Y} (h : f = g) (U : Y.Opens) (V : T.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) : f.appLE U V hf = g.appLE U V hg := by
  subst h; rfl

theorem fromSpec_appLE_of_le {Z : Scheme.{0}} {D V : Z.Opens} (hD : IsAffineOpen D) (hDV : D ≤ V)
    (h : (⊤ : (Spec Γ(Z, D)).Opens) ≤ hD.fromSpec ⁻¹ᵁ V) :
    hD.fromSpec.appLE V ⊤ h = Z.presheaf.map (homOfLE hDV).op ≫ (Scheme.ΓSpecIso Γ(Z, D)).inv := by
  rw [Scheme.Hom.appLE, hD.fromSpec_app_of_le V hDV, Category.assoc, Category.assoc, ← Functor.map_comp]
  congr 1

theorem eq_SpecMap_of_appTop {A B : CommRingCat.{0}} (ℓ : Spec B ⟶ Spec A) :
    ℓ = Spec.map ((Scheme.ΓSpecIso A).inv ≫ ℓ.appTop ≫ (Scheme.ΓSpecIso B).hom) := by
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso B).hom, Scheme.ΓSpecIso_naturality, Iso.hom_inv_id_assoc]

theorem fromSpec_eq_SpecMap {A : CommRingCat.{0}} {D : (Spec A).Opens} (hD : IsAffineOpen D) :
    hD.fromSpec = Spec.map ((Scheme.ΓSpecIso A).inv ≫ (Spec A).presheaf.map (homOfLE (le_top : D ≤ ⊤)).op) := by
  rw [Spec.map_comp, ← IsAffineOpen.map_fromSpec (isAffineOpen_top (Spec A)) hD (homOfLE (le_top : D ≤ ⊤)).op,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]

theorem sections_eq_of_forall_appLE_eq {Z : Scheme.{0}} (P : Z.Opens) {ι : Type} {S : ι → Scheme.{0}}
    (φ : ∀ i : ι, S i ⟶ Z) [hφ : ∀ i, IsOpenImmersion (φ i)]
    (hle : ∀ i, (φ i) ''ᵁ ⊤ ≤ P) (hcov : ∀ z : Z, z ∈ P → ∃ i, z ∈ (φ i) ''ᵁ ⊤)
    (τ τ' : Γ(Z, P)) (h : ∀ i, (φ i).appLE P ⊤ (by rw [← Scheme.Hom.preimage_image_eq (φ i) ⊤]; exact (φ i).preimage_mono (hle i)) τ =
      (φ i).appLE P ⊤ (by rw [← Scheme.Hom.preimage_image_eq (φ i) ⊤]; exact (φ i).preimage_mono (hle i)) τ') : τ = τ' := by
  apply TopCat.Sheaf.eq_of_locally_eq' Z.sheaf (fun i => (φ i) ''ᵁ ⊤) P (fun i => homOfLE (hle i))
  · intro z hz
    obtain ⟨i, hi⟩ := hcov z hz
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro i
    apply ((φ i).appIso ⊤).commRingCatIsoToRingEquiv.injective
    show ((φ i).appIso ⊤).hom.hom ((Z.presheaf.map (homOfLE (hle i)).op).hom τ) =
      ((φ i).appIso ⊤).hom.hom ((Z.presheaf.map (homOfLE (hle i)).op).hom τ')
    rw [Scheme.Hom.appIso_hom', ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    exact h i

theorem appLE_injective_of_le {S Z : Scheme.{0}} (f : S ⟶ Z) [IsOpenImmersion f] (O : Z.Opens)
    (hO : O ≤ f.opensRange) : Function.Injective (f.app O).hom := by
  intro u v huv
  have key := Scheme.Hom.app_invApp' f O hO
  have h2 := congrArg (fun w => ((f.appIso (f ⁻¹ᵁ O)).inv).hom w) huv
  simp only [← CommRingCat.comp_apply, key] at h2
  have hE : f ''ᵁ f ⁻¹ᵁ O = O := by rw [Scheme.Hom.image_preimage_eq_opensRange_inf]; exact inf_eq_right.mpr hO
  have h3 : (Z.presheaf.map (eqToHom hE).op).hom u = (Z.presheaf.map (eqToHom hE).op).hom v := by convert h2 using 2
  haveI : IsIso (Z.presheaf.map (eqToHom hE).op) := inferInstance
  exact ((asIso (Z.presheaf.map (eqToHom hE).op)).commRingCatIsoToRingEquiv).injective h3

theorem exists_section_of_compatible {Z : Scheme.{0}} (P : Z.Opens) {ι : Type} {S : ι → Scheme.{0}}
    (φ : ∀ i : ι, S i ⟶ Z) [hφ : ∀ i, IsOpenImmersion (φ i)]
    (hle : ∀ i, (φ i) ''ᵁ ⊤ ≤ P) (hcov : ∀ z : Z, z ∈ P → ∃ i, z ∈ (φ i) ''ᵁ ⊤)
    (e : ∀ i, Γ(S i, ⊤))
    (hcompat : ∀ i j, (Z.presheaf.map (homOfLE (inf_le_left : (φ i) ''ᵁ ⊤ ⊓ (φ j) ''ᵁ ⊤ ≤ _)).op).hom (((φ i).appIso ⊤).inv.hom (e i)) =
      (Z.presheaf.map (homOfLE (inf_le_right : (φ i) ''ᵁ ⊤ ⊓ (φ j) ''ᵁ ⊤ ≤ _)).op).hom (((φ j).appIso ⊤).inv.hom (e j))) :
    ∃ τ : Γ(Z, P), ∀ i, ((φ i).appLE P ⊤ (by rw [← Scheme.Hom.preimage_image_eq (φ i) ⊤]; exact (φ i).preimage_mono (hle i))).hom τ = e i := by
  let sf : ∀ i, Γ(Z, (φ i) ''ᵁ ⊤) := fun i => ((φ i).appIso ⊤).inv.hom (e i)
  have hsf : TopCat.Presheaf.IsCompatible Z.sheaf.1 (fun i => (φ i) ''ᵁ ⊤) sf := fun i j => hcompat i j
  obtain ⟨τ, hτ, -⟩ := TopCat.Sheaf.existsUnique_gluing' Z.sheaf (fun i => (φ i) ''ᵁ ⊤) P (fun i => homOfLE (hle i))
    (fun z hz => by obtain ⟨i, hi⟩ := hcov z hz; exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩) sf hsf
  refine ⟨τ, fun i => ?_⟩
  have h1 : ((φ i).appLE P ⊤ (by rw [← Scheme.Hom.preimage_image_eq (φ i) ⊤]; exact (φ i).preimage_mono (hle i))).hom τ =
      ((φ i).appIso ⊤).hom.hom ((Z.presheaf.map (homOfLE (hle i)).op).hom τ) := by
    rw [Scheme.Hom.appIso_hom', ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  rw [h1, show (Z.presheaf.map (homOfLE (hle i)).op).hom τ = sf i from hτ i]
  exact Iso.inv_hom_id_apply ((φ i).appIso ⊤) (e i)

theorem compat_of_agree {Z : Scheme.{0}} {G : Type} [Group G] (a : G →* Aut Z) {A : Type} [CommRing A]
    (κ : Spec (CommRingCat.of A) ⟶ Z) [IsOpenImmersion κ] (fam : A)
    (hagree : ∀ (g : G) (B : Type) [CommRing B] (x x' : A →+* B),
      Spec.map (CommRingCat.ofHom x) ≫ κ = (Spec.map (CommRingCat.ofHom x') ≫ κ) ≫ (a g).hom → x fam = x' fam)
    (g h : G) :
    (Z.presheaf.map (homOfLE (inf_le_left : (κ ≫ (a g).hom) ''ᵁ ⊤ ⊓ (κ ≫ (a h).hom) ''ᵁ ⊤ ≤ _)).op).hom
        (((κ ≫ (a g).hom).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom fam)) =
      (Z.presheaf.map (homOfLE (inf_le_right : (κ ≫ (a g).hom) ''ᵁ ⊤ ⊓ (κ ≫ (a h).hom) ''ᵁ ⊤ ≤ _)).op).hom
        (((κ ≫ (a h).hom).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom fam)) := by
  classical
  set φg : Spec (CommRingCat.of A) ⟶ Z := κ ≫ (a g).hom with hφg
  set φh : Spec (CommRingCat.of A) ⟶ Z := κ ≫ (a h).hom with hφh
  set e : Γ(Spec (CommRingCat.of A), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom fam with he
  let O : Z.Opens := φg ''ᵁ ⊤ ⊓ φh ''ᵁ ⊤
  have hOg : O ≤ φg.opensRange := inf_le_left.trans (by rw [Scheme.Hom.image_top_eq_opensRange])
  let O' : (Spec (CommRingCat.of A)).Opens := φg ⁻¹ᵁ O

  apply appLE_injective_of_le φg O hOg

  have hL : (φg.app O).hom ((Z.presheaf.map (homOfLE (inf_le_left : O ≤ _)).op).hom ((φg.appIso ⊤).inv.hom e)) =
      ((Spec (CommRingCat.of A)).presheaf.map (homOfLE (le_top : O' ≤ ⊤)).op).hom e := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE,
      Scheme.Hom.appIso_inv_appLE]

  have hR : (φg.app O).hom ((Z.presheaf.map (homOfLE (inf_le_right : O ≤ _)).op).hom ((φh.appIso ⊤).inv.hom e)) =
      (φg.appLE (φh ''ᵁ ⊤) O' (φg.preimage_mono inf_le_right)).hom ((φh.appIso ⊤).inv.hom e) := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE]
  rw [hL, hR]

  apply TopCat.Sheaf.eq_of_locally_eq' (Spec (CommRingCat.of A)).sheaf
    (fun r : {r : Γ(Spec (CommRingCat.of A), ⊤) // (Spec (CommRingCat.of A)).basicOpen r ≤ O'} =>
      (Spec (CommRingCat.of A)).basicOpen r.1) O' (fun r => homOfLE r.2)
  · intro z hz
    obtain ⟨r, hr, hzr⟩ := (isAffineOpen_top (Spec (CommRingCat.of A))).exists_basicOpen_le ⟨z, hz⟩ (Set.mem_univ _)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨r, hr⟩, hzr⟩
  rintro ⟨r, hr⟩
  let D : (Spec (CommRingCat.of A)).Opens := (Spec (CommRingCat.of A)).basicOpen r
  have hD : IsAffineOpen D := (isAffineOpen_top (Spec (CommRingCat.of A))).basicOpen r
  let B : CommRingCat.{0} := Γ(Spec (CommRingCat.of A), D)

  let x : A →+* B := ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (Spec (CommRingCat.of A)).presheaf.map (homOfLE (le_top : D ≤ ⊤)).op).hom
  have hrange : Set.range (hD.fromSpec ≫ φg).base ⊆ Set.range φh.base := by
    rintro _ ⟨w, rfl⟩
    have h1 : (hD.fromSpec.base w) ∈ D := by
      show hD.fromSpec.base w ∈ (D : Set _)
      exact hD.range_fromSpec ▸ Set.mem_range_self w
    have h2 : hD.fromSpec.base w ∈ O' := hr h1
    have h3 : φg.base (hD.fromSpec.base w) ∈ φh ''ᵁ ⊤ := (inf_le_right (a := φg ''ᵁ ⊤)) h2
    rw [Scheme.Hom.image_top_eq_opensRange] at h3
    exact h3
  let ℓ : Spec B ⟶ Spec (CommRingCat.of A) := IsOpenImmersion.lift φh (hD.fromSpec ≫ φg) hrange
  have hℓ : ℓ ≫ φh = hD.fromSpec ≫ φg := IsOpenImmersion.lift_fac φh (hD.fromSpec ≫ φg) hrange
  let x' : A →+* B := ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ ℓ.appTop ≫ (Scheme.ΓSpecIso B).hom).hom

  have hx : Spec.map (CommRingCat.ofHom x) = hD.fromSpec := by
    rw [fromSpec_eq_SpecMap hD]; rfl
  have hx' : Spec.map (CommRingCat.ofHom x') = ℓ := by
    rw [eq_SpecMap_of_appTop ℓ]; rfl
  have hrel : Spec.map (CommRingCat.ofHom x) ≫ κ = (Spec.map (CommRingCat.ofHom x') ≫ κ) ≫ (a (g⁻¹ * h)).hom := by
    rw [hx, hx', map_mul, map_inv, Aut.Aut_mul_def, Aut.Aut_inv_def, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    have : ℓ ≫ κ ≫ (a h).hom = hD.fromSpec ≫ κ ≫ (a g).hom := by
      rw [← Category.assoc, ← Category.assoc]; exact hℓ
    rw [show ℓ ≫ κ ≫ (a h).hom ≫ (a g).inv = (ℓ ≫ κ ≫ (a h).hom) ≫ (a g).inv by simp only [Category.assoc], this]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hag := hagree (g⁻¹ * h) B x x' hrel

  show ((Spec (CommRingCat.of A)).presheaf.map (homOfLE hr).op).hom
      (((Spec (CommRingCat.of A)).presheaf.map (homOfLE (le_top : O' ≤ ⊤)).op).hom e) =
    ((Spec (CommRingCat.of A)).presheaf.map (homOfLE hr).op).hom
      ((φg.appLE (φh ''ᵁ ⊤) O' (φg.preimage_mono inf_le_right)).hom ((φh.appIso ⊤).inv.hom e))
  have hLD : ((Spec (CommRingCat.of A)).presheaf.map (homOfLE hr).op).hom
      (((Spec (CommRingCat.of A)).presheaf.map (homOfLE (le_top : O' ≤ ⊤)).op).hom e) = x fam := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  have h5 := fromSpec_appLE_of_le hD (le_rfl : D ≤ D) (by rw [hD.fromSpec_preimage_self])
  have h6 : ∀ w : Γ(Spec (CommRingCat.of A), D), (Scheme.ΓSpecIso B).inv.hom w =
      (hD.fromSpec.appLE D ⊤ (by rw [hD.fromSpec_preimage_self])).hom w := by
    intro w
    rw [h5, CommRingCat.comp_apply]
    congr 1
  have hRD : ((Spec (CommRingCat.of A)).presheaf.map (homOfLE hr).op).hom
      ((φg.appLE (φh ''ᵁ ⊤) O' (φg.preimage_mono inf_le_right)).hom ((φh.appIso ⊤).inv.hom e)) = x' fam := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    apply (Scheme.ΓSpecIso B).commRingCatIsoToRingEquiv.symm.injective
    show (Scheme.ΓSpecIso B).inv.hom ((φg.appLE (φh ''ᵁ ⊤) D _).hom ((φh.appIso ⊤).inv.hom e)) =
      (Scheme.ΓSpecIso B).inv.hom ((Scheme.ΓSpecIso B).hom.hom (ℓ.appTop.hom e))
    rw [Iso.hom_inv_id_apply, h6, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
      appLE_congr_hom hℓ.symm (φh ''ᵁ ⊤) ⊤ _ (by rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq, Scheme.Hom.preimage_top]),
      ← Scheme.Hom.appLE_comp_appLE ℓ φh (φh ''ᵁ ⊤) ⊤ ⊤ (by rw [Scheme.Hom.preimage_image_eq]) (by rw [Scheme.Hom.preimage_top]),
      CommRingCat.comp_apply, appLE_top_top, ← Scheme.Hom.appIso_hom', Iso.inv_hom_id_apply]
  rw [hLD, hRD]
  exact hag

end TQD7

open TQD7 in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] {π : 𝒪}
    {X : ℕ → Scheme.{0}} {xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))}
    {xt : ∀ n : ℕ, X n ⟶ X (n + 1)}
    {G : Type} [Group G] {a : ∀ n : ℕ, G →* Aut (X n)}
    (D : TowerQuotientDatum 𝒪 π X xb xt G a)
    (ha_xt : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xt n = xt n ≫ (a (n + 1) g).hom)

    (A : ℕ → Type) [∀ n : ℕ, CommRing (A n)] (t : ∀ n : ℕ, A (n + 1) →+* A n)
    (κ : ∀ n : ℕ, Spec (CommRingCat.of (A n)) ⟶ X n) (hκ : ∀ n : ℕ, IsOpenImmersion (κ n))
    (hκt : ∀ n : ℕ, κ n ≫ xt n = Spec.map (CommRingCat.ofHom (t n)) ≫ κ (n + 1))

    (U : ∀ n : ℕ, (D.Y n).Opens)
    (hU : ∀ n : ℕ, (U n : Set (D.Y n)) = Set.range (κ n ≫ D.p n).base)
    (hUt : ∀ n : ℕ, (D.yt n) ⁻¹ᵁ (U (n + 1)) = U n)

    (fam : ∀ n : ℕ, A n) (hfam : ∀ n : ℕ, t n (fam (n + 1)) = fam n)
    (hagree : ∀ (n : ℕ) (g : G) (B : Type) [CommRing B] (x x' : A n →+* B),
      Spec.map (CommRingCat.ofHom x) ≫ κ n = (Spec.map (CommRingCat.ofHom x') ≫ κ n) ≫ (a n g).hom → x (fam n) = x' (fam n)) :
    ∃ s : ∀ n : ℕ, ↑((D.Y n).presheaf.obj (Opposite.op (U n))),
      (∀ (n : ℕ) (hle : U n ≤ (D.yt n) ⁻¹ᵁ (U (n + 1))),
        (D.Y n).presheaf.map (homOfLE hle).op (((D.yt n).app (U (n + 1))).hom (s (n + 1))) = s n) ∧
      ∀ (n : ℕ) (hle : (⊤ : (Spec (CommRingCat.of (A n))).Opens) ≤ (κ n ≫ D.p n) ⁻¹ᵁ (U n)),
        (Scheme.ΓSpecIso (CommRingCat.of (A n))).hom.hom
          ((Spec (CommRingCat.of (A n))).presheaf.map (homOfLE hle).op (((κ n ≫ D.p n).app (U n)).hom (s n))) = fam n := by
  classical

  have hle : ∀ (n : ℕ) (g : G), (κ n ≫ (a n g).hom) ''ᵁ ⊤ ≤ (D.p n) ⁻¹ᵁ (U n) := by
    intro n g z hz
    obtain ⟨s, -, rfl⟩ := hz
    show (D.p n).base ((κ n ≫ (a n g).hom).base s) ∈ (U n : Set (D.Y n))
    rw [hU n, ← Scheme.Hom.comp_apply, Category.assoc, D.p_inv]
    exact ⟨s, rfl⟩
  have hcov : ∀ (n : ℕ) (z : X n), z ∈ (D.p n) ⁻¹ᵁ (U n) → ∃ g : G, z ∈ (κ n ≫ (a n g).hom) ''ᵁ ⊤ := by
    intro n z hz
    have hz' : (D.p n).base z ∈ (U n : Set (D.Y n)) := hz
    rw [hU n] at hz'
    obtain ⟨s, hs⟩ := hz'
    obtain ⟨g, hg⟩ := TQD7.TowerQuotientDatum.exists_smul_eq_of_apply_eq D n ((κ n).base s) z
      (by rw [← Scheme.Hom.comp_apply]; exact hs)
    exact ⟨g, ⟨s, trivial, by show (κ n ≫ (a n g).hom).base s = z; rw [Scheme.Hom.comp_apply]; exact hg⟩⟩
  haveI hκi : ∀ n, IsOpenImmersion (κ n) := hκ

  have hσ : ∀ n : ℕ, ∃ σ : Γ(X n, (D.p n) ⁻¹ᵁ (U n)), ∀ g : G,
      ((κ n ≫ (a n g).hom).appLE ((D.p n) ⁻¹ᵁ (U n)) ⊤
        (by rw [← Scheme.Hom.preimage_image_eq (κ n ≫ (a n g).hom) ⊤]; exact (κ n ≫ (a n g).hom).preimage_mono (hle n g))).hom σ =
      (Scheme.ΓSpecIso (CommRingCat.of (A n))).inv.hom (fam n) := fun n =>
    TQD7.exists_section_of_compatible ((D.p n) ⁻¹ᵁ (U n)) (fun g => κ n ≫ (a n g).hom) (hle n) (hcov n)
      (fun _ => (Scheme.ΓSpecIso (CommRingCat.of (A n))).inv.hom (fam n))
      (fun g h => TQD7.compat_of_agree (a n) (κ n) (fam n) (hagree n) g h)
  choose σ hσ using hσ

  have SEP : ∀ (n : ℕ) (τ τ' : Γ(X n, (D.p n) ⁻¹ᵁ (U n))),
      (∀ g : G, ((κ n ≫ (a n g).hom).appLE ((D.p n) ⁻¹ᵁ (U n)) ⊤
        (by rw [← Scheme.Hom.preimage_image_eq (κ n ≫ (a n g).hom) ⊤]; exact (κ n ≫ (a n g).hom).preimage_mono (hle n g))).hom τ =
        ((κ n ≫ (a n g).hom).appLE ((D.p n) ⁻¹ᵁ (U n)) ⊤
        (by rw [← Scheme.Hom.preimage_image_eq (κ n ≫ (a n g).hom) ⊤]; exact (κ n ≫ (a n g).hom).preimage_mono (hle n g))).hom τ') →
      τ = τ' := fun n τ τ' h =>
    TQD7.sections_eq_of_forall_appLE_eq ((D.p n) ⁻¹ᵁ (U n)) (fun g => κ n ≫ (a n g).hom) (hle n) (hcov n) τ τ' h

  have hPinv : ∀ (n : ℕ) (g : G), (D.p n) ⁻¹ᵁ (U n) ≤ (a n g).hom ⁻¹ᵁ ((D.p n) ⁻¹ᵁ (U n)) := by
    intro n g; rw [← Scheme.Hom.comp_preimage, D.p_inv]
  have INV : ∀ (n : ℕ) (g' : G), ((a n g').hom.appLE ((D.p n) ⁻¹ᵁ (U n)) ((D.p n) ⁻¹ᵁ (U n)) (hPinv n g')).hom (σ n) = σ n := by
    intro n g'
    apply SEP n
    intro g
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
      TQD7.appLE_congr_hom (show (κ n ≫ (a n g).hom) ≫ (a n g').hom = κ n ≫ (a n (g' * g)).hom by
        rw [map_mul, Aut.Aut_mul_def, Iso.trans_hom, Category.assoc]) _ _ _
        (by rw [← Scheme.Hom.preimage_image_eq (κ n ≫ (a n (g' * g)).hom) ⊤]; exact (κ n ≫ (a n (g' * g)).hom).preimage_mono (hle n _)),
      hσ n (g' * g), hσ n g]

  have hPxt : ∀ n : ℕ, (D.p n) ⁻¹ᵁ (U n) ≤ (xt n) ⁻¹ᵁ ((D.p (n + 1)) ⁻¹ᵁ (U (n + 1))) := by
    intro n; rw [← Scheme.Hom.comp_preimage, D.p_xt, Scheme.Hom.comp_preimage, hUt]
  have XT : ∀ n : ℕ, ((xt n).appLE ((D.p (n + 1)) ⁻¹ᵁ (U (n + 1))) ((D.p n) ⁻¹ᵁ (U n)) (hPxt n)).hom (σ (n + 1)) = σ n := by
    intro n
    apply SEP n
    intro g
    have hcomm : (κ n ≫ (a n g).hom) ≫ xt n = Spec.map (CommRingCat.ofHom (t n)) ≫ (κ (n + 1) ≫ (a (n + 1) g).hom) := by
      rw [Category.assoc, ha_xt, ← Category.assoc, hκt, Category.assoc]
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
      TQD7.appLE_congr_hom hcomm ((D.p (n + 1)) ⁻¹ᵁ (U (n + 1))) ⊤ _
        (fun w _ => by
          show (Spec.map (CommRingCat.ofHom (t n)) ≫ κ (n + 1) ≫ (a (n + 1) g).hom).base w ∈ ((D.p (n + 1)) ⁻¹ᵁ (U (n + 1)) : Set _)
          rw [Scheme.Hom.comp_apply]
          exact hle (n + 1) g ⟨_, trivial, rfl⟩),
      ← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom (t n))) (κ (n + 1) ≫ (a (n + 1) g).hom) _ ⊤ ⊤
        (by rw [← Scheme.Hom.preimage_image_eq (κ (n + 1) ≫ (a (n + 1) g).hom) ⊤]; exact (κ (n + 1) ≫ (a (n + 1) g).hom).preimage_mono (hle (n + 1) g))
        (by rw [Scheme.Hom.preimage_top]),
      CommRingCat.comp_apply, hσ (n + 1) g, TQD7.appLE_top_top, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
      CommRingCat.comp_apply, hσ n g]
    show (Scheme.ΓSpecIso (CommRingCat.of (A n))).inv.hom (t n (fam (n + 1))) = _
    rw [hfam]

  let Bz : CommRingCat.{0} := CommRingCat.of (Polynomial ℤ)
  let χ : ∀ n : ℕ, Bz →+* Γ(X n, (D.p n) ⁻¹ᵁ (U n)) := fun n => (Polynomial.aeval (R := ℤ) (σ n)).toRingHom
  have hχ : ∀ (n : ℕ) (b : Bz) {S : CommRingCat.{0}} (ψ : Γ(X n, (D.p n) ⁻¹ᵁ (U n)) ⟶ S),
      ψ.hom (χ n b) = Polynomial.aeval (R := ℤ) (ψ.hom (σ n)) b := by
    intro n b S ψ
    show ψ.hom.toIntAlgHom (Polynomial.aeval (R := ℤ) (σ n) b) = _
    rw [← Polynomial.aeval_algHom_apply]
    rfl
  let u : ∀ n : ℕ, (↑((D.p n) ⁻¹ᵁ (U n)) : Scheme.{0}) ⟶ Spec Bz := fun n =>
    TQD7.homSpecOf _ Bz (CommRingCat.ofHom (χ n) ≫ ((D.p n) ⁻¹ᵁ (U n)).topIso.inv)
  have hu : ∀ (n : ℕ) (b : Bz), TQD7.secOf ((D.p n) ⁻¹ᵁ (U n)) Bz (u n) b = χ n b := fun n b =>
    TQD7.secOf_homSpecOf _ Bz (χ n) b
  have hinv : ∀ (n : ℕ) (g : G),
      Scheme.Hom.resLE (a n g).hom ((D.p n) ⁻¹ᵁ (U n)) ((D.p n) ⁻¹ᵁ (U n))
        (by rw [← Scheme.Hom.comp_preimage, D.p_inv]) ≫ u n = u n := by
    intro n g
    apply TQD7.eq_of_secOf_eq
    intro b
    rw [TQD7.secOf_resLE, hu, hχ, INV]
    rfl
  have hcmp : ∀ n : ℕ,
      Scheme.Hom.resLE (xt n) ((D.p (n + 1)) ⁻¹ᵁ (U (n + 1))) ((D.p n) ⁻¹ᵁ (U n))
        (by rw [← Scheme.Hom.comp_preimage, D.p_xt, Scheme.Hom.comp_preimage, hUt]) ≫ u (n + 1) = u n := by
    intro n
    apply TQD7.eq_of_secOf_eq
    intro b
    rw [TQD7.secOf_resLE, hu, hu, hχ, XT]
    rfl
  obtain ⟨v, hv⟩ := D.univ_loc (Spec Bz) U hUt u hinv hcmp

  have hpv : ∀ n : ℕ, ((D.p n).app (U n)).hom (TQD7.secOf (U n) Bz (v n) Polynomial.X) = σ n := by
    intro n
    rw [Scheme.Hom.app_eq_appLE, ← TQD7.secOf_resLE, Scheme.Hom.resLE_eq_morphismRestrict, hv n, hu]
    exact Polynomial.aeval_X (R := ℤ) (σ n)
  refine ⟨fun n => TQD7.secOf (U n) Bz (v n) Polynomial.X, ?_, ?_⟩
  ·
    intro n hle'
    haveI := D.p_epi_loc n (U n)
    apply TQD7.app_injective_of_epi (D.p n) (U n)
    show ((D.p n).app (U n)).hom (((D.yt n).appLE (U (n + 1)) (U n) hle').hom (TQD7.secOf (U (n + 1)) Bz (v (n + 1)) Polynomial.X)) =
      ((D.p n).app (U n)).hom (TQD7.secOf (U n) Bz (v n) Polynomial.X)
    rw [hpv n, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE (D.p n), Scheme.Hom.appLE_comp_appLE,
      TQD7.appLE_congr_hom (D.p_xt n).symm (U (n + 1)) ((D.p n) ⁻¹ᵁ (U n)) _
        ((hPxt n).trans ((xt n).preimage_mono le_rfl)),
      ← Scheme.Hom.appLE_comp_appLE (xt n) (D.p (n + 1)) (U (n + 1)) ((D.p (n + 1)) ⁻¹ᵁ (U (n + 1))) ((D.p n) ⁻¹ᵁ (U n))
        le_rfl (hPxt n),
      CommRingCat.comp_apply, ← Scheme.Hom.app_eq_appLE, hpv (n + 1), XT n]
  ·
    intro n hle'
    have hκP : (⊤ : (Spec (CommRingCat.of (A n))).Opens) ≤ (κ n) ⁻¹ᵁ ((D.p n) ⁻¹ᵁ (U n)) := fun w _ => by
      show (D.p n).base ((κ n).base w) ∈ (U n : Set (D.Y n))
      rw [hU n, ← Scheme.Hom.comp_apply]
      exact ⟨w, rfl⟩
    have e1 := Scheme.Hom.appLE_comp_appLE (κ n) (D.p n) (U n) ((D.p n) ⁻¹ᵁ (U n)) ⊤ le_rfl hκP
    show (Scheme.ΓSpecIso (CommRingCat.of (A n))).hom.hom (((κ n ≫ D.p n).appLE (U n) ⊤ hle').hom
      (TQD7.secOf (U n) Bz (v n) Polynomial.X)) = fam n
    rw [← e1, CommRingCat.comp_apply, ← Scheme.Hom.app_eq_appLE, hpv n]
    have h1 := hσ n 1
    rw [TQD7.appLE_congr_hom (show κ n ≫ (a n 1).hom = κ n by rw [map_one]; exact Category.comp_id _) _ _ _ hκP] at h1
    rw [h1]
    exact Iso.inv_hom_id_apply _ _

end S_AlgebraicGeometry_TowerQuotientDatum_exists_sections_eq_of_forall_specMap_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_TowerQuotientDatum_exists_sections_eq_of_forall_specMap_comp_eq (solution)
