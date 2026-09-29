-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.nilpPoints.existsUnique_hom_comp_eq_of_natural
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/e0963f3a-e9b5-5f4c-a8be-cf5f87dc34d8

import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_nilpPoints_existsUnique_hom_comp_eq_of_natural

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld.FormalOmega Opposite

namespace NilpYonedaGlue64

universe u

section Generic

variable {R : CommRingCat.{u}} {Y : Scheme.{u}}

noncomputable def resHom (g : Y ⟶ Spec R) (U : Y.Opens) : R ⟶ Y.presheaf.obj (op U) :=
  (Scheme.ΓSpecIso R).inv ≫ g.appTop ≫ Y.presheaf.map (homOfLE le_top).op

lemma resHom_res (g : Y ⟶ Spec R) {U V : Y.Opens} (h : U ≤ V) :
    resHom g V ≫ Y.presheaf.map (homOfLE h).op = resHom g U := by
  simp only [resHom, Category.assoc, ← Functor.map_comp, ← op_comp, homOfLE_comp]

lemma resHom_comp {S : CommRingCat.{u}} (g : Y ⟶ Spec R) (φ : S ⟶ R) (U : Y.Opens) :
    resHom (g ≫ Spec.map φ) U = φ ≫ resHom g U := by
  simp only [resHom, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_inv_naturality_assoc]

lemma fromSpec_comp_eq (g : Y ⟶ Spec R) {U : Y.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ g = Spec.map (resHom g U) := by
  calc hU.fromSpec ≫ g
      = hU.fromSpec ≫ g ≫ (Spec R).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso R).inv := by
        rw [toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    _ = Spec.map (resHom g U) := by
        rw [Scheme.toSpecΓ_naturality_assoc, hU.fromSpec_toSpecΓ_assoc, resHom]
        simp only [Spec.map_comp, Category.assoc]

end Generic

section OverO

variable {𝒪 : Type} [CommRing 𝒪]

@[reducible] noncomputable def algOfOpen {Y : Scheme.{0}} (g : Y ⟶ Spec (.of 𝒪)) (U : Y.Opens) :
    Algebra 𝒪 (Y.presheaf.obj (op U)) :=
  ((resHom g U).hom : 𝒪 →+* Y.presheaf.obj (op U)).toAlgebra

lemma algebraMap_algOfOpen {Y : Scheme.{0}} (g : Y ⟶ Spec (.of 𝒪)) (U : Y.Opens) :
    @algebraMap 𝒪 (Y.presheaf.obj (op U)) _ _ (algOfOpen g U) = (resHom g U).hom := rfl

lemma specOver_algOfOpen {Y : Scheme.{0}} (g : Y ⟶ Spec (.of 𝒪)) {U : Y.Opens}
    (hU : IsAffineOpen U) :
    hU.fromSpec ≫ g = Spec.map (CommRingCat.ofHom
      (@algebraMap 𝒪 (Y.presheaf.obj (op U)) _ _ (algOfOpen g U))) :=
  fromSpec_comp_eq g hU

lemma isNilpotent_algebraMap_algOfOpen (π : 𝒪) (n : ℕ) {Y : Scheme.{0}}
    (b : Y ⟶ Spec (.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) (g : Y ⟶ Spec (.of 𝒪))
    (hb : b ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) = g)
    (U : Y.Opens) :
    IsNilpotent (@algebraMap 𝒪 (Y.presheaf.obj (op U)) _ _ (algOfOpen g U) π) := by
  subst hb
  refine ⟨n + 1, ?_⟩
  have hq : (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})) (π ^ (n + 1)) = 0 := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  rw [← map_pow, algebraMap_algOfOpen, resHom_comp, CommRingCat.hom_comp, RingHom.comp_apply,
    CommRingCat.hom_ofHom, hq, map_zero]

variable (π : 𝒪) {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of 𝒪)) {T : Scheme.{0}}
  (t : T ⟶ Spec (CommRingCat.of 𝒪))
  (u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
    (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B)
  (hu : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B')
    (y : (Scheme.nilpPoints f).obj B),
    u B' hB' ((Scheme.nilpPoints f).map φ y) = (Scheme.nilpPoints t).map φ (u B hB y))
  {X' : Scheme.{0}} (a : X' ⟶ X) (n : ℕ)
  (b : X' ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
  (hb : b ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) = a ≫ f)

include hb in

lemma chartNil (U : X'.Opens) :
    IsNilpotent (@algebraMap 𝒪 (X'.presheaf.obj (op U)) _ _ (algOfOpen (a ≫ f) U) π) :=
  isNilpotent_algebraMap_algOfOpen π n b (a ≫ f) hb U

noncomputable def tautPoint {U : X'.Opens} (hU : IsAffineOpen U) :
    @AlgFunctor.obj 𝒪 _ (Scheme.nilpPoints f) (X'.presheaf.obj (op U)) _ (algOfOpen (a ≫ f) U) :=
  letI := algOfOpen (a ≫ f) U
  ⟨hU.fromSpec ≫ a, by rw [Category.assoc]; exact specOver_algOfOpen (a ≫ f) hU⟩

noncomputable def chart {U : X'.Opens} (hU : IsAffineOpen U) : Spec (X'.presheaf.obj (op U)) ⟶ T :=
  letI := algOfOpen (a ≫ f) U
  (u _ (chartNil π f a n b hb U) (tautPoint f a hU)).1

lemma chart_comp_t {U : X'.Opens} (hU : IsAffineOpen U) :
    chart π f t u a n b hb hU ≫ t = hU.fromSpec ≫ a ≫ f := by
  letI := algOfOpen (a ≫ f) U
  have h2 := (u _ (chartNil π f a n b hb U) (tautPoint f a hU)).2
  exact h2.trans (specOver_algOfOpen (a ≫ f) hU).symm

include hu in

lemma chart_res {U V : X'.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : U ≤ V) :
    Spec.map (X'.presheaf.map (homOfLE h).op) ≫ chart π f t u a n b hb hV =
      chart π f t u a n b hb hU := by
  letI iU := algOfOpen (a ≫ f) U
  letI iV := algOfOpen (a ≫ f) V
  let ρ : (X'.presheaf.obj (op V)) →ₐ[𝒪] (X'.presheaf.obj (op U)) :=
    { (X'.presheaf.map (homOfLE h).op).hom with
      commutes' := fun r => by
        change (resHom (a ≫ f) V ≫ X'.presheaf.map (homOfLE h).op).hom r = (resHom (a ≫ f) U).hom r
        rw [resHom_res] }
  have key := hu _ _ (chartNil π f a n b hb V) (chartNil π f a n b hb U) ρ (tautPoint f a hV)
  have hpt : (Scheme.nilpPoints f).map ρ (tautPoint f a hV) = tautPoint f a hU := by
    apply Subtype.ext
    rw [Scheme.nilpPoints_map_val]
    change Spec.map (X'.presheaf.map (homOfLE h).op) ≫ hV.fromSpec ≫ a = hU.fromSpec ≫ a
    rw [IsAffineOpen.map_fromSpec_assoc hV hU]
  rw [hpt] at key
  have key' := congrArg Subtype.val key
  rw [Scheme.nilpPoints_map_val] at key'
  exact key'.symm

noncomputable def chartFamily (U : X'.directedAffineCover.I₀) : X'.directedAffineCover.X U ⟶ T :=
  U.2.isoSpec.hom ≫ chart π f t u a n b hb U.2

include hu in
lemma chartFamily_compat {U V : X'.directedAffineCover.I₀} (hUV : U ⟶ V) :
    X'.directedAffineCover.trans hUV ≫ chartFamily π f t u a n b hb V =
      chartFamily π f t u a n b hb U := by
  rw [← homOfLE_leOfHom hUV, Scheme.directedAffineCover_trans]
  change X'.homOfLE (leOfHom hUV) ≫ V.2.isoSpec.hom ≫ chart π f t u a n b hb V.2 =
    U.2.isoSpec.hom ≫ chart π f t u a n b hb U.2
  rw [IsAffineOpen.isoSpec_hom, IsAffineOpen.isoSpec_hom,
    ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc _ _ (leOfHom hUV),
    chart_res π f t u hu a n b hb U.2 V.2]

noncomputable def glued : X' ⟶ T :=
  X'.directedAffineCover.glueMorphismsOfLocallyDirected (chartFamily π f t u a n b hb)
    (chartFamily_compat π f t u hu a n b hb)

lemma ι_glued {U : X'.Opens} (hU : IsAffineOpen U) :
    U.ι ≫ glued π f t u hu a n b hb = hU.isoSpec.hom ≫ chart π f t u a n b hb hU :=
  X'.directedAffineCover.map_glueMorphismsOfLocallyDirected (chartFamily π f t u a n b hb)
    (chartFamily_compat π f t u hu a n b hb) ⟨U, hU⟩

lemma glued_comp_t : glued π f t u hu a n b hb ≫ t = a ≫ f := by
  apply X'.directedAffineCover.hom_ext
  intro U
  change U.1.ι ≫ glued π f t u hu a n b hb ≫ t = U.1.ι ≫ a ≫ f
  rw [← Category.assoc, ι_glued π f t u hu a n b hb U.2, Category.assoc, chart_comp_t, IsAffineOpen.isoSpec_hom,
    IsAffineOpen.toSpecΓ_fromSpec_assoc]

lemma comp_glued_eq (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (p : Spec (CommRingCat.of B) ⟶ X')
    (hp : p ≫ a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B))) :
    p ≫ glued π f t u hu a n b hb = (u B hB ⟨p ≫ a, hp⟩).1 := by
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨V, hV, hxV, -⟩ : ∃ V : X'.Opens, V ∈ X'.affineOpens ∧ p x ∈ V ∧ V ≤ ⊤ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top (p x))
  obtain ⟨W, hW, hxW, hWV⟩ : ∃ W : (Spec (CommRingCat.of B)).Opens,
      W ∈ (Spec (CommRingCat.of B)).affineOpens ∧ x ∈ W ∧ W ≤ p ⁻¹ᵁ V :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Spec (CommRingCat.of B)).isBasis_affineOpens
      (show x ∈ p ⁻¹ᵁ V from hxV)
  refine ⟨W, hxW, ?_⟩
  replace hV : IsAffineOpen V := hV
  replace hW : IsAffineOpen W := hW

  let ψ : CommRingCat.of B ⟶ (Spec (CommRingCat.of B)).presheaf.obj (op W) := resHom (𝟙 _) W
  have hWψ : hW.fromSpec = Spec.map ψ := by
    rw [← Category.comp_id hW.fromSpec]; exact fromSpec_comp_eq (𝟙 _) hW
  letI iC : Algebra 𝒪 ((Spec (CommRingCat.of B)).presheaf.obj (op W)) :=
    (ψ.hom.comp (algebraMap 𝒪 B)).toAlgebra
  have hC : IsNilpotent (algebraMap 𝒪 ((Spec (CommRingCat.of B)).presheaf.obj (op W)) π) :=
    hB.map ψ.hom
  let ψₐ : B →ₐ[𝒪] (Spec (CommRingCat.of B)).presheaf.obj (op W) :=
    { ψ.hom with commutes' := fun _ => rfl }
  have hpC : (hW.fromSpec ≫ p ≫ a) ≫ f =
      Scheme.specOver ((Spec (CommRingCat.of B)).presheaf.obj (op W)) := by
    simp only [Category.assoc]
    rw [hp, hWψ, Scheme.specOver, ← Spec.map_comp]
    rfl

  have E1 : (u _ hC ⟨hW.fromSpec ≫ p ≫ a, hpC⟩).1 = hW.fromSpec ≫ (u B hB ⟨p ≫ a, hp⟩).1 := by
    have key := hu B _ hB hC ψₐ ⟨p ≫ a, hp⟩
    have hpt : (Scheme.nilpPoints f).map ψₐ ⟨p ≫ a, hp⟩ = ⟨hW.fromSpec ≫ p ≫ a, hpC⟩ := by
      apply Subtype.ext
      change Spec.map ψ ≫ p ≫ a = hW.fromSpec ≫ p ≫ a
      rw [hWψ]
    rw [hpt] at key
    rw [key]
    change Spec.map ψ ≫ (u B hB ⟨p ≫ a, hp⟩).1 = hW.fromSpec ≫ (u B hB ⟨p ≫ a, hp⟩).1
    rw [hWψ]

  have hrange : Set.range (hW.fromSpec ≫ p) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Hom.comp_apply]
    apply hWV
    show hW.fromSpec y ∈ (W : Set _)
    rw [← hW.range_fromSpec]
    exact ⟨y, rfl⟩
  let q := IsOpenImmersion.lift V.ι (hW.fromSpec ≫ p) hrange
  have hq : q ≫ V.ι = hW.fromSpec ≫ p := IsOpenImmersion.lift_fac _ _ _
  letI iV := algOfOpen (a ≫ f) V
  let χ : X'.presheaf.obj (op V) ⟶ (Spec (CommRingCat.of B)).presheaf.obj (op W) :=
    Spec.preimage (q ≫ hV.isoSpec.hom)
  have hχ : Spec.map χ = q ≫ hV.isoSpec.hom := Spec.map_preimage _
  have hχalg : resHom (a ≫ f) V ≫ χ = CommRingCat.ofHom (algebraMap 𝒪 B) ≫ ψ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hχ, ← hWψ, ← hp, ← fromSpec_comp_eq (a ≫ f) hV,
      ← Category.assoc hW.fromSpec p, ← hq, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_hom,
      IsAffineOpen.toSpecΓ_fromSpec_assoc]
  let χₐ : X'.presheaf.obj (op V) →ₐ[𝒪] (Spec (CommRingCat.of B)).presheaf.obj (op W) :=
    { χ.hom with
      commutes' := fun r => by
        change (resHom (a ≫ f) V ≫ χ).hom r = (CommRingCat.ofHom (algebraMap 𝒪 B) ≫ ψ).hom r
        rw [hχalg] }

  have E2 : (u _ hC ⟨hW.fromSpec ≫ p ≫ a, hpC⟩).1 =
      hW.fromSpec ≫ p ≫ glued π f t u hu a n b hb := by
    have key := hu _ _ (chartNil π f a n b hb V) hC χₐ (tautPoint f a hV)
    have hpt : (Scheme.nilpPoints f).map χₐ (tautPoint f a hV) = ⟨hW.fromSpec ≫ p ≫ a, hpC⟩ := by
      apply Subtype.ext
      rw [Scheme.nilpPoints_map_val]
      change Spec.map χ ≫ hV.fromSpec ≫ a = hW.fromSpec ≫ p ≫ a
      rw [hχ, ← Category.assoc hW.fromSpec p, ← hq, Category.assoc, Category.assoc,
        IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec_assoc]
    rw [hpt] at key
    rw [key, Scheme.nilpPoints_map_val]
    change Spec.map χ ≫ chart π f t u a n b hb hV = hW.fromSpec ≫ p ≫ glued π f t u hu a n b hb
    rw [hχ, ← Category.assoc hW.fromSpec p, ← hq, Category.assoc, Category.assoc,
      ι_glued π f t u hu a n b hb hV]
  have key : hW.fromSpec ≫ p ≫ glued π f t u hu a n b hb = hW.fromSpec ≫ (u B hB ⟨p ≫ a, hp⟩).1 :=
    E2.symm.trans E1
  rw [← IsAffineOpen.isoSpec_inv_ι] at key
  simp only [Category.assoc] at key
  exact (cancel_epi _).mp key

include hb in

lemma uniq (s₁ s₂ : X' ⟶ T)
    (h₁ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (p : Spec (CommRingCat.of B) ⟶ X')
      (hp : p ≫ a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B))),
      p ≫ s₁ = (u B hB ⟨p ≫ a, hp⟩).1)
    (h₂ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (p : Spec (CommRingCat.of B) ⟶ X')
      (hp : p ≫ a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B))),
      p ≫ s₂ = (u B hB ⟨p ≫ a, hp⟩).1) :
    s₁ = s₂ := by
  apply X'.directedAffineCover.hom_ext
  intro U
  letI := algOfOpen (a ≫ f) U.1
  have hp : U.2.fromSpec ≫ a ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (X'.presheaf.obj (op U.1)))) :=
    specOver_algOfOpen (a ≫ f) U.2
  have e₁ := h₁ (X'.presheaf.obj (op U.1)) (chartNil π f a n b hb U.1) U.2.fromSpec hp
  have e₂ := h₂ (X'.presheaf.obj (op U.1)) (chartNil π f a n b hb U.1) U.2.fromSpec hp
  change U.1.ι ≫ s₁ = U.1.ι ≫ s₂
  rw [← IsAffineOpen.toSpecΓ_fromSpec U.2, Category.assoc, Category.assoc, e₁, e₂]

include hu hb in
theorem main : ∃! s : X' ⟶ T, s ≫ t = a ≫ f ∧
    ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (p : Spec (CommRingCat.of B) ⟶ X')
      (hp : p ≫ a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B))),
      p ≫ s = (u B hB ⟨p ≫ a, hp⟩).1 :=
  ⟨glued π f t u hu a n b hb, ⟨glued_comp_t π f t u hu a n b hb, comp_glued_eq π f t u hu a n b hb⟩,
    fun s hs => uniq π f t u a n b hb s _ hs.2 (comp_glued_eq π f t u hu a n b hb)⟩

end OverO

end NilpYonedaGlue64

theorem solution
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of 𝒪)) (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
    (u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B)
    (hu : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints f).obj B),
      u B' hB' ((Scheme.nilpPoints f).map φ y) = (Scheme.nilpPoints t).map φ (u B hB y))

    (X' : Scheme.{0}) (a : X' ⟶ X) (n : ℕ) (b : X' ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (hb : b ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) = a ≫ f) :
    ∃! s : X' ⟶ T, s ≫ t = a ≫ f ∧
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (p : Spec (CommRingCat.of B) ⟶ X')
        (hp : p ≫ a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B))),
        p ≫ s = (u B hB ⟨p ≫ a, hp⟩).1 :=
  NilpYonedaGlue64.main π f t u hu a n b hb

end S_AlgebraicGeometry_Scheme_nilpPoints_existsUnique_hom_comp_eq_of_natural
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_nilpPoints_existsUnique_hom_comp_eq_of_natural (solution)
