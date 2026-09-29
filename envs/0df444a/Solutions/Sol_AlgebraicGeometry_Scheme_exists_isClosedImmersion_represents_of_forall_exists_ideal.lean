-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_isClosedImmersion_represents_of_forall_exists_ideal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/81612a90-50aa-5fb9-bfe8-fc0fe23bccd6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite

namespace ClosedRep

universe u

section Generalities

theorem section_eq_zero_of_cover {Y : Scheme.{0}} {V : Y.Opens} (s : Γ(Y, V)) {ι : Type} (U : ι → Y.Opens)
    (hU : ∀ i, U i ≤ V) (hcov : V ≤ ⨆ i, U i)
    (h : ∀ i, (Y.presheaf.map (homOfLE (hU i)).op).hom s = 0) : s = 0 := by
  refine TopCat.Sheaf.eq_of_locally_eq' Y.sheaf U V (fun i => homOfLE (hU i)) hcov s 0 fun i => ?_
  rw [map_zero]
  exact h i

variable {R : Type} [CommRing R]

theorem algebraMap_comm_of_Spec {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (ψ : A →+* B)
    (h : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B))) (r : R) :
    ψ (algebraMap R A r) = algebraMap R B r := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at h
  have := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  simp only [CommRingCat.hom_ofHom] at this
  exact RingHom.congr_fun this r

def algHomOfSpec {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (ψ : A →+* B)
    (h : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B))) : A →ₐ[R] B :=
  { ψ with commutes' := fun r => algebraMap_comm_of_Spec ψ h r }

@[scoped simp] theorem algHomOfSpec_toRingHom {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (ψ : A →+* B) (h) : (algHomOfSpec (R := R) ψ h).toRingHom = ψ := rfl

theorem algHomOfSpec_apply {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (ψ : A →+* B) (h) (x : A) : algHomOfSpec (R := R) ψ h x = ψ x := rfl

end Generalities

section Setting

variable {R : Type} [CommRing R]
  (F : ∀ (A : Type) [CommRing A] [Algebra R A], Type)
  (Fmap : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B], (A →ₐ[R] B) → F A → F B)
  {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R))
  (pt : ∀ (A : Type) [CommRing A] [Algebra R A],
    F A ≃ {g : Spec (CommRingCat.of A) ⟶ X // g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))})
  (W : ∀ (A : Type) [CommRing A] [Algebra R A], F A → Prop)

def PtNatural : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B) (s : F A),
    (pt B (Fmap A B φ s)).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt A s).1

def Closed : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra R A] (s : F A), ∃ 𝔞 : Ideal A,
    ∀ (B : Type) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B), W B (Fmap A B φ s) ↔ ∀ a ∈ 𝔞, φ a = 0

variable {F Fmap p pt W}

theorem Fmap_id (hn : PtNatural F Fmap p pt) (A : Type) [CommRing A] [Algebra R A] (s : F A) :
    Fmap A A (AlgHom.id R A) s = s := by
  apply (pt A).injective
  apply Subtype.ext
  rw [hn]
  change Spec.map (CommRingCat.ofHom (RingHom.id A)) ≫ _ = _
  rw [CommRingCat.ofHom_id]
  erw [Spec.map_id]
  exact Category.id_comp _

theorem Fmap_comp (hn : PtNatural F Fmap p pt) (A B C : Type) [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) (s : F A) :
    Fmap B C ψ (Fmap A B φ s) = Fmap A C (ψ.comp φ) s := by
  apply (pt C).injective
  apply Subtype.ext
  rw [hn, hn, hn, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem eq_of_pt_eq (A : Type) [CommRing A] [Algebra R A] (s t : F A) (h : (pt A s).1 = (pt A t).1) : s = t :=
  (pt A).injective (Subtype.ext h)

noncomputable def cl (hc : Closed F Fmap W) (A : Type) [CommRing A] [Algebra R A] (s : F A) : Ideal A :=
  (hc A s).choose

theorem cl_spec (hc : Closed F Fmap W) (A : Type) [CommRing A] [Algebra R A] (s : F A)
    (B : Type) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) :
    W B (Fmap A B φ s) ↔ ∀ a ∈ cl hc A s, φ a = 0 :=
  (hc A s).choose_spec B φ

theorem ideal_unique (A : Type) [CommRing A] [Algebra R A] (𝔞 𝔟 : Ideal A)
    (P : ∀ (B : Type) [CommRing B] [Algebra R B], (A →ₐ[R] B) → Prop)
    (h𝔞 : ∀ (B : Type) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B), P B φ ↔ ∀ a ∈ 𝔞, φ a = 0)
    (h𝔟 : ∀ (B : Type) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B), P B φ ↔ ∀ a ∈ 𝔟, φ a = 0) :
    𝔞 = 𝔟 := by
  have key : ∀ (𝔞 𝔟 : Ideal A),
      (∀ (B : Type) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B), P B φ ↔ ∀ a ∈ 𝔞, φ a = 0) →
      (∀ (B : Type) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B), P B φ ↔ ∀ a ∈ 𝔟, φ a = 0) → 𝔞 ≤ 𝔟 := by
    intro 𝔞 𝔟 h𝔞 h𝔟 a ha
    have h1 : ∀ b ∈ 𝔟, Ideal.Quotient.mkₐ R 𝔟 b = 0 := fun b hb =>
      (Ideal.Quotient.eq_zero_iff_mem).mpr hb
    have h2 := ((h𝔞 (A ⧸ 𝔟) (Ideal.Quotient.mkₐ R 𝔟)).mp ((h𝔟 (A ⧸ 𝔟) (Ideal.Quotient.mkₐ R 𝔟)).mpr h1)) a ha
    exact Ideal.Quotient.eq_zero_iff_mem.mp h2
  exact le_antisymm (key 𝔞 𝔟 h𝔞 h𝔟) (key 𝔟 𝔞 h𝔟 h𝔞)

theorem W_iff_cl_eq_bot (hn : PtNatural F Fmap p pt) (hc : Closed F Fmap W) (A : Type) [CommRing A]
    [Algebra R A] (s : F A) : W A s ↔ cl hc A s = ⊥ := by
  have h := cl_spec hc A s A (AlgHom.id R A)
  rw [Fmap_id hn] at h
  rw [h, Submodule.eq_bot_iff]
  rfl

theorem cl_map (hn : PtNatural F Fmap p pt) (hc : Closed F Fmap W) (A B : Type) [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B) (s : F A) :
    cl hc B (Fmap A B φ s) = (cl hc A s).map φ.toRingHom := by
  refine ideal_unique B _ _ (fun C _ _ ψ => W C (Fmap B C ψ (Fmap A B φ s))) (fun C _ _ ψ => cl_spec hc B _ C ψ)
    fun C _ _ ψ => ?_
  rw [Fmap_comp hn, cl_spec hc A s C (ψ.comp φ)]
  constructor
  · intro h b hb
    have : (cl hc A s).map φ.toRingHom ≤ RingHom.ker ψ.toRingHom := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      exact h a ha
    exact this hb
  · intro h a ha
    exact h _ (Ideal.mem_map_of_mem φ.toRingHom ha)

end Setting

section Charts

variable {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R))

noncomputable def ρ (U : X.affineOpens) : CommRingCat.of R ⟶ Γ(X, U) :=
  Spec.preimage (U.2.fromSpec ≫ p)

@[reducible] noncomputable def algU (U : X.affineOpens) : Algebra R Γ(X, U) := (ρ p U).hom.toAlgebra

theorem fromSpec_over (U : X.affineOpens) :
    letI := algU p U
    U.2.fromSpec ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) := by
  change _ = Spec.map (ρ p U)
  rw [ρ, Spec.map_preimage]

noncomputable abbrev Da (A : Type) [CommRing A] (a : A) : (Spec (CommRingCat.of A)).Opens :=
  (Spec (CommRingCat.of A)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)

theorem isAffineOpen_Da (A : Type) [CommRing A] (a : A) : IsAffineOpen (Da A a) :=
  (isAffineOpen_top (Spec (CommRingCat.of A))).basicOpen _

noncomputable def θ' (A : Type) [CommRing A] (a : A) : CommRingCat.of A ⟶ Γ(Spec (CommRingCat.of A), Da A a) :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (Spec (CommRingCat.of A)).presheaf.map (homOfLE le_top).op

theorem θ'_apply (A : Type) [CommRing A] (a : A) (x : A) :
    (θ' A a).hom x = ((Spec (CommRingCat.of A)).presheaf.map (homOfLE le_top).op).hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom x) := rfl

@[reducible] noncomputable def algL (A : Type) [CommRing A] [Algebra R A] (a : A) :
    Algebra R Γ(Spec (CommRingCat.of A), Da A a) :=
  ((θ' A a).hom.comp (algebraMap R A)).toAlgebra

noncomputable def θ (A : Type) [CommRing A] [Algebra R A] (a : A) :
    letI := algL (R := R) A a
    A →ₐ[R] Γ(Spec (CommRingCat.of A), Da A a) :=
  letI := algL (R := R) A a
  { (θ' A a).hom with commutes' := fun _ => rfl }

theorem fromSpec_Da (A : Type) [CommRing A] (a : A) : (isAffineOpen_Da A a).fromSpec = Spec.map (θ' A a) := by
  rw [← IsAffineOpen.map_fromSpec (isAffineOpen_top _) (isAffineOpen_Da A a) (homOfLE le_top).op,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

end Charts

section Sheaf

variable {R : Type} [CommRing R]
  {F : ∀ (A : Type) [CommRing A] [Algebra R A], Type}
  {Fmap : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B], (A →ₐ[R] B) → F A → F B}
  {X : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of R)}
  {pt : ∀ (A : Type) [CommRing A] [Algebra R A],
    F A ≃ {g : Spec (CommRingCat.of A) ⟶ X // g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))}}
  {W : ∀ (A : Type) [CommRing A] [Algebra R A], F A → Prop}
  (hn : PtNatural F Fmap p pt) (hc : Closed F Fmap W)

variable (pt) in

noncomputable def sU (U : X.affineOpens) : letI := algU p U; F Γ(X, U) :=
  letI := algU p U
  (pt Γ(X, U)).symm ⟨U.2.fromSpec, fromSpec_over p U⟩

theorem pt_sU (U : X.affineOpens) : letI := algU p U; (pt Γ(X, U) (sU pt U)).1 = U.2.fromSpec := by
  letI := algU p U
  change (pt Γ(X, U) ((pt Γ(X, U)).symm _)).1 = _
  rw [Equiv.apply_symm_apply]

variable (p) in

noncomputable def resAlg (U V : X.affineOpens) (h : V.1 ≤ U.1) :
    letI := algU p U; letI := algU p V; Γ(X, U) →ₐ[R] Γ(X, V) :=
  letI := algU p U; letI := algU p V
  algHomOfSpec (X.presheaf.map (homOfLE h).op).hom (by
    change Spec.map (X.presheaf.map (homOfLE h).op) ≫ Spec.map (ρ p U) = Spec.map (ρ p V)
    rw [ρ, ρ, Spec.map_preimage, Spec.map_preimage, ← Category.assoc, IsAffineOpen.map_fromSpec U.2 V.2])

include hn in
theorem Fmap_resAlg_sU (U V : X.affineOpens) (h : V.1 ≤ U.1) :
    letI := algU p U; letI := algU p V
    Fmap Γ(X, U) Γ(X, V) (resAlg p U V h) (sU pt U) = sU pt V := by
  letI := algU p U; letI := algU p V
  apply eq_of_pt_eq (pt := pt)
  rw [hn, pt_sU, pt_sU]
  exact IsAffineOpen.map_fromSpec U.2 V.2 (homOfLE h).op

noncomputable def J : X.IdealSheafData where
  ideal U := letI := algU p U; cl hc Γ(X, U) (sU pt U)
  map_ideal_basicOpen U f := by
    letI := algU p U; letI := algU p (X.affineBasicOpen f)
    have h := cl_map hn hc Γ(X, U) Γ(X, X.affineBasicOpen f)
      (resAlg p U (X.affineBasicOpen f) (X.basicOpen_le f)) (sU pt U)
    rw [Fmap_resAlg_sU hn] at h
    exact h.symm

section Key

variable (A : Type) [CommRing A] [Algebra R A] (s : F A)

include hn in

theorem local_iff (U : X.affineOpens) (a : A) (ha : Da A a ≤ (pt A s).1 ⁻¹ᵁ U.1) :
    letI := algU p U
    (∀ x ∈ cl hc Γ(X, U) (sU pt U), ((pt A s).1.appLE U.1 (Da A a) ha).hom x = 0) ↔
      ∀ x ∈ cl hc A s, (θ' A a).hom x = 0 := by
  letI := algU p U; letI := algL (R := R) A a
  let g := (pt A s).1
  have hg : g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A)) := (pt A s).2
  let ψ' : Γ(X, U.1) ⟶ Γ(Spec (CommRingCat.of A), Da A a) := g.appLE U.1 (Da A a) ha
  have hP1 : Spec.map ψ' ≫ U.2.fromSpec = (isAffineOpen_Da A a).fromSpec ≫ g :=
    IsAffineOpen.SpecMap_appLE_fromSpec g U.2 (isAffineOpen_Da A a) ha

  let ψ : Γ(X, U) →ₐ[R] Γ(Spec (CommRingCat.of A), Da A a) := algHomOfSpec ψ'.hom (by
    change Spec.map ψ' ≫ Spec.map (ρ p U) = Spec.map (CommRingCat.ofHom ((θ' A a).hom.comp (algebraMap R A)))
    rw [ρ, Spec.map_preimage, ← Category.assoc, hP1, Category.assoc, hg, fromSpec_Da, ← Spec.map_comp,
      CommRingCat.ofHom_comp, CommRingCat.ofHom_hom])

  have hP2 : Fmap Γ(X, U) Γ(Spec (CommRingCat.of A), Da A a) ψ (sU pt U) =
      Fmap A Γ(Spec (CommRingCat.of A), Da A a) (θ (R := R) A a) s := by
    apply eq_of_pt_eq (pt := pt)
    rw [hn, hn, pt_sU]
    change Spec.map ψ' ≫ U.2.fromSpec = Spec.map (θ' A a) ≫ (pt A s).1
    rw [hP1, fromSpec_Da]
  have h1 := cl_spec hc Γ(X, U) (sU pt U) Γ(Spec (CommRingCat.of A), Da A a) ψ
  have h2 := cl_spec hc A s Γ(Spec (CommRingCat.of A), Da A a) (θ (R := R) A a)
  rw [hP2, h2] at h1
  exact h1.symm

theorem preimage_le_iSup (g : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) :
    g ⁻¹ᵁ U ≤ ⨆ a : {a : A // Da A a ≤ g ⁻¹ᵁ U}, Da A a.1 := by
  intro q hq
  obtain ⟨f, hf, hqf⟩ := (isAffineOpen_top (Spec (CommRingCat.of A))).exists_basicOpen_le ⟨q, hq⟩ trivial
  let a : A := (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom f
  have ha : (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a = f := by
    change ((Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).inv).hom f = f
    rw [Iso.hom_inv_id]; rfl
  have hDa : Da A a = (Spec (CommRingCat.of A)).basicOpen f := by rw [Da, ha]
  have h1 : Da A a ≤ g ⁻¹ᵁ U := by rw [hDa]; exact hf
  have h2 : q ∈ Da A a := by rw [hDa]; exact hqf
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨a, h1⟩, h2⟩

include hn in

theorem J_le_ker_iff : J hn hc ≤ (pt A s).1.ker ↔ W A s := by
  let g := (pt A s).1
  rw [Scheme.Hom.ker, Scheme.IdealSheafData.le_ofIdeals_iff, W_iff_cl_eq_bot hn hc]
  constructor
  ·
    intro hJ
    rw [Submodule.eq_bot_iff]
    intro x hx
    let e := Scheme.ΓSpecIso (CommRingCat.of A)
    suffices h : e.inv.hom x = 0 by
      have := congrArg e.hom.hom h
      rw [map_zero] at this
      rw [← this]
      change x = (e.inv ≫ e.hom).hom x
      rw [Iso.inv_hom_id]; rfl
    let ι := Σ' (U : X.affineOpens), {a : A // Da A a ≤ g ⁻¹ᵁ U.1}
    refine section_eq_zero_of_cover (e.inv.hom x) (fun i : ι => Da A i.2.1) (fun _ => le_top) ?_ ?_
    · intro q _
      obtain ⟨_, ⟨U, hU, rfl⟩, hqU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g q)) isOpen_univ
      have hq : q ∈ g ⁻¹ᵁ U := hqU
      have := preimage_le_iSup A g U hq
      obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp this
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, a⟩, ha⟩
    · rintro ⟨U, a, ha⟩
      have hloc := (local_iff hn hc A s U a ha).mp (fun y hy => by
        have hy0 : (g.app U.1).hom y = 0 := hJ U hy
        change (g.app U.1 ≫ (Spec (CommRingCat.of A)).presheaf.map (homOfLE ha).op).hom y = 0
        rw [CommRingCat.hom_comp, RingHom.comp_apply, hy0, map_zero]) x hx
      exact hloc
  ·
    intro hs U x hx
    rw [RingHom.mem_ker]
    refine section_eq_zero_of_cover _ (fun a : {a : A // Da A a ≤ g ⁻¹ᵁ U.1} => Da A a.1) (fun a => a.2)
      (preimage_le_iSup A g U.1) fun a => ?_
    have hloc := (local_iff hn hc A s U a.1 a.2).mpr (fun y hy => by
      rw [hs] at hy
      rw [(Submodule.mem_bot A).mp hy, map_zero]) x hx
    exact hloc

end Key

end Sheaf

theorem main (R : Type) [CommRing R]
    (F : ∀ (A : Type) [CommRing A] [Algebra R A], Type)
    (Fmap : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B],
      (A →ₐ[R] B) → F A → F B)
    (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R))
    (pt : ∀ (A : Type) [CommRing A] [Algebra R A],
      F A ≃ {g : Spec (CommRingCat.of A) ⟶ X // g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))})
    (pt_natural : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
      (φ : A →ₐ[R] B) (s : F A),
      (pt B (Fmap A B φ s)).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt A s).1)
    (W : ∀ (A : Type) [CommRing A] [Algebra R A], F A → Prop)
    (closed : ∀ (A : Type) [CommRing A] [Algebra R A] (s : F A), ∃ 𝔞 : Ideal A,
      ∀ (B : Type) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B),
        W B (Fmap A B φ s) ↔ ∀ a ∈ 𝔞, φ a = 0) :
    ∃ (Z : Scheme.{0}) (ι : Z ⟶ X)
      (ptZ : ∀ (A : Type) [CommRing A] [Algebra R A],
        {s : F A // W A s} ≃
          {g : Spec (CommRingCat.of A) ⟶ Z //
            g ≫ ι ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))}),
      IsClosedImmersion ι ∧
      ∀ (A : Type) [CommRing A] [Algebra R A] (s : {s : F A // W A s}),
        (ptZ A s).1 ≫ ι = (pt A s.1).1 := by
  have hn : PtNatural F Fmap p pt := pt_natural
  have hc : Closed F Fmap W := closed
  let 𝒥 : X.IdealSheafData := J hn hc
  let Z := 𝒥.subscheme
  let ι := 𝒥.subschemeι
  have hker : ι.ker = 𝒥 := 𝒥.ker_subschemeι
  have key : ∀ (A : Type) [CommRing A] [Algebra R A] (s : F A), ι.ker ≤ (pt A s).1.ker ↔ W A s := by
    intro A _ _ s
    rw [hker]
    exact J_le_ker_iff hn hc A s
  let fwd : ∀ (A : Type) [CommRing A] [Algebra R A], {s : F A // W A s} →
      {g : Spec (CommRingCat.of A) ⟶ Z // g ≫ ι ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))} :=
    fun A _ _ s => ⟨IsClosedImmersion.lift ι (pt A s.1).1 ((key A s.1).mpr s.2), by
      rw [← Category.assoc, IsClosedImmersion.lift_fac]; exact (pt A s.1).2⟩
  have bwdW : ∀ (A : Type) [CommRing A] [Algebra R A]
      (g : {g : Spec (CommRingCat.of A) ⟶ Z // g ≫ ι ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))}),
      W A ((pt A).symm ⟨g.1 ≫ ι, by rw [Category.assoc]; exact g.2⟩) := by
    intro A _ _ g
    rw [← key, Equiv.apply_symm_apply]
    exact Scheme.Hom.le_ker_comp _ _
  let bwd : ∀ (A : Type) [CommRing A] [Algebra R A],
      {g : Spec (CommRingCat.of A) ⟶ Z // g ≫ ι ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))} →
      {s : F A // W A s} :=
    fun A _ _ g => ⟨(pt A).symm ⟨g.1 ≫ ι, by rw [Category.assoc]; exact g.2⟩, bwdW A g⟩
  refine ⟨Z, ι, fun A _ _ => { toFun := fwd A, invFun := bwd A, left_inv := ?_, right_inv := ?_ },
    inferInstance, ?_⟩
  · intro s
    apply Subtype.ext
    change (pt A).symm _ = s.1
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    exact IsClosedImmersion.lift_fac _ _ _
  · intro g
    apply Subtype.ext
    change IsClosedImmersion.lift ι _ _ = g.1
    rw [← cancel_mono ι, IsClosedImmersion.lift_fac, Equiv.apply_symm_apply]
  · intro A _ _ s
    exact IsClosedImmersion.lift_fac _ _ _

end ClosedRep
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal.ClosedRep"

theorem solution
    (R : Type) [CommRing R]
    (F : ∀ (A : Type) [CommRing A] [Algebra R A], Type)
    (Fmap : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B],
      (A →ₐ[R] B) → F A → F B)
    (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R))
    (pt : ∀ (A : Type) [CommRing A] [Algebra R A],
      F A ≃ {g : Spec (CommRingCat.of A) ⟶ X // g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))})
    (pt_natural : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
      (φ : A →ₐ[R] B) (s : F A),
      (pt B (Fmap A B φ s)).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt A s).1)
    (W : ∀ (A : Type) [CommRing A] [Algebra R A], F A → Prop)
    (closed : ∀ (A : Type) [CommRing A] [Algebra R A] (s : F A), ∃ 𝔞 : Ideal A,
      ∀ (B : Type) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B),
        W B (Fmap A B φ s) ↔ ∀ a ∈ 𝔞, φ a = 0) :
    ∃ (Z : Scheme.{0}) (ι : Z ⟶ X)
      (ptZ : ∀ (A : Type) [CommRing A] [Algebra R A],
        {s : F A // W A s} ≃
          {g : Spec (CommRingCat.of A) ⟶ Z //
            g ≫ ι ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))}),
      IsClosedImmersion ι ∧
      ∀ (A : Type) [CommRing A] [Algebra R A] (s : {s : F A // W A s}),
        (ptZ A s).1 ≫ ι = (pt A s.1).1 :=
  ClosedRep.main R F Fmap X p pt pt_natural W closed

end S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal (solution)
