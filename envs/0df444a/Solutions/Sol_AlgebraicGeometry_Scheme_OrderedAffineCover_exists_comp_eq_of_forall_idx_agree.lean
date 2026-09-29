-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.OrderedAffineCover.exists_comp_eq_of_forall_idx_agree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f623f66a-f2c7-5309-b817-577818c41ade

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Theorems.Thm_AlgebraicGeometry_IsPullback_exists_iso_Spec_quotient_comp_morphismRestrict_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_comp_eq_of_forall_idx_agree

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

namespace E163G

@[reassoc]
theorem isoSpec_hom_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) :
    hU.isoSpec.hom ≫ hU.fromSpec = U.ι := by
  rw [IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec]

theorem isoSpec_hom_map {X : Scheme.{u}} {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : V ≤ U) :
    hV.isoSpec.hom ≫ Spec.map (X.presheaf.map (homOfLE h).op) = X.homOfLE h ≫ hU.isoSpec.hom := by
  rw [← cancel_mono hU.fromSpec, Category.assoc, Category.assoc, hU.map_fromSpec hV, isoSpec_hom_fromSpec,
    isoSpec_hom_fromSpec, Scheme.homOfLE_ι]

theorem isoSpec_hom_algebraMap {T' : Type u} [CommRing T'] {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of T'))
    {D : P.Opens} (hD : IsAffineOpen D) :
    letI := algebraOfHom p D
    hD.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap T' Γ(P, D))) = D.ι ≫ p := by
  letI := algebraOfHom p D
  have hφ : CommRingCat.ofHom (algebraMap T' Γ(P, D)) =
      (Scheme.ΓSpecIso (.of T')).inv ≫ p.appLE ⊤ D le_top := rfl
  rw [hφ, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top,
    IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hD le_top, IsAffineOpen.isoSpec_hom,
    IsAffineOpen.toSpecΓ_fromSpec_assoc]

@[reassoc]
theorem morphismRestrict_homOfLE {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : Y.Opens} (h : V ≤ U) :
    f ∣_ V ≫ Y.homOfLE h = X.homOfLE (f.preimage_mono h) ≫ f ∣_ U := by
  rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι, Category.assoc, morphismRestrict_ι,
    Scheme.homOfLE_ι_assoc]

section Simplices

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)

def vertex (i : K.ι) : K.Idx 0 :=
  ⟨fun _ => i, fun a b hab => by rw [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b] at hab; exact absurd hab (lt_irrefl _)⟩

theorem inter_vertex (i : K.ι) : K.inter (vertex K i) = K.U i := by
  show ⨅ _ : Fin 1, K.U i = K.U i
  exact iInf_const

def edge (i j : K.ι) (h : i < j) : K.Idx 1 :=
  ⟨![i, j], Fin.strictMono_iff_lt_succ.mpr fun k => by
    fin_cases k
    simpa using h⟩

theorem face_edge_one (i j : K.ι) (h : i < j) (t : K.Idx 0) (ht : t.1 0 = i) : K.face (edge K i j h) 1 = t := by
  apply Subtype.ext
  funext k
  rw [Fin.fin_one_eq_zero k, K.face_val, Function.comp_apply, Fin.succAbove_ne_zero_zero one_ne_zero, ht]
  rfl

theorem face_edge_zero (i j : K.ι) (h : i < j) (t : K.Idx 0) (ht : t.1 0 = j) : K.face (edge K i j h) 0 = t := by
  apply Subtype.ext
  funext k
  rw [Fin.fin_one_eq_zero k, K.face_val, Function.comp_apply, Fin.succAbove_zero_apply, ht]
  rfl

theorem le_inter_edge (i j : K.ι) (h : i < j) (t t' : K.Idx 0) (ht : t.1 0 = i) (ht' : t'.1 0 = j)
    (W : V.Opens) (hW : W ≤ K.inter t) (hW' : W ≤ K.inter t') : W ≤ K.inter (edge K i j h) := by
  show W ≤ ⨅ k, K.U ((edge K i j h).1 k)
  refine le_iInf fun k => ?_
  fin_cases k
  · show W ≤ K.U i
    rw [← ht]; exact hW.trans (K.inter_le t 0)
  · show W ≤ K.U j
    rw [← ht']; exact hW'.trans (K.inter_le t' 0)

end Simplices

end E163G

theorem solution
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {P P₀ A : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of T')) [IsSeparated p]
    (p₀ : P₀ ⟶ Spec (CommRingCat.of T)) (G : P₀ ⟶ P) (hG : IsPullback G p₀ p (Spec.map (CommRingCat.ofHom π)))
    (f : A ⟶ Spec (CommRingCat.of T')) (μ : P₀ ⟶ A)
    (𝒲 : P.OrderedAffineCover)
    (m : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ A)
    (hmμ : ∀ i, G ∣_ (𝒲.U i) ≫ m i = (G ⁻¹ᵁ (𝒲.U i)).ι ≫ μ)
    (v : ∀ t : 𝒲.Idx 0, Spec (CommRingCat.of Γ(P, 𝒲.inter t)) ⟶ A)
    (hvf : ∀ t : 𝒲.Idx 0, letI := algebraOfHom p (𝒲.inter t)
      v t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(P, 𝒲.inter t))))
    (hvm : ∀ t : 𝒲.Idx 0, letI := algebraOfHom p (𝒲.inter t)
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(P, 𝒲.inter t))))) ≫
          ((Scheme.OrderedAffineCover.isAffineOpen_inter p 𝒲 t).isoSpec.inv ≫ P.homOfLE (𝒲.inter_le t 0) ≫ m (t.1 0)) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(P, 𝒲.inter t))))) ≫ v t)
    (hagree : ∀ s : 𝒲.Idx 1, letI := algebraOfHom p (𝒲.inter s)
      letI := algebraOfHom p (𝒲.inter (𝒲.face s 0)); letI := algebraOfHom p (𝒲.inter (𝒲.face s 1))
      Spec.map (CommRingCat.ofHom (restrictAlgHom p (𝒲.inter_le_inter_face s 1)).toRingHom) ≫ v (𝒲.face s 1) =
        Spec.map (CommRingCat.ofHom (restrictAlgHom p (𝒲.inter_le_inter_face s 0)).toRingHom) ≫ v (𝒲.face s 0)) :
    ∃ m' : P ⟶ A, m' ≫ f = p ∧ G ≫ m' = μ := by
  have hW : ∀ {n : ℕ} (t : 𝒲.Idx n), IsAffineOpen (𝒲.inter t) := fun t =>
    Scheme.OrderedAffineCover.isAffineOpen_inter p 𝒲 t

  let m' : ∀ t : 𝒲.Idx 0, (↑(𝒲.inter t) : Scheme.{u}) ⟶ A := fun t => (hW t).isoSpec.hom ≫ v t
  have key : ∀ (t₁ t₂ : 𝒲.Idx 0), t₁ = t₂ → ∀ (W : P.Opens) (h₁ : W ≤ 𝒲.inter t₁) (h₂ : W ≤ 𝒲.inter t₂),
      P.homOfLE h₁ ≫ m' t₁ = P.homOfLE h₂ ≫ m' t₂ := by
    rintro t₁ _ rfl W h₁ h₂; rfl

  have hedge : ∀ s : 𝒲.Idx 1, P.homOfLE (𝒲.inter_le_inter_face s 1) ≫ m' (𝒲.face s 1) =
      P.homOfLE (𝒲.inter_le_inter_face s 0) ≫ m' (𝒲.face s 0) := by
    intro s
    have h := hagree s
    change Spec.map (P.presheaf.map (homOfLE (𝒲.inter_le_inter_face s 1)).op) ≫ v (𝒲.face s 1) =
      Spec.map (P.presheaf.map (homOfLE (𝒲.inter_le_inter_face s 0)).op) ≫ v (𝒲.face s 0) at h
    calc P.homOfLE (𝒲.inter_le_inter_face s 1) ≫ (hW _).isoSpec.hom ≫ v (𝒲.face s 1)
        = (hW s).isoSpec.hom ≫ Spec.map (P.presheaf.map (homOfLE (𝒲.inter_le_inter_face s 1)).op) ≫
            v (𝒲.face s 1) := by
          rw [← Category.assoc, ← E163G.isoSpec_hom_map (hW _) (hW s), Category.assoc]
      _ = (hW s).isoSpec.hom ≫ Spec.map (P.presheaf.map (homOfLE (𝒲.inter_le_inter_face s 0)).op) ≫
            v (𝒲.face s 0) := by rw [h]
      _ = P.homOfLE (𝒲.inter_le_inter_face s 0) ≫ (hW _).isoSpec.hom ≫ v (𝒲.face s 0) := by
          rw [← Category.assoc, E163G.isoSpec_hom_map (hW _) (hW s), Category.assoc]

  have hlt : ∀ (t t' : 𝒲.Idx 0), t.1 0 < t'.1 0 → ∀ (W : P.Opens) (h : W ≤ 𝒲.inter t) (h' : W ≤ 𝒲.inter t'),
      P.homOfLE h ≫ m' t = P.homOfLE h' ≫ m' t' := by
    intro t t' hlt W h h'
    have hWs := E163G.le_inter_edge 𝒲 _ _ hlt t t' rfl rfl W h h'
    have h1 := E163G.face_edge_one 𝒲 _ _ hlt t rfl
    have h0 := E163G.face_edge_zero 𝒲 _ _ hlt t' rfl
    rw [key t _ h1.symm W h (hWs.trans (𝒲.inter_le_inter_face _ 1)),
      key t' _ h0.symm W h' (hWs.trans (𝒲.inter_le_inter_face _ 0)),
      ← Scheme.homOfLE_homOfLE P hWs (𝒲.inter_le_inter_face _ 1), Category.assoc, hedge,
      ← Category.assoc, Scheme.homOfLE_homOfLE]
  have hagr : ∀ t t' : 𝒲.Idx 0,
      P.homOfLE (inf_le_left : 𝒲.inter t ⊓ 𝒲.inter t' ≤ 𝒲.inter t) ≫ m' t =
        P.homOfLE (inf_le_right : 𝒲.inter t ⊓ 𝒲.inter t' ≤ 𝒲.inter t') ≫ m' t' := by
    intro t t'
    rcases lt_trichotomy (t.1 0) (t'.1 0) with hl | he | hg
    · exact hlt t t' hl _ _ _
    · have : t = t' := Subtype.ext (funext fun k => by rw [Fin.fin_one_eq_zero k]; exact he)
      exact key t t' this _ _ _
    · exact (hlt t' t hg _ _ _).symm

  have hcov : ∀ x : ↥P, ∃ (t : 𝒲.Idx 0) (y : ↥(𝒲.inter t)), (𝒲.inter t).ι y = x := by
    intro x
    have hx : x ∈ (⨆ i, 𝒲.U i) := by rw [𝒲.iSup_eq_top]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    refine ⟨E163G.vertex 𝒲 i, ⟨x, ?_⟩, rfl⟩
    rw [E163G.inter_vertex]; exact hi
  let 𝒱 : P.OpenCover := Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (𝒲.Idx 0)
    (fun t => (↑(𝒲.inter t) : Scheme.{u})) (fun t => (𝒲.inter t).ι) hcov
  have hcompat : ∀ t t' : 𝒲.Idx 0,
      pullback.fst (𝒱.f t) (𝒱.f t') ≫ m' t = pullback.snd (𝒱.f t) (𝒱.f t') ≫ m' t' := by
    intro t t'
    change pullback.fst (𝒲.inter t).ι (𝒲.inter t').ι ≫ m' t = pullback.snd (𝒲.inter t).ι (𝒲.inter t').ι ≫ m' t'
    rw [← (isPullback_opens_inf (𝒲.inter t) (𝒲.inter t')).isoPullback_inv_fst,
      ← (isPullback_opens_inf (𝒲.inter t) (𝒲.inter t')).isoPullback_inv_snd, Category.assoc, Category.assoc,
      hagr]
  refine ⟨𝒱.glueMorphisms m' hcompat, ?_, ?_⟩
  · refine Scheme.Cover.hom_ext 𝒱 _ _ fun t => ?_
    rw [Scheme.Cover.ι_glueMorphisms_assoc]
    change ((hW t).isoSpec.hom ≫ v t) ≫ f = (𝒲.inter t).ι ≫ p
    rw [Category.assoc, hvf t, E163G.isoSpec_hom_algebraMap]
  · apply Scheme.hom_ext_of_forall
    intro x
    obtain ⟨t, y, hy⟩ := hcov (G x)
    refine ⟨G ⁻¹ᵁ 𝒲.inter t, ?_, ?_⟩
    · show G x ∈ 𝒲.inter t
      rw [← hy]; exact y.2
    · have hι : (𝒲.inter t).ι ≫ 𝒱.glueMorphisms m' hcompat = m' t := Scheme.Cover.ι_glueMorphisms 𝒱 m' hcompat t
      rw [← morphismRestrict_ι_assoc, hι]
      letI := algebraOfHom p (𝒲.inter t)
      obtain ⟨-, ε, hε⟩ := AlgebraicGeometry.IsPullback.exists_iso_Spec_quotient_comp_morphismRestrict_eq
        π hπ hker p p₀ G hG (𝒲.inter t) (hW t)
      rw [← cancel_epi ε.hom]
      change ε.hom ≫ G ∣_ 𝒲.inter t ≫ (hW t).isoSpec.hom ≫ v t = ε.hom ≫ (G ⁻¹ᵁ 𝒲.inter t).ι ≫ μ
      rw [reassoc_of% hε, ← hvm t, ← reassoc_of% hε, Iso.hom_inv_id_assoc, E163G.morphismRestrict_homOfLE_assoc,
        hmμ, Scheme.homOfLE_ι_assoc]

#print axioms solution

end S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_comp_eq_of_forall_idx_agree
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_comp_eq_of_forall_idx_agree (solution)
