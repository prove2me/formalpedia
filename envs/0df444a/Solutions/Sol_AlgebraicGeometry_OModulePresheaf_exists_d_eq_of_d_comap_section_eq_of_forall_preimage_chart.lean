-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_d_eq_of_d_comap_section_eq_of_forall_preimage_chart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/b5e9a3aa-5b21-597f-877b-4d384a0f1ac3

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_rows_exact
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_dV_comp_biAug
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_of_d_comap_section_eq_of_forall_preimage_chart

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace C1Body

section Res
variable {P : Scheme.{u}}

theorem res_res {U V W : P.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (x : Γ(P, U)) :
    (P.presheaf.map (homOfLE h₁).op).hom ((P.presheaf.map (homOfLE h₂).op).hom x)
      = (P.presheaf.map (homOfLE (h₁.trans h₂)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

theorem res_self {U : P.Opens} (h : U ≤ U) (x : Γ(P, U)) :
    (P.presheaf.map (homOfLE h).op).hom x = x := by
  rw [Subsingleton.elim (homOfLE h).op (𝟙 (op U)), P.presheaf.map_id]; rfl

theorem res_res_self {U V : P.Opens} (h₁ : U ≤ V) (h₂ : V ≤ U) (x : Γ(P, U)) :
    (P.presheaf.map (homOfLE h₁).op).hom ((P.presheaf.map (homOfLE h₂).op).hom x) = x := by
  rw [res_res, res_self]

theorem res_app {X : Scheme.{u}} (s : X ⟶ P) {U V : P.Opens} (h : V ≤ U) (x : Γ(P, U)) :
    (s.app V).hom ((P.presheaf.map (homOfLE h).op).hom x)
      = (X.presheaf.map (homOfLE (s.preimage_mono h)).op).hom ((s.app U).hom x) := by
  have := congrArg (fun φ => φ.hom x) (s.naturality (homOfLE h).op)
  simpa using this

theorem res_appLE {X : Scheme.{u}} (p : P ⟶ X) {U : X.Opens} {V W : P.Opens} (e : V ≤ p ⁻¹ᵁ U)
    (h : W ≤ V) (y : Γ(X, U)) :
    (P.presheaf.map (homOfLE h).op).hom ((p.appLE U V e).hom y) = (p.appLE U W (h.trans e)).hom y := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_res {X : Scheme.{u}} (p : P ⟶ X) {U U' : X.Opens} {V : P.Opens} (e : V ≤ p ⁻¹ᵁ U)
    (h : U ≤ U') (y : Γ(X, U')) :
    (p.appLE U V e).hom ((X.presheaf.map (homOfLE h).op).hom y)
      = (p.appLE U' V (e.trans (p.preimage_mono h))).hom y := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

end Res

end C1Body

namespace C1Body

section ResAny
variable {P : Scheme.{u}}
theorem res_any {U W : P.Opens} (i : op U ⟶ op W) (h : W ≤ U) (x : Γ(P, U)) :
    (P.presheaf.map i).hom x = (P.presheaf.map (homOfLE h).op).hom x := by
  rw [Subsingleton.elim i (homOfLE h).op]

theorem appLE_of_eq_id {X : Scheme.{u}} (f : X ⟶ X) (hf : f = 𝟙 X) {U V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (h : V ≤ U) (y : Γ(X, U)) :
    (f.appLE U V e).hom y = (X.presheaf.map (homOfLE h).op).hom y := by
  subst hf
  rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
  change (X.presheaf.map (homOfLE e).op).hom ((𝟙 Γ(X, U) : Γ(X, U) ⟶ Γ(X, U)).hom y) = _
  rw [CommRingCat.id_apply]
  exact res_any _ h y
end ResAny

open AlgebraicGeometry.OModulePresheaf.Leray

section Main

variable {R : Type u} [CommRing R] {X P : Scheme.{u}}
  (πX : X ⟶ Spec (CommRingCat.of R)) (p : P ⟶ X) (s : X ⟶ P) [IsAffineHom s]
  (𝒲 : P.OrderedAffineCover)

theorem pre_pre (hs : s ≫ p = 𝟙 X) (V : X.Opens) : s ⁻¹ᵁ (p ⁻¹ᵁ V) = V := by
  rw [← Scheme.Hom.comp_preimage, hs]; rfl

abbrev XO {a b : ℕ} (σ : (𝒲.comap s).Idx a) (τ : (𝒲.comap s).Idx b) : X.Opens :=
  (𝒲.comap s).inter τ ⊓ s ⁻¹ᵁ (p ⁻¹ᵁ ((𝒲.comap s).inter σ))

theorem XO_le {a b : ℕ} (σ : (𝒲.comap s).Idx a) (τ : (𝒲.comap s).Idx b) :
    XO p s 𝒲 σ τ ≤ s ⁻¹ᵁ (biOpen p (𝒲.comap s) 𝒲 a b σ τ) :=
  inf_le_inf_right _ (𝒲.comap_inter_le s τ)

noncomputable def pull {a b : ℕ} (σ : (𝒲.comap s).Idx a) (τ : (𝒲.comap s).Idx b)
    (x : Γ(P, biOpen p (𝒲.comap s) 𝒲 a b σ τ)) : Γ(X, XO p s 𝒲 σ τ) :=
  (s.appLE (biOpen p (𝒲.comap s) 𝒲 a b σ τ) (XO p s 𝒲 σ τ) (XO_le p s 𝒲 σ τ)).hom x

theorem pull_res {a b a' b' : ℕ} (σ : (𝒲.comap s).Idx a) (τ : (𝒲.comap s).Idx b)
    (σ' : (𝒲.comap s).Idx a') (τ' : (𝒲.comap s).Idx b')
    (h : biOpen p (𝒲.comap s) 𝒲 a' b' σ' τ' ≤ biOpen p (𝒲.comap s) 𝒲 a b σ τ)
    (h' : XO p s 𝒲 σ' τ' ≤ XO p s 𝒲 σ τ)
    (x : Γ(P, biOpen p (𝒲.comap s) 𝒲 a b σ τ)) :
    pull p s 𝒲 σ' τ' ((P.presheaf.map (homOfLE h).op).hom x)
      = (X.presheaf.map (homOfLE h').op).hom (pull p s 𝒲 σ τ x) := by
  unfold pull
  rw [appLE_res, res_appLE]

theorem pull_sum {a b : ℕ} (σ : (𝒲.comap s).Idx a) (τ : (𝒲.comap s).Idx b) {ι : Type*} (t : Finset ι)
    (f : ι → Γ(P, biOpen p (𝒲.comap s) 𝒲 a b σ τ)) (n : ι → ℤ) :
    pull p s 𝒲 σ τ (∑ j ∈ t, n j • f j) = ∑ j ∈ t, n j • pull p s 𝒲 σ τ (f j) := by
  unfold pull; simp only [map_sum, map_zsmul]

theorem pull_sub {a b : ℕ} (σ : (𝒲.comap s).Idx a) (τ : (𝒲.comap s).Idx b)
    (x y : Γ(P, biOpen p (𝒲.comap s) 𝒲 a b σ τ)) :
    pull p s 𝒲 σ τ (x - y) = pull p s 𝒲 σ τ x - pull p s 𝒲 σ τ y := by
  unfold pull; simp only [map_sub]

theorem pull_appLE (hs : s ≫ p = 𝟙 X) {a b : ℕ} (σ : (𝒲.comap s).Idx a) (τ : (𝒲.comap s).Idx b)
    (y : Γ(X, (𝒲.comap s).inter σ)) (h : XO p s 𝒲 σ τ ≤ (𝒲.comap s).inter σ) :
    pull p s 𝒲 σ τ ((p.appLE ((𝒲.comap s).inter σ) (biOpen p (𝒲.comap s) 𝒲 a b σ τ) inf_le_right).hom y)
      = (X.presheaf.map (homOfLE h).op).hom y := by
  unfold pull
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  exact appLE_of_eq_id _ hs _ h y

end Main

end C1Body

namespace C1Body
open AlgebraicGeometry.OModulePresheaf.Leray

section MainC

variable {R : Type u} [CommRing R] {X P : Scheme.{u}}
  (πX : X ⟶ Spec (CommRingCat.of R)) (p : P ⟶ X) (s : X ⟶ P) [IsAffineHom s]
  (𝒲 : P.OrderedAffineCover)

local notation "𝒦" => (Scheme.OrderedAffineCover.comap 𝒲 s)

omit πX p s 𝒲 in
theorem alt_two {M : Type*} [AddCommGroup M] (x : M) :
    ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) • x = 0 := by
  show ∑ j : Fin 2, ((-1 : ℤ) ^ (j : ℕ)) • x = 0
  rw [Fin.sum_univ_two]; simp

noncomputable def ΘP {a b : ℕ} (y : ∀ σ : (𝒦).Idx a, Γ(X, (𝒦).inter σ)) : biC p πX 𝒦 𝒲 a b :=
  fun στ => (p.appLE ((𝒦).inter στ.1) (biOpen p 𝒦 𝒲 a b στ.1 στ.2) inf_le_right).hom (y στ.1)

theorem ΘP_apply {a b : ℕ} (y : ∀ σ : (𝒦).Idx a, Γ(X, (𝒦).inter σ)) (στ : BiIdx 𝒦 𝒲 a b) :
    ΘP πX p s 𝒲 y στ = (p.appLE ((𝒦).inter στ.1) (biOpen p 𝒦 𝒲 a b στ.1 στ.2) inf_le_right).hom (y στ.1) :=
  rfl

theorem dV_ΘP {a : ℕ} (y : ∀ σ : (𝒦).Idx a, Γ(X, (𝒦).inter σ)) :
    dV p πX 𝒦 𝒲 a 0 (ΘP πX p s 𝒲 y) = 0 := by
  funext στ
  rw [dV_apply', Pi.zero_apply]
  have : ∀ j : Fin (0 + 2),
      (P.presheaf.map (homOfLE (inf_le_inf_right ((Opens.map p.base).obj ((𝒦).inter στ.1))
        (𝒲.inter_le_inter_face στ.2 j))).op).hom (ΘP πX p s 𝒲 y (στ.1, 𝒲.face στ.2 j))
        = (p.appLE ((𝒦).inter στ.1) (biOpen p 𝒦 𝒲 a 1 στ.1 στ.2) inf_le_right).hom (y στ.1) := by
    intro j
    rw [ΘP_apply, res_appLE]
  simp only [this]
  exact alt_two _

noncomputable def dK {a : ℕ} (y : ∀ σ : (𝒦).Idx a, Γ(X, (𝒦).inter σ)) (σ : (𝒦).Idx (a + 1)) :
    Γ(X, (𝒦).inter σ) :=
  ∑ j : Fin (a + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    (X.presheaf.map (homOfLE ((𝒦).inter_le_inter_face σ j)).op).hom (y ((𝒦).face σ j))

theorem dH_ΘP {a b : ℕ} (y : ∀ σ : (𝒦).Idx a, Γ(X, (𝒦).inter σ)) (στ : BiIdx 𝒦 𝒲 (a + 1) b) :
    dH p πX 𝒦 𝒲 a b (ΘP πX p s 𝒲 y) στ
      = (p.appLE ((𝒦).inter στ.1) (biOpen p 𝒦 𝒲 (a + 1) b στ.1 στ.2) inf_le_right).hom
          (dK s 𝒲 y στ.1) := by
  rw [dH_apply', dK, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, ΘP_apply, res_appLE, appLE_res]

noncomputable def β0 (βi : ∀ i : 𝒲.ι, ∀ t : 𝒲.Idx 0, Γ(P, 𝒲.inter t ⊓ p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i))) :
    biC p πX 𝒦 𝒲 0 0 :=
  fun στ => (P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter στ.2)
      (p.preimage_mono ((𝒦).inter_le στ.1 0)))).op).hom (βi (στ.1.1 0) στ.2)

theorem β0_apply (βi : ∀ i : 𝒲.ι, ∀ t : 𝒲.Idx 0, Γ(P, 𝒲.inter t ⊓ p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i)))
    (στ : BiIdx 𝒦 𝒲 0 0) :
    β0 πX p s 𝒲 βi στ = (P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter στ.2)
      (p.preimage_mono ((𝒦).inter_le στ.1 0)))).op).hom (βi (στ.1.1 0) στ.2) :=
  rfl

theorem dV_β0 (c : (OModulePresheaf.unit (p ≫ πX)).cochain 𝒲 1)
    (βi : ∀ i : 𝒲.ι, ∀ t : 𝒲.Idx 0, Γ(P, 𝒲.inter t ⊓ p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i)))
    (hβi : ∀ i : 𝒲.ι, ∀ t : 𝒲.Idx (0 + 1),
        (P.presheaf.map (homOfLE (inf_le_left :
            𝒲.inter t ⊓ p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i) ≤ 𝒲.inter t)).op).hom (c t)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_right (p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i))
                (𝒲.inter_le_inter_face t j))).op).hom (βi i (𝒲.face t j))) :
    dV p πX 𝒦 𝒲 0 0 (β0 πX p s 𝒲 βi) = biAug p πX 𝒦 𝒲 1 c := by
  funext στ
  obtain ⟨σ, τ⟩ := στ
  rw [dV_apply', biAug_apply]
  have hle : biOpen p 𝒦 𝒲 0 1 σ τ ≤ 𝒲.inter τ ⊓ p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U (σ.1 0)) :=
    inf_le_inf_left _ (p.preimage_mono ((𝒦).inter_le σ 0))
  rw [show (P.presheaf.map (homOfLE (inf_le_left : biOpen p 𝒦 𝒲 0 1 σ τ ≤ 𝒲.inter τ)).op).hom (c τ)
      = (P.presheaf.map (homOfLE hle).op).hom ((P.presheaf.map (homOfLE (inf_le_left :
            𝒲.inter τ ⊓ p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U (σ.1 0)) ≤ 𝒲.inter τ)).op).hom (c τ)) from (res_res _ _ _).symm,
    hβi (σ.1 0) τ, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, β0_apply, res_res, res_res]
  rfl

theorem appLE_apply' {U : X.Opens} {V : P.Opens} (e : V ≤ p ⁻¹ᵁ U) (y : Γ(X, U)) :
    (p.appLE U V e).hom y = (P.presheaf.map (homOfLE e).op).hom ((p.app U).hom y) := rfl

omit πX p s 𝒲 in

theorem relAug_eq_zero {V' Z : Scheme.{u}} (q : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R))
    (K' : V'.OrderedAffineCover)
    (φ : OModulePresheaf.Hom (relHPresheaf q πZ K' 0) (pullOpen q πZ (⊤ : V'.Opens)))
    (hbij : ∀ U : Z.Opens, Function.Bijective (φ.app U))
    (haug : ∀ (U : Z.Opens) (x : LinearMap.ker (relAltd q πZ K' U 0)),
        relAug q πZ K' U (φ.app U (Submodule.Quotient.mk x)) = x.1)
    (U : Z.Opens) (w : (pullOpen q πZ (⊤ : V'.Opens)).obj U) (h : relAug q πZ K' U w = 0) :
    w = 0 := by
  obtain ⟨y, rfl⟩ := (hbij U).2 w
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hx : x.1 = 0 := by rw [← haug U x]; exact h
  have : x = 0 := Subtype.ext hx
  rw [this, Submodule.Quotient.mk_zero]; exact map_zero _

noncomputable def BX (bs : (OModulePresheaf.unit πX).cochain 𝒦 0) (σ : (𝒦).Idx 0) :
    relAltC s (p ≫ πX) 𝒦 (p ⁻¹ᵁ ((𝒦).inter σ)) 0 :=
  fun τ => (X.presheaf.map (homOfLE (inf_le_left : XO p s 𝒲 σ τ ≤ (𝒦).inter τ)).op).hom (bs τ)

theorem BX_apply (bs : (OModulePresheaf.unit πX).cochain 𝒦 0) (σ : (𝒦).Idx 0) (τ : (𝒦).Idx 0) :
    BX πX p s 𝒲 bs σ τ
      = (X.presheaf.map (homOfLE (inf_le_left : XO p s 𝒲 σ τ ≤ (𝒦).inter τ)).op).hom (bs τ) := rfl

noncomputable def ζX (β : biC p πX 𝒦 𝒲 0 0) (σ : (𝒦).Idx 0) :
    relAltC s (p ≫ πX) 𝒦 (p ⁻¹ᵁ ((𝒦).inter σ)) 0 :=
  fun τ => pull p s 𝒲 σ τ (β (σ, τ))

theorem ζX_apply (β : biC p πX 𝒦 𝒲 0 0) (σ : (𝒦).Idx 0) (τ : (𝒦).Idx 0) :
    ζX πX p s 𝒲 β σ τ = pull p s 𝒲 σ τ (β (σ, τ)) := rfl

theorem pull_dV_eq (c : (OModulePresheaf.unit (p ≫ πX)).cochain 𝒲 1) (β : biC p πX 𝒦 𝒲 0 0)
    (hβ : dV p πX 𝒦 𝒲 0 0 β = biAug p πX 𝒦 𝒲 1 c) (σ : (𝒦).Idx 0) (τ' : (𝒦).Idx (0 + 1)) :
    (∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        (X.presheaf.map (homOfLE (inf_le_inf_right ((Opens.map s.base).obj (p ⁻¹ᵁ ((𝒦).inter σ)))
          ((𝒦).inter_le_inter_face τ' j))).op).hom (ζX πX p s 𝒲 β σ ((𝒦).face τ' j)))
      = (s.appLE (𝒲.inter τ') (XO p s 𝒲 σ τ')
          ((inf_le_left : XO p s 𝒲 σ τ' ≤ (𝒦).inter τ').trans (𝒲.comap_inter_le s τ'))).hom (c τ') := by
  have h1 : pull p s 𝒲 σ τ' (dV p πX 𝒦 𝒲 0 0 β (σ, τ'))
      = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        (X.presheaf.map (homOfLE (inf_le_inf_right ((Opens.map s.base).obj (p ⁻¹ᵁ ((𝒦).inter σ)))
          ((𝒦).inter_le_inter_face τ' j))).op).hom (ζX πX p s 𝒲 β σ ((𝒦).face τ' j)) := by
    rw [dV_apply', pull_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ζX_apply]
    exact congrArg (((-1 : ℤ) ^ (j : ℕ)) • ·) (pull_res p s 𝒲 σ ((𝒦).face τ' j) σ τ' _
      (inf_le_inf_right _ ((𝒦).inter_le_inter_face τ' j)) _)
  rw [← h1, hβ, biAug_apply]
  unfold pull
  rw [appLE_res]

theorem relAltd_ζX_sub_BX (c : (OModulePresheaf.unit (p ≫ πX)).cochain 𝒲 1)
    (bs : (OModulePresheaf.unit πX).cochain 𝒦 0)
    (hbs : (OModulePresheaf.unit πX).d 𝒦 0 bs = fun t =>
        (X.presheaf.map (homOfLE (𝒲.comap_inter_le s t)).op).hom ((s.app (𝒲.inter t)).hom (c t)))
    (β : biC p πX 𝒦 𝒲 0 0) (hβ : dV p πX 𝒦 𝒲 0 0 β = biAug p πX 𝒦 𝒲 1 c) (σ : (𝒦).Idx 0) :
    relAltd s (p ≫ πX) 𝒦 (p ⁻¹ᵁ ((𝒦).inter σ)) 0 (ζX πX p s 𝒲 β σ - BX πX p s 𝒲 bs σ) = 0 := by
  rw [map_sub, sub_eq_zero]
  funext τ'
  rw [relAltd_apply', relAltd_apply', pull_dV_eq πX p s 𝒲 c β hβ σ τ']

  have h2 : ∀ j : Fin (0 + 2),
      (X.presheaf.map (homOfLE (inf_le_inf_right ((Opens.map s.base).obj (p ⁻¹ᵁ ((𝒦).inter σ)))
          ((𝒦).inter_le_inter_face τ' j))).op).hom (BX πX p s 𝒲 bs σ ((𝒦).face τ' j))
        = (X.presheaf.map (homOfLE ((inf_le_left : XO p s 𝒲 σ τ' ≤ (𝒦).inter τ').trans
            ((𝒦).inter_le_inter_face τ' j))).op).hom (bs ((𝒦).face τ' j)) := by
    intro j; rw [BX_apply, res_res]
  simp only [h2]
  have h3 : (X.presheaf.map (homOfLE (inf_le_left : XO p s 𝒲 σ τ' ≤ (𝒦).inter τ')).op).hom
      ((OModulePresheaf.unit πX).d 𝒦 0 bs τ')
      = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          (X.presheaf.map (homOfLE ((inf_le_left : XO p s 𝒲 σ τ' ≤ (𝒦).inter τ').trans
            ((𝒦).inter_le_inter_face τ' j))).op).hom (bs ((𝒦).face τ' j)) := by
    erw [OModulePresheaf.d_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    erw [map_zsmul]
    exact congrArg (((-1 : ℤ) ^ (j : ℕ)) • ·) (res_res _ _ _)
  rw [← h3, hbs, res_res]
  rfl

noncomputable def gK (hs : s ≫ p = 𝟙 X)
    (gX : ∀ σ : (𝒦).Idx 0, (pullOpen s (p ≫ πX) (⊤ : X.Opens)).obj (p ⁻¹ᵁ ((𝒦).inter σ)))
    (σ : (𝒦).Idx 0) : Γ(X, (𝒦).inter σ) :=
  (X.presheaf.map (homOfLE (le_inf le_top (pre_pre p s hs ((𝒦).inter σ)).symm.le :
      (𝒦).inter σ ≤ ⊤ ⊓ s ⁻¹ᵁ (p ⁻¹ᵁ ((𝒦).inter σ)))).op).hom (gX σ)

theorem gK_apply (hs : s ≫ p = 𝟙 X)
    (gX : ∀ σ : (𝒦).Idx 0, (pullOpen s (p ≫ πX) (⊤ : X.Opens)).obj (p ⁻¹ᵁ ((𝒦).inter σ)))
    (σ : (𝒦).Idx 0) :
    gK πX p s 𝒲 hs gX σ = (X.presheaf.map (homOfLE (le_inf le_top (pre_pre p s hs ((𝒦).inter σ)).symm.le :
      (𝒦).inter σ ≤ ⊤ ⊓ s ⁻¹ᵁ (p ⁻¹ᵁ ((𝒦).inter σ)))).op).hom (gX σ) := rfl

theorem XO_le_inter (hs : s ≫ p = 𝟙 X) {a b : ℕ} (σ : (𝒦).Idx a) (τ : (𝒦).Idx b) :
    XO p s 𝒲 σ τ ≤ (𝒦).inter σ :=
  inf_le_right.trans (pre_pre p s hs _).le

theorem e_eq_dK (hs : s ≫ p = 𝟙 X)
    (β : biC p πX 𝒦 𝒲 0 0) (e : ∀ σ : (𝒦).Idx 1, Γ(X, (𝒦).inter σ))
    (he : ∀ (σ : (𝒦).Idx 1) (τ : (𝒦).Idx 0), dH p πX 𝒦 𝒲 0 0 β (σ, τ)
        = (p.appLE ((𝒦).inter σ) (biOpen p 𝒦 𝒲 1 0 σ τ) inf_le_right).hom (e σ))
    (bs : (OModulePresheaf.unit πX).cochain 𝒦 0)
    (gX : ∀ σ : (𝒦).Idx 0, (pullOpen s (p ≫ πX) (⊤ : X.Opens)).obj (p ⁻¹ᵁ ((𝒦).inter σ)))
    (hg : ∀ σ : (𝒦).Idx 0, relAug s (p ≫ πX) 𝒦 (p ⁻¹ᵁ ((𝒦).inter σ)) (gX σ)
        = ζX πX p s 𝒲 β σ - BX πX p s 𝒲 bs σ)
    (φX : OModulePresheaf.Hom (relHPresheaf s (p ≫ πX) 𝒦 0) (pullOpen s (p ≫ πX) (⊤ : X.Opens)))
    (hφXbij : ∀ U : P.Opens, Function.Bijective (φX.app U))
    (hφXaug : ∀ (U : P.Opens) (x : LinearMap.ker (relAltd s (p ≫ πX) 𝒦 U 0)),
        relAug s (p ≫ πX) 𝒦 U (φX.app U (Submodule.Quotient.mk x)) = x.1)
    (σ : (𝒦).Idx 1) :
    e σ = dK s 𝒲 (gK πX p s 𝒲 hs gX) σ := by

  have hζ' : ∀ (σ0 : (𝒦).Idx 0) (τ : (𝒦).Idx 0),
      ζX πX p s 𝒲 β σ0 τ = BX πX p s 𝒲 bs σ0 τ + relAug s (p ≫ πX) 𝒦 (p ⁻¹ᵁ ((𝒦).inter σ0)) (gX σ0) τ := by
    intro σ0 τ
    have h := congrFun (hg σ0) τ
    rw [Pi.sub_apply] at h
    rw [h]; abel
  have hpt : ∀ τ : (𝒦).Idx 0,
      (X.presheaf.map (homOfLE (XO_le_inter p s 𝒲 hs σ τ)).op).hom (e σ)
        = (X.presheaf.map (homOfLE (XO_le_inter p s 𝒲 hs σ τ)).op).hom (dK s 𝒲 (gK πX p s 𝒲 hs gX) σ) := by
    intro τ
    have hB : ∀ j : Fin (0 + 2),
        XO p s 𝒲 σ τ ≤ ⊤ ⊓ s ⁻¹ᵁ (p ⁻¹ᵁ ((𝒦).inter ((𝒦).face σ j))) := fun j =>
      (inf_le_inf_left _ (s.preimage_mono (p.preimage_mono ((𝒦).inter_le_inter_face σ j)))).trans
        (inf_le_inf_right _ le_top)
    have step : ∀ (j : Fin (0 + 2))
        (hh : biOpen p 𝒦 𝒲 (0 + 1) 0 σ τ ≤ biOpen p 𝒦 𝒲 0 0 ((𝒦).face σ j) τ),
        pull p s 𝒲 σ τ ((P.presheaf.map (homOfLE hh).op).hom (β ((𝒦).face σ j, τ)))
          = (X.presheaf.map (homOfLE (inf_le_left : XO p s 𝒲 σ τ ≤ (𝒦).inter τ)).op).hom (bs τ)
            + (X.presheaf.map (homOfLE (hB j)).op).hom (gX ((𝒦).face σ j)) := by
      intro j hh
      rw [pull_res p s 𝒲 ((𝒦).face σ j) τ σ τ hh
        (inf_le_inf_left _ (s.preimage_mono (p.preimage_mono ((𝒦).inter_le_inter_face σ j)))),
        ← ζX_apply, hζ']
      erw [map_add]
      rw [BX_apply, res_res, relAug_apply, res_res]
    have L : (X.presheaf.map (homOfLE (XO_le_inter p s 𝒲 hs σ τ)).op).hom (e σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (X.presheaf.map (homOfLE (hB j)).op).hom (gX ((𝒦).face σ j)) := by
      rw [← pull_appLE p s 𝒲 hs σ τ (e σ) (XO_le_inter p s 𝒲 hs σ τ), ← he σ τ, dH_apply', pull_sum]
      calc ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) • pull p s 𝒲 σ τ
              ((P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter τ) ((Opens.map p.base).monotone
                ((𝒦).inter_le_inter_face σ j)))).op).hom (β ((𝒦).face σ j, τ)))
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              ((X.presheaf.map (homOfLE (inf_le_left : XO p s 𝒲 σ τ ≤ (𝒦).inter τ)).op).hom (bs τ)
                + (X.presheaf.map (homOfLE (hB j)).op).hom (gX ((𝒦).face σ j))) :=
            Finset.sum_congr rfl (fun j _ => by rw [step j])
        _ = (∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (X.presheaf.map (homOfLE (inf_le_left : XO p s 𝒲 σ τ ≤ (𝒦).inter τ)).op).hom (bs τ))
            + ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
                (X.presheaf.map (homOfLE (hB j)).op).hom (gX ((𝒦).face σ j)) := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl (fun j _ => smul_add _ _ _)
        _ = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (X.presheaf.map (homOfLE (hB j)).op).hom (gX ((𝒦).face σ j)) := by
            rw [alt_two, zero_add]
    have Rr : (X.presheaf.map (homOfLE (XO_le_inter p s 𝒲 hs σ τ)).op).hom (dK s 𝒲 (gK πX p s 𝒲 hs gX) σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (X.presheaf.map (homOfLE (hB j)).op).hom (gX ((𝒦).face σ j)) := by
      rw [dK, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, gK_apply, res_res, res_res]
    rw [L, Rr]

  have hw : (⊤ ⊓ s ⁻¹ᵁ (p ⁻¹ᵁ ((𝒦).inter σ)) : X.Opens) ≤ (𝒦).inter σ :=
    inf_le_right.trans (pre_pre p s hs _).le
  have h0 : relAug s (p ≫ πX) 𝒦 (p ⁻¹ᵁ ((𝒦).inter σ))
      ((X.presheaf.map (homOfLE hw).op).hom (e σ - dK s 𝒲 (gK πX p s 𝒲 hs gX) σ)) = 0 := by
    funext τ
    rw [relAug_apply, Pi.zero_apply, res_res, map_sub]
    exact sub_eq_zero.mpr (hpt τ)
  have h1 := relAug_eq_zero s (p ≫ πX) 𝒦 φX hφXbij hφXaug _ _ h0
  have h2 : e σ - dK s 𝒲 (gK πX p s 𝒲 hs gX) σ = 0 := by
    rw [← res_res_self (le_inf le_top (pre_pre p s hs ((𝒦).inter σ)).symm.le) hw
      (e σ - dK s 𝒲 (gK πX p s 𝒲 hs gX) σ), h1]
    exact map_zero _
  exact sub_eq_zero.mp h2

theorem main [IsSeparated πX] [IsSeparated (p ≫ πX)] (hs : s ≫ p = 𝟙 X)
    (hp : ∀ U : X.Opens, IsAffineOpen U → Function.Surjective (p.app U).hom)
    (c : (OModulePresheaf.unit (p ≫ πX)).cochain 𝒲 1)
    (hc : (OModulePresheaf.unit (p ≫ πX)).d 𝒲 1 c = 0)
    (hcU : ∀ i : 𝒲.ι, ∃ β : ∀ t : 𝒲.Idx 0, Γ(P, 𝒲.inter t ⊓ p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i)),
      ∀ t : 𝒲.Idx (0 + 1),
        (P.presheaf.map (homOfLE (inf_le_left :
            𝒲.inter t ⊓ p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i) ≤ 𝒲.inter t)).op).hom (c t)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_right (p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i))
                (𝒲.inter_le_inter_face t j))).op).hom (β (𝒲.face t j)))
    (hcs : ∃ b : (OModulePresheaf.unit πX).cochain (𝒲.comap s) 0,
      (OModulePresheaf.unit πX).d (𝒲.comap s) 0 b = fun t =>
        (X.presheaf.map (homOfLE (𝒲.comap_inter_le s t)).op).hom ((s.app (𝒲.inter t)).hom (c t))) :
    ∃ b : (OModulePresheaf.unit (p ≫ πX)).cochain 𝒲 0, (OModulePresheaf.unit (p ≫ πX)).d 𝒲 0 b = c := by
  classical
  obtain ⟨hexact, hker0, hinj⟩ := rows_exact p πX 𝒦 𝒲
  choose βi hβi using hcU
  have hdVβ : dV p πX 𝒦 𝒲 0 0 (β0 πX p s 𝒲 βi) = biAug p πX 𝒦 𝒲 1 c :=
    dV_β0 πX p s 𝒲 c βi hβi

  have hdVδ : dV p πX 𝒦 𝒲 1 0 (dH p πX 𝒦 𝒲 0 0 (β0 πX p s 𝒲 βi)) = 0 := by
    have h1 := LinearMap.congr_fun (dHV_comm p πX 𝒦 𝒲 0 0) (β0 πX p s 𝒲 βi)
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at h1
    rw [h1, hdVβ]
    have hm : biAug p πX 𝒦 𝒲 1 c ∈ LinearMap.ker ((LerayDblCpx p πX 𝒦 𝒲).dH 0 1) := by
      rw [hker0 1]; exact ⟨c, rfl⟩
    exact hm

  obtain ⟨φ, hφbij, hφaug⟩ := exists_hom_relHPresheaf_zero p πX 𝒲
  have he' : ∀ σ : (𝒦).Idx 1, ∃ eσ : Γ(X, (𝒦).inter σ), ∀ τ : (𝒦).Idx 0,
      dH p πX 𝒦 𝒲 0 0 (β0 πX p s 𝒲 βi) (σ, τ)
        = (p.appLE ((𝒦).inter σ) (biOpen p 𝒦 𝒲 1 0 σ τ) inf_le_right).hom eσ := by
    intro σ
    have hδσ : relAltd p πX 𝒲 ((𝒦).inter σ) 0
        (fun τ => dH p πX 𝒦 𝒲 0 0 (β0 πX p s 𝒲 βi) (σ, τ)) = 0 := by
      funext τ'
      have h2 := congrFun hdVδ (σ, τ')
      rw [dV_apply'] at h2
      rw [relAltd_apply']
      exact h2
    obtain ⟨eσ, heσ⟩ := hp ((𝒦).inter σ) (Scheme.OrderedAffineCover.isAffineOpen_inter πX 𝒦 σ)
      ((P.presheaf.map (homOfLE (le_inf le_top le_rfl :
          p ⁻¹ᵁ ((𝒦).inter σ) ≤ ⊤ ⊓ p ⁻¹ᵁ ((𝒦).inter σ))).op).hom
        (φ.app ((𝒦).inter σ) (Submodule.Quotient.mk ⟨_, LinearMap.mem_ker.mpr hδσ⟩)))
    refine ⟨eσ, fun τ => ?_⟩
    have h3 := congrFun (hφaug ((𝒦).inter σ) ⟨_, LinearMap.mem_ker.mpr hδσ⟩) τ
    rw [relAug_apply] at h3
    rw [appLE_apply', heσ, res_res]
    exact h3.symm
  choose e he using he'

  obtain ⟨bs, hbs⟩ := hcs
  obtain ⟨φX, hφXbij, hφXaug⟩ := exists_hom_relHPresheaf_zero s (p ≫ πX) 𝒦
  have hζ := relAltd_ζX_sub_BX πX p s 𝒲 c bs hbs (β0 πX p s 𝒲 βi) hdVβ
  have hg' : ∀ σ0 : (𝒦).Idx 0,
      ∃ g0 : (pullOpen s (p ≫ πX) (⊤ : X.Opens)).obj (p ⁻¹ᵁ ((𝒦).inter σ0)),
        relAug s (p ≫ πX) 𝒦 (p ⁻¹ᵁ ((𝒦).inter σ0)) g0
          = ζX πX p s 𝒲 (β0 πX p s 𝒲 βi) σ0 - BX πX p s 𝒲 bs σ0 :=
    fun σ0 => ⟨φX.app _ (Submodule.Quotient.mk ⟨_, LinearMap.mem_ker.mpr (hζ σ0)⟩), hφXaug _ _⟩
  choose gX hgX using hg'
  have heq : ∀ σ : (𝒦).Idx 1, e σ = dK s 𝒲 (gK πX p s 𝒲 hs gX) σ :=
    e_eq_dK πX p s 𝒲 hs (β0 πX p s 𝒲 βi) e he bs gX hgX φX hφXbij hφXaug

  have hH : dH p πX 𝒦 𝒲 0 0 (β0 πX p s 𝒲 βi - ΘP πX p s 𝒲 (gK πX p s 𝒲 hs gX)) = 0 := by
    rw [map_sub]
    funext στ
    obtain ⟨σ, τ⟩ := στ
    rw [Pi.sub_apply, Pi.zero_apply, he σ τ, dH_ΘP, ← heq σ]
    exact sub_self _
  have hV : dV p πX 𝒦 𝒲 0 0 (β0 πX p s 𝒲 βi - ΘP πX p s 𝒲 (gK πX p s 𝒲 hs gX))
      = biAug p πX 𝒦 𝒲 1 c := by
    rw [map_sub, hdVβ, dV_ΘP, sub_zero]
  have hmem : (β0 πX p s 𝒲 βi - ΘP πX p s 𝒲 (gK πX p s 𝒲 hs gX))
      ∈ LinearMap.range (biAug p πX 𝒦 𝒲 0) := by
    rw [← hker0 0]; exact hH
  obtain ⟨b, hb⟩ := hmem
  refine ⟨b, hinj 1 ?_⟩
  have h4 : (LerayDblCpx p πX 𝒦 𝒲).dV 0 0 (biAug p πX 𝒦 𝒲 0 b)
      = biAug p πX 𝒦 𝒲 (0 + 1) ((OModulePresheaf.unit (p ≫ πX)).d 𝒲 0 b) :=
    LinearMap.congr_fun (dV_comp_biAug p πX 𝒦 𝒲 0) b
  have h5 : (LerayDblCpx p πX 𝒦 𝒲).dV 0 0 (biAug p πX 𝒦 𝒲 0 b) = biAug p πX 𝒦 𝒲 1 c := by
    rw [hb]; exact hV
  exact h4.symm.trans h5

end MainC
end C1Body

theorem solution
    {R : Type u} [CommRing R] {X P : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R)) [IsSeparated πX]
    (p : P ⟶ X) [IsSeparated (p ≫ πX)]
    (s : X ⟶ P) [IsAffineHom s] (hs : s ≫ p = 𝟙 X)
    (hp : ∀ U : X.Opens, IsAffineOpen U → Function.Surjective (p.app U).hom)
    (𝒲 : P.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p ≫ πX)).cochain 𝒲 1)
    (hc : (OModulePresheaf.unit (p ≫ πX)).d 𝒲 1 c = 0)
    (hcU : ∀ i : 𝒲.ι, ∃ β : ∀ t : 𝒲.Idx 0, Γ(P, 𝒲.inter t ⊓ p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i)),
      ∀ t : 𝒲.Idx (0 + 1),
        (P.presheaf.map (homOfLE (inf_le_left :
            𝒲.inter t ⊓ p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i) ≤ 𝒲.inter t)).op).hom (c t)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_right (p ⁻¹ᵁ (s ⁻¹ᵁ 𝒲.U i))
                (𝒲.inter_le_inter_face t j))).op).hom (β (𝒲.face t j)))
    (hcs : ∃ b : (OModulePresheaf.unit πX).cochain (𝒲.comap s) 0,
      (OModulePresheaf.unit πX).d (𝒲.comap s) 0 b = fun t =>
        (X.presheaf.map (homOfLE (𝒲.comap_inter_le s t)).op).hom ((s.app (𝒲.inter t)).hom (c t))) :
    ∃ b : (OModulePresheaf.unit (p ≫ πX)).cochain 𝒲 0, (OModulePresheaf.unit (p ≫ πX)).d 𝒲 0 b = c := by
  exact C1Body.main πX p s 𝒲 hs hp c hc hcU hcs

end S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_of_d_comap_section_eq_of_forall_preimage_chart
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_of_d_comap_section_eq_of_forall_preimage_chart (solution)
