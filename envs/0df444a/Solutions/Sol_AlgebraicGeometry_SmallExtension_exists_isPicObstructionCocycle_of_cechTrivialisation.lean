-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.exists_isPicObstructionCocycle_of_cechTrivialisation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/8a7abad5-49a2-5272-b9a9-0a87bb305231

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_isUnit_transition_and_transition_face_mul_eq
import Theorems.Thm_AlgebraicGeometry_IsPullback_surjective_app_and_ker_app_eq_map_ker_of_isAffineOpen
import Theorems.Thm_AlgebraicGeometry_SmallExtension_IsFibreReading_eq_of_isFibreReading_of_flat
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isFibreReading_zero_add_mul_neg_restrict_and_exists_isFibreReading
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_exists_isPicObstructionCocycle_of_cechTrivialisation
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover Opposite TopologicalSpace"

universe u

namespace PV1P1

lemma presheaf_map_op_apply_eq {Y : Scheme.{u}} {U V : Y.Opens} (f g : U ⟶ V) (x : Y.presheaf.obj (op V)) :
    (Y.presheaf.map f.op).hom x = (Y.presheaf.map g.op).hom x := by
  rw [Subsingleton.elim f g]

lemma presheaf_map_map {Y : Scheme.{u}} {U V W : Y.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (x : Y.presheaf.obj (op U)) :
    (Y.presheaf.map (homOfLE h₁).op).hom ((Y.presheaf.map (homOfLE h₂).op).hom x) =
      (Y.presheaf.map (homOfLE (h₁.trans h₂)).op).hom x := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp]
  exact presheaf_map_op_apply_eq _ _ _

lemma presheaf_map_map' {Y : Scheme.{u}} {U V W : Y.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (h₃ : W ≤ U)
    (x : Y.presheaf.obj (op U)) :
    (Y.presheaf.map (homOfLE h₁).op).hom ((Y.presheaf.map (homOfLE h₂).op).hom x) =
      (Y.presheaf.map (homOfLE h₃).op).hom x :=
  presheaf_map_map h₁ h₂ x

lemma presheaf_map_map_self {Y : Scheme.{u}} {U V : Y.Opens} (h₁ : U ≤ V) (h₂ : V ≤ U) (x : Y.presheaf.obj (op U)) :
    (Y.presheaf.map (homOfLE h₁).op).hom ((Y.presheaf.map (homOfLE h₂).op).hom x) = x := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp, Subsingleton.elim (homOfLE h₁ ≫ homOfLE h₂) (𝟙 _),
    op_id, CategoryTheory.Functor.map_id]
  rfl

lemma app_res {X Y : Scheme.{u}} (g : X ⟶ Y) {U V : Y.Opens} (h : V ≤ U) (x : Y.presheaf.obj (op U)) :
    (g.app V).hom ((Y.presheaf.map (homOfLE h).op).hom x) =
      (X.presheaf.map (homOfLE (g.preimage_mono h : g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U)).op).hom ((g.app U).hom x) := by
  have e := congrArg (fun φ => φ.hom x) (Scheme.Hom.naturality g (U := V) (U' := U) (homOfLE h).op)
  simp only [CategoryTheory.comp_apply] at e
  exact e.trans (presheaf_map_op_apply_eq _ _ _)

lemma res_congr {X : Scheme.{u}} {I : Type*} (O : I → X.Opens) (u : ∀ s, X.presheaf.obj (op (O s))) {s s' : I}
    (e : s = s') {W : X.Opens} (h : W ≤ O s) (h' : W ≤ O s') :
    (X.presheaf.map (homOfLE h).op).hom (u s) = (X.presheaf.map (homOfLE h').op).hom (u s') := by
  subst e; rfl

lemma res_algebraMap {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    {U U' : X.Opens} (h : U' ≤ U) (b : R) :
    letI := algebraOfHom f U
    letI := algebraOfHom f U'
    (X.presheaf.map (homOfLE h).op).hom (algebraMap R Γ(X, U) b) = algebraMap R Γ(X, U') b := by
  show ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top ≫ X.presheaf.map (homOfLE h).op).hom b =
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U' le_top).hom b
  rw [Scheme.Hom.appLE_map]

lemma quad {R : Type*} [CommRing R] (X02 X00 Y01 X12 Y11 X22 X20 Y31 : R)
    (hbd : X20 * Y01 = 1) (hac : X12 * Y31 = 1)
    (h02 : (X02 * X00 * Y01 - 1) * (X22 * X20 * Y11 - 1) = 0)
    (h13 : (X12 * X00 * Y11 - 1) * (X22 * X02 * Y31 - 1) = 0) :
    (X02 * X00 * Y01 - 1) - (X12 * X00 * Y11 - 1) + (X22 * X20 * Y11 - 1) - (X22 * X02 * Y31 - 1) = 0 := by
  linear_combination (-1 : R) * h02 + h13 + (X22 * X02 * X00 * Y11) * hbd - (X22 * X02 * X00 * Y11) * hac

lemma exists_lift_unit {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (hφ : Function.Surjective φ)
    (hker : ∀ x y : A, φ x = 0 → φ y = 0 → x * y = 0) (t : B) (ht : IsUnit t) :
    ∃ ab : A × A, φ ab.1 = t ∧ ab.1 * ab.2 = 1 := by
  obtain ⟨a, ha⟩ := hφ t
  obtain ⟨b, hb⟩ := hφ (↑ht.unit⁻¹ : B)
  have he : φ (a * b - 1) = 0 := by
    rw [map_sub, map_mul, map_one, ha, hb, IsUnit.mul_val_inv, sub_self]
  refine ⟨⟨a, b * (2 - a * b)⟩, ha, ?_⟩
  have h2 := hker _ _ he he
  linear_combination (-1 : A) * h2

lemma face_face_eq {V : Scheme.{u}} (K : V.OrderedAffineCover) (t : K.Idx 3) (j j' : Fin 4) (a a' : Fin 3)
    (h : (Fin.succAbove j ∘ Fin.succAbove a : Fin 2 → Fin 4) = Fin.succAbove j' ∘ Fin.succAbove a') :
    K.face (K.face t j) a = K.face (K.face t j') a' :=
  Subtype.ext (congrArg (fun φ : Fin 2 → Fin 4 => t.1 ∘ φ) h)

lemma ff10 : (Fin.succAbove (1 : Fin 4) ∘ Fin.succAbove (0 : Fin 3) : Fin 2 → Fin 4) =
    Fin.succAbove 0 ∘ Fin.succAbove 0 := by funext x; fin_cases x <;> rfl
lemma ff32 : (Fin.succAbove (3 : Fin 4) ∘ Fin.succAbove (2 : Fin 3) : Fin 2 → Fin 4) =
    Fin.succAbove 2 ∘ Fin.succAbove 2 := by funext x; fin_cases x <;> rfl
lemma ff30 : (Fin.succAbove (3 : Fin 4) ∘ Fin.succAbove (0 : Fin 3) : Fin 2 → Fin 4) =
    Fin.succAbove 0 ∘ Fin.succAbove 2 := by funext x; fin_cases x <;> rfl
lemma ff21 : (Fin.succAbove (2 : Fin 4) ∘ Fin.succAbove (1 : Fin 3) : Fin 2 → Fin 4) =
    Fin.succAbove 1 ∘ Fin.succAbove 1 := by funext x; fin_cases x <;> rfl
lemma ff01 : (Fin.succAbove (0 : Fin 4) ∘ Fin.succAbove (1 : Fin 3) : Fin 2 → Fin 4) =
    Fin.succAbove 2 ∘ Fin.succAbove 0 := by funext x; fin_cases x <;> rfl
lemma ff31 : (Fin.succAbove (3 : Fin 4) ∘ Fin.succAbove (1 : Fin 3) : Fin 2 → Fin 4) =
    Fin.succAbove 1 ∘ Fin.succAbove 2 := by funext x; fin_cases x <;> rfl

end PV1P1

namespace PV1P1

theorem main
    {B₁ B₀ : Type u} [CommRing B₁] [IsLocalRing B₁] [CommRing B₀]
    (π : B₁ →+* B₀) (hπ : Function.Surjective π)
    (hsmall : RingHom.ker π * maximalIdeal B₁ = ⊥) (hI : RingHom.ker π ≤ maximalIdeal B₁)
    (V : Type u) [AddCommGroup V] [Module (ResidueField B₁) V] [Module.Finite (ResidueField B₁) V]
    [Module B₁ V] [IsScalarTower B₁ (ResidueField B₁) V]
    (ι : V →ₗ[B₁] B₁) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B₁ (RingHom.ker π))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁)) [IsSeparated f] [Flat f]
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of B₀)) (g : X₀ ⟶ X) [IsAffineHom g]
    (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of (ResidueField B₁))) (i : Xk ⟶ X) [IsAffineHom i]
    (hi : IsPullback i fk f (Spec.map (CommRingCat.ofHom (residue B₁))))
    (𝒰 : X.OrderedAffineCover)
    (𝓛₀ : X₀.Modules) (τ : Scheme.Modules.CechTrivialisation (𝒰.comap g) 𝓛₀) :
    ∃ c : Module.Dual (ResidueField B₁) V →ₗ[ResidueField B₁] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 2,
      IsPicObstructionCocycle V ι f fk i g 𝒰 𝓛₀ c ∧
      ∀ ξ : Module.Dual (ResidueField B₁) V, (OModulePresheaf.unit fk).d (𝒰.comap i) 2 (c ξ) = 0 := by
  classical
  obtain ⟨hunit, hcoc⟩ :=
    AlgebraicGeometry.Scheme.Modules.CechTrivialisation.isUnit_transition_and_transition_face_mul_eq (𝒰.comap g) 𝓛₀ τ

  haveI hdiag : IsAffineHom (pullback.diagonal (terminal.from X)) := by
    have e : terminal.from X = f ≫ terminal.from _ := terminal.hom_ext _ _
    rw [e]; infer_instance
  have haff : ∀ {n : ℕ} (s : 𝒰.Idx n), IsAffineOpen (𝒰.inter s) := fun s =>
    IsAffineOpen.iInf fun j => 𝒰.isAffineOpen _

  have hJJ0 : RingHom.ker π * RingHom.ker π = ⊥ :=
    le_bot_iff.mp ((Ideal.mul_mono_right hI).trans hsmall.le)
  have hnil : IsNilpotent (RingHom.ker π) := ⟨2, by rw [pow_two]; exact hJJ0⟩

  have H2 := fun (U : X.Opens) (hU : IsAffineOpen U) =>
    AlgebraicGeometry.IsPullback.surjective_app_and_ker_app_eq_map_ker_of_isAffineOpen π hπ hnil f f₀ g hg U hU
  have hker0 : ∀ (U : X.Opens), IsAffineOpen U → ∀ x y : Γ(X, U),
      (g.app U).hom x = 0 → (g.app U).hom y = 0 → x * y = 0 := by
    intro U hU x y hx hy
    letI := algebraOfHom f U
    have hx' : x ∈ (RingHom.ker π).map (algebraMap B₁ Γ(X, U)) := by rw [← (H2 U hU).2]; exact hx
    have hy' : y ∈ (RingHom.ker π).map (algebraMap B₁ Γ(X, U)) := by rw [← (H2 U hU).2]; exact hy
    have hxy := Ideal.mul_mem_mul hx' hy'
    rwa [← Ideal.map_mul, hJJ0, Ideal.map_bot, Ideal.mem_bot] at hxy

  let t' : ∀ s : 𝒰.Idx 1, Γ(X₀, g ⁻¹ᵁ 𝒰.inter s) := fun s =>
    (X₀.presheaf.map (homOfLE (𝒰.le_comap_inter g s)).op).hom (τ.transition s)
  have hl : ∀ s : 𝒰.Idx 1, ∃ ab : Γ(X, 𝒰.inter s) × Γ(X, 𝒰.inter s),
      (g.app (𝒰.inter s)).hom ab.1 = t' s ∧ ab.1 * ab.2 = 1 := fun s =>
    exists_lift_unit (g.app (𝒰.inter s)).hom (H2 _ (haff s)).1 (hker0 _ (haff s)) (t' s) ((hunit s).map _)
  choose uu huu using hl

  let δ : ∀ r : 𝒰.Idx 2, Γ(X, 𝒰.inter r) := fun r =>
    (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 2)).op).hom (uu (𝒰.face r 2)).1 *
        (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 0)).op).hom (uu (𝒰.face r 0)).1 *
        (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (uu (𝒰.face r 1)).2 - 1

  let T : ∀ (r : 𝒰.Idx 2) (j : Fin 3), Γ(X₀, g ⁻¹ᵁ 𝒰.inter r) := fun r j =>
    (X₀.presheaf.map (homOfLE ((g.preimage_mono (𝒰.inter_le_inter_face r j)).trans
      (𝒰.le_comap_inter g (𝒰.face r j)))).op).hom (τ.transition (𝒰.face r j))
  have hT : ∀ (r : 𝒰.Idx 2) (j : Fin 3),
      (g.app (𝒰.inter r)).hom ((X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r j)).op).hom (uu (𝒰.face r j)).1) =
        T r j := by
    intro r j
    rw [app_res, (huu _).1]
    exact presheaf_map_map _ _ _
  have hTcoc : ∀ r : 𝒰.Idx 2, T r 2 * T r 0 = T r 1 := by
    intro r
    have e := congrArg (fun x => (X₀.presheaf.map (homOfLE (𝒰.le_comap_inter g r)).op).hom x) (hcoc r)
    simp only [map_mul] at e
    simp only [T]
    convert e using 2 <;> exact (presheaf_map_map _ _ _).symm
  have hgδ : ∀ r : 𝒰.Idx 2, (g.app (𝒰.inter r)).hom (δ r) = 0 := by
    intro r
    have h1 : (g.app (𝒰.inter r)).hom
        ((X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (uu (𝒰.face r 1)).1) *
        (g.app (𝒰.inter r)).hom
        ((X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (uu (𝒰.face r 1)).2) = 1 := by
      rw [← map_mul, ← map_mul, (huu _).2, map_one, map_one]
    simp only [δ, map_sub, map_mul, map_one, hT, hTcoc]
    rw [← hT r 1, h1, sub_self]

  have hfam : ∀ r : 𝒰.Idx 2, ∃ (n : ℕ) (v : Fin n → V) (s : Fin n → Γ(X, 𝒰.inter r)),
      (letI := algebraOfHom f (𝒰.inter r)
       (∑ j, algebraMap B₁ (X.presheaf.obj (op (𝒰.inter r))) (ι (v j)) * s j) = δ r) := by
    intro r
    letI := algebraOfHom f (𝒰.inter r)
    have hmem : δ r ∈ (RingHom.ker π).map (algebraMap B₁ Γ(X, 𝒰.inter r)) := by
      rw [← (H2 _ (haff r)).2]; exact hgδ r
    rw [Ideal.map, Submodule.mem_span_set'] at hmem
    obtain ⟨n, cf, gen, hsum⟩ := hmem
    have hgen : ∀ l : Fin n, ∃ v : V, algebraMap B₁ Γ(X, 𝒰.inter r) (ι v) = (gen l : Γ(X, 𝒰.inter r)) := by
      intro l
      obtain ⟨b, hb, hbe⟩ := (gen l).2
      have hb' : b ∈ LinearMap.range ι := by
        rw [hιI, Submodule.restrictScalars_mem]; exact hb
      obtain ⟨v, rfl⟩ := hb'
      exact ⟨v, hbe⟩
    choose v hv using hgen
    refine ⟨n, v, cf, ?_⟩
    rw [← hsum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hv, smul_eq_mul, mul_comm]
  choose nn vv ss hsum using hfam

  let m : ∀ r : 𝒰.Idx 2, Fin (nn r) → (OModulePresheaf.unit fk).obj ((𝒰.comap i).inter r) := fun r j =>
    (OModulePresheaf.unit fk).res (𝒰.comap_inter_le i r)
      (show (OModulePresheaf.unit fk).obj (i ⁻¹ᵁ 𝒰.inter r) from (i.app (𝒰.inter r)).hom (ss r j))
  let c : Module.Dual (ResidueField B₁) V →ₗ[ResidueField B₁] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 2 :=
    { toFun := fun ξ r => ∑ j, ξ (vv r j) • m r j
      map_add' := fun ξ ξ' => by
        funext r
        simp only [LinearMap.add_apply, add_smul, Finset.sum_add_distrib, Pi.add_apply]
      map_smul' := fun a ξ => by
        funext r
        simp only [LinearMap.smul_apply, RingHom.id_apply, Pi.smul_apply, Finset.smul_sum, smul_smul, smul_eq_mul] }
  have hc : ∀ ξ r, c ξ r = ∑ j, ξ (vv r j) • m r j := fun _ _ => rfl
  have hread : ∀ r : 𝒰.Idx 2,
      IsFibreReading V ι f fk i (𝒰.inter r) ((𝒰.comap i).inter r) (𝒰.comap_inter_le i r) (δ r)
        ((LinearMap.proj r).comp c) := fun r =>
    ⟨nn r, vv r, ss r, hsum r, fun ξ => rfl⟩
  refine ⟨c, ⟨τ, fun s => (uu s).1, fun s => (uu s).2, ?_, fun s => (huu s).2, fun r => hread r⟩, ?_⟩
  · intro s
    rw [(huu s).1]
    exact presheaf_map_map_self _ _ _
  ·
    intro ξ
    funext t

    have e10 := face_face_eq 𝒰 t 1 0 0 0 ff10
    have e32 := face_face_eq 𝒰 t 3 2 2 2 ff32
    have e30 := face_face_eq 𝒰 t 3 0 0 2 ff30
    have e21 := face_face_eq 𝒰 t 2 1 1 1 ff21
    have e01 := face_face_eq 𝒰 t 0 2 1 0 ff01
    have e31 := face_face_eq 𝒰 t 3 1 1 2 ff31

    have hz : ∀ j : Fin 4, (g.app (𝒰.inter t)).hom
        ((X.presheaf.map (homOfLE (𝒰.inter_le_inter_face t j)).op).hom (δ (𝒰.face t j))) = 0 := by
      intro j; rw [app_res, hgδ, map_zero]
    have h02 := hker0 _ (haff t) _ _ (hz 0) (hz 2)
    have h13 := hker0 _ (haff t) _ _ (hz 1) (hz 3)

    have hΔ : (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face t 0)).op).hom (δ (𝒰.face t 0)) -
        (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face t 1)).op).hom (δ (𝒰.face t 1)) +
        (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face t 2)).op).hom (δ (𝒰.face t 2)) -
        (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face t 3)).op).hom (δ (𝒰.face t 3)) = 0 := by
      simp only [δ, map_sub, map_mul, map_one, presheaf_map_map] at h02 h13 ⊢
      have c10 : (X.presheaf.map (homOfLE ((𝒰.inter_le_inter_face t 1).trans
            (𝒰.inter_le_inter_face (𝒰.face t 1) 0))).op).hom (uu (𝒰.face (𝒰.face t 1) 0)).1 =
          (X.presheaf.map (homOfLE ((𝒰.inter_le_inter_face t 0).trans
            (𝒰.inter_le_inter_face (𝒰.face t 0) 0))).op).hom (uu (𝒰.face (𝒰.face t 0) 0)).1 :=
        res_congr (fun s => 𝒰.inter s) (fun s => (uu s).1) e10 _ _
      have c32 : (X.presheaf.map (homOfLE ((𝒰.inter_le_inter_face t 3).trans
            (𝒰.inter_le_inter_face (𝒰.face t 3) 2))).op).hom (uu (𝒰.face (𝒰.face t 3) 2)).1 =
          (X.presheaf.map (homOfLE ((𝒰.inter_le_inter_face t 2).trans
            (𝒰.inter_le_inter_face (𝒰.face t 2) 2))).op).hom (uu (𝒰.face (𝒰.face t 2) 2)).1 :=
        res_congr (fun s => 𝒰.inter s) (fun s => (uu s).1) e32 _ _
      have c30 : (X.presheaf.map (homOfLE ((𝒰.inter_le_inter_face t 3).trans
            (𝒰.inter_le_inter_face (𝒰.face t 3) 0))).op).hom (uu (𝒰.face (𝒰.face t 3) 0)).1 =
          (X.presheaf.map (homOfLE ((𝒰.inter_le_inter_face t 0).trans
            (𝒰.inter_le_inter_face (𝒰.face t 0) 2))).op).hom (uu (𝒰.face (𝒰.face t 0) 2)).1 :=
        res_congr (fun s => 𝒰.inter s) (fun s => (uu s).1) e30 _ _
      have c21 : (X.presheaf.map (homOfLE ((𝒰.inter_le_inter_face t 2).trans
            (𝒰.inter_le_inter_face (𝒰.face t 2) 1))).op).hom (uu (𝒰.face (𝒰.face t 2) 1)).2 =
          (X.presheaf.map (homOfLE ((𝒰.inter_le_inter_face t 1).trans
            (𝒰.inter_le_inter_face (𝒰.face t 1) 1))).op).hom (uu (𝒰.face (𝒰.face t 1) 1)).2 :=
        res_congr (fun s => 𝒰.inter s) (fun s => (uu s).2) e21 _ _
      have c01 : (X.presheaf.map (homOfLE ((𝒰.inter_le_inter_face t 0).trans
            (𝒰.inter_le_inter_face (𝒰.face t 0) 1))).op).hom (uu (𝒰.face (𝒰.face t 0) 1)).2 =
          (X.presheaf.map (homOfLE ((𝒰.inter_le_inter_face t 2).trans
            (𝒰.inter_le_inter_face (𝒰.face t 2) 0))).op).hom (uu (𝒰.face (𝒰.face t 2) 0)).2 :=
        res_congr (fun s => 𝒰.inter s) (fun s => (uu s).2) e01 _ _
      have c31 : (X.presheaf.map (homOfLE ((𝒰.inter_le_inter_face t 3).trans
            (𝒰.inter_le_inter_face (𝒰.face t 3) 1))).op).hom (uu (𝒰.face (𝒰.face t 3) 1)).2 =
          (X.presheaf.map (homOfLE ((𝒰.inter_le_inter_face t 1).trans
            (𝒰.inter_le_inter_face (𝒰.face t 1) 2))).op).hom (uu (𝒰.face (𝒰.face t 1) 2)).2 :=
        res_congr (fun s => 𝒰.inter s) (fun s => (uu s).2) e31 _ _
      have hbd : (X.presheaf.map (homOfLE ((𝒰.inter_le_inter_face t 2).trans
            (𝒰.inter_le_inter_face (𝒰.face t 2) 0))).op).hom (uu (𝒰.face (𝒰.face t 2) 0)).1 *
          (X.presheaf.map (homOfLE ((𝒰.inter_le_inter_face t 0).trans
            (𝒰.inter_le_inter_face (𝒰.face t 0) 1))).op).hom (uu (𝒰.face (𝒰.face t 0) 1)).2 = 1 := by
        rw [c01, ← map_mul, (huu _).2, map_one]
      have hac : (X.presheaf.map (homOfLE ((𝒰.inter_le_inter_face t 1).trans
            (𝒰.inter_le_inter_face (𝒰.face t 1) 2))).op).hom (uu (𝒰.face (𝒰.face t 1) 2)).1 *
          (X.presheaf.map (homOfLE ((𝒰.inter_le_inter_face t 3).trans
            (𝒰.inter_le_inter_face (𝒰.face t 3) 1))).op).hom (uu (𝒰.face (𝒰.face t 3) 1)).2 = 1 := by
        rw [c31, ← map_mul, (huu _).2, map_one]
      rw [c21] at h02
      rw [c10, c32, c30] at h13
      rw [c10, c32, c30, c21]
      linear_combination (quad _ _ _ _ _ _ _ _ hbd hac h02 h13)

    have RC := fun (U : X.Opens) (W : Xk.Opens) (hW : W ≤ i ⁻¹ᵁ U) =>
      AlgebraicGeometry.SmallExtension.isFibreReading_zero_add_mul_neg_restrict_and_exists_isFibreReading
        V ι f fk i U W hW
    have R : ∀ j : Fin 4, IsFibreReading V ι f fk i (𝒰.inter t) ((𝒰.comap i).inter t) (𝒰.comap_inter_le i t)
        ((X.presheaf.map (homOfLE (𝒰.inter_le_inter_face t j)).op).hom (δ (𝒰.face t j)))
        (((OModulePresheaf.unit fk).res ((𝒰.comap i).inter_le_inter_face t j)).comp
          ((LinearMap.proj (𝒰.face t j)).comp c)) := fun j =>
      (RC _ _ (𝒰.comap_inter_le i (𝒰.face t j))).2.2.2.2.1 _ _ _ _ (𝒰.inter_le_inter_face t j)
        ((𝒰.comap i).inter_le_inter_face t j) (𝒰.comap_inter_le i t) (hread (𝒰.face t j))
    obtain ⟨hzero, hadd, -, hneg, -, -⟩ := RC (𝒰.inter t) ((𝒰.comap i).inter t) (𝒰.comap_inter_le i t)
    have Rsum := hadd _ _ _ _ (hadd _ _ _ _ (hadd _ _ _ _ (R 0) (hneg _ _ (R 1))) (R 2)) (hneg _ _ (R 3))
    rw [← sub_eq_add_neg, ← sub_eq_add_neg, hΔ] at Rsum
    have key := AlgebraicGeometry.SmallExtension.IsFibreReading.eq_of_isFibreReading_of_flat V ι hι f fk i hi
      (𝒰.inter t) (haff t) ((𝒰.comap i).inter t) (𝒰.comap_inter_le i t) 0 _ _ Rsum hzero
    have key' := congrArg (fun φ => φ ξ) key
    simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.zero_apply] at key'

    rw [OModulePresheaf.d_apply, Fin.sum_univ_four]
    have e0 : ((-1 : ℤ) ^ ((0 : Fin 4) : ℕ)) = 1 := by norm_num
    have e1 : ((-1 : ℤ) ^ ((1 : Fin 4) : ℕ)) = -1 := by norm_num
    have e2 : ((-1 : ℤ) ^ ((2 : Fin 4) : ℕ)) = 1 := by norm_num
    have e3 : ((-1 : ℤ) ^ ((3 : Fin 4) : ℕ)) = -1 := by
      rw [show ((3 : Fin 4) : ℕ) = 3 from rfl]; norm_num
    rw [e0, e1, e2, e3, one_zsmul, one_zsmul, neg_one_zsmul, neg_one_zsmul]
    exact key'

end PV1P1

theorem solution
    {B₁ B₀ : Type u} [CommRing B₁] [IsLocalRing B₁] [CommRing B₀]
    (π : B₁ →+* B₀) (hπ : Function.Surjective π)
    (hsmall : RingHom.ker π * maximalIdeal B₁ = ⊥) (hI : RingHom.ker π ≤ maximalIdeal B₁)

    (V : Type u) [AddCommGroup V] [Module (ResidueField B₁) V] [Module.Finite (ResidueField B₁) V]
    [Module B₁ V] [IsScalarTower B₁ (ResidueField B₁) V]
    (ι : V →ₗ[B₁] B₁) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B₁ (RingHom.ker π))

    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁)) [IsSeparated f] [Flat f]
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of B₀)) (g : X₀ ⟶ X) [IsAffineHom g]
    (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of (ResidueField B₁))) (i : Xk ⟶ X) [IsAffineHom i]
    (hi : IsPullback i fk f (Spec.map (CommRingCat.ofHom (residue B₁))))
    (𝒰 : X.OrderedAffineCover)
    (𝓛₀ : X₀.Modules) (τ : Scheme.Modules.CechTrivialisation (𝒰.comap g) 𝓛₀) :
    ∃ c : Module.Dual (ResidueField B₁) V →ₗ[ResidueField B₁] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 2,
      IsPicObstructionCocycle V ι f fk i g 𝒰 𝓛₀ c ∧
      ∀ ξ : Module.Dual (ResidueField B₁) V, (OModulePresheaf.unit fk).d (𝒰.comap i) 2 (c ξ) = 0 :=
  PV1P1.main π hπ hsmall hI V ι hι hιI f f₀ g hg fk i hi 𝒰 𝓛₀ τ

end S_AlgebraicGeometry_SmallExtension_exists_isPicObstructionCocycle_of_cechTrivialisation
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_exists_isPicObstructionCocycle_of_cechTrivialisation (solution)
