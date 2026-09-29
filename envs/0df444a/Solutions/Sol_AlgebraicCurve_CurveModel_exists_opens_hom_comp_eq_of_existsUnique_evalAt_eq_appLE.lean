-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.exists_opens_hom_comp_eq_of_existsUnique_evalAt_eq_appLE
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/6f448fe7-1dd9-5e76-b798-cabdeca33c67

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_section_algebraMap_germ_eq_of_forall_mem_range
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace
import Theorems.Thm_AlgebraicCurve_CurveModel_surjective_and_eq_genericPoint_or_isClosed_singleton_of_isIso_stalkMap
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_AlgebraicGeometry_IsAffineOpen_eq_of_appLE_eq_and_exists_appLE_eq_of_ringHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_exists_opens_hom_comp_eq_of_existsUnique_evalAt_eq_appLE

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve Opposite TopologicalSpace

namespace K6aS3

section Eval
variable {F : Type} [Field F] [Algebra ℂ F]

theorem isRational [IsCurveOver ℂ F] (v : Place ℂ F) : v.IsRational := by
  haveI : Module.Finite ℂ v.ResidueField := IsCurveOver.finite_residueField v
  haveI : Algebra.IsIntegral ℂ v.ResidueField := Algebra.IsIntegral.of_finite ℂ _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := v.ResidueField)).2

theorem evalAt_add (v : Place ℂ F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (add_mem hf hg), map_add, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    ← map_add]
  rfl

theorem evalAt_eq_of_sub_algebraMap_mem_nonunits (v : Place ℂ F) {x : F} (hx : x ∈ v.toValuationSubring) (c : ℂ)
    (h : x - algebraMap ℂ F c ∈ v.toValuationSubring.nonunits) : v.evalAt x = c := by
  have hc : algebraMap ℂ F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hsub : (⟨x, hx⟩ : v.toValuationSubring) - algebraMap ℂ v.toValuationSubring c ∈
      IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    exact h
  have hres : IsLocalRing.residue v.toValuationSubring (⟨x, hx⟩ : v.toValuationSubring) =
      algebraMap ℂ v.ResidueField c := by
    rw [← sub_eq_zero, IsScalarTower.algebraMap_apply ℂ v.toValuationSubring v.ResidueField c,
      IsLocalRing.ResidueField.algebraMap_eq, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hsub
  rw [v.evalAt_of_mem hx, hres, v.residueInv_algebraMap]

end Eval

section Points
variable {K : Type} [Field K] {X : Scheme.{0}}

theorem appLE_congr_hom {X Y : Scheme.{0}} {p q : X ⟶ Y} (hpq : p = q) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ p ⁻¹ᵁ U) (h' : V ≤ q ⁻¹ᵁ U) : p.appLE U V h = q.appLE U V h' := by subst hpq; rfl

theorem top_le_preimage_iff (q : Spec (CommRingCat.of ℂ) ⟶ X) (U : X.Opens) :
    ⊤ ≤ q ⁻¹ᵁ U ↔ q.base (IsLocalRing.closedPoint ℂ) ∈ U := by
  constructor
  · intro h; exact h (Set.mem_univ (IsLocalRing.closedPoint ℂ))
  · intro h p _
    have hp : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst hp; exact h

def evalAlgHom (f : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) (P : Spec (CommRingCat.of K) ⟶ X)
    (hP1 : P ≫ f = 𝟙 _) (hP : ⊤ ≤ P ⁻¹ᵁ U) :
    letI := f.sectionsAlgebra U
    Γ(X, U) →ₐ[K] K :=
  letI := f.sectionsAlgebra U
  { toRingHom := (P.appLE U ⊤ hP ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom
    commutes' := fun r => by
      change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ U le_top ≫ P.appLE U ⊤ hP ≫
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom r = r
      have h1 : f.appLE ⊤ U le_top ≫ P.appLE U ⊤ hP = 𝟙 _ := by
        rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hP1 ⊤ ⊤ _ le_top]
        simp [Scheme.Hom.appLE]
      rw [← Category.assoc (f.appLE ⊤ U le_top), h1]
      simp }

theorem evalAlgHom_apply (f : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) (P : Spec (CommRingCat.of K) ⟶ X)
    (hP1 : P ≫ f = 𝟙 _) (hP : ⊤ ≤ P ⁻¹ᵁ U) (s : Γ(X, U)) :
    evalAlgHom f U P hP1 hP s = (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((P.appLE U ⊤ hP) s) := rfl

end Points

section Theta
variable {F : Type} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
  {Y : Scheme.{0}} (pY : Y ⟶ Spec (CommRingCat.of ℂ))
  (w : Place ℂ F → {P : Spec (CommRingCat.of ℂ) ⟶ Y // P ≫ pY = 𝟙 _})
  (U : Y.Opens)

theorem exists_ringHom_forall_mem_and_evalAt_eq
    (hB : ∀ φ : Γ(Y, U), ∃! ξ : F, ∀ (v : Place ℂ F) (h : ⊤ ≤ (w v).1 ⁻¹ᵁ U),
      ξ ∈ v.toValuationSubring ∧
        Place.evalAt v ξ = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((w v).1.appLE U ⊤ h) φ)) :
    letI := pY.sectionsAlgebra U
    ∃ θ : Γ(Y, U) →+* F,
      (∀ (φ : Γ(Y, U)) (v : Place ℂ F) (h : ⊤ ≤ (w v).1 ⁻¹ᵁ U),
        θ φ ∈ v.toValuationSubring ∧
          Place.evalAt v (θ φ) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((w v).1.appLE U ⊤ h) φ)) ∧
      ∀ c : ℂ, θ (algebraMap ℂ Γ(Y, U) c) = algebraMap ℂ F c := by
  classical
  letI := pY.sectionsAlgebra U
  choose ξ hξ hξu using hB
  have hv : ∀ v : Place ℂ F, v.IsRational := isRational
  have hmul : ∀ φ ψ : Γ(Y, U), ξ (φ * ψ) = ξ φ * ξ ψ := fun φ ψ =>
    (hξu (φ * ψ) _ fun v h => ⟨mul_mem (hξ φ v h).1 (hξ ψ v h).1, by
      rw [Place.evalAt_mul v (hv v) (hξ φ v h).1 (hξ ψ v h).1, (hξ φ v h).2, (hξ ψ v h).2, map_mul, map_mul]⟩).symm
  have hadd : ∀ φ ψ : Γ(Y, U), ξ (φ + ψ) = ξ φ + ξ ψ := fun φ ψ =>
    (hξu (φ + ψ) _ fun v h => ⟨add_mem (hξ φ v h).1 (hξ ψ v h).1, by
      rw [evalAt_add v (hv v) (hξ φ v h).1 (hξ ψ v h).1, (hξ φ v h).2, (hξ ψ v h).2, map_add, map_add]⟩).symm
  have hconst : ∀ c : ℂ, ξ (algebraMap ℂ Γ(Y, U) c) = algebraMap ℂ F c := fun c =>
    (hξu _ _ fun v h => ⟨v.algebraMap_mem' c, by
      rw [Place.evalAt_algebraMap, ← evalAlgHom_apply pY U (w v).1 (w v).2 h, AlgHom.commutes]; rfl⟩).symm
  have hone : ξ 1 = 1 := by simpa using hconst 1
  have hzero : ξ 0 = 0 := by simpa using hconst 0
  exact ⟨{ toFun := ξ, map_one' := hone, map_mul' := hmul, map_zero' := hzero, map_add' := hadd },
    fun φ v h => hξ φ v h, hconst⟩

end Theta

section Sections
variable {F : Type} [Field F] [Algebra ℂ F] (M : CurveModel ℂ F)

def goodOpen (S : Set (Place ℂ F)) (hS : Sᶜ.Finite) : M.C.Opens :=
  ⟨{x : M.C | ∀ hx : x ∈ closedPoints M.C, M.placeEquiv ⟨x, hx⟩ ∈ S}, by
    classical
    have hfin : Set.Finite {x : M.C | ∃ hx : x ∈ closedPoints M.C, M.placeEquiv ⟨x, hx⟩ ∉ S} := by
      refine (hS.image fun v => ((M.placeEquiv.symm v : closedPoints M.C) : M.C)).subset ?_
      rintro x ⟨hx, hxS⟩
      exact ⟨M.placeEquiv ⟨x, hx⟩, hxS, by simp⟩
    have hclosed : IsClosed {x : M.C | ∃ hx : x ∈ closedPoints M.C, M.placeEquiv ⟨x, hx⟩ ∉ S} := by
      rw [← Set.biUnion_of_singleton {x : M.C | ∃ hx : x ∈ closedPoints M.C, M.placeEquiv ⟨x, hx⟩ ∉ S}]
      exact hfin.isClosed_biUnion fun x hx => hx.1
    have heq : {x : M.C | ∀ hx : x ∈ closedPoints M.C, M.placeEquiv ⟨x, hx⟩ ∈ S} =
        {x : M.C | ∃ hx : x ∈ closedPoints M.C, M.placeEquiv ⟨x, hx⟩ ∉ S}ᶜ := by
      ext x; simp
    rw [heq]
    exact hclosed.isOpen_compl⟩

theorem mem_goodOpen_iff (S : Set (Place ℂ F)) (hS : Sᶜ.Finite) (x : M.C) :
    x ∈ goodOpen M S hS ↔ ∀ hx : x ∈ closedPoints M.C, M.placeEquiv ⟨x, hx⟩ ∈ S := Iff.rfl

theorem eq_genericPoint_or_isClosed (x : M.C) : x = genericPoint M.C ∨ IsClosed ({x} : Set M.C) := by
  have h := AlgebraicCurve.CurveModel.surjective_and_eq_genericPoint_or_isClosed_singleton_of_isIso_stalkMap
    ℂ M.toBase M (𝟙 M.C) (Category.id_comp _) (by rw [Scheme.Hom.stalkMap_id]; exact IsIso.id _)
  exact h.2 x

theorem exists_ringHom_sections {R : Type} [CommRing R] (θ : R →+* F)
    (S : Set (Place ℂ F)) (hS : Sᶜ.Finite)
    (hθ : ∀ (r : R) (v : Place ℂ F), v ∈ S → θ r ∈ v.toValuationSubring) :
    ∃ Θ : R →+* Γ(M.C, goodOpen M S hS),
      (∀ (r : R) (x : M.C) (hx : x ∈ goodOpen M S hS),
        algebraMap (M.C.presheaf.stalk x) M.C.functionField
          (M.C.presheaf.germ (goodOpen M S hS) x hx (Θ r)) = M.ffEquiv (θ r)) ∧
      ∀ (r : R) (u : Γ(M.C, goodOpen M S hS)),
        (∀ (x : M.C) (hx : x ∈ goodOpen M S hS),
          algebraMap (M.C.presheaf.stalk x) M.C.functionField
            (M.C.presheaf.germ (goodOpen M S hS) x hx u) = M.ffEquiv (θ r)) → u = Θ r := by
  classical

  have hreg : ∀ (r : R) (x : M.C), x ∈ goodOpen M S hS →
      M.ffEquiv (θ r) ∈ (algebraMap (M.C.presheaf.stalk x) M.C.functionField).range := by
    intro r x hx
    rcases eq_genericPoint_or_isClosed M x with hgen | hcl
    · subst hgen
      obtain ⟨W, hm, f, hf⟩ := TopCat.Presheaf.germ_exist (x := genericPoint M.C) M.C.presheaf (M.ffEquiv (θ r))
      refine ⟨M.C.presheaf.germ W (genericPoint M.C) hm f, ?_⟩
      rw [← hf]
      change (M.C.presheaf.stalkSpecializes (genericPoint_specializes (genericPoint M.C)))
        ((M.C.presheaf.germ W (genericPoint M.C) hm) f) = _
      rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
    · have hxc : x ∈ closedPoints M.C := hcl
      have hvS : M.placeEquiv ⟨x, hxc⟩ ∈ S := (mem_goodOpen_iff M S hS x).1 hx hxc
      have hmem : θ r ∈ (M.placeOfPoint ⟨x, hxc⟩).toValuationSubring.toSubring := hθ r _ hvS
      rw [← M.range_stalk_eq ⟨x, hxc⟩] at hmem
      obtain ⟨s, hs⟩ := hmem
      refine ⟨s, ?_⟩
      rw [← hs]
      simp

  have hsec := fun r : R =>
    AlgebraicGeometry.Scheme.existsUnique_section_algebraMap_germ_eq_of_forall_mem_range
      (goodOpen M S hS) (M.ffEquiv (θ r)) (hreg r)
  choose Θf hΘf hΘu using hsec
  refine ⟨{ toFun := Θf, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ },
    fun r x hx => hΘf r x hx, fun r u hu => hΘu r u hu⟩
  · exact (hΘu 1 1 fun x hx => by rw [map_one, map_one, map_one, map_one]).symm
  · intro a b
    exact (hΘu (a * b) (Θf a * Θf b) fun x hx => by
      rw [map_mul, map_mul, hΘf a x hx, hΘf b x hx, map_mul, map_mul]).symm
  · exact (hΘu 0 0 fun x hx => by rw [map_zero, map_zero, map_zero, map_zero]).symm
  · intro a b
    exact (hΘu (a + b) (Θf a + Θf b) fun x hx => by
      rw [map_add, map_add, hΘf a x hx, hΘf b x hx, map_add, map_add]).symm

end Sections

section PieceHelpers

theorem hom_eq_toSpecΓ {X : Scheme.{0}} {R : CommRingCat.{0}} (f : X ⟶ Spec R) :
    f = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ f.appTop) := by
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem val_fromSpec {M : Scheme.{0}} {U : M.Opens} (hU : IsAffineOpen U)
    (σ : Γ(M, U) ⟶ CommRingCat.of ℂ)
    (h : ⊤ ≤ (Spec.map σ ≫ hU.fromSpec) ⁻¹ᵁ U) (a : Γ(M, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Spec.map σ ≫ hU.fromSpec).appLE U ⊤ h) a) = σ a := by
  rw [Scheme.Hom.comp_appLE, hU.fromSpec_app_self]
  have e1 : (Spec (M.presheaf.obj (op U))).presheaf.map (eqToHom hU.fromSpec_preimage_self).op ≫
      (Spec.map σ).appLE (hU.fromSpec ⁻¹ᵁ U) ⊤ h = (Spec.map σ).appTop := by
    rw [Scheme.Hom.map_appLE]
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  have key : (((Scheme.ΓSpecIso (M.presheaf.obj (op U))).inv ≫
      (Spec (M.presheaf.obj (op U))).presheaf.map (eqToHom hU.fromSpec_preimage_self).op) ≫
        (Spec.map σ).appLE (hU.fromSpec ⁻¹ᵁ U) ⊤ h) ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom = σ := by
    simp only [Category.assoc]
    rw [← Category.assoc ((Spec (M.presheaf.obj (op U))).presheaf.map _), e1, Scheme.ΓSpecIso_naturality]
    erw [Iso.inv_hom_id_assoc]
  have := congrFun (congrArg (fun k => (CommRingCat.Hom.hom k : _ → _)) key) a
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
  exact this

theorem fromSpec_comp_eq_SpecMap {Y : Scheme.{0}} {R : CommRingCat.{0}} (pY : Y ⟶ Spec R) (U : Y.Opens) (hU : IsAffineOpen U) :
    hU.fromSpec ≫ pY = Spec.map ((Scheme.ΓSpecIso R).inv ≫ pY.appLE ⊤ U le_top) := by
  rw [hom_eq_toSpecΓ (hU.fromSpec ≫ pY)]
  rw [← hU.isoSpec_inv_ι]
  simp only [Scheme.Hom.comp_appTop, Category.assoc, IsAffineOpen.isoSpec_inv_appTop, Scheme.Opens.ι_appTop]

  rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
  congr 1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

  congr 1
  rw [Scheme.Opens.topIso_hom, ← Category.assoc]
  change pY.appLE ⊤ (U.ι ''ᵁ ⊤) le_top ≫ Y.presheaf.map _ = _
  rw [Scheme.Hom.appLE_map]

end PieceHelpers

section Morphism
variable {F : Type} [Field F] [Algebra ℂ F] (M : CurveModel ℂ F)
  {Y : Scheme.{0}} (pY : Y ⟶ Spec (CommRingCat.of ℂ))
  (w : Place ℂ F → {P : Spec (CommRingCat.of ℂ) ⟶ Y // P ≫ pY = 𝟙 _})

theorem exists_hom_piece (U : Y.Opens) (hU : IsAffineOpen U)
    (S : Set (Place ℂ F)) (hS : Sᶜ.Finite) (hSU : ∀ v ∈ S, ⊤ ≤ (w v).1 ⁻¹ᵁ U)
    (θ : letI := pY.sectionsAlgebra U; Γ(Y, U) →+* F)
    (hθ : ∀ (φ : Γ(Y, U)) (v : Place ℂ F) (h : ⊤ ≤ (w v).1 ⁻¹ᵁ U),
      θ φ ∈ v.toValuationSubring ∧
        Place.evalAt v (θ φ) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((w v).1.appLE U ⊤ h) φ))
    (hθc : letI := pY.sectionsAlgebra U; ∀ c : ℂ, θ (algebraMap ℂ Γ(Y, U) c) = algebraMap ℂ F c)
    (Θ : Γ(Y, U) →+* Γ(M.C, goodOpen M S hS))
    (hΘ : ∀ (φ : Γ(Y, U)) (x : M.C) (hx : x ∈ goodOpen M S hS),
        algebraMap (M.C.presheaf.stalk x) M.C.functionField
          (M.C.presheaf.germ (goodOpen M S hS) x hx (Θ φ)) = M.ffEquiv (θ φ))
    (hΘu : ∀ (φ : Γ(Y, U)) (u : Γ(M.C, goodOpen M S hS)),
        (∀ (x : M.C) (hx : x ∈ goodOpen M S hS),
          algebraMap (M.C.presheaf.stalk x) M.C.functionField
            (M.C.presheaf.germ (goodOpen M S hS) x hx u) = M.ffEquiv (θ φ)) → u = Θ φ) :
    ∃ W : (goodOpen M S hS : Scheme.{0}) ⟶ Y,
      W ≫ pY = (goodOpen M S hS).ι ≫ M.toBase ∧
      ∀ (p : {p : Spec (CommRingCat.of ℂ) ⟶ M.C // p ≫ M.toBase = 𝟙 _})
        (q : Spec (CommRingCat.of ℂ) ⟶ (goodOpen M S hS : Scheme.{0})), q ≫ (goodOpen M S hS).ι = p.1 →
        q ≫ W = (w (M.pointEquivPlace p)).1 := by
  classical
  letI algU : Algebra ℂ Γ(Y, U) := pY.sectionsAlgebra U

  have hVne : ∀ (x : M.C), x ∈ goodOpen M S hS → (genericPoint M.C) ∈ goodOpen M S hS := fun x hx =>
    ((genericPoint_spec M.C).mem_open_set_iff (goodOpen M S hS).2).2 ⟨x, Set.mem_univ _, hx⟩

  let Θ' : Γ(Y, U) →+* Γ((goodOpen M S hS : Scheme.{0}), ⊤) := (goodOpen M S hS).topIso.inv.hom.comp Θ
  let W : (goodOpen M S hS : Scheme.{0}) ⟶ Y :=
    (goodOpen M S hS : Scheme.{0}).toSpecΓ ≫ Spec.map (CommRingCat.ofHom Θ') ≫ hU.fromSpec

  have hconst : ∀ c : ℂ, Θ (algebraMap ℂ Γ(Y, U) c) =
      (M.toBase.appLE ⊤ (goodOpen M S hS) le_top) ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c) := by
    intro c
    refine (hΘu (algebraMap ℂ Γ(Y, U) c) _ fun x hx => ?_).symm
    rw [hθc, M.ffEquiv_algebraMap]

    change (M.C.presheaf.stalkSpecializes (genericPoint_specializes x))
      ((M.C.presheaf.germ (goodOpen M S hS) x hx)
        ((M.C.presheaf.map (homOfLE (le_top : goodOpen M S hS ≤ ⊤)).op)
          ((M.toBase.app ⊤) ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)))) = _
    rw [TopCat.Presheaf.germ_res_apply, ← CommRingCat.comp_apply (M.C.presheaf.germ _ _ _),
      TopCat.Presheaf.germ_stalkSpecializes]
    rfl

  have hover : W ≫ pY = (goodOpen M S hS).ι ≫ M.toBase := by
    have L3 : ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ pY.appLE ⊤ U le_top) ≫ CommRingCat.ofHom Θ' =
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ ((goodOpen M S hS).ι ≫ M.toBase).appTop := by
      ext c
      change Θ' ((pY.appLE ⊤ U le_top) ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) =
        ((goodOpen M S hS).ι ≫ M.toBase).appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)
      have h1 : (pY.appLE ⊤ U le_top) ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c) = algebraMap ℂ Γ(Y, U) c := rfl
      rw [h1]
      change (goodOpen M S hS).topIso.inv (Θ (algebraMap ℂ Γ(Y, U) c)) = _
      rw [hconst, Scheme.Hom.comp_appTop, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv, CommRingCat.comp_apply]
      change (M.toBase.appLE ⊤ (goodOpen M S hS) le_top ≫ M.C.presheaf.map (eqToHom (goodOpen M S hS).ι_image_top).op)
          ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c) =
        (M.toBase.appLE ⊤ ((goodOpen M S hS).ι ''ᵁ ⊤) le_top) ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)
      rw [Scheme.Hom.appLE_map]
    rw [hom_eq_toSpecΓ ((goodOpen M S hS).ι ≫ M.toBase)]
    simp only [W, Category.assoc]
    rw [fromSpec_comp_eq_SpecMap pY U hU, ← Spec.map_comp]
    exact congrArg (fun f => (goodOpen M S hS : Scheme.{0}).toSpecΓ ≫ Spec.map f) L3
  refine ⟨W, hover, ?_⟩

  intro p q hq
  set x : M.C := p.1.base (IsLocalRing.closedPoint ℂ) with hxdef
  have hxc : x ∈ closedPoints M.C := by
    rw [hxdef, ← pointEquivClosedPoint_apply_coe M.toBase p]; exact (pointEquivClosedPoint M.toBase p).2
  have hpV : ⊤ ≤ p.1 ⁻¹ᵁ goodOpen M S hS := by
    rw [← hq, Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]; simp
  have hxV : x ∈ goodOpen M S hS := (top_le_preimage_iff _ _).1 hpV
  haveI : Nonempty ((goodOpen M S hS : Scheme.{0})) := ⟨⟨x, hxV⟩⟩

  set v : Place ℂ F := M.pointEquivPlace p with hvdef
  have hv : v = M.placeEquiv ⟨x, hxc⟩ := by
    rw [hvdef, AlgebraicCurve.CurveModel.pointEquivPlace_apply, AlgebraicCurve.CurveModel.placeEquiv_apply]
    congr 1
  have hvS : v ∈ S := by rw [hv]; exact (mem_goodOpen_iff M S hS x).1 hxV hxc
  have hwU : ⊤ ≤ (w v).1 ⁻¹ᵁ U := hSU v hvS

  let σ : Γ(Y, U) ⟶ CommRingCat.of ℂ :=
    CommRingCat.ofHom Θ' ≫ q.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
  have hqW : q ≫ W = Spec.map σ ≫ hU.fromSpec := by
    simp only [W, σ, ← Category.assoc]
    congr 1
    rw [Scheme.toSpecΓ_naturality, ← SpecMap_ΓSpecIso_hom, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  have hqWU : ⊤ ≤ (q ≫ W) ⁻¹ᵁ U := by
    rw [hqW, Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]; simp
  have hqW1 : (q ≫ W) ≫ pY = 𝟙 _ := by rw [Category.assoc, hover, ← Category.assoc, hq, p.2]

  have hval_q : ∀ φ : Γ(Y, U),
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((q ≫ W).appLE U ⊤ hqWU) φ) =
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((p.1.appLE (goodOpen M S hS) ⊤ hpV) (Θ φ)) := by
    intro φ
    have h1 : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((q ≫ W).appLE U ⊤ hqWU) φ) = σ φ := by
      have h' : ⊤ ≤ (Spec.map σ ≫ hU.fromSpec) ⁻¹ᵁ U := by rw [← hqW]; exact hqWU
      rw [appLE_congr_hom hqW U ⊤ hqWU h']
      exact val_fromSpec hU σ h' φ
    rw [h1]

    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (q.appTop ((goodOpen M S hS).topIso.inv (Θ φ))) = _
    congr 1
    have h2 : p.1.appLE (goodOpen M S hS) ⊤ hpV =
        (goodOpen M S hS).ι.appLE (goodOpen M S hS) ⊤ (by rw [Scheme.Opens.ι_preimage_self]) ≫ q.appLE ⊤ ⊤ le_top := by
      rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hq]
    rw [h2, CommRingCat.comp_apply]
    congr 1
    · rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]; rfl

  have hval_p : ∀ φ : Γ(Y, U),
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((p.1.appLE (goodOpen M S hS) ⊤ hpV) (Θ φ)) = Place.evalAt v (θ φ) := by
    intro φ
    obtain ⟨hmem, hnu⟩ :=
      AlgebraicCurve.CurveModel.ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace
        M (goodOpen M S hS) (Θ φ) p hpV
    have hgerm : M.ffEquiv.symm (M.C.germToFunctionField (goodOpen M S hS) (Θ φ)) = θ φ := by
      apply M.ffEquiv.injective
      rw [RingEquiv.apply_symm_apply]
      have := hΘ φ (genericPoint M.C) (hVne x hxV)
      rw [← this]
      change _ = (M.C.presheaf.stalkSpecializes (genericPoint_specializes (genericPoint M.C))).hom
        ((M.C.presheaf.germ (goodOpen M S hS) (genericPoint M.C) (hVne x hxV)).hom (Θ φ))
      rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
    rw [hgerm] at hmem hnu
    rw [← hvdef] at hmem hnu
    exact (evalAt_eq_of_sub_algebraMap_mem_nonunits v hmem _ hnu).symm

  refine (AlgebraicGeometry.IsAffineOpen.eq_of_appLE_eq_and_exists_appLE_eq_of_ringHom pY U hU).1
    (q ≫ W) (w v).1 hqW1 (w v).2 hqWU hwU ?_
  ext φ
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((q ≫ W).appLE U ⊤ hqWU) φ) =
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((w v).1.appLE U ⊤ hwU) φ)
  rw [hval_q, hval_p, (hθ φ v hwU).2]

end Morphism

end K6aS3

namespace K6aS3

theorem exists_mem_closedPoints {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType f] [Nonempty X] :
    ∃ x : X, x ∈ closedPoints X := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have h := JacobsonSpace.closure_inter_closedPoints_eq_closure (isOpen_univ.isLocallyClosed (X := X))
  rw [Set.univ_inter, closure_univ] at h
  by_contra hne
  push Not at hne
  have h0 : closedPoints (X : Type) = ∅ := Set.eq_empty_iff_forall_notMem.mpr hne
  rw [h0, closure_empty] at h
  exact Set.empty_ne_univ h
end K6aS3

open K6aS3
open scoped Manifold ContDiff Topology

theorem solution
    (F : Type) [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    (M : CurveModel ℂ F)
    {Y : Scheme.{0}} (pY : Y ⟶ Spec (CommRingCat.of ℂ))
    (w : Place ℂ F → {P : Spec (CommRingCat.of ℂ) ⟶ Y // P ≫ pY = 𝟙 _})
    (U : Y.Opens) (hU : IsAffineOpen U)
    (hA : Set.Finite {v : Place ℂ F | ¬ (⊤ ≤ (w v).1 ⁻¹ᵁ U)})
    (hB : ∀ φ : Γ(Y, U), ∃! ξ : F, ∀ (v : Place ℂ F) (h : ⊤ ≤ (w v).1 ⁻¹ᵁ U),
      ξ ∈ v.toValuationSubring ∧
        Place.evalAt v ξ = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((w v).1.appLE U ⊤ h) φ)) :
    ∃ (V : M.C.Opens),
      (∀ x : M.C, x ∈ V ↔ ∀ hx : x ∈ closedPoints M.C, ⊤ ≤ (w (M.placeEquiv ⟨x, hx⟩)).1 ⁻¹ᵁ U) ∧
      ∃ W : (V : Scheme.{0}) ⟶ Y,
        W ≫ pY = V.ι ≫ M.toBase ∧
        ∀ (p : {p : Spec (CommRingCat.of ℂ) ⟶ M.C // p ≫ M.toBase = 𝟙 _})
          (q : Spec (CommRingCat.of ℂ) ⟶ (V : Scheme.{0})), q ≫ V.ι = p.1 →
          q ≫ W = (w (M.pointEquivPlace p)).1 := by
  classical
  letI := pY.sectionsAlgebra U
  have hS : ({v : Place ℂ F | ⊤ ≤ (w v).1 ⁻¹ᵁ U})ᶜ.Finite := by
    simpa [Set.compl_setOf] using hA
  obtain ⟨θ, hθ, hθc⟩ := exists_ringHom_forall_mem_and_evalAt_eq pY w U hB
  obtain ⟨Θ, hΘ, hΘu⟩ := exists_ringHom_sections M θ {v : Place ℂ F | ⊤ ≤ (w v).1 ⁻¹ᵁ U} hS
    (fun φ v hv => (hθ φ v hv).1)
  obtain ⟨W, hover, hpt⟩ := exists_hom_piece M pY w U hU {v : Place ℂ F | ⊤ ≤ (w v).1 ⁻¹ᵁ U} hS
    (fun v hv => hv) θ hθ hθc Θ hΘ hΘu
  exact ⟨goodOpen M _ hS, fun x => mem_goodOpen_iff M _ hS x, W, hover, hpt⟩

end
end S_AlgebraicCurve_CurveModel_exists_opens_hom_comp_eq_of_existsUnique_evalAt_eq_appLE
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_exists_opens_hom_comp_eq_of_existsUnique_evalAt_eq_appLE (solution)
