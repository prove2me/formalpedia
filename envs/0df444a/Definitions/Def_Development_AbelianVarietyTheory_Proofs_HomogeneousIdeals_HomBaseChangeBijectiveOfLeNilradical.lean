-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:20:32.045168+00:00
-- url     : https://prove2.me/theorems/e79a9763-679a-4911-8e24-02d0e9ccef2c
-- title:
--   Hom Base Change Bijective Of Le Nilradical
-- statement:
--   Definitions and structural lemmas for Hom Base Change Bijective Of Le Nilradical, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HomBaseChangeBijectiveOfLeNilradical.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_appTop_comp_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_chi_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_coord_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_coord_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_cr_iso_bij
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_isUnit_single_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_ringHom_ext_ZU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
universe u
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open AddMonoidAlgebra (single)
namespace GlobalTheory
namespace SplitTorus
section Points
variable {S : Scheme.{u}} {X Y Z : Type u} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  {T T' : Over S}
def val (g : T ⟶ splitTorus S X) (a : X) : Γ(T.left, ⊤) := (coord g).hom (single a 1)
theorem val_eq (g : T ⟶ splitTorus S X) (a : X) : val g a = g.left.appTop.hom (chi X a) := by
  rw [val, chi, ← Category.comp_id g, coord_comp, Category.comp_id]; rfl
theorem val_id (a : X) : val (𝟙 (splitTorus S X)) a = chi X a := rfl
theorem val_comp (h : T' ⟶ T) (g : T ⟶ splitTorus S X) (a : X) :
    val (h ≫ g) a = h.left.appTop.hom (val g a) := by
  rw [val, coord_comp]; rfl
theorem val_add (g : T ⟶ splitTorus S X) (a b : X) : val g (a + b) = val g a * val g b := by
  rw [val, val, val, ← map_mul, AddMonoidAlgebra.single_mul_single, _root_.mul_one]
theorem isUnit_val (g : T ⟶ splitTorus S X) (a : X) : IsUnit (val g a) :=
  (isUnit_single_one (R := ULift.{u} ℤ) a).map _
theorem hom_ext {g g' : T ⟶ splitTorus S X} (h : ∀ a, val g a = val g' a) : g = g' := by
  apply coord_injective
  ext1
  exact ringHom_ext_ZU h
theorem mul_left_comp_fst {S' : Scheme.{u}} (G : Over S) [GrpObj G] (f : S' ⟶ S) {T : Over S'}
    (x y : T ⟶ (Over.pullback f).obj G) (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G)
    (hx : x₀.left = x.left ≫ pullback.fst G.hom f) (hy : y₀.left = y.left ≫ pullback.fst G.hom f) :
    (x₀ * y₀).left = (x * y).left ≫ pullback.fst G.hom f := by
  have A : ∀ {X Y : Over S} (a : X ⟶ Y),
      ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left :=
    fun a => pullback.lift_fst _ _ _
  let z : T ⟶ (Over.pullback f).obj (G ⊗ G) :=
    lift x y ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G
  have z₁ : z ≫ (Over.pullback f).map (fst G G) = x := by simp [z]
  have z₂ : z ≫ (Over.pullback f).map (snd G G) = y := by simp [z]
  have hz : (lift x₀ y₀).left = z.left ≫ pullback.fst (G ⊗ G).hom f := by
    apply pullback.hom_ext
    · show (lift x₀ y₀ ≫ fst G G).left = _ ≫ (fst G G).left
      rw [lift_fst, hx, Category.assoc, ← A, ← Category.assoc, ← Over.comp_left, z₁]
    · show (lift x₀ y₀ ≫ snd G G).left = _ ≫ (snd G G).left
      rw [lift_snd, hy, Category.assoc, ← A, ← Category.assoc, ← Over.comp_left, z₂]
  have hxy : x * y = z ≫ (Over.pullback f).map μ[G] := by
    rw [Hom.mul_def, Functor.obj.μ_def, ← Category.assoc]
  rw [hxy, Over.comp_left, Category.assoc, A, ← Category.assoc, ← hz]
  rfl
theorem specMap_appTop_apply {A B : CommRingCat.{u}} (φ : A ⟶ B) (c : A) :
    (Spec.map φ).appTop.hom ((Scheme.ΓSpecIso A).inv.hom c) =
      (Scheme.ΓSpecIso B).inv.hom (φ.hom c) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.ΓSpecIso_inv_naturality]
theorem aff_mul {R A : CommRingCat.{u}} [Bialgebra R A] {W : Over (Spec R)}
    (x y : W ⟶ (Spec A).asOver (Spec R)) {a : A} (ha : IsGroupLikeElem R a) :
    (x * y).left.appTop.hom ((Scheme.ΓSpecIso A).inv.hom a) =
      x.left.appTop.hom ((Scheme.ΓSpecIso A).inv.hom a) *
        y.left.appTop.hom ((Scheme.ΓSpecIso A).inv.hom a) := by
  let l₀ : W.left ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (Spec.map (CommRingCat.ofHom (algebraMap R A))) := (lift x y).left
  let x' : W.left ⟶ Spec A := x.left
  let y' : W.left ⟶ Spec A := y.left
  let m : W.left ⟶ Spec A := (x * y).left
  have h0 : m = (l₀ ≫ (pullbackSpecIso R A A).hom) ≫
      Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom R A)) := by
    rw [Category.assoc]; rfl
  have h1 : x' = (l₀ ≫ (pullbackSpecIso R A A).hom) ≫
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := by
    rw [Category.assoc, pullbackSpecIso_hom_fst]
    exact congrArg (·.left) (lift_fst x y).symm
  have h2 : y' = (l₀ ≫ (pullbackSpecIso R A A).hom) ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A)) := by
    rw [Category.assoc, pullbackSpecIso_hom_snd]
    exact congrArg (·.left) (lift_snd x y).symm
  have key : ∀ {B : CommRingCat.{u}} (l : W.left ⟶ Spec B) (φ₀ φ₁ φ₂ : A ⟶ B),
      φ₀.hom a = φ₁.hom a * φ₂.hom a →
      (l ≫ Spec.map φ₀).appTop.hom ((Scheme.ΓSpecIso A).inv.hom a) =
        (l ≫ Spec.map φ₁).appTop.hom ((Scheme.ΓSpecIso A).inv.hom a) *
          (l ≫ Spec.map φ₂).appTop.hom ((Scheme.ΓSpecIso A).inv.hom a) := by
    intro B l φ₀ φ₁ φ₂ h
    rw [appTop_comp_apply, appTop_comp_apply, appTop_comp_apply, specMap_appTop_apply,
      specMap_appTop_apply, specMap_appTop_apply, h, map_mul, map_mul]
  change m.appTop.hom _ = x'.appTop.hom _ * y'.appTop.hom _
  rw [h0, h1, h2]
  exact key _ _ _ _ (by simp [ha.comul_eq_tmul_self])
theorem val_mul (x y : T ⟶ splitTorus S X) (a : X) : val (x * y) a = val x a * val y a := by
  let p : ∀ (z : T ⟶ splitTorus S X), Over.mk (T.hom ≫ toZ S) ⟶ splitTorusAff ZU X := fun z =>
    Over.homMk (z.left ≫ torusFst S X) (specULiftZIsTerminal.hom_ext _ _)
  have h := mul_left_comp_fst (splitTorusAff ZU X) (toZ S) x y (p x) (p y) rfl rfl
  have e := aff_mul (p x) (p y) (AddMonoidAlgebra.isGroupLikeElem_single_one (R := ZU.{u}) (A := ZU.{u}) a)
  rw [h] at e
  exact e
theorem val_one (a : X) : val (1 : T ⟶ splitTorus S X) a = 1 := by
  have h := val_mul (1 : T ⟶ splitTorus S X) 1 a
  rw [_root_.mul_one] at h
  exact (isUnit_val _ a).mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
def ofCoord (c : torusRing ZU X ⟶ Γ(T.left, ⊤)) : T ⟶ splitTorus S X :=
  Over.homMk (pullback.lift (T.left.toSpecΓ ≫ Spec.map c) T.hom (specULiftZIsTerminal.hom_ext _ _))
    (pullback.lift_snd _ _ _)
theorem coord_ofCoord (c : torusRing ZU X ⟶ Γ(T.left, ⊤)) : coord (ofCoord c) = c := by
  have : (ofCoord c).left ≫ torusFst S X = T.left.toSpecΓ ≫ Spec.map c := pullback.lift_fst _ _ _
  rw [coord, this, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  simp
def ofVal (c : X →+ Additive Γ(T.left, ⊤)ˣ) : T ⟶ splitTorus S X :=
  ofCoord (CommRingCat.ofHom (AddMonoidAlgebra.liftNCRingHom
    ((Int.castRingHom Γ(T.left, ⊤)).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom)
    ((Units.coeHom _).comp (AddMonoidHom.toMultiplicativeLeft c)) (fun _ _ => Commute.all _ _)))
theorem val_ofVal (c : X →+ Additive Γ(T.left, ⊤)ˣ) (a : X) :
    val (ofVal c) a = (Additive.toMul (c a)).val := by
  rw [val, ofVal, coord_ofCoord]
  simp
def valHom (g : T ⟶ splitTorus S X) : X →+ Additive Γ(T.left, ⊤)ˣ :=
  AddMonoidHom.mk' (fun a => Additive.ofMul (isUnit_val g a).unit) fun a b => by
    rw [← ofMul_mul]; congr 1; ext; simp [val_add]
@[simp] theorem valHom_apply (g : T ⟶ splitTorus S X) (a : X) :
    (Additive.toMul (valHom g a)).val = val g a := rfl
def pointsEquiv (T : Over S) (X : Type u) [AddCommGroup X] :
    (T ⟶ splitTorus S X) ≃ (X →+ Additive Γ(T.left, ⊤)ˣ) where
  toFun := valHom
  invFun := ofVal
  left_inv g := hom_ext fun a => by rw [val_ofVal, valHom_apply]
  right_inv c := by
    ext a
    exact val_ofVal c a
@[simp] theorem pointsEquiv_apply (g : T ⟶ splitTorus S X) (a : X) :
    (Additive.toMul (pointsEquiv T X g a)).val = g.left.appTop.hom (chi X a) := val_eq g a
theorem pointsEquiv_mul (x y : T ⟶ splitTorus S X) :
    pointsEquiv T X (x * y) = pointsEquiv T X x + pointsEquiv T X y := by
  ext a
  exact val_mul x y a
def pointsMulEquiv (T : Over S) (X : Type u) [AddCommGroup X] :
    (T ⟶ splitTorus S X) ≃* Multiplicative (X →+ Additive Γ(T.left, ⊤)ˣ) where
  toEquiv := (pointsEquiv T X).trans Multiplicative.ofAdd
  map_mul' x y := congrArg Multiplicative.ofAdd (pointsEquiv_mul x y)
instance isCommMonObj (S : Scheme.{u}) (X : Type u) [AddCommGroup X] :
    IsCommMonObj (splitTorus S X) where
  mul_comm := by
    have h : ∀ {W : Over S} (x y : W ⟶ splitTorus S X), x * y = y * x := fun x y =>
      hom_ext fun a => by rw [val_mul, val_mul, _root_.mul_comm]
    have := h (snd (splitTorus S X) (splitTorus S X)) (fst _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, lift_snd_fst] at this
    exact this
theorem isMonHom_of_val {G : Over S} [GrpObj G] (f : G ⟶ splitTorus S X)
    (h : ∀ a, val (μ[G] ≫ f) a = val (fst G G ≫ f) a * val (snd G G ≫ f) a) : IsMonHom f := by
  have hm : μ[G] ≫ f = (f ⊗ₘ f) ≫ μ := by
    refine hom_ext fun a => ?_
    rw [h, ← val_mul, Hom.mul_def]
    congr 2
  refine ⟨?_, hm⟩
  have e : (η[G] ≫ f) * (η[G] ≫ f) = η[G] ≫ f := by
    rw [Hom.mul_def, ← lift_map, Category.assoc, ← hm, ← Category.assoc]
    congr 1
    simpa [Hom.mul_def, Hom.one_def] using _root_.mul_one (1 : 𝟙_ (Over S) ⟶ G)
  have e' : η[G] ≫ f = 1 := by simpa using e
  rw [e', Hom.one_def]; simp
def torusMap (S : Scheme.{u}) (φ : Y →+ X) : splitTorus S X ⟶ splitTorus S Y :=
  ofVal ((valHom (𝟙 (splitTorus S X))).comp φ)
theorem val_torusMap (φ : Y →+ X) (b : Y) : val (torusMap S φ) b = chi X (φ b) := by
  rw [torusMap, val_ofVal]; rfl
theorem val_comp_torusMap (g : T ⟶ splitTorus S X) (φ : Y →+ X) (b : Y) :
    val (g ≫ torusMap S φ) b = val g (φ b) := by
  rw [val_comp, val_torusMap, ← val_eq]
instance isMonHom_torusMap (φ : Y →+ X) : IsMonHom (torusMap S φ) :=
  isMonHom_of_val _ fun a => by
    rw [val_comp_torusMap, val_comp_torusMap, val_comp_torusMap, ← val_mul, Hom.mul_def, lift_fst_snd,
      Category.id_comp]
end Points
section Ring
variable {A : Type*} [CommRing A] {X : Type*}
open Classical in

theorem coeff_mul_coeff {u : AddMonoidAlgebra A X} (hu : IsGroupLikeElem A u) (x y : X) :
    u.coeff x * u.coeff y = if x = y then u.coeff x else 0 := by
  let c : X → AddMonoidAlgebra A X →ₗ[A] A := fun x =>
    { toFun := fun v => v.coeff x, map_add' := by simp, map_smul' := by simp }
  let L : AddMonoidAlgebra A X ⊗[A] AddMonoidAlgebra A X →ₗ[A] A :=
    TensorProduct.lift ((LinearMap.mul A A).compl₁₂ (c x) (c y))
  have hc : ∀ v w, L (v ⊗ₜ w) = v.coeff x * w.coeff y := fun v w => rfl
  have hL : ∀ v : AddMonoidAlgebra A X,
      L (Coalgebra.comul (R := A) v) = if x = y then v.coeff x else 0 := by
    intro v
    induction v using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb]; split_ifs <;> simp
    | single a r =>
      simp [hc, Finsupp.single_apply]
      aesop
  rw [← hL, hu.comul_eq_tmul_self, hc]
theorem sum_coeff {u : AddMonoidAlgebra A X} (hu : IsGroupLikeElem A u) :
    ∑ x ∈ u.coeff.support, u.coeff x = 1 := by
  have hL : ∀ v : AddMonoidAlgebra A X,
      Coalgebra.counit (R := A) v = v.coeff.sum fun _ r => r := by
    intro v
    induction v using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add, ha, hb]; simp [Finsupp.sum_add_index']
    | single a r => simp
  rw [← hu.counit_eq_one, hL]; rfl
theorem isIdempotentElem_coeff {u : AddMonoidAlgebra A X} (hu : IsGroupLikeElem A u) (x : X) :
    IsIdempotentElem (u.coeff x) := by
  simpa [IsIdempotentElem] using coeff_mul_coeff hu x x
theorem eq_single_of_coeff_eq_zero {u : AddMonoidAlgebra A X} (hu : IsGroupLikeElem A u) (x : X)
    (h : ∀ y, y ≠ x → u.coeff y = 0) : u = single x 1 := by
  have h1 : u.coeff x = 1 := by
    rw [← sum_coeff hu, Finset.sum_eq_single x (fun y _ hy => h y hy)
      (fun hx => Finsupp.notMem_support_iff.1 hx)]
  ext y
  by_cases hy : y = x
  · subst hy; simp [h1]
  · simp [h y hy, Finsupp.single_apply, Ne.symm hy]
theorem isGroupLikeElem_iff [Nontrivial A] (hA : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1)
    (u : AddMonoidAlgebra A X) : IsGroupLikeElem A u ↔ ∃ x, u = single x 1 := by
  refine ⟨fun hu => ?_, ?_⟩
  · obtain ⟨x, hx⟩ : ∃ x, u.coeff x ≠ 0 := by
      by_contra! h
      have := sum_coeff hu
      simp [h] at this
    have h1 := (hA _ (isIdempotentElem_coeff hu x)).resolve_left hx
    refine ⟨x, eq_single_of_coeff_eq_zero hu x fun y hy => ?_⟩
    have := coeff_mul_coeff hu y x
    rwa [h1, _root_.mul_one, if_neg hy] at this
  · rintro ⟨x, rfl⟩
    exact AddMonoidAlgebra.isGroupLikeElem_single_one x
theorem single_one_injective [Nontrivial A] :
    Function.Injective fun x : X => (single x 1 : AddMonoidAlgebra A X) := by
  intro x y h
  by_contra hxy
  have := congrArg (fun v : AddMonoidAlgebra A X => v.coeff x) h
  simp [Finsupp.single_apply, Ne.symm hxy] at this
end Ring
section Eval
variable {S : Scheme.{u}} {X : Type u} [AddCommGroup X] {A B : CommRingCat.{u}}
def pull {s : Spec B ⟶ S} (g : Over.mk s ⟶ splitTorus S X) :
    Γ((splitTorus S X).left, ⊤) →+* B :=
  (Scheme.ΓSpecIso B).hom.hom.comp (Scheme.Hom.appTop (X := Spec B) g.left).hom
theorem pull_chi {s : Spec B ⟶ S} (g : Over.mk s ⟶ splitTorus S X) (a : X) :
    pull g (chi X a) = (Scheme.ΓSpecIso B).hom.hom (val g a) := by
  rw [val_eq]; rfl
theorem pull_ext {s : Spec B ⟶ S} {g g' : Over.mk s ⟶ splitTorus S X}
    (h : ∀ a, pull g (chi X a) = pull g' (chi X a)) : g = g' :=
  hom_ext fun a => (cr_iso_bij (Scheme.ΓSpecIso B)).1 (by rw [← pull_chi, ← pull_chi, h])
theorem pull_mul_chi {s : Spec B ⟶ S} (g g' : Over.mk s ⟶ splitTorus S X) (a : X) :
    pull (g * g') (chi X a) = pull g (chi X a) * pull g' (chi X a) := by
  rw [pull_chi, pull_chi, pull_chi, val_mul]; exact map_mul _ _ _
theorem pull_one_chi {s : Spec B ⟶ S} (a : X) :
    pull (1 : Over.mk s ⟶ splitTorus S X) (chi X a) = 1 := by
  rw [pull_chi, val_one]; exact map_one _
variable (X) in

def univPt (t : Spec A ⟶ S) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A (torusRing A X))) ≫ t) ⟶ splitTorus S X :=
  ofCoord (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom X
    ((Int.castRingHom A).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom)) ≫
      (Scheme.ΓSpecIso (torusRing A X)).inv)
def ev (t : Spec A ⟶ S) : Γ((splitTorus S X).left, ⊤) →+* AddMonoidAlgebra A X :=
  pull (univPt X t)
theorem ev_chi (t : Spec A ⟶ S) (a : X) : ev t (chi X a) = single a 1 := by
  rw [ev, pull_chi, val, univPt, coord_ofCoord]
  erw [← CommRingCat.comp_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp
def ptOf (t : Spec A ⟶ S) (ψ : AddMonoidAlgebra A X →+* B) {s : Spec B ⟶ S}
    (hs : Spec.map (CommRingCat.ofHom (ψ.comp (algebraMap A _))) ≫ t = s) :
    Over.mk s ⟶ splitTorus S X :=
  (Over.homMk (Spec.map (CommRingCat.ofHom (R := torusRing A X) ψ))
    (by rw [← hs]; simp [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]) :
      Over.mk s ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A (torusRing A X))) ≫ t)) ≫
    univPt X t
theorem pull_ptOf (t : Spec A ⟶ S) (ψ : AddMonoidAlgebra A X →+* B) {s : Spec B ⟶ S}
    (hs : Spec.map (CommRingCat.ofHom (ψ.comp (algebraMap A _))) ≫ t = s)
    (u : Γ((splitTorus S X).left, ⊤)) : pull (ptOf t ψ hs) u = ψ (ev t u) := by
  let p : Spec (torusRing A X) ⟶ (splitTorus S X).left := (univPt X t).left
  change (Scheme.ΓSpecIso B).hom.hom
    ((Spec.map (CommRingCat.ofHom (R := torusRing A X) ψ) ≫ p).appTop.hom u) =
      ψ ((Scheme.ΓSpecIso (torusRing A X)).hom.hom (p.appTop.hom u))
  rw [appTop_comp_apply, ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality]
  rfl
theorem ev_comp (t : Spec A ⟶ S) (φ : A ⟶ B) (u : Γ((splitTorus S X).left, ⊤)) :
    ev (Spec.map φ ≫ t) u = AddMonoidAlgebra.mapRingHom X φ.hom (ev t u) := by
  have hs : Spec.map (CommRingCat.ofHom (S := torusRing B X)
      ((AddMonoidAlgebra.mapRingHom X φ.hom).comp (algebraMap A _))) ≫ t =
      Spec.map (CommRingCat.ofHom (algebraMap B (torusRing B X))) ≫ Spec.map φ ≫ t := by
    rw [← Spec.map_comp_assoc]
    congr 2
    ext; simp
  have e : univPt X (Spec.map φ ≫ t) =
      ptOf (B := torusRing B X) t (AddMonoidAlgebra.mapRingHom X φ.hom) hs :=
    pull_ext fun a => by
      rw [pull_ptOf, ev_chi]
      exact (ev_chi _ a).trans (by simp)
  rw [ev, e, pull_ptOf]
theorem eq_of_ev {u v : Γ((splitTorus S X).left, ⊤)}
    (h : ∀ (A : CommRingCat.{u}) (t : Spec A ⟶ S), ev t u = ev t v) : u = v := by
  refine (splitTorus S X).left.affineOpenCover.openCover.ext_elem u v fun i => ?_
  let j := (splitTorus S X).left.affineOpenCover.f i
  let B := (splitTorus S X).left.affineOpenCover.X i
  let g : Over.mk (j ≫ (splitTorus S X).hom) ⟶ splitTorus S X := Over.homMk j
  let ψ : AddMonoidAlgebra B X →ₐ[B] B := AddMonoidAlgebra.lift B B X
    { toFun := fun a => pull g (chi X a.toAdd)
      map_one' := by simp [chi_zero]
      map_mul' := fun a b => by
        rw [toAdd_mul, ← val_id, val_add, map_mul]; rfl }
  have hs : Spec.map (CommRingCat.ofHom (ψ.toRingHom.comp (algebraMap B _))) ≫
      (j ≫ (splitTorus S X).hom) = j ≫ (splitTorus S X).hom := by
    have : ψ.toRingHom.comp (algebraMap B _) = RingHom.id B := by ext; simp
    rw [this]; simp
  have e : g = ptOf _ ψ.toRingHom hs := pull_ext fun a => by
    rw [pull_ptOf, ev_chi]; simp [ψ]
  have : pull g u = pull g v := by rw [e, pull_ptOf, pull_ptOf, h]
  exact (cr_iso_bij (Scheme.ΓSpecIso B)).1 this
theorem isGroupLikeElem_ev {u : Γ((splitTorus S X).left, ⊤)} (hu : IsUnit u)
    (hm : ∀ (T : Over S) (x y : T ⟶ splitTorus S X),
      (x * y).left.appTop.hom u = x.left.appTop.hom u * y.left.appTop.hom u)
    (t : Spec A ⟶ S) : IsGroupLikeElem A (ev t u) := by
  have hm' : ∀ {B : CommRingCat.{u}} {s : Spec B ⟶ S} (x y : Over.mk s ⟶ splitTorus S X),
      pull (x * y) u = pull x u * pull y u := fun {B s} x y =>
    (congrArg (Scheme.ΓSpecIso B).hom.hom (hm _ x y)).trans (map_mul _ _ _)
  have hs : ∀ {B : Type u} [CommRing B] [Algebra A B] (ψ : AddMonoidAlgebra A X →ₐ[A] B),
      Spec.map (CommRingCat.ofHom (ψ.toRingHom.comp (algebraMap A _))) ≫ t =
        Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ t := fun ψ => by
    congr 3; exact ψ.comp_algebraMap
  constructor
  · have e : ptOf (B := .of A) t _ (hs (Bialgebra.counitAlgHom A (AddMonoidAlgebra A X))) = 1 :=
      pull_ext fun a => by rw [pull_ptOf, ev_chi, pull_one_chi]; simp
    have h1 := hm' (1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A A)) ≫ t) ⟶ _) 1
    rw [_root_.mul_one] at h1
    have h2 := (hu.map _).mul_left_cancel (h1.symm.trans (_root_.mul_one _).symm)
    rw [← e, pull_ptOf] at h2
    exact h2
  · let B : CommRingCat.{u} := .of (AddMonoidAlgebra A X ⊗[A] AddMonoidAlgebra A X)
    have e : ptOf (B := B) t _ (hs (Bialgebra.comulAlgHom A (AddMonoidAlgebra A X))) =
        ptOf (B := B) t _ (hs Algebra.TensorProduct.includeLeft) *
          ptOf (B := B) t _ (hs Algebra.TensorProduct.includeRight) :=
      pull_ext fun a => by
        rw [pull_mul_chi, pull_ptOf, pull_ptOf, pull_ptOf, ev_chi]; simp [B]
    have h1 := hm' (ptOf (B := B) t _ (hs Algebra.TensorProduct.includeLeft))
      (ptOf (B := B) t _ (hs Algebra.TensorProduct.includeRight))
    rw [← e, pull_ptOf, pull_ptOf, pull_ptOf] at h1
    simpa [B] using h1
end Eval
section Characters
variable {S : Scheme.{u}} {X Y Z : Type u} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
theorem chi_injective [Nonempty S] : Function.Injective (chi (S := S) X) := by
  intro a b h
  obtain ⟨s⟩ := ‹Nonempty S›
  have := congrArg (ev (S.fromSpecResidueField s)) h
  rw [ev_chi, ev_chi] at this
  exact single_one_injective this
theorem exists_eq_chi_of_ev [ConnectedSpace S] {u : Γ((splitTorus S X).left, ⊤)}
    (hu : ∀ (A : CommRingCat.{u}) (t : Spec A ⟶ S), IsGroupLikeElem A (ev t u)) :
    ∃ a, u = chi X a := by
  have h0 : ∀ s : S, ∃ a, ev (S.fromSpecResidueField s) u = single a 1 := fun s =>
    (isGroupLikeElem_iff (fun e he => IsIdempotentElem.iff_eq_zero_or_one.1 he) _).1 (hu _ _)
  choose idx hidx using h0
  have hA : ∀ (K : Type u) [Field K] (t : Spec (.of K) ⟶ S),
      ev t u = single (idx (t (IsLocalRing.closedPoint K))) 1 := fun K _ t => by
    conv_lhs => rw [← Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S t]
    rw [ev_comp, hidx]; simp
  have hB : ∀ (A : CommRingCat.{u}) (t : Spec A ⟶ S) (p : Spec A) (a : X),
      (ev t u).coeff a ∉ p.asIdeal ↔ idx (t p) = a := fun A t p a => by
    haveI := p.isPrime
    let φ : A ⟶ .of p.asIdeal.ResidueField := CommRingCat.ofHom (algebraMap _ _)
    have h1 := hA p.asIdeal.ResidueField (Spec.map φ ≫ t)
    have h2 : (Spec.map φ ≫ t) (IsLocalRing.closedPoint p.asIdeal.ResidueField) = t p := by
      refine (Scheme.Hom.comp_apply _ _ _).trans (congrArg t ?_)
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap A p.asIdeal.ResidueField) (IsLocalRing.maximalIdeal _) = _
      rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot,
        Ideal.ker_algebraMap_residueField]
    rw [h2, ev_comp] at h1
    have h3 := congrArg (fun v => v.coeff a) h1
    simp only [AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.coeff_single] at h3
    rw [← Ideal.algebraMap_residueField_eq_zero]
    change ¬ φ.hom _ = 0 ↔ _
    rw [h3]
    classical
    simp [Finsupp.single_apply]
  have hloc : IsLocallyConstant idx := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro a
    rw [isOpen_iff_forall_mem_open]
    intro s hs
    obtain ⟨i, p, rfl⟩ := S.affineOpenCover.openCover.exists_eq s
    let t := S.affineOpenCover.f i
    haveI : IsOpenImmersion t := S.affineOpenCover.map_prop i
    refine ⟨t '' {q | (ev t u).coeff a ∉ q.asIdeal}, ?_, ?_, p, ?_, rfl⟩
    · rintro _ ⟨q, hq, rfl⟩
      exact (hB _ t q a).1 hq
    · exact t.isOpenEmbedding.isOpenMap _ (PrimeSpectrum.basicOpen _).isOpen
    · exact (hB _ t p a).2 hs
  obtain ⟨s₀⟩ : Nonempty S := inferInstance
  refine ⟨idx s₀, eq_of_ev fun A t => ?_⟩
  rw [ev_chi]
  refine eq_single_of_coeff_eq_zero (hu A t) _ fun y hy => ?_
  have hn : IsNilpotent ((ev t u).coeff y) := by
    rw [nilpotent_iff_mem_prime]
    intro p hp
    by_contra h
    exact hy (((hB A t ⟨p, hp⟩ y).1 h).symm.trans (hloc.apply_eq_of_preconnectedSpace _ _))
  exact (isIdempotentElem_coeff (hu A t) y).eq_zero_of_isNilpotent hn
theorem exists_val_eq_chi [ConnectedSpace S] (f : splitTorus S X ⟶ splitTorus S Y) [IsMonHom f]
    (b : Y) : ∃ a, val f b = chi X a :=
  exists_eq_chi_of_ev fun _ t => isGroupLikeElem_ev (isUnit_val f b) (fun T x y => by
    rw [← val_comp, ← val_comp, ← val_comp, MonObj.mul_comp, val_mul]) t
theorem torusMap_injective [Nonempty S] :
    Function.Injective (torusMap S : (Y →+ X) → (splitTorus S X ⟶ splitTorus S Y)) := by
  intro φ ψ h
  ext b
  apply chi_injective (S := S)
  rw [← val_torusMap, ← val_torusMap, h]
theorem exists_eq_torusMap [ConnectedSpace S] (f : splitTorus S X ⟶ splitTorus S Y) [IsMonHom f] :
    ∃ φ : Y →+ X, f = torusMap S φ := by
  choose φ hφ using exists_val_eq_chi f
  refine ⟨AddMonoidHom.mk' φ fun a b => chi_injective (S := S) ?_, hom_ext fun b => ?_⟩
  · rw [← hφ, val_add, hφ, hφ, ← val_id, ← val_id, ← val_id, val_add]
  · rw [val_torusMap, hφ]; rfl
variable (S X Y) in

def homEquiv [ConnectedSpace S] :
    (Y →+ X) ≃ {f : splitTorus S X ⟶ splitTorus S Y // IsMonHom f} :=
  Equiv.ofBijective (fun φ => ⟨torusMap S φ, inferInstance⟩)
    ⟨fun _ _ h => torusMap_injective (congrArg Subtype.val h), fun ⟨f, _⟩ => by
      obtain ⟨φ, rfl⟩ := exists_eq_torusMap f
      exact ⟨φ, rfl⟩⟩
@[simp] theorem homEquiv_apply [ConnectedSpace S] (φ : Y →+ X) :
    (homEquiv S X Y φ).1 = torusMap S φ := rfl
variable (X) in

def uliftMultiples : X ≃ (ULift.{u} ℤ →+ X) where
  toFun a := (zmultiplesHom X a).comp (AddEquiv.ulift : ULift.{u} ℤ ≃+ ℤ).toAddMonoidHom
  invFun φ := φ (ULift.up 1)
  left_inv a := one_zsmul a
  right_inv φ := by
    ext ⟨n⟩
    change n • φ (ULift.up 1) = _
    rw [← map_zsmul]
    congr 1
    ext
    simp
variable (S X) in

def charactersEquiv [ConnectedSpace S] : X ≃ characters (splitTorus S X) :=
  (uliftMultiples X).trans (homEquiv S X (ULift.{u} ℤ))
end Characters
section BaseChange
variable {S S' : Scheme.{u}} (f : S' ⟶ S) (X Y : Type u) [AddCommGroup X] [AddCommGroup Y]
def bcMap : (splitTorus S' X).left ⟶ (splitTorus S X).left :=
  pullback.lift (torusFst S' X) ((splitTorus S' X).hom ≫ f) (specULiftZIsTerminal.hom_ext _ _)
@[reassoc] theorem bcMap_torusFst : bcMap f X ≫ torusFst S X = torusFst S' X :=
  pullback.lift_fst _ _ _
@[reassoc] theorem bcMap_hom : bcMap f X ≫ (splitTorus S X).hom = (splitTorus S' X).hom ≫ f :=
  pullback.lift_snd _ _ _
theorem chi_eq (a : X) : chi (S := S) X a = (torusFst S X).appTop.hom
    ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (single a 1)) := by
  rw [chi, coord, Over.id_left, Category.id_comp]; rfl
theorem bcMap_appTop_chi (a : X) : (bcMap f X).appTop.hom (chi X a) = chi X a := by
  rw [chi_eq, chi_eq, ← appTop_comp_apply, bcMap_torusFst]
theorem isPullback_bcMap :
    IsPullback (bcMap f X) (splitTorus S' X).hom (splitTorus S X).hom f := by
  have h1 : IsPullback (torusFst S X) (splitTorus S X).hom (splitTorusAff ZU X).hom (toZ S) :=
    IsPullback.of_hasPullback _ _
  have h2 : IsPullback (bcMap f X ≫ torusFst S X) (splitTorus S' X).hom (splitTorusAff ZU X).hom
      (f ≫ toZ S) := by
    rw [bcMap_torusFst, show f ≫ toZ S = toZ S' from specULiftZIsTerminal.hom_ext _ _]
    exact IsPullback.of_hasPullback _ _
  exact h2.of_right (bcMap_hom f X) h1
def bcIso : splitTorus S' X ≅ (Over.pullback f).obj (splitTorus S X) :=
  Over.isoMk (isPullback_bcMap f X).isoPullback (isPullback_bcMap f X).isoPullback_hom_snd
@[reassoc] theorem bcIso_inv_bcMap :
    (bcIso f X).inv.left ≫ bcMap f X = pullback.fst (splitTorus S X).hom f :=
  (isPullback_bcMap f X).isoPullback_inv_fst
variable {X} in
theorem val_comp_bcIso_inv {T : Over S'} (z : T ⟶ (Over.pullback f).obj (splitTorus S X)) (a : X) :
    val (z ≫ (bcIso f X).inv) a =
      (z.left ≫ pullback.fst (splitTorus S X).hom f).appTop.hom (chi X a) := by
  rw [val_eq, ← bcIso_inv_bcMap, ← Category.assoc, appTop_comp_apply _ (bcMap f X),
    bcMap_appTop_chi, Over.comp_left]
instance isMonHom_bcIso_inv : IsMonHom (bcIso f X).inv :=
  isMonHom_of_val _ fun a => by
    let G := (Over.pullback f).obj (splitTorus S X)
    let p : (G ⊗ G ⟶ G) → (Over.mk ((G ⊗ G).hom ≫ f) ⟶ splitTorus S X) := fun z =>
      Over.homMk (z.left ≫ pullback.fst (splitTorus S X).hom f) (by
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        exact congrArg (· ≫ f) (Over.w z))
    have h := mul_left_comp_fst (splitTorus S X) f (fst G G) (snd G G) (p _) (p _) rfl rfl
    have h1 : fst G G * snd G G = μ[G] := by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
    have h2 := val_mul (p (fst G G)) (p (snd G G)) a
    rw [val_eq, val_eq, val_eq, h, h1] at h2
    rw [val_comp_bcIso_inv, val_comp_bcIso_inv, val_comp_bcIso_inv]
    exact h2
instance isMonHom_bcIso_hom : IsMonHom (bcIso f X).hom :=
  haveI : IsMonHom (bcIso f X).symm.hom := isMonHom_bcIso_inv f X
  inferInstanceAs (IsMonHom (bcIso f X).symm.inv)
variable {X Y}
variable (X Y) in

def homBaseChange (g : {g : splitTorus S X ⟶ splitTorus S Y // IsMonHom g}) :
    {g' : (Over.pullback f).obj (splitTorus S X) ⟶ (Over.pullback f).obj (splitTorus S Y) //
      IsMonHom g'} :=
  ⟨(Over.pullback f).map g.1, by have := g.2; infer_instance⟩
end BaseChange
end SplitTorus
end GlobalTheory


