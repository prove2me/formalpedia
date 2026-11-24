-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ModulesTensor
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ModulesTensor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:03.83174+00:00
-- url     : https://prove2.me/theorems/7e93c60e-35cf-467e-ac49-eacf5d0d0527
-- title:
--   Modules Tensor
-- statement:
--   Definitions and structural lemmas for Modules Tensor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ModulesTensor.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory Opposite TensorProduct
universe u v₁ u₁
variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) {R : Cᵒᵖ ⥤ CommRingCat.{u}}
namespace GroundTheory.Arith.SchemeCoh
namespace ModulesTensor
def zeroSieve {M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} {U : Cᵒᵖ} (x : M.obj U) :
    Sieve U.unop where
  arrows _ g := M.map g.op x = 0
  downward_closed {_ _} g hg h := by
    rw [op_comp, PresheafOfModules.map_comp_apply]
    erw [hg]; exact map_zero _
def imSieve {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (φ : M ⟶ N) {U : Cᵒᵖ}
    (y : N.obj U) : Sieve U.unop where
  arrows V g := ∃ x : M.obj (op V), φ.app (op V) x = N.map g.op y
  downward_closed {_ _} g := by
    rintro ⟨x, hx⟩ h
    refine ⟨M.map h.op x, ?_⟩
    rw [PresheafOfModules.naturality_apply, hx]
    change _ = N.map (h ≫ g).op y
    rw [op_comp, PresheafOfModules.map_comp_apply]
variable {J}
variable {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}
lemma zeroSieve_pullback {U : Cᵒᵖ} (x : M.obj U) {V : C} (g : V ⟶ U.unop) :
    (zeroSieve x).pullback g = zeroSieve (M.map g.op x) := by
  ext W h
  change M.map (h ≫ g).op x = 0 ↔ M.map h.op (M.map g.op x) = 0
  rw [op_comp, PresheafOfModules.map_comp_apply]
  exact Iff.rfl
lemma zeroSieve_zero {U : Cᵒᵖ} : zeroSieve (0 : M.obj U) = ⊤ := by
  ext W h
  simp only [Sieve.top_apply, iff_true]
  exact map_zero _
lemma zeroSieve_add {U : Cᵒᵖ} (x y : M.obj U) :
    zeroSieve x ⊓ zeroSieve y ≤ zeroSieve (x + y) := by
  rintro W h ⟨hx, hy⟩
  change M.map h.op (x + y) = 0
  rw [map_add]
  erw [hx, hy]
  exact add_zero _
lemma imSieve_add (φ : M ⟶ N) {U : Cᵒᵖ} (x y : N.obj U) :
    imSieve φ x ⊓ imSieve φ y ≤ imSieve φ (x + y) := by
  rintro W h ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  refine ⟨a + b, ?_⟩
  rw [map_add, ha, hb, map_add]
  rfl
section
variable (P : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
lemma whiskerRight_imSieve_mem (φ : M ⟶ N) (hφ : ∀ (U : Cᵒᵖ) (y : N.obj U), imSieve φ y ∈ J U.unop)
    (U : Cᵒᵖ) (y : (N ⊗ P).obj U) : imSieve (φ ▷ P) y ∈ J U.unop := by
  induction y using TensorProduct.induction_on with
  | zero =>
    refine J.superset_covering ?_ (J.top_mem _)
    rintro W h -
    exact ⟨0, by erw [map_zero]⟩
  | tmul n p =>
    refine J.superset_covering ?_ (hφ U n)
    rintro W h ⟨m, hm⟩
    refine ⟨m ⊗ₜ P.map h.op p, ?_⟩
    change φ.app _ m ⊗ₜ _ = N.map h.op n ⊗ₜ P.map h.op p
    rw [hm]
    rfl
  | add a b ha hb =>
    exact J.superset_covering (imSieve_add (M := M ⊗ P) (N := N ⊗ P) (φ ▷ P) a b)
      (J.intersection_covering ha hb)
lemma tmul_zeroSieve_le {U : Cᵒᵖ} (m : M.obj U) (p : P.obj U) :
    zeroSieve m ≤ zeroSieve (M := M ⊗ P) (m ⊗ₜ p : (M ⊗ P).obj U) := by
  intro W h hm
  change M.map h.op m ⊗ₜ P.map h.op p = 0
  erw [hm]
  exact TensorProduct.zero_tmul _ _
lemma zeroSieve_mem_of_rTensor_rangeRestrict (φ : M ⟶ N)
    (hφ : ∀ (U : Cᵒᵖ) (x : M.obj U), φ.app U x = 0 → zeroSieve x ∈ J U.unop)
    (V : Cᵒᵖ) (z : (M ⊗ P).obj V)
    (hz : ((φ.app V).hom.rangeRestrict.rTensor (P.obj V)) z = 0) :
    zeroSieve z ∈ J V.unop := by
  have hex : Function.Exact (LinearMap.ker (φ.app V).hom.rangeRestrict).subtype
      (φ.app V).hom.rangeRestrict := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
  have hex' := rTensor_exact (P.obj V) hex (φ.app V).hom.surjective_rangeRestrict
  obtain ⟨w, rfl⟩ := (hex' z).1 hz
  clear hz hex hex'
  induction w using TensorProduct.induction_on with
  | zero =>
    rw [map_zero]
    exact J.superset_covering (zeroSieve_zero (M := M ⊗ P) (U := V)).ge (J.top_mem _)
  | tmul k p =>
    refine J.superset_covering (tmul_zeroSieve_le P (k : M.obj V) p) (hφ V _ ?_)
    have := k.2
    rw [LinearMap.mem_ker] at this
    exact congrArg Subtype.val this
  | add a b ha hb =>
    rw [map_add]
    exact J.superset_covering (zeroSieve_add (M := M ⊗ P) _ _) (J.intersection_covering ha hb)
end
section
variable (P : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
lemma finset_inf_mem {X : C} {ι : Type*} (T : Finset ι) (S : ι → Sieve X)
    (h : ∀ t ∈ T, S t ∈ J X) : T.inf S ∈ J X :=
  Finset.inf_induction (p := (· ∈ J X)) (J.top_mem X)
    (fun _ h₁ _ h₂ => J.intersection_covering h₁ h₂) h
lemma whiskerRight_zeroSieve_mem (φ : M ⟶ N)
    (hinj : ∀ (U : Cᵒᵖ) (x : M.obj U), φ.app U x = 0 → zeroSieve x ∈ J U.unop)
    (hsurj : ∀ (U : Cᵒᵖ) (y : N.obj U), imSieve φ y ∈ J U.unop)
    (U : Cᵒᵖ) (x : (M ⊗ P).obj U) (hx : (φ ▷ P).app U x = 0) : zeroSieve x ∈ J U.unop := by
  have hx' : (φ.app U).hom.rTensor (P.obj U) x = 0 := hx
  obtain ⟨A, hA, y, rfl⟩ := Submodule.exists_fg_le_eq_rTensor_subtype (x : (M.obj U) ⊗[_] (P.obj U))
  set f := (φ.app U).hom with hf
  let fA : A →ₗ[_] A.map f := f.submoduleMap A
  have h1 : (A.map f).subtype ∘ₗ fA = f ∘ₗ A.subtype := LinearMap.ext fun _ => rfl
  have h2 : (A.map f).subtype.rTensor (P.obj U) (fA.rTensor (P.obj U) y) =
      (A.map f).subtype.rTensor (P.obj U) 0 := by
    rw [← LinearMap.rTensor_comp_apply, h1, LinearMap.rTensor_comp_apply, map_zero]
    exact hx'
  obtain ⟨B, hB, hle, hB0⟩ := (hA.map f).exists_rTensor_fg_inclusion_eq h2
  rw [map_zero] at hB0
  obtain ⟨T, hT⟩ := hB
  refine J.transitive (finset_inf_mem T _ (fun t _ => hsurj U t)) _ (fun W g hg => ?_)
  erw [zeroSieve_pullback (M := M ⊗ P)]
  apply zeroSieve_mem_of_rTensor_rangeRestrict P φ hinj
  have hT' : ∀ t ∈ T, ∃ m, φ.app (op W) m = N.map g.op t :=
    fun t ht => (Finset.inf_le ht : _ ≤ imSieve φ t) g hg
  have hρ : ∀ b ∈ B, N.map g.op b ∈ LinearMap.range (φ.app (op W)).hom := by
    intro b hb
    rw [← hT] at hb
    induction hb using Submodule.span_induction with
    | mem t ht => obtain ⟨m, hm⟩ := hT' t ht; exact ⟨m, hm⟩
    | zero => erw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => erw [map_add]; exact add_mem ha hb
    | smul r a _ ha => erw [PresheafOfModules.map_smul]; exact Submodule.smul_mem _ _ ha
  let ρ : B →+ LinearMap.range (φ.app (op W)).hom :=
    { toFun := fun b => ⟨N.map g.op b, hρ b b.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ _ _) }
  let RW := (R ⋙ forget₂ CommRingCat RingCat).obj (op W)
  let pW : P.obj U →+ P.obj (op W) :=
    { toFun := fun p => (P.map g.op p : P.obj (op W))
      map_zero' := map_zero (P.map g.op).hom
      map_add' := map_add (P.map g.op).hom }
  have pW_smul : ∀ (r : (R ⋙ forget₂ CommRingCat RingCat).obj U) (p : P.obj U),
      pW (r • p) = ((R ⋙ forget₂ CommRingCat RingCat).map g.op).hom r • pW p :=
    fun r p => PresheafOfModules.map_smul _ _ _ _
  have ρ_smul : ∀ (r : (R ⋙ forget₂ CommRingCat RingCat).obj U) (b : B),
      ρ (r • b) = ((R ⋙ forget₂ CommRingCat RingCat).map g.op).hom r • ρ b :=
    fun r b => Subtype.ext (PresheafOfModules.map_smul _ _ _ _)
  let F : B ⊗[(R ⋙ forget₂ CommRingCat RingCat).obj U] P.obj U →+
      (LinearMap.range (φ.app (op W)).hom) ⊗[RW] P.obj (op W) :=
    TensorProduct.liftAddHom (R := (R ⋙ forget₂ CommRingCat RingCat).obj U)
      { toFun := fun b => AddMonoidHom.mk' (fun p => ρ b ⊗ₜ[RW] pW p)
          (fun p q => by rw [map_add, tmul_add])
        map_zero' := by ext p; simp
        map_add' := fun a b => by ext p; simp [add_tmul] }
      (fun r b p => by
        change ρ (r • b) ⊗ₜ[RW] pW p = ρ b ⊗ₜ[RW] pW (r • p)
        rw [ρ_smul, pW_smul, smul_tmul])
  have key : ∀ z : A ⊗[_] P.obj U,
      (φ.app (op W)).hom.rangeRestrict.rTensor (P.obj (op W))
        ((M ⊗ P).map g.op (A.subtype.rTensor (P.obj U) z)) =
      F ((A.map f).inclusion hle |>.rTensor (P.obj U) (fA.rTensor (P.obj U) z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]; erw [map_zero]
    | tmul a p =>
      change (φ.app (op W)).hom.rangeRestrict (M.map g.op a) ⊗ₜ[RW] pW p = ρ _ ⊗ₜ[RW] pW p
      congr 1
      exact Subtype.ext (PresheafOfModules.naturality_apply φ g.op (a : M.obj U))
    | add a b ha hb =>
      simp only [map_add] at ha hb ⊢
      exact (congrArg _ (map_add ((M ⊗ P).map g.op).hom _ _)).trans
        ((map_add _ _ _).trans (congrArg₂ (· + ·) ha hb))
  erw [key, hB0, map_zero]
end
section
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
lemma W_toPresheaf_iff (φ : M ⟶ N) :
    J.W ((PresheafOfModules.toPresheaf _).map φ) ↔
      (∀ (U : Cᵒᵖ) (x : M.obj U), φ.app U x = 0 → zeroSieve x ∈ J U.unop) ∧
      (∀ (U : Cᵒᵖ) (y : N.obj U), imSieve φ y ∈ J U.unop) := by
  rw [J.W_iff_isLocallyBijective]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun U x hx => ?_, fun U y => h2.imageSieve_mem y⟩
    have := h1.equalizerSieve_mem (X := U) x 0 (by
      erw [hx, map_zero]; rfl)
    refine J.superset_covering ?_ this
    intro W g hg
    change M.map g.op x = 0
    have hg' : M.map g.op x = M.map g.op 0 := hg
    rw [hg']
    exact map_zero _
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun {U} x y hxy => ?_⟩, ⟨fun {U} y => h2 _ y⟩⟩
    let x' : M.obj U := x
    let y' : M.obj U := y
    have hxy' : φ.app U x' = φ.app U y' := hxy
    have h := h1 U (x' - y') (by rw [map_sub, hxy', sub_self])
    refine J.superset_covering ?_ h
    intro W g hg
    have hg' : M.map g.op (x' - y') = 0 := hg
    rw [map_sub, sub_eq_zero] at hg'
    exact hg'
end
variable (J R) in

abbrev W : MorphismProperty (PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :=
  J.W.inverseImage (PresheafOfModules.toPresheaf _)
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
lemma W_whiskerRight {φ : M ⟶ N} (hφ : W J R φ) (P : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    W J R (φ ▷ P) := by
  rw [W, MorphismProperty.inverseImage_iff, W_toPresheaf_iff] at hφ ⊢
  exact ⟨whiskerRight_zeroSieve_mem P φ hφ.1 hφ.2, whiskerRight_imSieve_mem P φ hφ.2⟩
instance isMonoidal_W : (W J R).IsMonoidal where
  whiskerLeft P _ _ φ hφ :=
    ((W J R).arrow_mk_iso_iff (Arrow.isoMk (β_ P _) (β_ P _) (by simp))).2 (W_whiskerRight hφ P)
  whiskerRight φ hφ P := W_whiskerRight hφ P
end ModulesTensor
section
variable {C' : Type u} [Category.{u} C'] (K : GrothendieckTopology C') (S : Sheaf K CommRingCat.{u})
abbrev ringSheaf : Sheaf K RingCat.{u} := (sheafCompose K (forget₂ CommRingCat RingCat)).obj S
abbrev ringSheafId : S.obj ⋙ forget₂ CommRingCat RingCat ⟶ (ringSheaf K S).obj := 𝟙 _
instance : IsIso (ringSheafId K S) := inferInstanceAs (IsIso (𝟙 (S.obj ⋙ forget₂ CommRingCat RingCat)))
variable [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
noncomputable abbrev modulesSheafification :
    PresheafOfModules.{u} (S.obj ⋙ forget₂ CommRingCat RingCat) ⥤ SheafOfModules.{u} (ringSheaf K S) :=
  PresheafOfModules.sheafification (J := K) (R₀ := S.obj ⋙ forget₂ CommRingCat RingCat)
    (R := ringSheaf K S) (ringSheafId K S)
instance : (modulesSheafification K S).IsLocalization (ModulesTensor.W K S.obj) :=
  inferInstanceAs ((PresheafOfModules.sheafification (J := K) (R₀ := S.obj ⋙ forget₂ CommRingCat RingCat)
    (R := ringSheaf K S) (ringSheafId K S)).IsLocalization
      (K.W.inverseImage (PresheafOfModules.toPresheaf (S.obj ⋙ forget₂ CommRingCat RingCat))))
instance : IsIso (PresheafOfModules.sheafificationAdjunction (J := K)
    (R₀ := S.obj ⋙ forget₂ CommRingCat RingCat) (R := ringSheaf K S) (ringSheafId K S)).counit :=
  inferInstanceAs (IsIso (PresheafOfModules.sheafificationAdjunction (J := K)
    (R := ringSheaf K S) (𝟙 (ringSheaf K S).obj)).counit)
noncomputable def sheafificationUnitIso :
    (modulesSheafification K S).obj (𝟙_ _) ≅ SheafOfModules.unit (ringSheaf K S) :=
  @asIso _ _ _ _ _ (NatIso.isIso_app_of_isIso (PresheafOfModules.sheafificationAdjunction (J := K)
    (R₀ := S.obj ⋙ forget₂ CommRingCat RingCat) (R := ringSheaf K S) (ringSheafId K S)).counit
      (SheafOfModules.unit (ringSheaf K S)))
end
section
variable {C' : Type u} [Category.{u} C'] (K : GrothendieckTopology C') (S : Sheaf K CommRingCat.{u})
variable [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
@[instance_reducible]
noncomputable def sheafModulesMonoidal : MonoidalCategory (SheafOfModules.{u} (ringSheaf K S)) :=
  inferInstanceAs (MonoidalCategory (LocalizedMonoidal (L := modulesSheafification K S)
    (W := ModulesTensor.W K S.obj) (sheafificationUnitIso K S)))
attribute [local instance] sheafModulesMonoidal
@[instance_reducible]
noncomputable def sheafModulesSymmetric : SymmetricCategory (SheafOfModules.{u} (ringSheaf K S)) :=
  inferInstanceAs (SymmetricCategory (LocalizedMonoidal (L := modulesSheafification K S)
    (W := ModulesTensor.W K S.obj) (sheafificationUnitIso K S)))
@[instance_reducible]
noncomputable def modulesSheafificationMonoidal : (modulesSheafification K S).Monoidal :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory (L := modulesSheafification K S)
    (W := ModulesTensor.W K S.obj) (sheafificationUnitIso K S)).Monoidal
attribute [local instance] modulesSheafificationMonoidal
end
end GroundTheory.Arith.SchemeCoh


