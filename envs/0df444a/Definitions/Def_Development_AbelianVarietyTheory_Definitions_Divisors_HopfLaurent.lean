-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HopfLaurent
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_HopfLaurent
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T16:32:40.283821+00:00
-- url     : https://prove2.me/theorems/35146d46-52fc-4d58-8b16-277995dc3b2c
-- title:
--   Hopf Laurent
-- statement:
--   Definitions and structural lemmas for Hopf Laurent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HopfLaurent.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AbTan
variable {R : Type} [CommRing R]
def Lifts {X : Scheme.{0}} (s : X ⟶ Sp R) {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ X) (z : Sp (TrivSqZeroExt B M) ⟶ X) : Prop :=
  z ≫ s = spMap ((TrivSqZeroExt.inlHom B M).comp (algebraMap R B)) ∧
    spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z = P
def unitPt (A : Over (Sp R)) [GrpObj A] (B : Type) [CommRing B] [Algebra R B] : Sp B ⟶ A.left :=
  spMap (algebraMap R B) ≫ (show Sp R ⟶ A.left from η[A].left)
def IsSum {B M B' M' : Type} [CommRing B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [CommRing B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M'] [IsCentralScalar B' M']
    (β : TrivSqZeroExt B M →+* TrivSqZeroExt B' M') (α : B → B') (f : M → M') : Prop :=
  (∀ b, β (TrivSqZeroExt.inl b) = TrivSqZeroExt.inl (α b)) ∧ ∀ m, β (TrivSqZeroExt.inr m) = TrivSqZeroExt.inr (f m)
structure TanRep (A : Over (Sp R)) [GrpObj A] (W : Type) [AddCommGroup W] [Module R W] where

  Φ : ∀ {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module R M] [IsScalarTower R B M] (_ : Sp (TrivSqZeroExt B M) ⟶ A.left), W →ₗ[R] M

  bij : ∀ {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module R M] [IsScalarTower R B M] (l : W →ₗ[R] M),
    ∃! z : Sp (TrivSqZeroExt B M) ⟶ A.left, Lifts A.hom (unitPt A B) z ∧ Φ z = l

  nat : ∀ {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module R M] [IsScalarTower R B M] {B' M' : Type} [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M']
    [Module B'ᵐᵒᵖ M'] [IsCentralScalar B' M'] [Module R M'] [IsScalarTower R B' M'] (α : B →ₐ[R] B') (f : M →ₗ[R] M')
    (β : TrivSqZeroExt B M →+* TrivSqZeroExt B' M'), IsSum β α f →
    ∀ z : Sp (TrivSqZeroExt B M) ⟶ A.left, Lifts A.hom (unitPt A B) z → Φ (spMap β ≫ z) = f ∘ₗ Φ z
example {X : Scheme.{0}} (s : X ⟶ Sp R) {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ X) (h : P ≫ s = spMap (algebraMap R B)) :
    (spMap (TrivSqZeroExt.inlHom B M) ≫ P) ≫ s = spMap ((TrivSqZeroExt.inlHom B M).comp (algebraMap R B)) := by
  rw [Category.assoc, h, GlobalTheory.Cris.spMap_comp]
example {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] :
    IsSum (RingHom.id (TrivSqZeroExt B M)) id id := ⟨fun _ => rfl, fun _ => rfl⟩
end GlobalTheory.AbTan
namespace GlobalTheory.AbTan.MultGroup
open LaurentPolynomial
variable (R : Type) [CommRing R]
local instance hopfLaurent : HopfAlgebra (CommRingCat.of R) (CommRingCat.of R[T;T⁻¹]) :=
  inferInstanceAs (HopfAlgebra R R[T;T⁻¹])
abbrev G : Over (Sp R) := (Spec (CommRingCat.of R[T;T⁻¹])).asOver (Spec (CommRingCat.of R))
theorem G_hom : (G R).hom = spMap (algebraMap R R[T;T⁻¹]) := rfl
theorem unit_eq (B : Type) [CommRing B] [Algebra R B] :
    unitPt (G R) B = spMap (algebraMap R B) ≫ spMap (Bialgebra.counitAlgHom R R[T;T⁻¹]).toRingHom := rfl
theorem comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl
theorem inj' {A B : Type} [CommRing A] [CommRing B] {p q : A →+* B} (h : spMap p = spMap q) : p = q := by
  have h' := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom h'
variable {R}
def pre {C : Type} [CommRing C] (z : Sp C ⟶ (G R).left) : R[T;T⁻¹] →+* C :=
  (Spec.preimage (R := CommRingCat.of R[T;T⁻¹]) (S := CommRingCat.of C) z).hom
theorem spMap_pre {C : Type} [CommRing C] (z : Sp C ⟶ (G R).left) : spMap (pre z) = z := by
  simp only [spMap, pre, CommRingCat.ofHom_hom]
  exact Spec.map_preimage z
theorem pre_spMap {C : Type} [CommRing C] (φ : R[T;T⁻¹] →+* C) : pre (R := R) (spMap φ) = φ := by
  simp only [pre, spMap, Spec.preimage_map, CommRingCat.hom_ofHom]
theorem hom_ext' {C : Type} [CommRing C] {φ ψ : R[T;T⁻¹] →+* C}
    (h0 : φ.comp (algebraMap R _) = ψ.comp (algebraMap R _)) (h1 : φ (T 1) = ψ (T 1)) : φ = ψ := by
  have hC : ∀ a : R, φ (LaurentPolynomial.C a) = ψ (LaurentPolynomial.C a) := fun a => by
    rw [LaurentPolynomial.C_eq_algebraMap]
    exact congrArg (fun f : R →+* C => f a) h0
  have hinv : φ (T (-1)) = ψ (T (-1)) := by
    have e : (T (-1) : R[T;T⁻¹]) * T 1 = 1 := by rw [← T_add]; simp
    have eφ : φ (T (-1)) * φ (T 1) = 1 := by rw [← map_mul, e, map_one]
    have eψ : ψ (T 1) * ψ (T (-1)) = 1 := by rw [← map_mul, mul_comm, e, map_one]
    calc φ (T (-1)) = φ (T (-1)) * (ψ (T 1) * ψ (T (-1))) := by rw [eψ, _root_.mul_one]
      _ = (φ (T (-1)) * φ (T 1)) * ψ (T (-1)) := by rw [h1, _root_.mul_assoc]
      _ = ψ (T (-1)) := by rw [eφ, _root_.one_mul]
  have hT : ∀ n : ℤ, φ (T n) = ψ (T n) := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih => rw [T_add, map_mul, map_mul, ih, h1]
    | pred k ih => rw [sub_eq_add_neg, T_add, map_mul, map_mul, ih, hinv]
  refine RingHom.ext fun p => ?_
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | C_mul_T n a => rw [map_mul, map_mul, hC, hT]
theorem lifts_iff {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
    [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (φ : R[T;T⁻¹] →+* TrivSqZeroExt B M) :
    Lifts (G R).hom (unitPt (G R) B) (spMap φ) ↔
      φ.comp (algebraMap R _) = (TrivSqZeroExt.inlHom B M).comp (algebraMap R B) ∧ (φ (T 1)).fst = 1 := by
  have hε : Bialgebra.counitAlgHom R R[T;T⁻¹] (T 1) = 1 := by
    rw [Bialgebra.counitAlgHom_apply]
    exact AddMonoidAlgebra.counit_single (1 : ℤ) (1 : R)
  have hεC : ∀ r : R, Bialgebra.counitAlgHom R R[T;T⁻¹] (algebraMap R _ r) = r := fun r =>
    (Bialgebra.counitAlgHom R R[T;T⁻¹]).commutes r
  have e1 : spMap φ ≫ (G R).hom = spMap (φ.comp (algebraMap R _)) := by
    rw [G_hom]; exact comp' _ _
  have e2 : spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ spMap φ =
      spMap ((TrivSqZeroExt.fstHom B B M).toRingHom.comp φ) := comp' _ _
  have e3 : unitPt (G R) B =
      spMap ((algebraMap R B).comp (Bialgebra.counitAlgHom R R[T;T⁻¹]).toRingHom) := by
    rw [unit_eq]; exact comp' _ _
  unfold Lifts
  constructor
  · rintro ⟨h1, h2⟩
    have h1' := inj' (e1.symm.trans h1)
    have h2' := inj' (e2.symm.trans (h2.trans e3))
    refine ⟨h1', ?_⟩
    have := congrArg (fun f : R[T;T⁻¹] →+* B => f (T 1)) h2'
    simpa [hε] using this
  · rintro ⟨h1, h2⟩
    refine ⟨e1.trans (congrArg spMap h1), e2.trans ((congrArg spMap ?_).trans e3.symm)⟩
    apply hom_ext'
    · ext r
      have := congrArg (fun f : R →+* TrivSqZeroExt B M => (f r).fst) h1
      simpa [hεC] using this
    · simpa [hε] using h2
def tanRep : TanRep (G R) R where
  Φ z := LinearMap.toSpanSingleton R _ (pre z (T 1)).snd
  bij := by
    intro B M _ _ _ _ _ _ _ _ l
    let u : (TrivSqZeroExt B M)ˣ :=
      ⟨TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (l 1), TrivSqZeroExt.inl 1 - TrivSqZeroExt.inr (l 1),
        by ext <;> simp, by ext <;> simp⟩
    let φ := LaurentPolynomial.eval₂ ((TrivSqZeroExt.inlHom B M).comp (algebraMap R B)) u
    have hT : φ (T 1) = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (l 1) := by
      simp [φ, u, LaurentPolynomial.eval₂_T]
    have hC : φ.comp (algebraMap R _) = (TrivSqZeroExt.inlHom B M).comp (algebraMap R B) := by
      refine RingHom.ext fun r => ?_
      simp [φ, ← LaurentPolynomial.C_eq_algebraMap]
    refine ⟨spMap φ, ⟨(lifts_iff φ).2 ⟨hC, by simp [hT]⟩, ?_⟩, ?_⟩
    · ext; simp [pre_spMap, hT]
    · rintro z ⟨hz, hl⟩
      rw [← spMap_pre z] at hz ⊢
      obtain ⟨h1, h2⟩ := (lifts_iff _).1 hz
      refine congrArg _ (hom_ext' (h1.trans hC.symm) ?_)
      have h3 : (pre z (T 1)).snd = l 1 := by rw [← hl]; simp
      rw [hT]; ext
      · simp [h2]
      · simp [h3]
  nat := by
    intro B M _ _ _ _ _ _ _ _ B' M' _ _ _ _ _ _ _ _ α f β hβ z _
    have : pre (spMap β ≫ z) = β.comp (pre z) := by
      apply inj'
      rw [spMap_pre, ← comp']
      erw [spMap_pre]
      rfl
    ext
    simp only [this, LinearMap.toSpanSingleton_apply, one_smul, LinearMap.comp_apply, RingHom.comp_apply]
    rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq (pre z (T 1)), map_add, hβ.1, hβ.2]
    simp
example {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module R M] [IsScalarTower R B M] (φ : R[T;T⁻¹] →+* TrivSqZeroExt B M) :
    (tanRep (R := R)).Φ (spMap φ) 1 = (φ (T 1)).snd := by
  change LinearMap.toSpanSingleton R _ (pre (R := R) (spMap φ) (T 1)).snd 1 = _
  simp [pre_spMap]
end GlobalTheory.AbTan.MultGroup


