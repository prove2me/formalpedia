-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CrystallineConnectionFormCoboundaryZero
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_CrystallineConnectionFormCoboundaryZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:53.225589+00:00
-- url     : https://prove2.me/theorems/3b6dc14b-44cc-4cd0-8c7e-c912ac4d1289
-- title:
--   Crystalline Connection Form Coboundary Zero
-- statement:
--   Definitions and structural lemmas for Crystalline Connection Form Coboundary Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CrystallineConnectionFormCoboundaryZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration
import Theorems.Thm_GlobalTheory_Cris_Thick_Hom_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
namespace GlobalTheory.Cris
open CatCoh
variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}}
def derSec {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M]
    [IsScalarTower R Bᵐᵒᵖ M] (D : Derivation R B M) : B →ₐ[R] TrivSqZeroExt B M where
  toFun b := TrivSqZeroExt.inl b + TrivSqZeroExt.inr (D b)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp
  commutes' r := by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']
section
variable {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M]
    [IsScalarTower R Bᵐᵒᵖ M] (D : Derivation R B M) (b : B)
@[simp] theorem fst_derSec : (derSec D b).fst = b := by
  exact add_zero b
@[simp] theorem snd_derSec : (derSec D b).snd = D b := by
  exact zero_add (D b)
end
section Conn
open KaehlerDifferential
variable (R) (B B' : Type) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
@[reducible] def opModule : Module Bᵐᵒᵖ Ω[B⁄R] :=
  Module.compHom _ ((RingHom.id B).fromOpposite mul_comm)
attribute [local instance] opModule
theorem isCentralScalar_kaehler : IsCentralScalar B Ω[B⁄R] := ⟨fun _ _ ↦ rfl⟩
theorem isScalarTower_kaehler : IsScalarTower R Bᵐᵒᵖ Ω[B⁄R] := ⟨fun r b m ↦ smul_assoc r b.unop m⟩
attribute [local instance] isCentralScalar_kaehler isScalarTower_kaehler
abbrev diagExt : SqExt R := SqExt.ofModule R B Ω[B⁄R]
abbrev diagSec : B →ₐ[R] TrivSqZeroExt B Ω[B⁄R] := derSec (D R B)
def diagMap [Algebra B B'] [IsScalarTower R B B'] :
    TrivSqZeroExt B Ω[B⁄R] →ₐ[R] TrivSqZeroExt B' Ω[B'⁄R] where
  toFun c := TrivSqZeroExt.inl (algebraMap B B' c.fst) +
    TrivSqZeroExt.inr (KaehlerDifferential.map R R B B' c.snd)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp
  commutes' r := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl', ← IsScalarTower.algebraMap_apply]
variable {R B B'} {s : X ⟶ Sp R}
def connForm (f : Z1 (O (dp0 R) s)) (x : Sp B ⟶ X) (hx : x ≫ s = spMap (algebraMap R B)) : Ω[B⁄R] :=
  TrivSqZeroExt.snd (R := B) (ev f ((diagExt R B).secHom hx (diagExt R B).i fun _ ↦ rfl) -
    ev f ((diagExt R B).secHom hx (diagSec R B) (fst_derSec _)))
end Conn
section Chern
def evalAt {B : Type} [CommRing B] (x : Sp B ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.comp (x.appLE U ⊤ h).hom
variable (γ : DividedPowers I) (s : X ⟶ Sp R)
def IsSmall {ι : Type} (U : ι → X.Opens) : ObjectProperty (Thick γ s) :=
  fun T ↦ ∃ i, ⊤ ≤ T.x ⁻¹ᵁ U i
variable {γ s} in

theorem Thick.Hom.le_preimage {T T' : Thick γ s} (φ : T ⟶ T') {U : X.Opens} (h : ⊤ ≤ T.x ⁻¹ᵁ U) :
    ⊤ ≤ T'.x ⁻¹ᵁ U := by
  rw [← φ.pt]
  exact fun p _ ↦ h (Set.mem_univ ((spMap φ.φ₀) p))
def IsChern (L : LB X) (z : H2 γ s) : Prop :=
  ∃ (i : (IsSmall γ s L.U).FullSubcategory → L.ι) (hi : ∀ T, ⊤ ≤ T.obj.x ⁻¹ᵁ L.U (i T))
    (u : ∀ T T' : (IsSmall γ s L.U).FullSubcategory, (T ⟶ T') → T'.obj.B)
    (ℓ : Z2 ((IsSmall γ s L.U).ι ⋙ O γ s)),
    (∀ T T' φ, T'.obj.π (u T T' φ) = evalAt T'.obj.x (L.U (i T') ⊓ L.U (i T))
      (le_inf (hi T') (φ.hom.le_preimage (hi T))) (L.g (i T') (i T)).val) ∧
    (∀ T T' T'' φ ψ, (ℓ.1 T T' T'' φ ψ : T''.obj.B) ∈ T''.obj.J ∧
      dpExp T''.obj.δ (ℓ.1 T T' T'' φ ψ) * u T T'' (φ ≫ ψ) = ψ.hom.φ (u T T' φ) * u T' T'' ψ) ∧
    (CoefMap.restrict (O γ s) (IsSmall γ s L.U).ι).pull2 z = H2.mk _ ℓ
end Chern
section Examples
open Polynomial
abbrev lineStr (R : Type) [CommRing R] : Sp R[X] ⟶ Sp R := spMap (algebraMap R R[X])
def coordLift (T : Thick (dp0 R) (lineStr R)) : T.B := (T.surj ((Spec.preimage T.x).hom Polynomial.X)).choose
theorem π_coordLift (T : Thick (dp0 R) (lineStr R)) :
    T.π (coordLift T) = (Spec.preimage T.x).hom Polynomial.X := (T.surj _).choose_spec
theorem coordLift_sub_mem {T T' : Thick (dp0 R) (lineStr R)} (φ : T ⟶ T') :
    coordLift T' - φ.φ (coordLift T) ∈ T'.J := by
  rw [← T'.ker, map_sub, ← φ.comm, π_coordLift, π_coordLift, ← φ.pt, sub_eq_zero]
  have : Spec.preimage (spMap φ.φ₀ ≫ T.x) = Spec.preimage T.x ≫ CommRingCat.ofHom φ.φ₀ := by
    apply Spec.map_injective
    simp
  rw [this]; rfl
theorem dpow_two_add {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {a b : B} (ha : a ∈ J)
    (hb : b ∈ J) : δ.dpow 2 (a + b) = δ.dpow 2 a + a * b + δ.dpow 2 b := by
  rw [δ.dpow_add ha hb]
  simp [Finset.Nat.antidiagonal_succ, δ.dpow_zero ha, δ.dpow_zero hb, δ.dpow_one ha, δ.dpow_one hb]
  ring
def tdt (R : Type) [CommRing R] : Form (lineStr R) :=
  ⟨⟨fun T T' φ ↦ φ.φ (coordLift T) * (coordLift T' - φ.φ (coordLift T)) +
      T'.δ.dpow 2 (coordLift T' - φ.φ (coordLift T)), fun T T' T'' φ ψ ↦ by
    have e : coordLift T'' - (φ ≫ ψ).φ (coordLift T) =
        ψ.φ (coordLift T' - φ.φ (coordLift T)) + (coordLift T'' - ψ.φ (coordLift T')) := by simp
    have h1 := ψ.mem (coordLift_sub_mem φ)
    have h2 := coordLift_sub_mem ψ
    have h3 : ψ.φ (T'.δ.dpow 2 (coordLift T' - φ.φ (coordLift T))) =
      T''.δ.dpow 2 (ψ.φ (coordLift T' - φ.φ (coordLift T))) := ψ.dp.map_dpow (coordLift_sub_mem φ)
    change (_ * _ + T''.δ.dpow 2 (_ - _) : T''.B) = ψ.φ (_ + _) + (_ * _ + _)
    rw [e, dpow_two_add _ h1 h2, map_add, h3]
    simp only [map_mul, map_sub, Thick.comp_φ]
    ring⟩, fun T T' φ _ h ↦ by
    have := coordLift_sub_mem φ
    rw [h, Ideal.mem_bot] at this
    change (_ * _ + _ : T'.B) = 0
    rw [this, mul_zero, zero_add, dpow_eval_zero _ two_ne_zero]⟩
end Examples
end GlobalTheory.Cris


