-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyEquivPiOfWeights
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyEquivPiOfWeights
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:41:12.85108+00:00
-- url     : https://prove2.me/theorems/9f432d6b-1416-4959-a738-860e55d414f2
-- title:
--   Nonempty Equiv Pi Of Weights
-- statement:
--   Definitions and structural lemmas for Nonempty Equiv Pi Of Weights, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/NonemptyEquivPiOfWeights.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_add

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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.MulSplit
section Values
variable {X Y B : Scheme.{0}} (L : LB X) (p : Y ⟶ B)
def Idx : Type :=
  {t : Y × ((Y ⟶ X) → L.ι) × (Y ⟶ Y) // Good L t.1 t.2.1 ∧ t.2.2 ≫ p = p}
def Vals : Type := ∀ i : Idx L p, Y.presheaf.stalk i.1.1
instance : CommRing (Vals L p) := inferInstanceAs (CommRing (∀ i : Idx L p, Y.presheaf.stalk i.1.1))
def cstHom : Γ(B, ⊤) →+* Vals L p :=
  Pi.ringHom fun i => (Y.presheaf.germ (p ⁻¹ᵁ ⊤) i.1.1 trivial).hom.comp (p.app ⊤).hom
instance : Algebra Γ(B, ⊤) (Vals L p) := (cstHom L p).toAlgebra
variable {L p}
theorem algebraMap_vals (c : Γ(B, ⊤)) (i : Idx L p) :
    algebraMap Γ(B, ⊤) (Vals L p) c i = gs p i.1.1 ⊤ c := (gs_eq p i.1.1 ⊤ trivial c).symm
theorem mul_vals (v w : Vals L p) (i : Idx L p) : (v * w) i = v i * w i := rfl
variable {K K' : Type} [Fintype K] [Fintype K']
variable (p) in

def ev {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) : Vals L p :=
  fun i => sval s i.1.2.2 i.1.1 i.1.2.1
def dv (φ : K → (Y ⟶ X)) (ε : K → ℤ) : (Y ⟶ X) →₀ ℤ := ∑ k, Finsupp.single (φ k) (ε k)
theorem ev_add {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s t u : LB.Sec (LB.LinComb L φ ε)}
    (h : ∀ j, u.f j = s.f j + t.f j) : ev p u = ev p s + ev p t :=
  funext fun i => (congrArg (gs _ _ _) (h _)).trans (gs_add _ _ _ (i.2.1.mem φ _) _ _)
theorem ev_smul {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s u : LB.Sec (LB.LinComb L φ ε)} (c : Γ(B, ⊤))
    (h : ∀ j, u.f j = (Y.presheaf.map (homOfLE le_top).op).hom (p.appTop.hom c) * s.f j) :
    ev p u = c • ev p s := by
  funext i
  have hm := i.2.1.mem φ i.1.2.2
  refine (congrArg (gs _ _ _) (h _)).trans ((gs_mul _ _ _ hm _ _).trans ?_)
  rw [Algebra.smul_def, mul_vals, algebraMap_vals]
  refine congrArg₂ (· * ·) ((gs_res _ _ _ hm _).trans ((gs_pull _ p _ ⊤ trivial c).trans ?_)) rfl
  rw [i.2.2]
theorem ev_zero {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s : LB.Sec (LB.LinComb L φ ε)} (h : ∀ j, s.f j = 0) :
    ev p s = 0 :=
  funext fun i => (congrArg (gs _ _ _) (h _)).trans ((gs_eq _ _ _ (i.2.1.mem φ _) _).trans
    ((congrArg _ (map_zero _)).trans (map_zero _)))
variable (L p) in

def Sg (D : (Y ⟶ X) →₀ ℤ) : Submodule Γ(B, ⊤) (Vals L p) where
  carrier := {v | ∃ s : LB.Sec (LB.LinComb L (fun k : D.support => k.1) (fun k => D k.1)), ev p s = v}
  add_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨secAdd s t, ev_add fun _ => rfl⟩
  zero_mem' := ⟨secZero _, ev_zero fun _ => rfl⟩
  smul_mem' := by
    rintro c _ ⟨s, rfl⟩
    exact ⟨secCMul (fun _ => le_top) (p.appTop.hom c) s, ev_smul c fun _ => rfl⟩
variable (L) in

def pl (h : Y ⟶ Y) (hh : h ≫ p = p) : Vals L p →ₐ[Γ(B, ⊤)] Vals L p where
  toFun v := fun i => v ⟨(i.1.1, i.1.2.1, i.1.2.2 ≫ h), i.2.1, by rw [Category.assoc, hh, i.2.2]⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
def IsG (D : (Y ⟶ X) →₀ ℤ) (u : (Vals L p)ˣ) : Prop := u.val ∈ Sg L p D ∧ (u⁻¹).val ∈ Sg L p (-D)
theorem IsG.inv {D : (Y ⟶ X) →₀ ℤ} {u : (Vals L p)ˣ} (h : IsG D u) : IsG (-D) u⁻¹ :=
  ⟨h.2, by rw [inv_inv, neg_neg]; exact h.1⟩
end Values
section Descent
variable {X Y B : Scheme.{0}} {L : LB X} {p : Y ⟶ B} {G : Type}
def Descends (q : Y ⟶ Y) (τ : G → (Y ⟶ Y)) : Prop :=
  (∀ U : Y.Opens, Function.Injective (q.app U).hom) ∧
  ∀ (U : Y.Opens) (f : Γ(Y, q ⁻¹ᵁ U)),
    (∀ g, ∀ y ∈ q ⁻¹ᵁ U, gs (τ g) y (q ⁻¹ᵁ U) f = gs (𝟙 Y) y (q ⁻¹ᵁ U) f) → ∃ a, (q.app U).hom a = f
end Descent
section Group
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S}
end Group
section Weights
variable {X Y B : Scheme.{0}} {L : LB X} {p : Y ⟶ B}
end Weights
end GlobalTheory.MulSplit
namespace GlobalTheory
end GlobalTheory


