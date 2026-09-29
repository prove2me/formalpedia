-- Prove2me | Definitions.Def_IntegralRelativeSymbols
-- name    : IntegralRelativeSymbols
-- status  : Definition
-- author  : @davidloeffler
-- created : 2026-09-06T16:20:10.373344+00:00
-- url     : https://prove2.me/theorems/4384d58d-792d-4c6e-b1e1-e47ddc44a2e2
-- title:
--   Integral relative symbols and finite-index coinduction
-- statement:
--   Relative degree-one group cohomology is modeled by additive, equivariant functions on pairs in a group set X. The coefficient values lie in an integral submodule U of an ambient module. Define the finite-index coinduced coefficient module as equivariant functions on the ambient group with values in U, its right-translation action, and the relative Shapiro map Φ(φ)(x,y)(g)=φ(gx,gy). For a genuine action on U these are the usual modular symbols and coinduction. The ambient formulation only requires linear coefficient operators and also applies directly to homogeneous polynomial submodules. The specialization sl2Symbols uses the standard action on the rational cusps.
-- source:
--   Degree-one relative Shapiro construction in the modular-symbol model of Ash–Stevens §4, Definition 4.1. Finite-index induction and coinduction agree. https://math.bu.edu/people/ghs/papers/Mod_fms_char_ell.pdf

import Definitions.Def_MTT_Cohomology
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RepresentationTheory.Basic
set_option autoImplicit false
noncomputable section
namespace IntegralRelativeSymbols
variable {G X V : Type*} [Group G] [MulAction G X] [AddCommGroup V]
/-- Relative H¹ in the divisor-pair model, with values in U. Linear coefficient
operators suffice for the finiteness argument; representations are a special case.
Allowing an ambient module avoids choosing a restricted polynomial action. -/
def symbols (ρ : G → V →ₗ[ℤ] V) (U : Submodule ℤ V) :
    Submodule ℤ ((X × X) → V) where
  carrier := {φ | (∀ x y, φ (x,y) ∈ U) ∧
    (∀ x y z, φ (x,y) + φ (y,z) = φ (x,z)) ∧
    ∀ g x y, φ (g • x,g • y) = ρ g (φ (x,y))}
  zero_mem' := by simp
  add_mem' := by
    rintro φ ψ ⟨hp, ha, he⟩ ⟨hq, hb, hf⟩
    refine ⟨fun x y => U.add_mem (hp x y) (hq x y), ?_, ?_⟩
    · intro x y z
      change (φ _ + ψ _) + (φ _ + ψ _) = φ _ + ψ _
      rw [add_add_add_comm, ha, hb]
    · intro g x y
      change φ _ + ψ _ = ρ g (φ _ + ψ _)
      rw [map_add, he, hf]
  smul_mem' := by
    rintro a φ ⟨hp, ha, he⟩
    refine ⟨fun x y => U.smul_mem a (hp x y), ?_, ?_⟩
    · intro x y z
      change a • φ _ + a • φ _ = a • φ _
      rw [← smul_add, ha]
    · intro g x y
      change a • φ _ = ρ g (a • φ _)
      rw [map_smul, he]

/-- Finite-index coinduction, realized as equivariant functions with values in U.
For a genuine action on U this is the usual coinduced (hence also induced) module. -/
def coind (Γ : Subgroup G) (ρ : Γ → V →ₗ[ℤ] V) (U : Submodule ℤ V) :
    Submodule ℤ (G → V) where
  carrier := {F | (∀ g, F g ∈ U) ∧ ∀ h : Γ, ∀ g, F (h.val*g) = ρ h (F g)}
  zero_mem' := by simp
  add_mem' := by
    rintro f g ⟨hf, he⟩ ⟨hg, hh⟩
    exact ⟨fun x => U.add_mem (hf x) (hg x), by simpa using fun h x => congrArg₂ (· + ·) (he h x) (hh h x)⟩
  smul_mem' := by
    rintro a f ⟨hf, he⟩
    exact ⟨fun x => U.smul_mem a (hf x), by simpa using fun h x => congrArg (a • ·) (he h x)⟩

def coindAction (Γ : Subgroup G) (ρ : Γ → V →ₗ[ℤ] V) (U : Submodule ℤ V)
    (g : G) : coind Γ ρ U →ₗ[ℤ] coind Γ ρ U where
  toFun F := ⟨fun h => F.val (h*g), ⟨fun h => F.property.1 _,
    fun h x => by simpa [mul_assoc] using F.property.2 h (x*g)⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Relative Shapiro map: Φ(D)(g)=φ(gD). -/
def shapiroMap (Γ : Subgroup G) (ρ : Γ → V →ₗ[ℤ] V) (U : Submodule ℤ V) :
    symbols (X := X) ρ U →ₗ[ℤ]
      symbols (X := X) (coindAction Γ ρ U) ⊤ where
  toFun φ := ⟨fun D => ⟨fun g => φ.val (g • D.1,g • D.2),
    ⟨fun g => φ.property.1 _ _, fun h g => by
      simpa only [mul_smul, Subgroup.smul_def] using φ.property.2.2 h (g • D.1) (g • D.2)⟩⟩,
    ⟨by simp, fun x y z => by ext g; exact φ.property.2.1 _ _ _,
      fun g x y => by ext h; simp [coindAction, mul_smul]⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Compactly supported group cohomology for an integral subgroup of SL₂,
in the relative divisor-pair model. -/
def sl2Symbols (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (ρ : Γ → V →ₗ[ℤ] V) (U : Submodule ℤ V) :
    Submodule ℤ ((MTT.Cohomology.Cusp × MTT.Cohomology.Cusp) → V) :=
  letI : MulAction (Matrix.SpecialLinearGroup (Fin 2) ℤ) MTT.Cohomology.Cusp :=
    MulAction.compHom MTT.Cohomology.Cusp (Matrix.SpecialLinearGroup.mapGL ℚ)
  symbols ρ U

end IntegralRelativeSymbols


