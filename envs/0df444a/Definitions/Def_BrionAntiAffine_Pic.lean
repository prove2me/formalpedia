-- Prove2me | Definitions.Def_BrionAntiAffine_Pic
-- name    : BrionAntiAffine_Pic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:03.219409+00:00
-- url     : https://prove2.me/theorems/9af83a7a-aa31-4607-a007-7ed9a856065d
-- title:
--   The Picard group of a scheme
-- statement:
--   For a scheme $X$, the **Picard group** $\mathrm{Pic}(X)$ is the set of isomorphism classes of invertible $\mathcal O_X$-modules, with multiplication induced by the tensor product, identity the class of $\mathcal O_X$, and inverse the class of a tensor inverse. A morphism $f:X\to Y$ induces a pullback map $f^*:\mathrm{Pic}(Y)\to\mathrm{Pic}(X)$.
--
--   Here $\mathrm{Pic}(A_{k_s})$ and $\mathrm{Pic}(G_{k_s})$ carry the lattice invariant of an anti-affine group.
--
--   **Formalization Note** No finiteness or rigidification is imposed. Invertibility is the published predicate `Scheme.Modules.IsInvertible` (local triviality); the group law uses the published theorems that tensor products of invertible sheaves are invertible and that invertible sheaves have tensor inverses.
-- source:
--   M. Brion, Anti-affine algebraic groups, arXiv:0710.5211v3, §2.1, p.7 (Pic(A_ks)); §2.4, p.11 (pull-back map to Pic(X))

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry MonoidalCategory

noncomputable section

namespace BrionAntiAffine

/-- Invertible sheaves on `X`, with isomorphism as the relation. -/
def picSetoid (X : Scheme.{u}) :
    Setoid {M : X.Modules // Scheme.Modules.IsInvertible M} where
  r M N := Nonempty (M.1 ≅ N.1)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e ≪≫ f⟩⟩

/-- The Picard group of a scheme `X`: isomorphism classes of invertible sheaves, with no finiteness
or rigidification condition. Used on `A_ks` and `G_ks` by Brion, arXiv:0710.5211v3, §2, p.7. -/
def Pic (X : Scheme.{u}) : Type (u + 1) := Quotient (picSetoid X)

namespace Pic

variable {X : Scheme.{u}}

/-- The class of an invertible sheaf. -/
def mk (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) : Pic X :=
  Quotient.mk (picSetoid X) ⟨M, hM⟩

/-- `𝒪_X` is invertible, as the monoidal unit of `X.Modules`. -/
theorem isInvertible_unit : Scheme.Modules.IsInvertible (𝟙_ X.Modules) :=
  Scheme.Modules.isInvertible_unit X

instance : CommGroup (Pic X) :=
  letI : Mul (Pic X) := ⟨Quotient.map₂
    (fun M N => ⟨M.1 ⊗ N.1, Scheme.Modules.IsInvertible.tensor M.2 N.2⟩)
    (fun _ _ ⟨e⟩ _ _ ⟨f⟩ => ⟨e ⊗ᵢ f⟩)⟩
  letI : One (Pic X) := ⟨mk (𝟙_ X.Modules) isInvertible_unit⟩
  letI : Inv (Pic X) := ⟨Quotient.lift
    (fun M => mk (Classical.choose (Scheme.Modules.IsInvertible.exists_tensor_inverse M.2))
      (Classical.choose_spec (Scheme.Modules.IsInvertible.exists_tensor_inverse M.2)).1)
    (by
      rintro ⟨M, hM⟩ ⟨N, hN⟩ ⟨e⟩
      obtain ⟨hM', ⟨a⟩⟩ := Classical.choose_spec (Scheme.Modules.IsInvertible.exists_tensor_inverse hM)
      obtain ⟨hN', ⟨b⟩⟩ := Classical.choose_spec (Scheme.Modules.IsInvertible.exists_tensor_inverse hN)
      set M' := Classical.choose (Scheme.Modules.IsInvertible.exists_tensor_inverse hM)
      set N' := Classical.choose (Scheme.Modules.IsInvertible.exists_tensor_inverse hN)
      refine Quotient.sound ⟨?_⟩
      exact (ρ_ M').symm ≪≫ whiskerLeftIso M' b.symm ≪≫ whiskerLeftIso M' (whiskerRightIso e.symm N') ≪≫
        (α_ M' M N').symm ≪≫ whiskerRightIso (β_ M' M ≪≫ a) N' ≪≫ λ_ N')⟩
  { mul_assoc := by
      rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
      exact Quotient.sound ⟨α_ _ _ _⟩
    one_mul := by
      rintro ⟨a⟩
      exact Quotient.sound ⟨λ_ _⟩
    mul_one := by
      rintro ⟨a⟩
      exact Quotient.sound ⟨ρ_ _⟩
    mul_comm := by
      rintro ⟨a⟩ ⟨b⟩
      exact Quotient.sound ⟨β_ _ _⟩
    inv_mul_cancel := by
      rintro ⟨M, hM⟩
      obtain ⟨hM', ⟨a⟩⟩ := Classical.choose_spec (Scheme.Modules.IsInvertible.exists_tensor_inverse hM)
      exact Quotient.sound ⟨β_ _ _ ≪≫ a⟩ }

/-- The structure sheaf `𝒪_X` as a sheaf of modules on `X`. -/
abbrev unitMod (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- Pullback of classes of invertible sheaves along a morphism of schemes. -/
def pullback {X Y : Scheme.{u}} (f : X ⟶ Y) : Pic Y → Pic X :=
  Quotient.map' (s₁ := picSetoid Y) (s₂ := picSetoid X)
    (fun M => ⟨(Scheme.Modules.pullback f).obj M.1, Scheme.Modules.IsInvertible.pullback f M.2⟩)
    (fun _ _ ⟨e⟩ => ⟨(Scheme.Modules.pullback f).mapIso e⟩)

end Pic

end BrionAntiAffine


