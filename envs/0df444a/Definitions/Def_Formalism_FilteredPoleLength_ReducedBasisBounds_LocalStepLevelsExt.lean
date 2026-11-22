-- Prove2me | Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_LocalStepLevelsExt
-- name    : Formalism_FilteredPoleLength_ReducedBasisBounds_LocalStepLevelsExt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:50:56.360509+00:00
-- url     : https://prove2.me/theorems/68abb104-295d-411c-82e9-99688e9f06bd
-- title:
--   Local Step Levels Ext
-- statement:
--   Definitions and structural lemmas for Local Step Levels Ext, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/ReducedBasisBounds/LocalStepLevelsExt.lean

import Mathlib
import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_LengthBaseChangeLocal
import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_FilteredPoleLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.LatticeBaseChangeAlt
open Module
def LevelsLengthSum : Prop :=
  ∀ (O' : Type) [CommRing O'] [IsLocalRing O'] (ι : Type) [Fintype ι]
    (Rr A : ι → Type) [∀ z, CommRing (Rr z)] [∀ z, IsLocalRing (Rr z)] [∀ z, Algebra O' (Rr z)]
    [∀ z, IsLocalHom (algebraMap O' (Rr z))] [∀ z, AddCommGroup (A z)] [∀ z, Module (Rr z) (A z)]
    [∀ z, Module O' (A z)] [∀ z, IsScalarTower O' (Rr z) (A z)]
    (x : ∀ z, Rr z) (mm n : ι → ℕ) (F : ∀ z, ℕ → Submodule (Rr z) (A z)) (r : ι → ℕ → ℕ) (R : ℕ),
    (∀ z, F z 0 = ⊤) → (∀ z, F z (n z) = ⊥) → (∀ z k, k < n z → F z (k + 1) ≤ F z k) →
    (∀ z k, k < n z → ∀ a ∈ F z k, x z • a ∈ F z (k + 1) → a ∈ F z (k + 1)) →
    (∀ z k, k < n z →
      Module.length (Rr z)
          (↥(F z k) ⧸ (F z (k + 1) ⊔ (F z k).map ((x z ^ mm z) • (LinearMap.id : A z →ₗ[Rr z] A z))).comap
            (F z k).subtype) = ((r z k * mm z : ℕ) : ℕ∞)) →
    (∀ z, ∑ k ∈ Finset.range (n z), r z k = R) →
      Module.length O' (∀ z, A z ⧸ (⊤ : Submodule (Rr z) (A z)).map
          ((x z ^ mm z) • (LinearMap.id : A z →ₗ[Rr z] A z))) =
        ∑ z, ((R * mm z : ℕ) : ℕ∞) *
          Module.length (IsLocalRing.ResidueField O') (IsLocalRing.ResidueField (Rr z))
def LocalStepLevels : Prop :=
  ∀ (ι : Type) [Fintype ι] (ep f : ι → ℕ) (ν v : ι → ℝ) (νs c' : ℝ) (T R I : ℕ),
    (∀ z, 1 ≤ ep z) → 1 ≤ T → 0 ≤ c' → (∀ z, 0 ≤ v z) → (∀ z, ν z ≤ νs + c' * v z) →

  ∀ (O K V W : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module O W]
    (ϖ : O), Irreducible ϖ → ∀ (M Θ N₁ Z Zm N' : Submodule O V) (e be n : ℕ) (th : Fin n → V)
    (c : V →ₗ[K] (Fin n → K)) (AA AA' N₁' : Submodule O W) (ρ : ↥N' →ₗ[O] W) (a a' : O),
    let X : Submodule O V := M.map ((ϖ ^ e) • (LinearMap.id : V →ₗ[O] V))
    let NK : Submodule O V := (Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V)).restrictScalars O
    Formalism.LatticeIndexTer.IsLat O K V M → Formalism.LatticeIndexTer.IsLat O K V Θ →
    N₁ ⊔ Z ≤ Θ → (∀ j, th j ∈ M) → (∀ j, th j ∈ Θ) →
    LinearMap.ker c ≤ Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V) →
    (∀ x ∈ M, ∀ i, ∃ u : O, c x i = (algebraMap O K ϖ) ^ (-(be : ℤ)) * algebraMap O K u) →
    a ≠ 0 → a' ≠ 0 →
    algebraMap O K a = (Matrix.of fun i j => c (th j) i).det * algebraMap O K a' →
    X ⊓ NK ≤ N' → N₁ ≤ N' → Z ≤ Zm → Zm ≤ N' → (∀ x, ρ x ∈ AA') →
    LinearMap.ker ρ = Zm.comap N'.subtype → (N₁.comap N'.subtype).map ρ = N₁' → N₁' ≤ AA →
    AA ≤ AA' →
    Module.length O (↥AA' ⧸ AA.comap AA'.subtype) ≠ ⊤ →
    Module.length O (↥AA ⧸ N₁'.comap AA.subtype) ≠ ⊤ →
    Module.length O (↥Zm ⧸ Z.comap Zm.subtype) ≠ ⊤ →

    (((T : ℝ) * νs ≤ (e : ℝ) ∧ ∀ z, ∃ m : ℤ, (ep z : ℝ) * ν z = m) ∨ (e : ℤ) = ⌈(T : ℝ) * (νs + 1)⌉) →
    Module.length O (↥AA' ⧸ AA.comap AA'.subtype) =
      ((R * ∑ z, (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat * f z : ℕ) : ℕ∞) →
    Module.length O (↥AA ⧸ N₁'.comap AA.subtype) = ((R * I : ℕ) : ℕ∞) →
    ∀ V' : Submodule K V,
      (Formalism.LatticeIndexTer.idx O V (M ⊓ V'.restrictScalars O) (Θ ⊓ V'.restrictScalars O) : ℝ) ≤
        (e : ℝ) * (finrank K V' : ℝ) +
          (R : ℝ) * ((T : ℝ) * c' * ∑ z, ((ep z : ℝ) * f z) * v z) +
          (R : ℝ) * (I : ℝ) +
          ((Module.length O (↥Zm ⧸ Z.comap Zm.subtype)).toNat : ℝ) +
          (((IsDiscreteValuationRing.addVal O a).toNat : ℝ) -
            ((IsDiscreteValuationRing.addVal O a').toNat : ℝ) + (n : ℝ) * (be : ℝ))
def LocalStepLevelsExt : Prop :=
  ∀ (ι : Type) [Fintype ι] (ep f : ι → ℕ) (ν v : ι → ℝ) (νs c' : ℝ) (T R I : ℕ),
    (∀ z, 1 ≤ ep z) → 1 ≤ T → 0 ≤ c' → (∀ z, 0 ≤ v z) → (∀ z, ν z ≤ νs + c' * v z) →
  ∀ (O K K₁ V W : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [Field K₁] [Algebra K K₁] [FiniteDimensional K K₁]
    [Algebra.IsSeparable K K₁] [Algebra O K₁] [IsScalarTower O K K₁]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module O W]
    (ϖ : O), Irreducible ϖ → ∀ (M Θ N₁ Z Zm N' : Submodule O V) (e be n : ℕ) (th : Fin n → V)
    (c : V →ₗ[K] (Fin n → K₁)) (AA AA' N₁' : Submodule O W) (ρ : ↥N' →ₗ[O] W) (a a' : O),
    Formalism.LatticeIndexTer.IsLat O K V M → Formalism.LatticeIndexTer.IsLat O K V Θ →
    N₁ ⊔ Z ≤ Θ → (∀ j, th j ∈ M) → (∀ j, th j ∈ Θ) →
    LinearMap.ker c ≤ Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V) →
    LinearMap.ker c ⊔ Submodule.span K (Set.range th) = ⊤ →
    (∀ x ∈ M, ∀ i, ∃ y ∈ integralClosure O K₁, c x i = (algebraMap O K₁ ϖ) ^ (-(be : ℤ)) * y) →
    a ≠ 0 → a' ≠ 0 →
    algebraMap O K a =
      Algebra.norm K (Matrix.of fun i j => c (th j) i).det * algebraMap O K a' →
    M.map ((ϖ ^ e) • (LinearMap.id : V →ₗ[O] V)) ⊓
      (Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V)).restrictScalars O ≤ N' →
    N₁ ≤ N' → Z ≤ Zm → Zm ≤ N' → (∀ x, ρ x ∈ AA') →
    LinearMap.ker ρ = Zm.comap N'.subtype → (N₁.comap N'.subtype).map ρ = N₁' → N₁' ≤ AA →
    AA ≤ AA' →
    Module.length O (↥Zm ⧸ Z.comap Zm.subtype) ≠ ⊤ →
    (((T : ℝ) * νs ≤ (e : ℝ) ∧ ∀ z, ∃ m : ℤ, (ep z : ℝ) * ν z = m) ∨ (T : ℝ) * νs + 1 ≤ (e : ℝ)) →
    Module.length O (↥AA' ⧸ AA.comap AA'.subtype) ≤
      ((R * ∑ z, (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat * f z : ℕ) : ℕ∞) →
    Module.length O (↥AA ⧸ N₁'.comap AA.subtype) ≤ ((R * I : ℕ) : ℕ∞) →
    ∀ V' : Submodule K V,
      (finrank K K₁ : ℝ) *
          (Formalism.LatticeIndexTer.idx O V (M ⊓ V'.restrictScalars O) (Θ ⊓ V'.restrictScalars O) : ℝ) ≤
        (finrank K K₁ : ℝ) * ((e : ℝ) * (finrank K V' : ℝ) +
            (R : ℝ) * ((T : ℝ) * c' * ∑ z, ((ep z : ℝ) * f z) * v z) + (R : ℝ) * (I : ℝ) +
            ((Module.length O (↥Zm ⧸ Z.comap Zm.subtype)).toNat : ℝ)) +
          (((IsDiscreteValuationRing.addVal O a).toNat : ℝ) -
            ((IsDiscreteValuationRing.addVal O a').toNat : ℝ) +
            (finrank K K₁ : ℝ) * (n : ℝ) * (be : ℝ))
end Formalism.LatticeBaseChangeAlt


