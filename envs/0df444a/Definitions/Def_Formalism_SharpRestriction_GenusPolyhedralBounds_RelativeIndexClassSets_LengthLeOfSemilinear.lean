-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LengthLeOfSemilinear
-- name    : Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LengthLeOfSemilinear
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:52:57.532154+00:00
-- url     : https://prove2.me/theorems/9b104c31-83bd-4904-9ebf-09d2112aea2d
-- title:
--   Length Le Of Semilinear
-- statement:
--   Definitions and structural lemmas for Length Le Of Semilinear, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LengthLeOfSemilinear.lean

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepClosed
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepDescent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.Gaps.T0
open Module Formalism.LatticeBaseChangeAlt Formalism.LatticeBaseChangeAlt.BQuot
section General
variable {O V W : Type*} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup W] [Module O W]
end General
def LocalStepQ : Prop :=
  ∀ (O K V W : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module O W]
    (ϖ : O), Irreducible ϖ → ∀ (M Θ N₁ Z Zm N' Mgg : Submodule O V) (e n q : ℕ) (th : Fin n → V)
    (AA AA' N₁' : Submodule O W) (ρ : ↥N' →ₗ[O] W),
    Formalism.LatticeIndexTer.IsLat O K V M → Formalism.LatticeIndexTer.IsLat O K V Θ →
    N₁ ⊔ Z ≤ Θ → (∀ j, th j ∈ M) → (∀ j, th j ∈ Θ) →
    Mgg ≤ M →
    Submodule.span K (Mgg : Set V) ≤ Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V) →
    Module.length O (↥M ⧸ (Mgg ⊔ Submodule.span O (Set.range th)).comap M.subtype) ≤ (q : ℕ∞) →
    M.map ((ϖ ^ e) • (LinearMap.id : V →ₗ[O] V)) ⊓
      (Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V)).restrictScalars O ≤ N' →
    N₁ ≤ N' → Z ≤ Zm → Zm ≤ N' → (∀ x, ρ x ∈ AA') →
    LinearMap.ker ρ = Zm.comap N'.subtype → (N₁.comap N'.subtype).map ρ = N₁' → N₁' ≤ AA →
    AA ≤ AA' →
    Module.length O (↥AA' ⧸ AA.comap AA'.subtype) ≠ ⊤ →
    Module.length O (↥AA ⧸ N₁'.comap AA.subtype) ≠ ⊤ →
    Module.length O (↥Zm ⧸ Z.comap Zm.subtype) ≠ ⊤ →
    ∀ V' : Submodule K V,
      Formalism.LatticeIndexTer.idx O V (M ⊓ V'.restrictScalars O) (Θ ⊓ V'.restrictScalars O) ≤
        (e : ℤ) * (finrank K V' : ℤ) +
          ((Module.length O (↥AA' ⧸ AA.comap AA'.subtype)).toNat : ℤ) +
          ((Module.length O (↥AA ⧸ N₁'.comap AA.subtype)).toNat : ℤ) +
          ((Module.length O (↥Zm ⧸ Z.comap Zm.subtype)).toNat : ℤ) + (q : ℤ)
def LocalStepLevelsQ : Prop :=
  ∀ (ι : Type) [Fintype ι] (ep f : ι → ℕ) (ν v : ι → ℝ) (νs c' : ℝ) (T R I : ℕ),
    (∀ z, 1 ≤ ep z) → 1 ≤ T → 0 ≤ c' → (∀ z, 0 ≤ v z) → (∀ z, ν z ≤ νs + c' * v z) →
  ∀ (O K V W : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module O W]
    (ϖ : O), Irreducible ϖ → ∀ (M Θ N₁ Z Zm N' Mgg : Submodule O V) (e n q : ℕ) (th : Fin n → V)
    (AA AA' N₁' : Submodule O W) (ρ : ↥N' →ₗ[O] W),
    Formalism.LatticeIndexTer.IsLat O K V M → Formalism.LatticeIndexTer.IsLat O K V Θ →
    N₁ ⊔ Z ≤ Θ → (∀ j, th j ∈ M) → (∀ j, th j ∈ Θ) →
    Mgg ≤ M →
    Submodule.span K (Mgg : Set V) ≤ Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V) →
    Module.length O (↥M ⧸ (Mgg ⊔ Submodule.span O (Set.range th)).comap M.subtype) ≤ (q : ℕ∞) →
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
      (Formalism.LatticeIndexTer.idx O V (M ⊓ V'.restrictScalars O) (Θ ⊓ V'.restrictScalars O) : ℝ) ≤
        (e : ℝ) * (finrank K V' : ℝ) +
            (R : ℝ) * ((T : ℝ) * c' * ∑ z, ((ep z : ℝ) * f z) * v z) + (R : ℝ) * (I : ℝ) +
            ((Module.length O (↥Zm ⧸ Z.comap Zm.subtype)).toNat : ℝ) + (q : ℝ)
def LocalStepClosedQ : Prop :=
  ∀ (ι : Type) [Fintype ι] (ep f : ι → ℕ) (ν v : ι → ℝ) (νs c' : ℝ) (T R I : ℕ),
    (∀ z, 1 ≤ ep z) → 1 ≤ T → 0 ≤ c' → (∀ z, 0 ≤ v z) → (∀ z, ν z ≤ νs + c' * v z) →
  ∀ (O K V W : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module O W]
    (ϖ : O), Irreducible ϖ → ∀ (M Θ N₁ Z Zm N' Mgg : Submodule O V) (e n q : ℕ) (th : Fin n → V)
    (AA AA' N₁' : Submodule O W) (ρ : ↥N' →ₗ[O] W),
    Formalism.LatticeIndexTer.IsLat O K V M → Formalism.LatticeIndexTer.IsLat O K V Θ →
    N₁ ⊔ Z ≤ Θ → (∀ j, th j ∈ M) → (∀ j, th j ∈ Θ) →
    Mgg ≤ M →
    Submodule.span K (Mgg : Set V) ≤ Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V) →
    Module.length O (↥M ⧸ (Mgg ⊔ Submodule.span O (Set.range th)).comap M.subtype) ≤ (q : ℕ∞) →
    M.map ((ϖ ^ e) • (LinearMap.id : V →ₗ[O] V)) ⊓
      (Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V)).restrictScalars O ≤ N' →
    N₁ ≤ N' → Z ≤ Zm → Zm ≤ N' → (∀ x, ρ x ∈ AA') →
    LinearMap.ker ρ = Zm.comap N'.subtype → (N₁.comap N'.subtype).map ρ = N₁' → N₁' ≤ AA →
    AA ≤ AA' →
    Module.length O (↥Zm ⧸ Z.comap Zm.subtype) ≠ ⊤ →
    (((T : ℝ) * νs ≤ (e : ℝ) ∧ ∀ z, ∃ m : ℤ, (ep z : ℝ) * ν z = m) ∨ (T : ℝ) * νs + 1 ≤ (e : ℝ)) →
    ∀ (Rr Aq : ι → Type) [∀ z, CommRing (Rr z)] [∀ z, IsLocalRing (Rr z)] [∀ z, Algebra O (Rr z)]
      [∀ z, IsLocalHom (algebraMap O (Rr z))] [∀ z, AddCommGroup (Aq z)] [∀ z, Module (Rr z) (Aq z)]
      [∀ z, Module O (Aq z)] [∀ z, IsScalarTower O (Rr z) (Aq z)]
      (xq : ∀ z, Rr z) (nq : ι → ℕ) (Fq : ∀ z, ℕ → Submodule (Rr z) (Aq z)) (rq : ι → ℕ → ℕ),
    (∀ z, Fq z 0 = ⊤) → (∀ z, Fq z (nq z) = ⊥) → (∀ z k, k < nq z → Fq z (k + 1) ≤ Fq z k) →
    (∀ z k, k < nq z → ∀ y ∈ Fq z k, xq z • y ∈ Fq z (k + 1) → y ∈ Fq z (k + 1)) →
    (∀ z k, k < nq z →
      Module.length (Rr z)
          (↥(Fq z k) ⧸ (Fq z (k + 1) ⊔ (Fq z k).map
            ((xq z ^ (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat) •
              (LinearMap.id : Aq z →ₗ[Rr z] Aq z))).comap (Fq z k).subtype) =
        ((rq z k * (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat : ℕ) : ℕ∞)) →
    (∀ z, ∑ k ∈ Finset.range (nq z), rq z k = R) →
    (∀ z, Module.length (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField (Rr z)) = (f z : ℕ∞)) →
    Nonempty ((↥AA' ⧸ AA.comap AA'.subtype) ≃ₗ[O]
      ((z : ι) → Aq z ⧸ (⊤ : Submodule (Rr z) (Aq z)).map
        ((xq z ^ (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat) •
          (LinearMap.id : Aq z →ₗ[Rr z] Aq z)))) →
    ∀ (A0 : Type) [AddCommGroup A0] [Module O A0] (n1 : ℕ) (F1 : ℕ → Submodule O ↥AA) (ι1 : Type)
      [Fintype ι1] [DecidableEq ι1] (deg : ι1 → ℕ) (δ : ℕ) (t : Fin δ → A0)
      (σ : ∀ k, ↥(F1 k) →ₗ[O] ({α : ι1 // deg α = k} → A0)) (u : ι1 → Fin δ → ↥AA),
    F1 0 = ⊤ → F1 n1 = ⊥ → (∀ k, F1 (k + 1) ≤ F1 k) →
    (∀ k, LinearMap.ker (σ k) = (F1 (k + 1)).comap (F1 k).subtype) →
    (∀ k, Function.Surjective (σ k)) → (∀ α, deg α < n1) →
    (∀ α i, ∃ h : u α i ∈ F1 (deg α), σ (deg α) ⟨u α i, h⟩ = Pi.single ⟨α, rfl⟩ (t i)) →
    LinearIndependent O t →
    N₁'.comap AA.subtype = Submodule.span O (Set.range fun p : ι1 × Fin δ => u p.1 p.2) →
    Fintype.card ι1 = R →
    Module.length O (A0 ⧸ Submodule.span O (Set.range t)) = (I : ℕ∞) →
    ∀ V' : Submodule K V,
      (Formalism.LatticeIndexTer.idx O V (M ⊓ V'.restrictScalars O) (Θ ⊓ V'.restrictScalars O) : ℝ) ≤
        (e : ℝ) * (finrank K V' : ℝ) +
            (R : ℝ) * ((T : ℝ) * c' * ∑ z, ((ep z : ℝ) * f z) * v z) + (R : ℝ) * (I : ℝ) +
            ((Module.length O (↥Zm ⧸ Z.comap Zm.subtype)).toNat : ℝ) + (q : ℝ)
section Semilinear
variable {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O']
  [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
end Semilinear
def LocalStepClosedQDescUp : Prop :=
  ∀ (ι : Type) [Fintype ι] (ep f : ι → ℕ) (ν v : ι → ℝ) (νs c' : ℝ) (T R I : ℕ),
    (∀ z, 1 ≤ ep z) → 1 ≤ T → 0 ≤ c' → (∀ z, 0 ≤ v z) → (∀ z, ν z ≤ νs + c' * v z) →
  ∀ (O O' K K' V V₁ W : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    [Field K] [Algebra O K] [IsFractionRing O K] [Field K'] [Algebra O' K'] [IsFractionRing O' K']
    [Algebra K K'] [Algebra O K'] [IsScalarTower O K K'] [IsScalarTower O O' K']
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    [AddCommGroup V₁] [Module K' V₁] [Module O' V₁] [IsScalarTower O' K' V₁]
    [Module K V₁] [IsScalarTower K K' V₁] [AddCommGroup W] [Module O' W]
    (j : V →ₗ[K] V₁), IsBaseChange K' j →
    ∀ ϖ : O, Irreducible ϖ → Irreducible (algebraMap O O' ϖ) →
    ∀ (M Θ : Submodule O V) (N₁ Z Zm N' Mgg : Submodule O' V₁) (e n q : ℕ) (th : Fin n → V₁)
    (AA AA' N₁' : Submodule O' W) (ρ : ↥N' →ₗ[O'] W),
    Formalism.LatticeIndexTer.IsLat O K V M → Formalism.LatticeIndexTer.IsLat O K V Θ →
    N₁ ⊔ Z ≤ Submodule.span O' (j '' (Θ : Set V)) →
    (∀ i, th i ∈ Submodule.span O' (j '' (M : Set V))) →
    (∀ i, th i ∈ Submodule.span O' (j '' (Θ : Set V))) →
    Mgg ≤ Submodule.span O' (j '' (M : Set V)) →
    Submodule.span K' (Mgg : Set V₁) ≤ Submodule.span K' ((N₁ ⊔ Z : Submodule O' V₁) : Set V₁) →
    Module.length O' (↥(Submodule.span O' (j '' (M : Set V))) ⧸
      (Mgg ⊔ Submodule.span O' (Set.range th)).comap
        (Submodule.span O' (j '' (M : Set V))).subtype) ≤ (q : ℕ∞) →
    (Submodule.span O' (j '' (M : Set V))).map
        ((algebraMap O O' ϖ ^ e) • (LinearMap.id : V₁ →ₗ[O'] V₁)) ⊓
      (Submodule.span K' ((N₁ ⊔ Z : Submodule O' V₁) : Set V₁)).restrictScalars O' ≤ N' →
    N₁ ≤ N' → Z ≤ Zm → Zm ≤ N' → (∀ x, ρ x ∈ AA') →
    LinearMap.ker ρ = Zm.comap N'.subtype → (N₁.comap N'.subtype).map ρ = N₁' → N₁' ≤ AA →
    AA ≤ AA' →
    Module.length O' (↥Zm ⧸ Z.comap Zm.subtype) ≠ ⊤ →
    (((T : ℝ) * νs ≤ (e : ℝ) ∧ ∀ z, ∃ m : ℤ, (ep z : ℝ) * ν z = m) ∨ (T : ℝ) * νs + 1 ≤ (e : ℝ)) →
    ∀ (Rr Aq : ι → Type) [∀ z, CommRing (Rr z)] [∀ z, IsLocalRing (Rr z)] [∀ z, Algebra O' (Rr z)]
      [∀ z, IsLocalHom (algebraMap O' (Rr z))] [∀ z, AddCommGroup (Aq z)] [∀ z, Module (Rr z) (Aq z)]
      [∀ z, Module O' (Aq z)] [∀ z, IsScalarTower O' (Rr z) (Aq z)]
      (xq : ∀ z, Rr z) (nq : ι → ℕ) (Fq : ∀ z, ℕ → Submodule (Rr z) (Aq z)) (rq : ι → ℕ → ℕ),
    (∀ z, Fq z 0 = ⊤) → (∀ z, Fq z (nq z) = ⊥) → (∀ z k, k < nq z → Fq z (k + 1) ≤ Fq z k) →
    (∀ z k, k < nq z → ∀ y ∈ Fq z k, xq z • y ∈ Fq z (k + 1) → y ∈ Fq z (k + 1)) →
    (∀ z k, k < nq z →
      Module.length (Rr z)
          (↥(Fq z k) ⧸ (Fq z (k + 1) ⊔ (Fq z k).map
            ((xq z ^ (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat) •
              (LinearMap.id : Aq z →ₗ[Rr z] Aq z))).comap (Fq z k).subtype) =
        ((rq z k * (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat : ℕ) : ℕ∞)) →
    (∀ z, ∑ k ∈ Finset.range (nq z), rq z k = R) →
    (∀ z, Module.length (IsLocalRing.ResidueField O') (IsLocalRing.ResidueField (Rr z)) = (f z : ℕ∞)) →
    Nonempty ((↥AA' ⧸ AA.comap AA'.subtype) ≃ₗ[O']
      ((z : ι) → Aq z ⧸ (⊤ : Submodule (Rr z) (Aq z)).map
        ((xq z ^ (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat) •
          (LinearMap.id : Aq z →ₗ[Rr z] Aq z)))) →
    ∀ (A0 : Type) [AddCommGroup A0] [Module O' A0] (n1 : ℕ) (F1 : ℕ → Submodule O' ↥AA) (ι1 : Type)
      [Fintype ι1] [DecidableEq ι1] (deg : ι1 → ℕ) (δ : ℕ) (t : Fin δ → A0)
      (σ : ∀ k, ↥(F1 k) →ₗ[O'] ({α : ι1 // deg α = k} → A0)) (u : ι1 → Fin δ → ↥AA),
    F1 0 = ⊤ → F1 n1 = ⊥ → (∀ k, F1 (k + 1) ≤ F1 k) →
    (∀ k, LinearMap.ker (σ k) = (F1 (k + 1)).comap (F1 k).subtype) →
    (∀ k, Function.Surjective (σ k)) → (∀ α, deg α < n1) →
    (∀ α i, ∃ h : u α i ∈ F1 (deg α), σ (deg α) ⟨u α i, h⟩ = Pi.single ⟨α, rfl⟩ (t i)) →
    LinearIndependent O' t →
    N₁'.comap AA.subtype = Submodule.span O' (Set.range fun p : ι1 × Fin δ => u p.1 p.2) →
    Fintype.card ι1 = R →
    Module.length O' (A0 ⧸ Submodule.span O' (Set.range t)) = (I : ℕ∞) →
    ∀ V' : Submodule K V,
      (Formalism.LatticeIndexTer.idx O V (M ⊓ V'.restrictScalars O) (Θ ⊓ V'.restrictScalars O) : ℝ) ≤
        (e : ℝ) * (finrank K V' : ℝ) +
            (R : ℝ) * ((T : ℝ) * c' * ∑ z, ((ep z : ℝ) * f z) * v z) + (R : ℝ) * (I : ℝ) +
            ((Module.length O' (↥Zm ⧸ Z.comap Zm.subtype)).toNat : ℝ) + (q : ℝ)
def LocalStepClosedQDesc : Prop :=
  ∀ (ι : Type) [Fintype ι] (ep f : ι → ℕ) (ν v : ι → ℝ) (νs c' : ℝ) (T R I : ℕ),
    (∀ z, 1 ≤ ep z) → 1 ≤ T → 0 ≤ c' → (∀ z, 0 ≤ v z) → (∀ z, ν z ≤ νs + c' * v z) →
  ∀ (O O' K K' V V₁ W : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    [Field K] [Algebra O K] [IsFractionRing O K] [Field K'] [Algebra O' K'] [IsFractionRing O' K']
    [Algebra K K'] [Algebra O K'] [IsScalarTower O K K'] [IsScalarTower O O' K']
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    [AddCommGroup V₁] [Module K' V₁] [Module O' V₁] [IsScalarTower O' K' V₁]
    [Module K V₁] [IsScalarTower K K' V₁] [AddCommGroup W] [Module O' W]
    (j : V →ₗ[K] V₁), IsBaseChange K' j →
    ∀ ϖ : O, Irreducible ϖ → Irreducible (algebraMap O O' ϖ) →
    ∀ (M Θ Mgg : Submodule O V) (N₁ Z Zm N' : Submodule O' V₁) (e n q : ℕ) (th : Fin n → V)
    (AA AA' N₁' : Submodule O' W) (ρ : ↥N' →ₗ[O'] W),
    Formalism.LatticeIndexTer.IsLat O K V M → Formalism.LatticeIndexTer.IsLat O K V Θ →
    N₁ ⊔ Z ≤ Submodule.span O' (j '' (Θ : Set V)) → (∀ i, th i ∈ M) → (∀ i, th i ∈ Θ) →
    Mgg ≤ M →
    (∀ x ∈ Mgg, j x ∈ Submodule.span K' ((N₁ ⊔ Z : Submodule O' V₁) : Set V₁)) →
    Module.length O (↥M ⧸ (Mgg ⊔ Submodule.span O (Set.range th)).comap M.subtype) ≤ (q : ℕ∞) →
    (Submodule.span O' (j '' (M : Set V))).map
        ((algebraMap O O' ϖ ^ e) • (LinearMap.id : V₁ →ₗ[O'] V₁)) ⊓
      (Submodule.span K' ((N₁ ⊔ Z : Submodule O' V₁) : Set V₁)).restrictScalars O' ≤ N' →
    N₁ ≤ N' → Z ≤ Zm → Zm ≤ N' → (∀ x, ρ x ∈ AA') →
    LinearMap.ker ρ = Zm.comap N'.subtype → (N₁.comap N'.subtype).map ρ = N₁' → N₁' ≤ AA →
    AA ≤ AA' →
    Module.length O' (↥Zm ⧸ Z.comap Zm.subtype) ≠ ⊤ →
    (((T : ℝ) * νs ≤ (e : ℝ) ∧ ∀ z, ∃ m : ℤ, (ep z : ℝ) * ν z = m) ∨ (T : ℝ) * νs + 1 ≤ (e : ℝ)) →
    ∀ (Rr Aq : ι → Type) [∀ z, CommRing (Rr z)] [∀ z, IsLocalRing (Rr z)] [∀ z, Algebra O' (Rr z)]
      [∀ z, IsLocalHom (algebraMap O' (Rr z))] [∀ z, AddCommGroup (Aq z)] [∀ z, Module (Rr z) (Aq z)]
      [∀ z, Module O' (Aq z)] [∀ z, IsScalarTower O' (Rr z) (Aq z)]
      (xq : ∀ z, Rr z) (nq : ι → ℕ) (Fq : ∀ z, ℕ → Submodule (Rr z) (Aq z)) (rq : ι → ℕ → ℕ),
    (∀ z, Fq z 0 = ⊤) → (∀ z, Fq z (nq z) = ⊥) → (∀ z k, k < nq z → Fq z (k + 1) ≤ Fq z k) →
    (∀ z k, k < nq z → ∀ y ∈ Fq z k, xq z • y ∈ Fq z (k + 1) → y ∈ Fq z (k + 1)) →
    (∀ z k, k < nq z →
      Module.length (Rr z)
          (↥(Fq z k) ⧸ (Fq z (k + 1) ⊔ (Fq z k).map
            ((xq z ^ (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat) •
              (LinearMap.id : Aq z →ₗ[Rr z] Aq z))).comap (Fq z k).subtype) =
        ((rq z k * (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat : ℕ) : ℕ∞)) →
    (∀ z, ∑ k ∈ Finset.range (nq z), rq z k = R) →
    (∀ z, Module.length (IsLocalRing.ResidueField O') (IsLocalRing.ResidueField (Rr z)) = (f z : ℕ∞)) →
    Nonempty ((↥AA' ⧸ AA.comap AA'.subtype) ≃ₗ[O']
      ((z : ι) → Aq z ⧸ (⊤ : Submodule (Rr z) (Aq z)).map
        ((xq z ^ (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat) •
          (LinearMap.id : Aq z →ₗ[Rr z] Aq z)))) →
    ∀ (A0 : Type) [AddCommGroup A0] [Module O' A0] (n1 : ℕ) (F1 : ℕ → Submodule O' ↥AA) (ι1 : Type)
      [Fintype ι1] [DecidableEq ι1] (deg : ι1 → ℕ) (δ : ℕ) (t : Fin δ → A0)
      (σ : ∀ k, ↥(F1 k) →ₗ[O'] ({α : ι1 // deg α = k} → A0)) (u : ι1 → Fin δ → ↥AA),
    F1 0 = ⊤ → F1 n1 = ⊥ → (∀ k, F1 (k + 1) ≤ F1 k) →
    (∀ k, LinearMap.ker (σ k) = (F1 (k + 1)).comap (F1 k).subtype) →
    (∀ k, Function.Surjective (σ k)) → (∀ α, deg α < n1) →
    (∀ α i, ∃ h : u α i ∈ F1 (deg α), σ (deg α) ⟨u α i, h⟩ = Pi.single ⟨α, rfl⟩ (t i)) →
    LinearIndependent O' t →
    N₁'.comap AA.subtype = Submodule.span O' (Set.range fun p : ι1 × Fin δ => u p.1 p.2) →
    Fintype.card ι1 = R →
    Module.length O' (A0 ⧸ Submodule.span O' (Set.range t)) = (I : ℕ∞) →
    ∀ V' : Submodule K V,
      (Formalism.LatticeIndexTer.idx O V (M ⊓ V'.restrictScalars O) (Θ ⊓ V'.restrictScalars O) : ℝ) ≤
        (e : ℝ) * (finrank K V' : ℝ) +
            (R : ℝ) * ((T : ℝ) * c' * ∑ z, ((ep z : ℝ) * f z) * v z) + (R : ℝ) * (I : ℝ) +
            ((Module.length O' (↥Zm ⧸ Z.comap Zm.subtype)).toNat : ℝ) + (q : ℝ)
end Formalism.MainNotions.Gaps.T0


