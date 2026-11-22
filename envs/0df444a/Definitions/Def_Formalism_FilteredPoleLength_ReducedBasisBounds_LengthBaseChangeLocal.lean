-- Prove2me | Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_LengthBaseChangeLocal
-- name    : Formalism_FilteredPoleLength_ReducedBasisBounds_LengthBaseChangeLocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:44:35.763283+00:00
-- url     : https://prove2.me/theorems/c542171f-b5c5-4282-acd9-c67b35c62702
-- title:
--   Length Base Change Local
-- statement:
--   Definitions and structural lemmas for Length Base Change Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/ReducedBasisBounds/LengthBaseChangeLocal.lean

import Mathlib
import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_IncomingBounds_IndexLastStep
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
def LocalStep : Prop :=
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
    ∀ V' : Submodule K V,
      Formalism.LatticeIndexTer.idx O V (M ⊓ V'.restrictScalars O) (Θ ⊓ V'.restrictScalars O) ≤
        (e : ℤ) * (finrank K V' : ℤ) +
          ((Module.length O (↥AA' ⧸ AA.comap AA'.subtype)).toNat : ℤ) +
          ((Module.length O (↥AA ⧸ N₁'.comap AA.subtype)).toNat : ℤ) +
          ((Module.length O (↥Zm ⧸ Z.comap Zm.subtype)).toNat : ℤ) +
          (((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
            ((IsDiscreteValuationRing.addVal O a').toNat : ℤ) + (n : ℤ) * (be : ℤ))
def LevelsChain : Prop :=
  ∀ (ι : Type) [Fintype ι] (ep f : ι → ℕ) (ν v : ι → ℝ) (νs c' : ℝ) (T : ℕ) (e : ℤ),
    (∀ z, 1 ≤ ep z) → 1 ≤ T → 0 ≤ c' → (∀ z, 0 ≤ v z) → (∀ z, ν z ≤ νs + c' * v z) →
    (((T : ℝ) * νs ≤ e ∧ ∀ z, ∃ n : ℤ, (ep z : ℝ) * ν z = n) ∨ e = ⌈(T : ℝ) * (νs + 1)⌉) →
      ∑ z, ((max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - e)⌉ : ℤ) : ℝ) * f z ≤
        T * c' * ∑ z, ((ep z : ℝ) * f z) * v z
def LengthBaseChange : Prop :=
  ∀ (O O₁ Q : Type) [CommRing O] [CommRing O₁] [Algebra O O₁] [AddCommGroup Q] [Module O Q]
    (d : ℕ), Nonempty (Basis (Fin d) O O₁) →
      Module.length O (TensorProduct O O₁ Q) = d * Module.length O Q
def LengthBaseChangeLocal : Prop :=
  ∀ (O O₁ Q : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O₁]
    [IsDomain O₁] [IsDiscreteValuationRing O₁] [Algebra O O₁] [AddCommGroup Q] [Module O Q]
    (ϖ : O) (ϖ₁ : O₁) (u : O₁ˣ) (ε : ℕ), Irreducible ϖ → Irreducible ϖ₁ →
    algebraMap O O₁ ϖ = u * ϖ₁ ^ ε → Module.length O Q ≠ ⊤ →
      Module.length O₁ (TensorProduct O O₁ Q) = ε * Module.length O Q
def QuotientLengthExt : Prop :=
  ∀ (O K K₁ V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [Field K₁] [Algebra K K₁] [FiniteDimensional K K₁]
    [Algebra.IsSeparable K K₁] [Algebra O K₁] [IsScalarTower O K K₁]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (ϖ : O), Irreducible ϖ → ∀ (n : ℕ) (c : V →ₗ[K] (Fin n → K₁)) (N : Submodule K V),
    LinearMap.ker c ≤ N → ∀ (th : Fin n → V),
    LinearMap.ker c ⊔ Submodule.span K (Set.range th) = ⊤ →
    ∀ (X : Submodule O V) (e be : ℕ),
    (∀ x ∈ X, ∀ i, ∃ y ∈ integralClosure O K₁,
        c x i = (algebraMap O K₁ ϖ) ^ ((e : ℤ) - (be : ℤ)) * y) →
    (∀ j, (algebraMap O K ϖ) ^ e • th j ∈ X) →
    ∀ a a' : O, a ≠ 0 → a' ≠ 0 →
    algebraMap O K a = Algebra.norm K (Matrix.of fun i j => c (th j) i).det * algebraMap O K a' →
      let Tj : Submodule O V := Submodule.span O (Set.range fun j => (algebraMap O K ϖ) ^ e • th j)
      ∃ m : ℕ, Module.length O (↥X ⧸ ((X ⊓ N.restrictScalars O) ⊔ Tj).comap X.subtype) = m ∧
        (finrank K K₁ : ℤ) * (m : ℤ) ≤ ((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
          ((IsDiscreteValuationRing.addVal O a').toNat : ℤ) + (finrank K K₁ : ℤ) * (n : ℤ) * (be : ℤ)
def LocalStepExt : Prop :=
  ∀ (O K K₁ V W : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [Field K₁] [Algebra K K₁] [FiniteDimensional K K₁]
    [Algebra.IsSeparable K K₁] [Algebra O K₁] [IsScalarTower O K K₁]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module O W]
    (ϖ : O), Irreducible ϖ → ∀ (M Θ N₁ Z Zm N' : Submodule O V) (e be n : ℕ) (th : Fin n → V)
    (c : V →ₗ[K] (Fin n → K₁)) (AA AA' N₁' : Submodule O W) (ρ : ↥N' →ₗ[O] W) (a a' : O),
    let X : Submodule O V := M.map ((ϖ ^ e) • (LinearMap.id : V →ₗ[O] V))
    let NK : Submodule O V := (Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V)).restrictScalars O
    Formalism.LatticeIndexTer.IsLat O K V M → Formalism.LatticeIndexTer.IsLat O K V Θ →
    N₁ ⊔ Z ≤ Θ → (∀ j, th j ∈ M) → (∀ j, th j ∈ Θ) →
    LinearMap.ker c ≤ Submodule.span K ((N₁ ⊔ Z : Submodule O V) : Set V) →
    LinearMap.ker c ⊔ Submodule.span K (Set.range th) = ⊤ →
    (∀ x ∈ M, ∀ i, ∃ y ∈ integralClosure O K₁, c x i = (algebraMap O K₁ ϖ) ^ (-(be : ℤ)) * y) →
    a ≠ 0 → a' ≠ 0 →
    algebraMap O K a = Algebra.norm K (Matrix.of fun i j => c (th j) i).det * algebraMap O K a' →
    X ⊓ NK ≤ N' → N₁ ≤ N' → Z ≤ Zm → Zm ≤ N' → (∀ x, ρ x ∈ AA') →
    LinearMap.ker ρ = Zm.comap N'.subtype → (N₁.comap N'.subtype).map ρ = N₁' → N₁' ≤ AA →
    AA ≤ AA' →
    Module.length O (↥AA' ⧸ AA.comap AA'.subtype) ≠ ⊤ →
    Module.length O (↥AA ⧸ N₁'.comap AA.subtype) ≠ ⊤ →
    Module.length O (↥Zm ⧸ Z.comap Zm.subtype) ≠ ⊤ →
    ∀ V' : Submodule K V,
      (finrank K K₁ : ℤ) *
          Formalism.LatticeIndexTer.idx O V (M ⊓ V'.restrictScalars O) (Θ ⊓ V'.restrictScalars O) ≤
        (finrank K K₁ : ℤ) * ((e : ℤ) * (finrank K V' : ℤ) +
          ((Module.length O (↥AA' ⧸ AA.comap AA'.subtype)).toNat : ℤ) +
          ((Module.length O (↥AA ⧸ N₁'.comap AA.subtype)).toNat : ℤ) +
          ((Module.length O (↥Zm ⧸ Z.comap Zm.subtype)).toNat : ℤ)) +
          (((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
            ((IsDiscreteValuationRing.addVal O a').toNat : ℤ) +
            (finrank K K₁ : ℤ) * (n : ℤ) * (be : ℤ))
end Formalism.LatticeBaseChangeAlt


