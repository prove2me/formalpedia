-- Prove2me | Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
-- name    : Formalism_LogFactorialIndices_StatementIdx
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:30:24.862455+00:00
-- url     : https://prove2.me/theorems/424da02c-3300-49fc-8579-697cd321af95
-- title:
--   Statement Idx
-- statement:
--   Definitions and structural lemmas for Statement Idx, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/StatementIdx.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.LatticeIndexTer
open Module
open scoped Pointwise
section Defs
variable (O K X : Type) [CommRing O] [Field K] [Algebra O K] [AddCommGroup X] [Module K X]
  [Module O X]
def IsLat (A : Submodule O X) : Prop := A.FG ∧ Submodule.span K (A : Set X) = ⊤
end Defs
section Defs2
variable (O X : Type) [CommRing O] [AddCommGroup X] [Module O X]
def qlen (A B : Submodule O X) : ℕ∞ := Module.length O (A ⧸ B.comap A.subtype)
def idx (A B : Submodule O X) : ℤ := ((qlen O X A B).toNat : ℤ) - ((qlen O X B A).toNat : ℤ)
end Defs2
def LatFinite : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    (A B : Submodule O X), IsLat O K X A → IsLat O K X B → qlen O X A B ≠ ⊤
def LatBasis : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [FiniteDimensional K X] (A : Submodule O X), IsLat O K X A →
      ∃ b : Basis (Fin (finrank K X)) K X, A = Submodule.span O (Set.range b)
def IdxAdd : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    (A B C : Submodule O X), IsLat O K X A → IsLat O K X B → IsLat O K X C →
      idx O X A C = idx O X A B + idx O X B C
def IdxDet : Prop :=
  ∀ (O K X Y ι : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [AddCommGroup Y] [Module K Y] [Module O Y] [IsScalarTower O K Y] [Fintype ι] [DecidableEq ι]
    (bX : Basis ι K X) (bY : Basis ι K Y) (f : X ≃ₗ[K] Y) (a b : O), a ≠ 0 → b ≠ 0 →
    algebraMap O K a = (LinearMap.toMatrix bX bY (f : X →ₗ[K] Y)).det * algebraMap O K b →
      idx O Y (Submodule.span O (Set.range bY))
          ((Submodule.span O (Set.range bX)).map ((f : X →ₗ[K] Y).restrictScalars O)) =
        ((IsDiscreteValuationRing.addVal O a).toNat : ℤ) - ((IsDiscreteValuationRing.addVal O b).toNat : ℤ)
def ThreeIdx : Prop :=
  ∀ (O K X₁ X₂ X₃ X₄ ι : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K]
    [AddCommGroup X₁] [Module K X₁] [Module O X₁] [IsScalarTower O K X₁]
    [AddCommGroup X₂] [Module K X₂] [Module O X₂] [IsScalarTower O K X₂]
    [AddCommGroup X₃] [Module K X₃] [Module O X₃] [IsScalarTower O K X₃]
    [AddCommGroup X₄] [Module K X₄] [Module O X₄] [IsScalarTower O K X₄] [Fintype ι] [DecidableEq ι]
    (b₁ : Basis ι K X₁) (b₂ : Basis ι K X₂) (b₃ : Basis ι K X₃) (b₄ : Basis ι K X₄)
    (θ' : X₁ ≃ₗ[K] X₂) (j : X₂ ≃ₗ[K] X₃) (θ : X₃ ≃ₗ[K] X₄) (a b : O), a ≠ 0 → b ≠ 0 →
    algebraMap O K a =
      (LinearMap.toMatrix b₁ b₄ ((θ : X₃ →ₗ[K] X₄) ∘ₗ (j : X₂ →ₗ[K] X₃) ∘ₗ (θ' : X₁ →ₗ[K] X₂))).det *
        algebraMap O K b →
    let A := Submodule.span O (Set.range b₁)
    let B' := Submodule.span O (Set.range b₂)
    let B := Submodule.span O (Set.range b₃)
    let A' := Submodule.span O (Set.range b₄)
    ((IsDiscreteValuationRing.addVal O a).toNat : ℤ) - ((IsDiscreteValuationRing.addVal O b).toNat : ℤ) =
      idx O X₂ B' (A.map ((θ' : X₁ →ₗ[K] X₂).restrictScalars O)) +
        idx O X₃ B (B'.map ((j : X₂ →ₗ[K] X₃).restrictScalars O)) +
        idx O X₄ A' (B.map ((θ : X₃ →ₗ[K] X₄).restrictScalars O))
def IdxScale : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [FiniteDimensional K X] (ϖ : O), Irreducible ϖ → ∀ (s : ℤ) (N : Submodule O X), IsLat O K X N →
      idx O X N (N.map ((((algebraMap O K ϖ) ^ (-s)) • LinearMap.id : X →ₗ[K] X).restrictScalars O)) =
        -s * (finrank K X : ℤ)
def SubspaceIndex : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [FiniteDimensional K X] (ϖ : O), Irreducible ϖ →
    ∀ (F : ℕ) (M Θ : Submodule O X), IsLat O K X M → Θ ≤ (ϖ ^ F) • M → ∀ W : Submodule K X,
      let MW : Submodule O X := M ⊓ W.restrictScalars O
      let ΘW : Submodule O X := Θ ⊓ W.restrictScalars O
      Module.length O (MW ⧸ ΘW.comap MW.subtype) + ((F * (finrank K X - finrank K W) : ℕ) : ℕ∞) ≤
        Module.length O (M ⧸ Θ.comap M.subtype)
def GoodIndex : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [FiniteDimensional K X] (e : X →ₗ[K] X), e ∘ₗ e = e →
    ∀ (A Θ : Submodule O X), IsLat O K X A → IsLat O K X Θ → Θ ≤ A →
      let V₀ : Submodule O X := (LinearMap.range e).restrictScalars O
      idx O X (A ⊓ V₀) (Θ ⊓ V₀) ≤ idx O X A Θ ∧
        idx O X (A ⊓ V₀) (Θ.map (e.restrictScalars O)) ≤ idx O X (A ⊓ V₀) (Θ ⊓ V₀)
def GoodIso : Prop :=
  ∀ (O V : Type) [CommRing O] [AddCommGroup V] [Module O V] (e : V →ₗ[O] V), e ∘ₗ e = e →
    ∀ (A : Submodule O V) (n : O), (∀ a ∈ A, n • e a ∈ A) →
      let V₀ := LinearMap.range e
      let V₁ := LinearMap.ker e
      let P := A.map e
      let Q := A.map (LinearMap.id - e)
      (∀ a ∈ A, n • e a ∈ A ⊓ V₀) ∧ A ⊓ V₀ ≤ P ∧ A ⊓ V₁ ≤ Q ∧
        Nonempty ((P ⧸ (A ⊓ V₀).comap P.subtype) ≃ₗ[O] (Q ⧸ (A ⊓ V₁).comap Q.subtype)) ∧
        ∀ x : P ⧸ (A ⊓ V₀).comap P.subtype, n • x = 0
def GoodGen : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [FiniteDimensional K X] (e : X →ₗ[K] X), e ∘ₗ e = e → ∀ A : Submodule O X, IsLat O K X A →
      let V₀ : Submodule O X := (LinearMap.range e).restrictScalars O
      let P : Submodule O X := A.map (e.restrictScalars O)
      ∃ s : Finset (P ⧸ (A ⊓ V₀).comap P.subtype),
        s.card ≤ min (finrank K (LinearMap.range e)) (finrank K (LinearMap.ker e)) ∧
          Submodule.span O (s : Set (P ⧸ (A ⊓ V₀).comap P.subtype)) = ⊤
def GoodDual : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [FiniteDimensional K X] (B : LinearMap.BilinForm K X), B.Nondegenerate →
    ∀ (e : X →ₗ[K] X), e ∘ₗ e = e → (∀ x y, B (e x) y = B x (e y)) →
    ∀ A : Submodule O X, IsLat O K X A →
      {x : X | x ∈ LinearMap.range e ∧
          ∀ y ∈ A ⊓ (LinearMap.range e).restrictScalars O, B x y ∈ Set.range (algebraMap O K)} =
        e '' {z : X | ∀ y ∈ A, B z y ∈ Set.range (algebraMap O K)}
def PointwiseLength : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [Infinite (IsLocalRing.ResidueField O)]
    (T ι : Type) [CommRing T] [Algebra O T] [Fintype ι] (π : ι → T →ₐ[O] O) (d : ι → ℕ)
    (c : Ideal T), (∀ i, ∃ t ∈ c, π i t ≠ 0) →
    ∀ (X X' : Submodule O ((i : ι) → Fin (d i) → K)), IsLat O K ((i : ι) → Fin (d i) → K) X →
      X' ≤ X →
      (∀ t ∈ c, ∀ x ∈ X, (fun i k => algebraMap O K (π i t) * x i k) ∈ X') →
      Module.length O (X ⧸ X'.comap X.subtype) ≤
        ∑ i, (d i : ℕ∞) * ⨅ t ∈ c, IsDiscreteValuationRing.addVal O (π i t)
end Formalism.LatticeIndexTer


