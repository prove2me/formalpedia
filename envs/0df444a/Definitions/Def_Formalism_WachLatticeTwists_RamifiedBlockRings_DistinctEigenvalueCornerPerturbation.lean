-- Prove2me | Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_DistinctEigenvalueCornerPerturbation
-- name    : Formalism_WachLatticeTwists_RamifiedBlockRings_DistinctEigenvalueCornerPerturbation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:19.083514+00:00
-- url     : https://prove2.me/theorems/9f5ff9ae-985c-4bfa-bfd0-d498c9393786
-- title:
--   Distinct Eigenvalue Corner Perturbation
-- statement:
--   Definitions and structural lemmas for Distinct Eigenvalue Corner Perturbation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/DistinctEigenvalueCornerPerturbation.lean

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_Statement
import Definitions.Def_Formalism_WachLatticeTwists_CoprimeLiftBounds_WachTwistTheoremDeltaClause
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
structure RingData (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X d G : Type)
    [Fintype d] [DecidableEq d] [Group G] (t : ℕ) (bl : d → Fin (t + 1)) where
  X' : Type
  T' : Subalgebra O (X' → O)
  p : X' → X
  q : ℕ
  b : Fin q → (X' → O)
  R' : Subalgebra O (X' → Matrix d d (FractionRing O))
  algT : Algebra T' R'
  modEv : ∀ x', Module T' (EvalSp O d R' x')
  r : G →* R'
  χ : G →* (T')ˣ
  eB : R'
  e₁ : R'
  X₀ : R'
  E : R'
  rr : ℕ → T'
  π' : X'
  ρπ : R' →ₐ[O] Matrix d d O
  ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O
  blockModuleStructure : ∀ k, Module T' (blockRestrictedRepresentationType bl ρk k)
  sE : Finset G
  tE : G → T'
attribute [instance] RingData.algT RingData.modEv RingData.blockModuleStructure
section
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X d G : Type}
  [Fintype d] [DecidableEq d] [Group G] {t : ℕ} {bl : d → Fin (t + 1)}
def RingData.δ (D : RingData O X d G t bl) : D.T' := ∏ i ∈ Finset.Ioo 0 t, (D.rr 0 - D.rr i)
def RingData.δO (D : RingData O X d G t bl) : O := (D.δ : D.X' → O) D.π'
def RingData.τ (D : RingData O X d G t bl) : D.T' := ∑ g ∈ D.sE, D.tE g * ((D.χ g : (D.T')ˣ) : D.T')
end
def RingDef (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X d G : Type}
    [Fintype d] [DecidableEq d] [Group G] {t : ℕ} {bl : d → Fin (t + 1)} (T : Subalgebra O (X → O))
    (r₀ : G →* (X → Matrix d d O)) (π : X) (χ₁ ε : G →* Oˣ) (g₀ : G) (eB e₁ s : X → Matrix d d O)
    (D : RingData O X d G t bl) : Prop :=
  let ι := algebraMap O (FractionRing O)

  (∀ x', blockPoly ((eB (D.p x')).map ι)
      ((eB (D.p x') * r₀ g₀ (D.p x') * eB (D.p x') + s (D.p x')).map ι) =
    ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C (ι ((D.rr i : D.X' → O) x')))) ∧
  (∀ (x : X) (α : ℕ → O), blockPoly ((eB x).map ι) ((eB x * r₀ g₀ x * eB x + s x).map ι) =
      ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C (ι (α i))) →
    ∃! x', D.p x' = x ∧ ∀ i, i < t → (D.rr i : D.X' → O) x' = α i) ∧

  D.T' = Algebra.adjoin O ({f' | ∃ f ∈ T, f' = f ∘ D.p} ∪ {f' | ∃ i, i < t ∧ f' = (D.rr i : D.X' → O)}) ∧
  D.q = t.factorial ∧

  D.p D.π' = π ∧
  (∀ i, i < t → (D.rr i : D.X' → O) D.π' = (χ₁ g₀ : O) * (((ε g₀)⁻¹ ^ i : Oˣ) : O)) ∧

  (∀ g x', ((D.r g : D.R') : D.X' → Matrix d d (FractionRing O)) x' = (r₀ g (D.p x')).map ι) ∧
  (∀ a, a ∈ D.R' ↔ a ∈ tSpan D.T' (D.R'.val.toRingHom.toMonoidHom.comp D.r)) ∧

  (∀ (f : D.T') (a : D.R') x', ((f • a : D.R') : D.X' → Matrix d d (FractionRing O)) x' =
    ι ((f : D.X' → O) x') • (a : D.X' → Matrix d d (FractionRing O)) x') ∧
  (∀ (f : D.T') x' (v : EvalSp O d D.R' x'), f • v = ι ((f : D.X' → O) x') • v) ∧
  (∀ (f : D.T') k (m : blockRestrictedRepresentationType bl D.ρk k), f • m = ((f : D.X' → O) D.π') • m) ∧

  (∀ g x', (((D.χ g : (D.T')ˣ) : D.T') : D.X' → O) x' = (χ₁ g : O)) ∧
  (∀ x', (D.eB : D.X' → Matrix d d (FractionRing O)) x' = (eB (D.p x')).map ι) ∧
  (∀ x', (D.e₁ : D.X' → Matrix d d (FractionRing O)) x' = (e₁ (D.p x')).map ι) ∧
  (∀ x', (D.X₀ : D.X' → Matrix d d (FractionRing O)) x' =
    (eB (D.p x') * r₀ g₀ (D.p x') * eB (D.p x') + s (D.p x')).map ι) ∧

  D.E = D.eB * ((List.range t).tail.map fun i => D.X₀ - D.rr i • D.eB).prod ∧

  (∀ a : D.R', (D.ρπ a).map ι = (a : D.X' → Matrix d d (FractionRing O)) D.π') ∧
  (∀ (a : D.R') k, (D.ρπ a).toSquareBlock bl k = D.ρk k a) ∧

  (∀ k, D.b k ∈ D.T') ∧
  (∀ f' ∈ D.T', ∃ a : Fin D.q → (X → O), (∀ k, a k ∈ T) ∧ f' = ∑ k, (a k ∘ D.p) * D.b k) ∧
  (∀ a : Fin D.q → (X → O), (∀ k, a k ∈ T) → ∑ k, (a k ∘ D.p) * D.b k = 0 → a = 0) ∧

  D.E = ∑ g ∈ D.sE, D.tE g • D.r g
def RingTop (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X X' : Type)
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (p : X' → X) (q : ℕ)
    (b : Fin q → (X' → O)) (d : Type) [Fintype d] [DecidableEq d]
    (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    (Tc : Type) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
    (G : Type) [Group G] (r : G →* R') (χ : G →* Tcˣ) (E e₁ : R') (δ : Tc)
    (π' : X') (ρπ : R' →ₐ[O] Matrix d d O) (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1))
    (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
    [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] [∀ k, Module Tc (blockRestrictedRepresentationType bl ρk k)]
    (sE : Finset G) (tE : G → Tc) (δO : O) : Prop :=

  (∀ f' ∈ T', ∃ a : Fin q → (X → O), (∀ k, a k ∈ T) ∧ f' = ∑ k, (a k ∘ p) * b k) ∧
  (∀ x, ∀ a : Fin q → O, (∀ x', p x' = x → ∑ k, a k * b k x' = 0) → a = 0) ∧

  (∀ (g : Type) [Fintype g] [DecidableEq g] (Θ : Matrix g g R'), ∃ f ∈ T', ∀ x',
    algebraMap O (FractionRing O) (f x') =
      (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).det) ∧

  E * E = algebraMap Tc R' δ * E ∧ e₁ * e₁ = e₁ ∧
  (∀ x', ∃ δx : FractionRing O, δx ≠ 0 ∧ (∀ v : EvalSp O d R' x', δ • v = δx • v) ∧
    Module.finrank (FractionRing O)
      (LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') E)) = 1 ∧
    Module.finrank (FractionRing O)
      (LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') e₁)) = 1) ∧

  (∀ r : R', (ρπ r).map (algebraMap O (FractionRing O)) = (r : X' → Matrix d d (FractionRing O)) π') ∧
  (∀ r, (ρπ r).BlockTriangular bl) ∧ (∀ k, Function.Surjective (ρk k)) ∧
  (∀ r k, (ρπ r).toSquareBlock bl k = ρk k r) ∧
  (∀ c : Fin (t + 1), c ≠ 0 → Fintype.card {a // bl a = c} = 1) ∧

  E = ∑ g ∈ sE, tE g • r g ∧

  (∀ m : blockRestrictedRepresentationType bl ρk 0, E • m = 0) ∧ (∀ m : blockRestrictedRepresentationType bl ρk 0, δ • m = δO • m) ∧
  (∀ m : blockRestrictedRepresentationType bl ρk 0, (∑ g ∈ sE, tE g * ((χ g : Tcˣ) : Tc)) • m = δO • m) ∧
  Nonempty (↥(LinearMap.range (DistribSMul.toLinearMap O (blockRestrictedRepresentationType bl ρk 0) e₁)) ≃ₗ[O] KO O) ∧

  (∀ c : Fin (t + 1), 2 ≤ (c : ℕ) →
    (∀ m : blockRestrictedRepresentationType bl ρk c, e₁ • m = 0) ∧ (∀ m : blockRestrictedRepresentationType bl ρk c, E • m = 0) ∧
    (∀ m : blockRestrictedRepresentationType bl ρk c, δ • m = δO • m) ∧
    (∀ m : blockRestrictedRepresentationType bl ρk c, (∑ g ∈ sE, tE g * ((χ g : Tcˣ) : Tc)) • m = δO • m)) ∧

  (let c1 : Fin (t + 1) := ⟨1, by omega⟩
   (∀ g (m : blockRestrictedRepresentationType bl ρk c1), uElt r χ g • m = m) ∧ (∀ m : blockRestrictedRepresentationType bl ρk c1, e₁ • m = 0) ∧
   (∀ m : blockRestrictedRepresentationType bl ρk c1, E • m = δO • m) ∧ (∀ m : blockRestrictedRepresentationType bl ρk c1, δ • m = δO • m))
def RingInst {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X d G : Type}
    [Fintype d] [DecidableEq d] [Group G] {t : ℕ} {bl : d → Fin (t + 1)}
    (D : RingData O X d G t bl) : Prop :=
  IsNoetherian D.R' D.R' ∧ (∀ x', IsScalarTower D.T' D.R' (EvalSp O d D.R' x')) ∧
  (∀ k, SMulCommClass D.R' O (blockRestrictedRepresentationType bl D.ρk k)) ∧ (∀ k, IsScalarTower D.T' D.R' (blockRestrictedRepresentationType bl D.ρk k)) ∧
  (∀ k, IsScalarTower O D.R' (blockRestrictedRepresentationType bl D.ρk k))
def RingData.Top {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X d G : Type}
    [Fintype d] [DecidableEq d] [Group G] {t : ℕ} {bl : d → Fin (t + 1)}
    (D : RingData O X d G t bl) (T : Subalgebra O (X → O)) (ht : 1 ≤ t)
    [∀ k, SMulCommClass D.R' O (blockRestrictedRepresentationType bl D.ρk k)] : Prop :=
  RingTop O X D.X' T D.T' D.p D.q D.b d D.R' D.T' G D.r D.χ D.E D.e₁ D.δ D.π' D.ρπ t ht bl D.ρk
    D.sE D.tE D.δO
def DistinctEigenvalueCornerPerturbation (O : Type) [CommRing O] [IsDomain O] {X : Type} (T : Subalgebra O (X → O)) {d : Type}
    [Fintype d] [DecidableEq d] {G : Type} [Group G] (r : G →* (X → Matrix d d O)) (π : X) (t : ℕ)
    (g₀ : G) (eB s : X → Matrix d d O) : Prop :=
  s ∈ tSpan T r ∧ eB * s = s ∧ s * eB = s ∧ s π = 0 ∧
  ∀ x, ∃ α : Fin t → FractionRing O, Function.Injective α ∧
    blockPoly ((eB x).map (algebraMap O (FractionRing O)))
      ((eB x * r g₀ x * eB x + s x).map (algebraMap O (FractionRing O))) =
      ∏ i, (Polynomial.X - Polynomial.C (α i))
def RingObjectsExist : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X : Type) [Fintype X]
    (T : Subalgebra O (X → O)) (d : Type) [Fintype d] [DecidableEq d] (G : Type) [Group G]
    (r₀ : G →* (X → Matrix d d O)) (π : X) (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1))
    (χ₁ ε : G →* Oˣ),
    PrimHyp O T r₀ π bl χ₁ ε →
    AbsIrr (fun g => ((r₀ g π).toSquareBlock bl 0).map (IsLocalRing.residue O)) →
    ∀ eB e₁ : X → Matrix d d O, IdemHyp O T r₀ π bl eB e₁ →
    ∀ (g₀ : G) (s : X → Matrix d d O), DistinctEigenvalueCornerPerturbation O T r₀ π t g₀ eB s →
    ∃ D : RingData O X d G t bl, RingDef O T r₀ π χ₁ ε g₀ eB e₁ s D ∧ RingInst D ∧
      ∃ _ : ∀ k, SMulCommClass D.R' O (blockRestrictedRepresentationType bl D.ρk k), D.Top T ht
end Formalism.RepresentationBoundsCohomology.ringDataObjects


