-- Prove2me | Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_Statement
-- name    : Formalism_WachLatticeTwists_RamifiedBlockRings_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:27:01.241586+00:00
-- url     : https://prove2.me/theorems/84e8f95c-dc9e-4d44-96d9-c2de34bc9b49
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/Statement.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatOntoLattice
import Definitions.Def_Formalism_TruncatedSeriesCounting_LemmaDetPoly
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
def blockPoly {A : Type*} [CommRing A] {d : Type*} [Fintype d] [DecidableEq d] (e a : Matrix d d A) :
    Polynomial A :=
  Matrix.det ((Polynomial.X : Polynomial A) • e.map Polynomial.C - a.map Polynomial.C +
    (1 - e).map Polynomial.C)
def AbsIrr {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {G : Type*}
    (ρ : G → Matrix n n k) : Prop :=
  (∀ W : Submodule k (n → k), (∀ g, ∀ v ∈ W, (ρ g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) ∧
  (∀ M : Matrix n n k, (∀ g, M * ρ g = ρ g * M) → ∃ c : k, M = c • (1 : Matrix n n k))
def BlockDiagonalIrreducibleAt {K : Type*} [Field K] {d : Type*} [Fintype d] [DecidableEq d] {G : Type*}
    (ρ : G → Matrix d d K) (m : ℕ) (c : d → Fin m) (P : Matrix d d K) : Prop :=
  IsUnit P ∧
  (∀ g a b, c a ≠ c b → (P * ρ g * P⁻¹) a b = 0) ∧
  (∀ i, AbsIrr (fun g => (P * ρ g * P⁻¹).toSquareBlock c i)) ∧
  (∀ i j, i ≠ j → ∀ M : Matrix {a // c a = i} {a // c a = j} K,
    (∀ g, M * (P * ρ g * P⁻¹).toSquareBlock c j = (P * ρ g * P⁻¹).toSquareBlock c i * M) → M = 0)
def PrimHyp (O : Type) [CommRing O] {X : Type} (T : Subalgebra O (X → O)) {d : Type} [Fintype d]
    [DecidableEq d] {G : Type} [Group G] (r : G →* (X → Matrix d d O)) (π : X) {t : ℕ}
    (bl : d → Fin (t + 1)) (χ₁ ε : G →* Oˣ) : Prop :=
  IsLocalRing T ∧
  (∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) ∧
  (∀ (g : G) (k : ℕ), (fun x => (Matrix.charpolyRev (r g x)).coeff k) ∈ T) ∧
  (∀ g a b, bl a ≠ bl b → r g π a b = 0) ∧
  (∀ c : Fin (t + 1), c ≠ 0 → Fintype.card {a // bl a = c} = 1) ∧
  (∀ g a, bl a ≠ 0 → r g π a a = (χ₁ g : O) * (((ε g)⁻¹ ^ ((bl a : ℕ) - 1) : Oˣ) : O))
def IdemHyp (O : Type) [CommRing O] [IsDomain O] {X : Type} (T : Subalgebra O (X → O)) {d : Type}
    [Fintype d] [DecidableEq d] {G : Type} [Group G] (r : G →* (X → Matrix d d O)) (π : X) {t : ℕ}
    (bl : d → Fin (t + 1)) (eB e₁ : X → Matrix d d O) : Prop :=
  eB ∈ tSpan T r ∧ e₁ ∈ tSpan T r ∧ eB * eB = eB ∧ e₁ * e₁ = e₁ ∧ eB * e₁ = 0 ∧ e₁ * eB = 0 ∧
  (∀ x, ((eB x).map (algebraMap O (FractionRing O))).rank = t) ∧
  (∀ x, ((e₁ x).map (algebraMap O (FractionRing O))).rank = 1) ∧
  eB π = Matrix.diagonal (fun a => if bl a = 0 then 0 else 1) ∧
  (∀ a b, (bl a ≠ 0 ∨ bl b ≠ 0) → e₁ π a b = 0)
def StatResConst : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (X : Type) (T : Subalgebra O (X → O)), IsLocalRing T →
    ∀ f ∈ T, ∀ x y : X, IsLocalRing.residue O (f x) = IsLocalRing.residue O (f y)
def StatSepPoint : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (X : Type) [Fintype X] (T : Subalgebra O (X → O)),
    (∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) →
    ∀ x : X, ∃ f ∈ T, f x ≠ 0 ∧ ∀ y, y ≠ x → f y = 0
def StatCharT : Prop :=
  ∀ (O : Type) [CommRing O] (X : Type) (T : Subalgebra O (X → O)) (d : Type) [Fintype d]
    [DecidableEq d] (G : Type) [Group G] (r : G →* (X → Matrix d d O)),
    (∀ (g : G) (k : ℕ), (fun x => (Matrix.charpolyRev (r g x)).coeff k) ∈ T) →
    ∀ a ∈ tSpan T r, ∀ k : ℕ, (fun x => (Matrix.charpolyRev (a x)).coeff k) ∈ T
def StatBlockPolyT : Prop :=
  ∀ (O : Type) [CommRing O] (X : Type) (T : Subalgebra O (X → O)) (d : Type) [Fintype d]
    [DecidableEq d] (G : Type) [Group G] (r : G →* (X → Matrix d d O)),
    (∀ (g : G) (k : ℕ), (fun x => (Matrix.charpolyRev (r g x)).coeff k) ∈ T) →
    ∀ e ∈ tSpan T r, ∀ a ∈ tSpan T r, ∀ k : ℕ, (fun x => (blockPoly (e x) (a x)).coeff k) ∈ T
def StatRankConst : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] (X : Type) (T : Subalgebra O (X → O))
    (d : Type) [Fintype d] [DecidableEq d], IsLocalRing T →
    ∀ e : X → Matrix d d O, e * e = e →
    (∀ k : ℕ, (fun x => (Matrix.charpolyRev (e x)).coeff k) ∈ T) →
    ∀ x y, ((e x).map (algebraMap O (FractionRing O))).rank =
      ((e y).map (algebraMap O (FractionRing O))).rank
def StatNilConst : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (X : Type) (T : Subalgebra O (X → O))
    (d : Type) [Fintype d] [DecidableEq d], IsLocalRing T →
    ∀ a : X → Matrix d d O, (∀ k : ℕ, (fun x => (Matrix.charpolyRev (a x)).coeff k) ∈ T) →
    ∀ y, (a y).map (IsLocalRing.residue O) = 0 →
    ∀ x, ((a x) ^ Fintype.card d).map (IsLocalRing.residue O) = 0
def DvrArtinReesInclusion : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (M : Type) [AddCommGroup M]
    [Module O M] [Module.Free O M] [Module.Finite O M] (R : Submodule O M),
    ∃ N : ℕ, ∀ a ∈ R, a ∈ (IsLocalRing.maximalIdeal O) ^ N • (⊤ : Submodule O M) →
      a ∈ (IsLocalRing.maximalIdeal O) • R
def StatBurnsideMat : Prop :=
  ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] [Nonempty n] (G : Type) [Monoid G]
    (ρ : G →* Matrix n n k), AbsIrr ρ → Submodule.span k (Set.range ρ) = ⊤
def CornerIdempotentInSubalgebra : Prop :=
  ∀ (k : Type) [Field k] (n ι : Type) [Fintype n] [DecidableEq n]
    (B : Subalgebra k (Matrix n n k × (ι → k))), 2 ≤ Fintype.card n →
    (∀ A : Matrix n n k, ∃ z ∈ B, z.1 = A) → ∀ A : Matrix n n k, (A, 0) ∈ B
def StatIdemSmall : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] (n : Type) [Fintype n] [DecidableEq n]
    (e : Matrix n n O), e * e = e → e.map (IsLocalRing.residue O) = 0 → e = 0
def StatDensity : Prop :=
  ∀ (K : Type) [Field K] (d : Type) [Fintype d] [DecidableEq d] (G : Type) [Monoid G]
    (ρ : G →* Matrix d d K) (m : ℕ) (c : d → Fin m) (P : Matrix d d K), BlockDiagonalIrreducibleAt ρ m c P →
    ∀ A : Matrix d d K, (∀ a b, c a ≠ c b → (P * A * P⁻¹) a b = 0) →
      A ∈ Submodule.span K (Set.range ρ)
def StatCornerSimple : Prop :=
  ∀ (K : Type) [Field K] [Infinite K] (d : Type) [Fintype d] [DecidableEq d] (m : ℕ) (c : d → Fin m)
    (P e : Matrix d d K), IsUnit P → e * e = e → (∀ a b, c a ≠ c b → (P * e * P⁻¹) a b = 0) →
    ∃ A : Matrix d d K, (∀ a b, c a ≠ c b → (P * A * P⁻¹) a b = 0) ∧
      (blockPoly e (e * A * e)).Separable
def StatCommonNonzero : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [Infinite O] (σ ι : Type) [Fintype ι]
    (D : ι → MvPolynomial σ O), (∀ i, D i ≠ 0) → ∃ z : σ → O, ∀ i, MvPolynomial.eval z (D i) ≠ 0
def StatIdem : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (X : Type) [Fintype X] (T : Subalgebra O (X → O))
    (d : Type) [Fintype d] [DecidableEq d] (G : Type) [Group G] (r : G →* (X → Matrix d d O)) (π : X)
    (t : ℕ) (bl : d → Fin (t + 1)) (χ₁ ε : G →* Oˣ),
    PrimHyp O T r π bl χ₁ ε →
    AbsIrr (fun g => ((r g π).toSquareBlock bl 0).map (IsLocalRing.residue O)) →
    2 ≤ Fintype.card {a // bl a = 0} →
    ∃ eB e₁ : X → Matrix d d O, IdemHyp O T r π bl eB e₁
def DensityPointExists : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X : Type) [Fintype X]
    (T : Subalgebra O (X → O)) (d : Type) [Fintype d] [DecidableEq d] (G : Type) [Group G]
    (r : G →* (X → Matrix d d O)) (π : X) (t : ℕ) (bl : d → Fin (t + 1)) (χ₁ ε : G →* Oˣ),
    PrimHyp O T r π bl χ₁ ε →
    ∀ eB e₁ : X → Matrix d d O, IdemHyp O T r π bl eB e₁ →
    (∀ x, ∃ (m : ℕ) (c : d → Fin m) (P : Matrix d d (FractionRing O)),
      BlockDiagonalIrreducibleAt (fun g => (r g x).map (algebraMap O (FractionRing O))) m c P) →
    ∀ g₀ : G, (∀ i j : ℕ, i < t → j < t → (ε g₀) ^ i = (ε g₀) ^ j → i = j) →
    ∀ (L : ℕ) (ϖ : O), ϖ ≠ 0 →
    ∃ (m : ℕ) (jj : Fin m → X → O) (a : Fin m → X → Matrix d d O),
      (∀ i, jj i ∈ T ∧ jj i π = 0 ∧ a i ∈ tSpan T r) ∧
      ∀ x, (blockPoly ((eB x).map (algebraMap O (FractionRing O)))
        ((eB x * r g₀ x * eB x + ϖ ^ L • ∑ i, jj i x • (eB x * a i x * eB x)).map
          (algebraMap O (FractionRing O)))).Separable
end Formalism.RepresentationBoundsCohomology.ringDataObjects


