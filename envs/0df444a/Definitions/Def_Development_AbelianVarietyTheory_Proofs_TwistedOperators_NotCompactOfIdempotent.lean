-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:22.619365+00:00
-- url     : https://prove2.me/theorems/a53010c2-bfc8-4f55-8e66-826b093b507f
-- title:
--   Not Compact Of Idempotent
-- statement:
--   Definitions and structural lemmas for Not Compact Of Idempotent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
namespace GlobalTheory.RegSS
def krylov {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n A)
    (v : n → A) : Matrix n n A :=
  Matrix.of fun i j => ((M ^ ((Fintype.equivFin n j : Fin (Fintype.card n)) : ℕ)) *ᵥ v) i
section Objects
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]
def tConj (P : Type) [CommRing P] [Algebra F P] (σ : E →ₐ[F] E) : P ⊗[F] E →ₐ[F] P ⊗[F] E :=
  Algebra.TensorProduct.map (AlgHom.id F P) σ
def tConj3 (P : Type) [CommRing P] [Algebra F P] (σ : E →ₐ[F] E) (R : Type) [CommRing R]
    [Algebra F R] : P ⊗[F] (E ⊗[F] R) →ₐ[F] P ⊗[F] (E ⊗[F] R) :=
  Algebra.TensorProduct.map (AlgHom.id F P) (Algebra.TensorProduct.map σ (AlgHom.id F R))
def PointsClause (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E) : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra F R],
    Function.Injective (toMat σ J (γ : Matrix n n E) R) ∧
    (∀ u, toMat σ J (γ : Matrix n n E) R (lConj σ J (γ : Matrix n n E) R u) =
      adj (sigR σ R) (J.map (inclE (F := F) R)) (toMat σ J (γ : Matrix n n E) R u)) ∧
    ∀ g : GL n (E ⊗[F] R), g ∈ centPts σ J γ R ↔
      ∃ u ∈ normOne σ J (γ : Matrix n n E) R,
        toMat σ J (γ : Matrix n n E) R (u : LPts σ J (γ : Matrix n n E) R) =
          (g : Matrix n n (E ⊗[F] R))
def IsIdemFamily (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E) {ι : Type}
    (ε : ι → Matrix n n E) : Prop :=
  (∀ i, ε i ∈ genAlg (γ : Matrix n n E)) ∧ (∀ i, ε i ≠ 0) ∧ (∀ i, ε i * ε i = ε i) ∧
    (∀ i j, i ≠ j → ε i * ε j = 0) ∧ ∀ i j, ε i * adj (σ : E →+* E) J (ε j) = 0
end Objects
def UnitBounded (F B : Type) [Field F] [NumberField F] [CommRing B] [Algebra F B]
    (τ : B →ₐ[F] B) : Prop :=
  letI : TopologicalSpace (B ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := B) (AdeleRing (𝓞 F) F)
  ∃ D : Set (B ⊗[F] AdeleRing (𝓞 F) F), IsCompact D ∧
    ∀ u : B ⊗[F] AdeleRing (𝓞 F) F, u * sigR τ (AdeleRing (𝓞 F) F) u = 1 →
      ∃ β : B, IsUnit β ∧ u * inclE (F := F) (AdeleRing (𝓞 F) F) β ∈ D
def NormBounded (F B : Type) [Field F] [NumberField F] [CommRing B] [Algebra F B]
    (τ : B →ₐ[F] B) : Prop :=
  letI : TopologicalSpace (B ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := B) (AdeleRing (𝓞 F) F)
  ∃ D : Set (B ⊗[F] AdeleRing (𝓞 F) F), IsCompact D ∧
    ∀ u : B ⊗[F] AdeleRing (𝓞 F) F, u * sigR τ (AdeleRing (𝓞 F) F) u = 1 →
      ∃ β : B, β * τ β = 1 ∧ u * inclE (F := F) (AdeleRing (𝓞 F) F) β ∈ D
def MatBounded {F E : Type} [Field F] [NumberField F] [CommRing E] [Algebra F E]
    {n : Type} [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E) : Prop :=
  letI : TopologicalSpace (E ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := E) (AdeleRing (𝓞 F) F)
  ∃ D : Set (Matrix n n (E ⊗[F] AdeleRing (𝓞 F) F)), IsCompact D ∧
    ∀ g ∈ centPts σ J γ (AdeleRing (𝓞 F) F), ∃ δ ∈ centRat σ J γ,
      (g : Matrix n n (E ⊗[F] AdeleRing (𝓞 F) F)) *
        (δ : Matrix n n E).map (inclE (F := F) (AdeleRing (𝓞 F) F)) ∈ D
def CyclicField : Prop :=
  ∀ (K : Type) [Field K] (n : Type) [Fintype n] [DecidableEq n] (M : Matrix n n K),
    M.charpoly.Separable → ∃ v, IsUnit (krylov M v).det
def CyclicSemilocal : Prop :=
  ∀ (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (n : Type) [Fintype n] [DecidableEq n]
    (M : Matrix n n A), M.charpoly.Separable → ∃ v, IsUnit (krylov M v).det
def CyclicAlgebra : Prop :=
  ∀ (A : Type) [CommRing A] (n : Type) [Fintype n] [DecidableEq n] (M : Matrix n n A) (v : n → A),
    IsUnit (krylov M v).det →
      (∃ e : AdjoinRoot M.charpoly ≃ₐ[A] genAlg M, e (AdjoinRoot.root _) = gen M) ∧
      Nonempty (Module.Basis n A (genAlg M)) ∧
      Function.Bijective (fun l : genAlg M => (l : Matrix n n A) *ᵥ v)
def PlusTensorBijective : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E),
    IsRegular σ J γ →
    ClauseAlg σ J γ → Function.Bijective (plusTensor σ J (γ : Matrix n n E))
def PlusEtale : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E),
    IsRegular σ J γ →
    ClauseAlg σ J γ → Function.Bijective (plusTensor σ J (γ : Matrix n n E)) → ClausePlus σ J γ
def PointsCommutant : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E),
    IsRegular σ J γ →
    ClauseAlg σ J γ → ClausePlus σ J γ → ∀ (R : Type) [CommRing R] [Algebra F R],
      Function.Injective (toMat σ J (γ : Matrix n n E) R) ∧
      ∀ N : Matrix n n (E ⊗[F] R),
        N * (γ : Matrix n n E).map (inclE (F := F) R) =
          (γ : Matrix n n E).map (inclE (F := F) R) * N ↔
        ∃ u, toMat σ J (γ : Matrix n n E) R u = N
def PointsAdjoint : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E),
    IsRegular σ J γ →
    ∀ (R : Type) [CommRing R] [Algebra F R] (u : LPts σ J (γ : Matrix n n E) R),
      toMat σ J (γ : Matrix n n E) R (lConj σ J (γ : Matrix n n E) R u) =
        adj (sigR σ R) (J.map (inclE (F := F) R)) (toMat σ J (γ : Matrix n n E) R u)
def PointsCentraliser : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E),
    IsRegular σ J γ →
    ClauseAlg σ J γ → ClausePlus σ J γ → PointsClause σ J γ
def SplitClosed : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [CommRing E] [Algebra F E] (σ : E →ₐ[F] E),
    IsQuadInvol F E σ → ∀ (P : Type) [CommRing P] [Algebra F P] (n : Type) [Fintype n],
    Algebra.Etale F P → Nonempty (Module.Basis n F P) →
    ∀ (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω],
      ∃ φ : P ⊗[F] (E ⊗[F] Ω) ≃ₐ[F] (n → Ω × Ω),
        (∀ ω : Ω, φ (1 ⊗ₜ (1 ⊗ₜ ω)) = fun _ => (ω, ω)) ∧
        ∀ u i, φ (tConj3 P σ Ω u) i = (φ u i).swap
def SplitIdempotents : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [CommRing E] [Algebra F E] (σ : E →ₐ[F] E),
    IsQuadInvol F E σ → ∀ (P : Type) [CommRing P] [Algebra F P],
    ∀ (k : ℕ) (K : Fin k → Type) [∀ i, Field (K i)] [∀ i, Algebra F (K i)],
      Nonempty (P ≃ₐ[F] ∀ i, K i) →
      ∃ ε : {i : Fin k // ¬ IsField (K i ⊗[F] E)} → P ⊗[F] E,
        (∀ i, ε i ≠ 0) ∧ (∀ i, ε i * ε i = ε i) ∧ (∀ i j, i ≠ j → ε i * ε j = 0) ∧
          ∀ i j, ε i * tConj P σ (ε j) = 0
def SubtorusOfIdempotents : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E),
    IsRegular σ J γ →
    ClauseAlg σ J γ → ∀ (s : ℕ) (ε : Fin s → Matrix n n E), IsIdemFamily σ J γ ε →
      ∃ A : SplitSubtorus σ J γ s, ∀ (R : Type) [CommRing R] [Algebra F R] (t : Fin s → Rˣ)
        (i : Fin s), (A.hom R t : Matrix n n (E ⊗[F] R)) * (ε i).map (inclE (F := F) R) =
          ((1 : E) ⊗ₜ[F] (t i : R)) • (ε i).map (inclE (F := F) R)
def SubtorusLaurent : Prop :=
  ∀ (F E : Type) [Field F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E)
    (s : ℕ) (A : SplitSubtorus σ J γ s),
    ∃ (S : Finset (Fin s → ℤ)) (C : (Fin s → ℤ) → Matrix n n (E ⊗[F] F)), ∀ t : Fin s → Fˣ,
      (A.hom F t : Matrix n n (E ⊗[F] F)) = ∑ a ∈ S, ((∏ j, t j ^ a j : Fˣ) : F) • C a
def CharacterMonomial : Prop :=
  ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (s : ℕ) (f : (Fin s → Fˣ) →* Ω)
    (S : Finset (Fin s → ℤ)) (c : (Fin s → ℤ) → Ω),
    (∀ t, f t = ∑ a ∈ S, ((∏ j, t j ^ a j : Fˣ) : F) • c a) →
      ∃ a : Fin s → ℤ, ∀ t, f t = algebraMap F Ω ((∏ j, t j ^ a j : Fˣ) : F)
def SeparatingPoints : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [CommRing E] [Algebra F E] (σ : E →ₐ[F] E),
    IsQuadInvol F E σ → ∀ (P : Type) [CommRing P] [Algebra F P] [Module.Finite F P],
    ∀ (k : ℕ) (K : Fin k → Type) [∀ i, Field (K i)] [∀ i, Algebra F (K i)],
      Nonempty (P ≃ₐ[F] ∀ i, K i) →
      ∃ ψ : Fin k → (P ⊗[F] (E ⊗[F] F) →ₐ[F] AlgebraicClosure F),
        (∀ x, (∀ i, ψ i x = 0 ∧ ψ i (tConj3 P σ F x) = 0) → x = 0) ∧
        ∀ i, IsField (K i ⊗[F] E) → ∀ x, ψ i x = 0 → ψ i (tConj3 P σ F x) = 0
def SplitRankUpper : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E),
    IsRegular σ J γ →
    ClausePlus σ J γ → PointsClause σ J γ →
    ∀ (k : ℕ) (K : Fin k → Type) [∀ i, Field (K i)] [∀ i, Algebra F (K i)],
      Nonempty (plusAlg σ J (γ : Matrix n n E) ≃ₐ[F] ∀ i, K i) →
      ∀ s : ℕ, Nonempty (SplitSubtorus σ J γ s) →
        s ≤ Nat.card {i : Fin k // ¬ IsField (K i ⊗[F] E)}
def TensorFieldIff : Prop :=
  ∀ (F E : Type) [Field F] [CommRing E] [Algebra F E] [Nontrivial E]
    (P : Type) [CommRing P] [Algebra F P],
    ∀ (k : ℕ) (K : Fin k → Type) [∀ i, Field (K i)] [∀ i, Algebra F (K i)],
      Nonempty (P ≃ₐ[F] ∀ i, K i) →
      (IsField (P ⊗[F] E) ↔ k = 1 ∧ ∀ i, IsField (K i ⊗[F] E))
def UnitaryCommutant : Prop :=
  ∀ (A : Type) [CommRing A] [CharZero A], IsField A → ∀ (σ : A →+* A), (∀ x, σ (σ x) = x) →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (J : Matrix n n A), IsHerm σ J → IsUnit J.det →
    ∀ a : Matrix n n A, (∀ g ∈ UJ σ J, (g : Matrix n n A) * a = a * (g : Matrix n n A)) →
      ∃ c : A, a = c • (1 : Matrix n n A)
def SubtorusNotCentral : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E),
    IsRegular σ J γ →
    IsField E → ∀ (s : ℕ), 1 ≤ s → ∀ A : SplitSubtorus σ J γ s,
      ∃ g ∈ UPts σ J F, ∃ t : Fin s → Fˣ, g * A.hom F t ≠ A.hom F t * g
def TracePerfect : Prop :=
  ∀ (F E L : Type) [Field F] [CharZero F] [CommRing E] [CommRing L] [Algebra F E] [Algebra E L]
    [Algebra F L] [IsScalarTower F E L] [Module.Finite F E] [Module.Free E L] [Module.Finite E L]
    [IsReduced L],
    Function.Bijective (fun x : L => (Algebra.traceForm E L x : L →ₗ[E] E))
def TraceClause : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E),
    IsRegular σ J γ →
    ClauseAlg σ J γ → ClauseTrace σ J γ
def NormOnePacking : Prop :=
  ∀ (X : Type) [CommRing X] [TopologicalSpace X] [IsTopologicalRing X] [LocallyCompactSpace X]
    [T2Space X] [SecondCountableTopology X] [NoncompactSpace X] (τ : X →+* X), Continuous τ →
    (∀ x, τ (τ x) = x) → ∀ Λ : AddSubgroup X, Countable Λ →
    (∃ C : Set X, IsCompact C ∧ ∀ x, ∃ l ∈ Λ, x - l ∈ C) →
      ∃ D : Set X, IsCompact D ∧ ∀ u : X, u * τ u = 1 → ∃ β ∈ Λ, β ≠ 0 ∧ u * β ∈ D
def TensorLattice : Prop :=
  ∀ (F B : Type) [Field F] [NumberField F] [CommRing B] [Algebra F B] [Module.Finite F B],
    letI : TopologicalSpace (B ⊗[F] AdeleRing (𝓞 F) F) :=
      Formalism.BasicNotions.tensTopL (F := F) (E := B) (AdeleRing (𝓞 F) F)
    IsTopologicalRing (B ⊗[F] AdeleRing (𝓞 F) F) ∧
    LocallyCompactSpace (B ⊗[F] AdeleRing (𝓞 F) F) ∧
    T2Space (B ⊗[F] AdeleRing (𝓞 F) F) ∧
    SecondCountableTopology (B ⊗[F] AdeleRing (𝓞 F) F) ∧
    Function.Injective (inclE (F := F) (E := B) (AdeleRing (𝓞 F) F)) ∧
    (∀ D : Set (B ⊗[F] AdeleRing (𝓞 F) F), IsCompact D →
      {β : B | inclE (F := F) (AdeleRing (𝓞 F) F) β ∈ D}.Finite) ∧
    ∃ C : Set (B ⊗[F] AdeleRing (𝓞 F) F), IsCompact C ∧
      ∀ x, ∃ β : B, x - inclE (F := F) (AdeleRing (𝓞 F) F) β ∈ C
def FieldUnitBounded : Prop :=
  ∀ (F B : Type) [Field F] [NumberField F] [CommRing B] [Algebra F B] [Module.Finite F B]
    (τ : B →ₐ[F] B), IsField B → (∀ x, τ (τ x) = x) → UnitBounded F B τ
def NormOfUnitBounded : Prop :=
  ∀ (F B : Type) [Field F] [NumberField F] [CommRing B] [Algebra F B] [Module.Finite F B]
    (τ : B →ₐ[F] B), UnitBounded F B τ → NormBounded F B τ
def ProductUnitBounded : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [CommRing E] [Algebra F E] [Module.Finite F E]
    (σ : E →ₐ[F] E) (P : Type) [CommRing P] [Algebra F P] [Module.Finite F P],
    ∀ (k : ℕ) (K : Fin k → Type) [∀ i, Field (K i)] [∀ i, Algebra F (K i)],
      Nonempty (P ≃ₐ[F] ∀ i, K i) →
      (∀ i, UnitBounded F (K i ⊗[F] E) (tConj (K i) σ)) → UnitBounded F (P ⊗[F] E) (tConj P σ)
def MatOfNormBounded : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E),
    IsRegular σ J γ →
    ClauseAlg σ J γ → ClausePlus σ J γ → PointsClause σ J γ →
    NormBounded F (plusAlg σ J (γ : Matrix n n E) ⊗[F] E)
      (tConj (plusAlg σ J (γ : Matrix n n E)) σ) → MatBounded σ J γ
def CompactOfMatBounded : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E),
    IsRegular σ J γ →
    MatBounded σ J γ → AdelicCompact σ J γ
def IdempotentDet : Prop :=
  ∀ (F E : Type) [Field F] [CommRing E] [Algebra F E] [Module.Finite F E]
    (n : Type) [Fintype n] [DecidableEq n] (ε : Matrix n n E), ε ≠ 0 → ε * ε = ε →
    ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R],
    letI : TopologicalSpace (E ⊗[F] R) := Formalism.BasicNotions.tensTopL (F := F) (E := E) R
    ∃ (d : ℕ) (χ : Matrix n n (E ⊗[F] R) → R), 0 < d ∧ Continuous χ ∧ χ 1 = 1 ∧
      (∀ g h, h * ε.map (inclE (F := F) R) = ε.map (inclE (F := F) R) * h →
        χ (g * h) = χ g * χ h) ∧
      (∀ g : Matrix n n E, ∃ c : F, χ (g.map (inclE (F := F) R)) = algebraMap F R c) ∧
      ∀ g (t : R), g * ε.map (inclE (F := F) R) =
        ((1 : E) ⊗ₜ[F] t) • ε.map (inclE (F := F) R) → χ g = t ^ d
def NotCompactOfIdempotent : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [CommRing E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (γ : GL n E),
    IsRegular σ J γ →
    ∀ ε ∈ genAlg (γ : Matrix n n E), ε ≠ 0 → ε * ε = ε →
    (∀ t : (AdeleRing (𝓞 F) F)ˣ, ∃ g ∈ centPts σ J γ (AdeleRing (𝓞 F) F),
      (g : Matrix n n (E ⊗[F] AdeleRing (𝓞 F) F)) * ε.map (inclE (F := F) (AdeleRing (𝓞 F) F)) =
        ((1 : E) ⊗ₜ[F] (t : AdeleRing (𝓞 F) F)) • ε.map (inclE (F := F) (AdeleRing (𝓞 F) F))) →
    ¬ AdelicCompact σ J γ
section Adjoint
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
end Adjoint
section Quad
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n E} {γ : GL n E}
end Quad
end GlobalTheory.RegSS


