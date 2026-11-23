-- Prove2me | Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PowerSeriesPresentations_PresentationStatement
-- name    : ReciprocityTheory_CommutativeAlgebra_PowerSeriesPresentations_PresentationStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:44.53222+00:00
-- url     : https://prove2.me/theorems/8372fd92-74df-42cf-bfc4-e1cd7e41df97
-- title:
--   Presentation Statement
-- statement:
--   Definitions and structural lemmas for Presentation Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PowerSeriesPresentations/PresentationStatement.lean

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.CA.PS
open IsLocalRing MvPowerSeries
universe u v
structure IsCNL (A : Type*) [CommRing A] : Prop where
  noeth : IsNoetherianRing A
  loc : IsLocalRing A
  complete : IsAdicComplete (maximalIdeal A) A
def MaxIdealStatement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsLocalRing O] (a : ℕ),
    maximalIdeal (MvPowerSeries (Fin a) O) =
      (maximalIdeal O).map (C : O →+* MvPowerSeries (Fin a) O) ⊔ Ideal.span (Set.range X)
def CompleteStatement : Prop :=
  ∀ (O : Type u) [CommRing O], IsCNL O → ∀ a : ℕ, IsCNL (MvPowerSeries (Fin a) O)
def DimStatement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (a : ℕ),
    ringKrullDim (MvPowerSeries (Fin a) O) = ringKrullDim O + a
def RegularStatement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsRegularLocalRing O] (a : ℕ),
    IsRegularLocalRing (MvPowerSeries (Fin a) O)
def CMStatement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsLocalRing O], IsCM O → ∀ a : ℕ, IsCM (MvPowerSeries (Fin a) O)
def EvalStatement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsLocalRing O] (A : Type v) [CommRing A] [IsLocalRing A] [Algebra O A]
    [IsLocalHom (algebraMap O A)], IsAdicComplete (maximalIdeal A) A →
    ∀ (a : ℕ) (t : Fin a → A), (∀ i, t i ∈ maximalIdeal A) →
      ∃! φ : MvPowerSeries (Fin a) O →ₐ[O] A, ∀ i, φ (X i) = t i
def SurjStatement : Prop :=
  ∀ (O : Type u) [CommRing O], IsCNL O → ∀ [IsLocalRing O] (A : Type v) [CommRing A] [IsLocalRing A]
    [Algebra O A] [IsLocalHom (algebraMap O A)], IsHausdorff (maximalIdeal A) A →
    Function.Surjective (ResidueField.map (algebraMap O A)) →
    ∀ (a : ℕ) (φ : MvPowerSeries (Fin a) O →ₐ[O] A),
      maximalIdeal A = (maximalIdeal O).map (algebraMap O A) ⊔ Ideal.span (Set.range fun i => φ (X i)) →
      Function.Surjective φ
noncomputable def relEmbDim (O : Type*) [CommRing O] [IsLocalRing O] (A : Type*) [CommRing A]
    [IsLocalRing A] [Algebra O A] : ℕ :=
  ((maximalIdeal A).map
    (Ideal.Quotient.mk ((maximalIdeal O).map (algebraMap O A)))).spanFinrank
abbrev RelCotangent (O : Type*) [CommRing O] [IsLocalRing O] (A : Type*) [CommRing A]
    [IsLocalRing A] [Algebra O A] : Type _ :=
  (maximalIdeal A) ⧸ (Submodule.comap (maximalIdeal A).subtype
    ((maximalIdeal A) ^ 2 ⊔ (maximalIdeal O).map (algebraMap O A)))
def RelCotangentStatement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsLocalRing O] (A : Type v) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [Algebra O A] [IsLocalHom (algebraMap O A)],
    Module.length A (RelCotangent O A) = (relEmbDim O A : ℕ∞)
def PresentationStatement : Prop :=
  ∀ (O : Type u) [CommRing O], IsCNL O → ∀ [IsLocalRing O] (A : Type v) [CommRing A], IsCNL A →
    ∀ [IsLocalRing A] [Algebra O A] [IsLocalHom (algebraMap O A)],
    Function.Surjective (ResidueField.map (algebraMap O A)) →
    (∃ φ : MvPowerSeries (Fin (relEmbDim O A)) O →ₐ[O] A, Function.Surjective φ) ∧
    ∀ (a : ℕ) (φ : MvPowerSeries (Fin a) O →ₐ[O] A), Function.Surjective φ → relEmbDim O A ≤ a
def QuotientStatement : Prop :=
  ∀ (A : Type u) [CommRing A], IsCNL A → ∀ I : Ideal A, I ≠ ⊤ → IsCNL (A ⧸ I)
def DimBoundStatement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsLocalRing O], IsCM O → ∀ (a : ℕ) (s : Finset (MvPowerSeries (Fin a) O)),
    ∀ p ∈ (Ideal.span (s : Set (MvPowerSeries (Fin a) O))).minimalPrimes,
      ringKrullDim O + a ≤ ringKrullDim (MvPowerSeries (Fin a) O ⧸ p) + s.card
end ReciprocityTheory.CA.PS


