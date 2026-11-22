-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_StatementG
-- name    : Formalism_CharacterColumnKernels_StatementG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:16:05.090226+00:00
-- url     : https://prove2.me/theorems/30421c62-2584-4aca-b910-12a9924c9842
-- title:
--   Statement G
-- statement:
--   Definitions and structural lemmas for Statement G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/StatementG.lean

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.NG
def bigRect {R O : Type*} [CommRing O] {m g d : Type*} (ρ : R → Matrix d d O) (P : Matrix m g R) :
    Matrix (m × d) (g × d) O :=
  fun p q => ρ (P p.1 q.1) p.2 q.2
def StatGeneric : Prop :=
  ∀ (R O : Type*) [Ring R] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O R]
    [Infinite (IsLocalRing.ResidueField O)]
    (m g s : Type) [Fintype m] [Fintype g] [DecidableEq g] [Fintype s]
    (d : s → Type) [∀ w, Fintype (d w)] [∀ w, DecidableEq (d w)]
    (ρ : ∀ w, R →ₐ[O] Matrix (d w) (d w) O), (∀ w, Function.Surjective (ρ w)) →
    ∀ P : Matrix m g R, ∃ C : Matrix g m R, ∀ w,
      Module.length O (LinearMap.ker (matQ O (bigMat (ρ w) (C * P)))) =
        Module.length O (LinearMap.ker (relMap O (KO O) (bigRect (ρ w) P)))
def StatGlobalNN : Prop :=
  ∀ (O T T' Ω : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Infinite (IsLocalRing.ResidueField O)] [CommRing T] [CommRing T'] [Algebra O T] [Algebra O T']
    [Algebra T T'] [IsScalarTower O T T'] [Field Ω] [IsAlgClosed Ω] [Algebra O Ω] (J : Ideal T),
    Function.Injective (algebraMap O Ω) →
    IsReduced (baseChange T' J) → Module.Finite O (baseChange T' J) →
    NoZeroSMulDivisors O (baseChange T' J) →
    ∀ (π : T →+* O) (π' : T' →+* O), π'.comp (algebraMap T T') = π →
    ∀ (R : Type*) [Ring R] [Algebra O R] (m g d : Type) [Fintype m] [Fintype g] [DecidableEq g]
      [Fintype d] [DecidableEq d] (α : Type) [LinearOrder α] [Fintype α]
      (ρ : R → Matrix d d O) (b : d → α), (∀ r, (ρ r).BlockTriangular b) →
      ∀ (ρk : ∀ k : α, R →ₐ[O] Matrix {a // b a = k} {a // b a = k} O),
      (∀ k, Function.Surjective (ρk k)) → (∀ r k, (ρ r).toSquareBlock b k = ρk k r) →
      ∀ P : Matrix m g R, ∃ C : Matrix g m R, ∀ f : T',
        (∀ φ : baseChange T' J →ₐ[O] Ω, φ (Ideal.Quotient.mk _ f) = 0) →
        π' f = (bigMat ρ (C * P)).det →
        vIdeal O (congIdeal J π) ≤
          ∑ k ∈ univ.image b, Module.length O (LinearMap.ker (relMap O (KO O) (bigRect (ρk k) P)))
def StatGenericFin : Prop :=
  ∀ (R O : Type*) [Ring R] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O R]
    (m g s : Type) [Fintype m] [Fintype g] [DecidableEq g] [Fintype s]
    (d : s → Type) [∀ w, Fintype (d w)] [∀ w, DecidableEq (d w)],
    ((Fintype.card g * ∑ w, Fintype.card (d w) : ℕ) : Cardinal) <
      Cardinal.mk (IsLocalRing.ResidueField O) →
    ∀ (ρ : ∀ w, R →ₐ[O] Matrix (d w) (d w) O), (∀ w, Function.Surjective (ρ w)) →
    ∀ P : Matrix m g R, ∃ C : Matrix g m R, ∀ w,
      Module.length O (LinearMap.ker (matQ O (bigMat (ρ w) (C * P)))) =
        Module.length O (LinearMap.ker (relMap O (KO O) (bigRect (ρ w) P)))
def StatGlobalNNFin : Prop :=
  ∀ (O T T' Ω : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing T] [CommRing T'] [Algebra O T] [Algebra O T']
    [Algebra T T'] [IsScalarTower O T T'] [Field Ω] [IsAlgClosed Ω] [Algebra O Ω] (J : Ideal T),
    Function.Injective (algebraMap O Ω) →
    IsReduced (baseChange T' J) → Module.Finite O (baseChange T' J) →
    NoZeroSMulDivisors O (baseChange T' J) →
    ∀ (π : T →+* O) (π' : T' →+* O), π'.comp (algebraMap T T') = π →
    ∀ (R : Type*) [Ring R] [Algebra O R] (m g d : Type) [Fintype m] [Fintype g] [DecidableEq g]
      [Fintype d] [DecidableEq d] (α : Type) [LinearOrder α] [Fintype α]
      (ρ : R → Matrix d d O) (b : d → α), (∀ r, (ρ r).BlockTriangular b) →
      ((Fintype.card g * ∑ k : α, Fintype.card {a // b a = k} : ℕ) : Cardinal) <
        Cardinal.mk (IsLocalRing.ResidueField O) →
      ∀ (ρk : ∀ k : α, R →ₐ[O] Matrix {a // b a = k} {a // b a = k} O),
      (∀ k, Function.Surjective (ρk k)) → (∀ r k, (ρ r).toSquareBlock b k = ρk k r) →
      ∀ P : Matrix m g R, ∃ C : Matrix g m R, ∀ f : T',
        (∀ φ : baseChange T' J →ₐ[O] Ω, φ (Ideal.Quotient.mk _ f) = 0) →
        π' f = (bigMat ρ (C * P)).det →
        vIdeal O (congIdeal J π) ≤
          ∑ k ∈ univ.image b, Module.length O (LinearMap.ker (relMap O (KO O) (bigRect (ρk k) P)))
end Formalism.NG


