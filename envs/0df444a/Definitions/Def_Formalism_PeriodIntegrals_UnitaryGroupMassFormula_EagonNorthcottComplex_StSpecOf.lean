-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_StSpecOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_StSpecOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:57.650562+00:00
-- url     : https://prove2.me/theorems/5c4e2bcf-87d4-4df2-a849-94551cf46524
-- title:
--   St Spec Of
-- statement:
--   Definitions and structural lemmas for St Spec Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottComplex/StSpecOf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_EagonNorthcottSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
namespace PIW.ENSpec
open PI.EagonNorthcott MvPolynomial RingTheory.Sequence
def StBase : Prop :=
  ∀ (D a : ℕ) (n : ℕ → ℕ) (e : Fin (n 0) → Fin D → ℕ) (C : ∀ j, Matrix (Fin (n j)) (Fin (n (j + 1))) (Fin D → ℤ)),
    Resolves (MvPolynomial.X : Fin D → MvPolynomial (Fin D) ℤ) a e C →
      ∀ (R : Type u) [CommRing R], Resolves (MvPolynomial.X : Fin D → MvPolynomial (Fin D) R) a e C
def StSpec : Prop :=
  ∀ (D a : ℕ) (n : ℕ → ℕ) (e : Fin (n 0) → Fin D → ℕ) (C : ∀ j, Matrix (Fin (n j)) (Fin (n (j + 1))) (Fin D → ℤ))
    (R : Type u) [CommRing R] (x : Fin D → R), IsWeaklyRegular R (List.ofFn x) →
      Resolves (MvPolynomial.X : Fin D → MvPolynomial (Fin D) R) a e C → Resolves x a e C
noncomputable def tl {R : Type u} [CommRing R] {D : ℕ} (x : Fin D → R) : List (MvPolynomial (Fin D) R) :=
  List.ofFn fun i => MvPolynomial.X i - MvPolynomial.C (x i)
def StCut : Prop :=
  ∀ (S : Type u) [CommRing S] (G : ℕ → Type u) [∀ j, AddCommGroup (G j)] [∀ j, Module S (G j)]
    (A N : Type u) [AddCommGroup A] [Module S A] [AddCommGroup N] [Module S N]
    (d : ∀ j, G (j + 1) →ₗ[S] G j) (α : G 0 →ₗ[S] A) (π : A →ₗ[S] N),
    (∀ j, Function.Exact (d (j + 1)) (d j)) → Function.Exact (d 0) α → Function.Exact α π → Function.Surjective π →
    ∀ ts : List S, (∀ j, IsWeaklyRegular (G j) ts) → IsWeaklyRegular A ts → IsWeaklyRegular N ts →
      (∀ z : G 0, α z ∈ (Ideal.ofList ts • ⊤ : Submodule S A) →
        ∃ w : G 1, z - d 0 w ∈ (Ideal.ofList ts • ⊤ : Submodule S (G 0))) ∧
      ∀ (j : ℕ) (z : G (j + 1)), d j z ∈ (Ideal.ofList ts • ⊤ : Submodule S (G j)) →
        ∃ w : G (j + 2), z - d (j + 1) w ∈ (Ideal.ofList ts • ⊤ : Submodule S (G (j + 1)))
def StRegS : Prop :=
  ∀ (R : Type u) [CommRing R] (D m : ℕ) (x : Fin D → R), IsWeaklyRegular (Fin m → MvPolynomial (Fin D) R) (tl x)
def StRegN : Prop :=
  ∀ (R : Type u) [CommRing R] (D a : ℕ) (x : Fin D → R), IsWeaklyRegular R (List.ofFn x) →
    IsWeaklyRegular (MvPolynomial (Fin D) R ⧸ (Ideal.span (Set.range (MvPolynomial.X : Fin D → MvPolynomial (Fin D) R))) ^ a) (tl x)
def StEv : Prop :=
  ∀ (R : Type u) [CommRing R] (D m : ℕ) (x : Fin D → R) (z : Fin m → MvPolynomial (Fin D) R),
    z ∈ (Ideal.ofList (tl x) • ⊤ : Submodule (MvPolynomial (Fin D) R) (Fin m → MvPolynomial (Fin D) R)) ↔
      ∀ k, MvPolynomial.eval x (z k) = 0
def StSpecOf : Prop := StCut.{u} → StRegS.{u} → StRegN.{u} → StEv.{u} → StSpec.{u}
end PIW.ENSpec


