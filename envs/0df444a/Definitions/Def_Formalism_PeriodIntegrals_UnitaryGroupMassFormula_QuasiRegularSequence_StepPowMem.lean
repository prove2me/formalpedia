-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuasiRegularSequence_StepPowMem
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuasiRegularSequence_StepPowMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:24.517364+00:00
-- url     : https://prove2.me/theorems/9654cf9f-3824-42d6-b2e2-5b9779418b43
-- title:
--   Step Pow Mem
-- statement:
--   Definitions and structural lemmas for Step Pow Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuasiRegularSequence/StepPowMem.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RegSeqQuasiReg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
namespace PI.RSQR
open MvPolynomial
section Defs
variable {R : Type u} [CommRing R] {n : ℕ}
def Ii (x : Fin n → R) (i : ℕ) : Ideal R :=
  Ideal.span (x '' {j : Fin n | (j : ℕ) < i})
def Below (i : ℕ) (F : MvPolynomial (Fin n) R) : Prop :=
  ∀ m ∈ F.support, ∀ j : Fin n, i ≤ (j : ℕ) → m j = 0
def HB (i k : ℕ) (F : MvPolynomial (Fin n) R) : Prop :=
  F.IsHomogeneous k ∧ Below i F
def Qz (x : Fin n → R) (i k : ℕ) : Prop :=
  ∀ F : MvPolynomial (Fin n) R, HB i k F → eval x F = 0 → ∀ m, F.coeff m ∈ Ii x i
def Qp (x : Fin n → R) (i k : ℕ) : Prop :=
  ∀ F : MvPolynomial (Fin n) R, HB i k F → eval x F ∈ Ii x i ^ (k + 1) →
    ∀ m, F.coeff m ∈ Ii x i
end Defs
def StepW : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (x : Fin n → R),
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x) →
    ∀ (i : Fin n) (r : R), x i * r ∈ Ii x i → r ∈ Ii x i
def StepPowMem : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (x : Fin n → R) (i k : ℕ) (F : MvPolynomial (Fin n) R),
    HB i k F → eval x F ∈ Ii x i ^ k
def StepPowEx : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (x : Fin n → R) (i k : ℕ) (a : R),
    a ∈ Ii x i ^ k → ∃ F : MvPolynomial (Fin n) R, HB i k F ∧ eval x F = a
def StepPowC : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (x : Fin n → R) (i k : ℕ) (F : MvPolynomial (Fin n) R),
    HB i k F → (∀ m, F.coeff m ∈ Ii x i) → eval x F ∈ Ii x i ^ (k + 1)
def StepZ : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (x : Fin n → R) (i k : ℕ), Qz x i k → Qp x i k
def StepDec : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (i : Fin n) (k : ℕ) (F : MvPolynomial (Fin n) R),
    HB ((i : ℕ) + 1) (k + 1) F →
    ∃ G H : MvPolynomial (Fin n) R, HB i (k + 1) G ∧ HB ((i : ℕ) + 1) k H ∧ F = G + X i * H
def StepDeg0 : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (x : Fin n → R) (i : ℕ), Qz x i 0
def StepBase : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (x : Fin n → R) (k : ℕ), Qz x 0 k
def StepL : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (x : Fin n → R) (i : Fin n),
    (∀ r : R, x i * r ∈ Ii x i → r ∈ Ii x i) → (∀ k, Qp x i k) →
    ∀ (k : ℕ) (a : R), x i * a ∈ Ii x i ^ k → a ∈ Ii x i ^ k
def StepStep : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (x : Fin n → R) (i : Fin n),
    (∀ r : R, x i * r ∈ Ii x i → r ∈ Ii x i) → (∀ k, Qp x i k) →
    ∀ k, Qz x ((i : ℕ) + 1) k
def StepQ : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (x : Fin n → R),
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x) →
    ∀ i ≤ n, ∀ k, Qp x i k
end PI.RSQR


