-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_PermutedRowProductSplit
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_PermutedRowProductSplit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:47:49.833452+00:00
-- url     : https://prove2.me/theorems/27a967e4-74ce-406d-98b5-e1d4f0c4314f
-- title:
--   Permuted Row Product Split
-- statement:
--   Definitions and structural lemmas for Permuted Row Product Split, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RowFormPermutationSplit/PermutedRowProductSplit.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
namespace PI.UnitaryGroupMassFormula.QmRowForm
def pF {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A) (a b : Fin t → Fin n)
    (x : Fin t → ℂ) (σ τ : Equiv.Perm (Fin t)) (k : Fin t) : A :=
  Tm E (x k) (a (σ k)) (b (τ k))
def pε {A : Type*} [Ring A] {t : ℕ} (σ τ : Equiv.Perm (Fin t)) : A :=
  (((Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign τ : ℤ) : ℤ) : A)
def pL {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (a b : Fin (m + 1) → Fin n)
    (x : Fin (m + 1) → ℂ) (i : Fin m) (σ τ : Equiv.Perm (Fin (m + 1))) : A :=
  ((List.ofFn (pF E a b x σ τ)).take (i : ℕ)).prod
def pR {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (a b : Fin (m + 1) → Fin n)
    (x : Fin (m + 1) → ℂ) (i : Fin m) (σ τ : Equiv.Perm (Fin (m + 1))) : A :=
  ((List.ofFn (pF E a b x σ τ)).drop ((i : ℕ) + 2)).prod
def permutedRowProductSplitSum {A : Type*} [Ring A] {n m : ℕ} (E : Fin n → Fin n → A) (a b : Fin (m + 1) → Fin n) (i : Fin m)
    (σ τ : Equiv.Perm (Fin (m + 1))) : A :=
  if b (τ i.castSucc) = a (σ i.succ) then E (a (σ i.castSucc)) (b (τ i.succ)) else 0
def permutedRowProductSplit {A : Type*} [Ring A] {n m : ℕ} (E : Fin n → Fin n → A) (a b : Fin (m + 1) → Fin n) (i : Fin m)
    (σ τ : Equiv.Perm (Fin (m + 1))) : A :=
  if b (τ i.succ) = a (σ i.castSucc) then E (a (σ i.succ)) (b (τ i.castSucc)) else 0
end PI.UnitaryGroupMassFormula.QmRowForm


