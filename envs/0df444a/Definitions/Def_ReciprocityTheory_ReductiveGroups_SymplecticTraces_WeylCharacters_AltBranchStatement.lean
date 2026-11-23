-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AltBranchStatement
-- name    : ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AltBranchStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:29.168039+00:00
-- url     : https://prove2.me/theorems/6756593f-58c6-4051-bdd8-ce6ad6a68459
-- title:
--   Alt Branch Statement
-- statement:
--   Definitions and structural lemmas for Alt Branch Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/AltBranchStatement.lean

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
open Finset
namespace ReciprocityTheory.ChartRestriction.TR.Weyl
def wsum {n : ℕ} (lam : Fin n → ℤ) : ℤ := ∑ i, lam i
def interl {n : ℕ} (lam : Fin (n + 1) → ℤ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun i : Fin n => Finset.Icc (lam i.succ) (lam i.castSucc)
def gtChar {K : Type*} [Field K] : (n : ℕ) → (Fin n → ℤ) → (Fin n → K) → K
  | 0, _, _ => 1
  | n + 1, lam, t =>
      ∑ mu ∈ interl lam, gtChar n mu (fun i => t i.castSucc) * t (Fin.last n) ^ (wsum lam - wsum mu)
def alt {K : Type*} [Field K] (n : ℕ) (a : Fin n → ℤ) (t : Fin n → K) : K :=
  (Matrix.of fun i j : Fin n => t i ^ a j).det
def delta (n : ℕ) : Fin n → ℤ := fun j => (n : ℤ) - 1 - (j : ℤ)
def wden {K : Type*} [Field K] (n : ℕ) (t : Fin n → K) : K :=
  ∏ i : Fin n, ∏ j : Fin n, if i < j then t i - t j else 1
def WeylGTStatement : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ t : Fin n → K, (∀ i, t i ≠ 0) →
    wden n t * gtChar n lam t = alt n (lam + delta n) t
def WdenSuccStatement : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (t : Fin (n + 1) → K),
    wden (n + 1) t = wden n (fun i => t i.castSucc) * ∏ i : Fin n, (t i.castSucc - t (Fin.last n))
def AltBranchStatement : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (lam : Fin (n + 1) → ℤ), Antitone lam → ∀ t : Fin (n + 1) → K, (∀ i, t i ≠ 0) →
    alt (n + 1) (lam + delta (n + 1)) t =
      (∏ i : Fin n, (t i.castSucc - t (Fin.last n))) *
        ∑ mu ∈ interl lam, alt n (mu + delta n) (fun i => t i.castSucc) * t (Fin.last n) ^ (wsum lam - wsum mu)
end ReciprocityTheory.ChartRestriction.TR.Weyl


