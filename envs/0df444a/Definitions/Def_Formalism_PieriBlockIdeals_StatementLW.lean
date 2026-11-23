-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_StatementLW
-- name    : Formalism_PieriBlockIdeals_StatementLW
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:01.418475+00:00
-- url     : https://prove2.me/theorems/61108b6f-a303-45bf-81c8-21533bfd0964
-- title:
--   Statement LW
-- statement:
--   Definitions and structural lemmas for Statement LW, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/StatementLW.lean

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
open Finset Polynomial
namespace Formalism.CohomologicalDescent
def KapBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (σ : Equiv.Perm ι) (l h : ℕ) (kap s : ι → ℤ), 2 ≤ l →
    (∀ i, 0 ≤ s i ∧ s i ≤ (h : ℤ)) →
    (∀ i, 0 ≤ (l : ℤ) * kap (σ i) + s i - kap i ∧ (l : ℤ) * kap (σ i) + s i - kap i ≤ (h : ℤ)) →
    ∀ i, ((l : ℤ) - 1) * |kap i| ≤ (h : ℤ)
def ThetaCong : Prop :=
  ∀ (l : ℕ) (a : ℤ) (u : ℕ),
    (1 + (l : ℤ) * a) ^ u * (1 - (l : ℤ) * u * a) ≡ 1 [ZMOD ((l : ℤ) ^ 2)]
def CharpolyBlocks : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (M : Matrix (Fin n) (Fin n) K) (b : Fin n → ℕ)
    (S : Finset (Fin n)) (r : Fin n → K), M.BlockTriangular b →
    (∀ s ∈ S, ∀ j, b j = b s → j = s) → M.charpoly = ∏ u, (X - C (r u)) →
    Multiset.map (fun s => M s s) S.val ≤ Multiset.map r Finset.univ.val
def MinorBound : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (π : R) (n : ℕ) (Φ : Matrix (Fin n) (Fin n) R)
    (b : Fin n → ℕ) (S : Finset (Fin n)) (al : Fin n → ℕ) (c : ℕ), Prime π → Φ.BlockTriangular b →
    (∀ s ∈ S, ∀ j, b j = b s → j = s) → (∀ s ∈ S, ∃ u : Rˣ, Φ s s = (u : R) * π ^ al s) →
    π ^ c ∣ (Φ.submatrix (fun s : S => (s : Fin n)) (fun s : S => (s : Fin n))).det →
    c ≤ ∑ s ∈ S, al s
end Formalism.CohomologicalDescent


