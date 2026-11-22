-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_StatementB
-- name    : Formalism_MahlerMeasure_StatementB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:30:42.253729+00:00
-- url     : https://prove2.me/theorems/993a324b-b8a5-47e3-828b-c34184dba4a1
-- title:
--   Statement B
-- statement:
--   Definitions and structural lemmas for Statement B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/StatementB.lean

import Definitions.Def_Formalism_MahlerMeasure_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM
open Finset Polynomial
noncomputable def binPoly (F : Type) [Field F] (t₀ : F) (i : ℕ) : F[X] :=
  Polynomial.C ((i.factorial : F)⁻¹) * (descPochhammer F i).comp (X - Polynomial.C t₀)
def MahlerDisc : Prop :=
  ∀ (p k i : ℕ) (t₀ : ℤ), p.Prime → i ≤ p ^ k →
    ∀ n : ℕ, padicNorm p
      ((Polynomial.C ((i.factorial : ℚ)⁻¹) *
        (descPochhammer ℚ i).comp (Polynomial.C ((p : ℚ) ^ k) * X + Polynomial.C (t₀ : ℚ))).coeff n) ≤ 1
def RowsDet : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (S : Finset (Fin n)),
    (∀ i ∈ S, ∀ j, M i j ∈ I) → M.det ∈ I ^ S.card
def NewtonSpan : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (S : Subring F) (d : ℕ) (t₀ : ℤ) (P : F[X]),
    P.natDegree ≤ d → (∀ k : ℕ, k ≤ d → P.eval ((t₀ : F) + k) ∈ S) →
    ∃ c : Fin (d + 1) → F, (∀ i, c i ∈ S) ∧ P = ∑ i, Polynomial.C (c i) * binPoly F (t₀ : F) i
end Formalism.GM


