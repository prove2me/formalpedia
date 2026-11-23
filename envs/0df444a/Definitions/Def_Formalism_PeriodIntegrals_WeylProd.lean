-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_WeylProd
-- name    : Formalism_PeriodIntegrals_WeylProd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:16:22.964116+00:00
-- url     : https://prove2.me/theorems/a08033a2-ca56-4147-b82d-c09e24398ba0
-- title:
--   Weyl Prod
-- statement:
--   Definitions and structural lemmas for Weyl Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/WeylProd.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI
open Finset
def vandN (x : ℕ → ℝ) (N : ℕ) : ℝ := ∏ i ∈ range N, ∏ j ∈ Ico (i + 1) N, (x i - x j)
noncomputable def dimVN (x : ℕ → ℝ) (N : ℕ) : ℝ := vandN x N / ∏ i ∈ range N, ((i.factorial : ℕ) : ℝ)
def shiftSeq {n : ℕ} (w : Fin n → ℤ) : ℕ → ℝ := fun i => if h : i < n then ((w ⟨i, h⟩ : ℤ) : ℝ) - i else 0
def WeylProd : Prop :=
  ∀ (n : ℕ) (μ w : Fin n → ℤ) (c : ℤ), (∀ t, μ t = w t - c) →
    (((∏ i : Fin n, ∏ j : Fin n,
      if i < j then (((μ i : ℤ) : ℚ) - ((μ j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) /
        (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) else 1 : ℚ)) : ℝ) = dimVN (shiftSeq w) n
end PI


