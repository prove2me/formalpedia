-- Prove2me | Definitions.Def_Formalism_LogSumExpBounds_StatementD
-- name    : Formalism_LogSumExpBounds_StatementD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:11.1738+00:00
-- url     : https://prove2.me/theorems/c6e5bb3c-863a-4f93-bf46-79822459d434
-- title:
--   Statement D
-- statement:
--   Definitions and structural lemmas for Statement D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/StatementD.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.NuclearRankWeightBounds.D
open Finset
noncomputable def lead {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (i : ℕ) : ℂ :=
  if hi : i ≤ N then (A.submatrix (Fin.castLE hi) (Fin.castLE hi)).det else 1
noncomputable def hs {N : ℕ} (Y : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  Real.sqrt (∑ a, ∑ b, ‖Y a b‖ ^ 2)
def q0 {N : ℕ} (ep : Fin N → Bool) : ℕ :=
  min (univ.filter fun a => ep a = true).card (univ.filter fun a => ep a = false).card
def Decay : Prop :=
  ∀ (N : ℕ) (s : ℕ → ℝ) (ep : Fin N → Bool) (h : ℝ) (Y : Matrix (Fin N) (Fin N) ℂ),
    (∀ i, 0 ≤ s i) → Y.IsHermitian → (∀ a b, ep a = ep b → Y a b = 0) →
    (∀ a b : Fin N, b < a → ep a ≠ ep b → h ≤ ∑ i ∈ Ico (b.val + 1) (a.val + 1), s i) →
    ∏ i ∈ Ico 1 N, (lead (NormedSpace.exp Y) i).re ^ (-(s i))
      ≤ Real.exp (-(h * min (hs Y ^ 2) (hs Y / Real.sqrt (2 * (q0 ep : ℝ)))) / 8)
end Formalism.NuclearRankWeightBounds.D


