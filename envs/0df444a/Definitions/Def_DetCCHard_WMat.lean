-- Prove2me | Definitions.Def_DetCCHard_WMat
-- name    : DetCCHard_WMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:35:57.469746+00:00
-- url     : https://prove2.me/theorems/deeef8c0-8dc7-4e52-ab53-8987ca51d925
-- title:
--   Weighted tables and the initial matrix $R_0$
-- statement:
--   A **weighted table** consists of finite input sets $X, Y$, a total table $X \times Y \to \{0,1\}$, and positive normalized rational row and column weights; these are the base matrices of the amplifier (Theorem 5.3).
--
--   For $L \ge 1$ let $p_0 = \mathrm{pow2}(64(L+1))$. The **initial matrix** is
--   $$
--   R_0(z, j) = z_j \quad \text{on } \{0,1\}^{p_0} \times [p_0],
--   $$
--   with uniform input weights.
--
--   **Formalization Note** Coordinates are indexed from $0$. The module contains the trivial lemma that uniform weights are positive and normalized.
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Lemma 5.4, p.17

import Mathlib
import Definitions.Def_DetCCHard_IsWeight
import Definitions.Def_DetCCHard_pow2

namespace DetCCHard

/-- A **weighted table** (Gaspers–He–Mackenzie, arXiv:2508.05597, held version sha256
ad552d13…a4a03, Definition 4.1, p.13, and §4.2, p.14): finite input sets `X`, `Y`, a total table
`entry : X × Y → {0, 1}`, and positive normalized rational row and column weights (the "base
matrices with positive normalized rational input weights" of Theorem 5.3, p.17). The input sets
are nonempty because their weights sum to one. -/
structure WMat where
  /-- Alice's input set (row labels) -/
  X : Type
  /-- Bob's input set (column labels) -/
  Y : Type
  [instFX : Fintype X]
  [instFY : Fintype Y]
  [instDX : DecidableEq X]
  [instDY : DecidableEq Y]
  /-- the table -/
  entry : X → Y → Bool
  /-- row weights -/
  μX : X → ℚ
  /-- column weights -/
  μY : Y → ℚ
  hμX : IsWeight μX
  hμY : IsWeight μY

attribute [instance] WMat.instFX WMat.instFY WMat.instDX WMat.instDY

/-- Uniform weights `1/|X|` on a finite set. -/
noncomputable def uniformWt (X : Type) [Fintype X] : X → ℚ := fun _ => 1 / (Fintype.card X : ℚ)

theorem isWeight_uniformWt (X : Type) [Fintype X] [Nonempty X] : IsWeight (uniformWt X) := by
  have hc : (0 : ℚ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  refine ⟨fun _ => by unfold uniformWt; positivity, ?_⟩
  simp only [uniformWt, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- The **initial matrix** of Lemma 5.4 (p.17): for `p₀ = pow2(64(L + 1))`,
`R₀(z, j) = z_j` on `{0, 1}^{p₀} × [p₀]` with uniform input weights.

**Formalization Note** Coordinates are indexed from `0` (`Fin p₀`). -/
noncomputable def initialMatrix (L : ℕ) : WMat where
  X := Fin (pow2 (64 * (L + 1))) → Bool
  Y := Fin (pow2 (64 * (L + 1)))
  entry := fun z j => z j
  μX := uniformWt _
  μY := uniformWt _
  hμX := isWeight_uniformWt _
  hμY := by
    have : 0 < pow2 (64 * (L + 1)) := by unfold pow2; positivity
    have : Nonempty (Fin (pow2 (64 * (L + 1)))) := ⟨⟨0, this⟩⟩
    exact isWeight_uniformWt _

end DetCCHard


