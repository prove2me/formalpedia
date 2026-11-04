-- Prove2me | Definitions.Def_QMCLeafB_zeroedge_m6
-- name    : QMCLeafB_zeroedge_m6
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T01:56:41.532492+00:00
-- url     : https://prove2.me/theorems/c5739570-545e-4ace-ab2d-2d869204ceb6
-- title:
--   QMCLeafB zeroedge_m6
-- statement:
--   # leaf B phase 16 — the zero-edge end of the leaf (member m6, direction d9)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_QMCLeafB_numcert_m6
/-
# leaf B phase 16 — the zero-edge end of the leaf (member m6, direction d9)

For an input with no edges the whole leaf is unconditional: the weight matrix is the zero matrix, its
Max-Cut SDP value is `0`, and both sandwich inequalities are trivial.  This file proves that end
explicitly, and records the vacuity of the interior bracket there, so that the run-side work
(`hd`) may be assumed to live at `2 ≤ G.n` and `0 < Rq G` only.

* `isMaxcutSDPValue_zero` — `IsMaxcutSDPValue 0 0` for every dimension (the objective vanishes on
  the zero matrix, and the unit-diagonal PSD set is nonempty since `1` is in it);
* `leaf_at_zero_matrix` — the leaf's per-input conclusion at `L := 0` whenever the weight matrix
  vanishes;
* `bracket_empty_of_Rq_nonpos` — `-Rq G ≤ t` together with `t < -Rq G/40000` is unsatisfiable when
  `Rq G ≤ 0`, i.e. the interior bracket has no point on the degenerate inputs.

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false

namespace QMCLeafB.ZeroEdge

open QuantumMaxCutEnergy

/-- **The Max-Cut SDP value of the zero matrix is zero.** -/
theorem isMaxcutSDPValue_zero (n : ℕ) :
    ModernConvex.Relaxations.IsMaxcutSDPValue (0 : Matrix (Fin n) (Fin n) ℝ) 0 := by
  have hobj : ∀ X : Matrix (Fin n) (Fin n) ℝ,
      ModernConvex.Relaxations.maxcutRelaxationObjective (0 : Matrix (Fin n) (Fin n) ℝ) X = 0 := by
    intro X
    simp [ModernConvex.Relaxations.maxcutRelaxationObjective]
  have hne : (ModernConvex.Relaxations.maxcutRelaxationObjective (0 : Matrix (Fin n) (Fin n) ℝ)
        '' {X | ModernConvex.Relaxations.IsUnitDiagPSD X}) = {0} := by
    ext v
    constructor
    · rintro ⟨X, -, rfl⟩
      exact Set.mem_singleton_iff.mpr (hobj X)
    · intro hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      refine ⟨1, ⟨Matrix.PosSemidef.one, fun i => by simp⟩, hobj 1⟩
  rw [ModernConvex.Relaxations.IsMaxcutSDPValue, hne]
  exact isLUB_singleton

/-- The weight matrix spelled as in the leaf's statement is the zero matrix when every weight is. -/
theorem weightMatrix_eq_zero (G : Input) (hw : ∀ e : Edge G.n, G.weights e = 0) :
    (Matrix.of fun i j : Fin G.n =>
      if h : i < j then ((G.weights ⟨(i, j), h⟩ : ℚ≥0) : ℝ)
      else if h : j < i then ((G.weights ⟨(j, i), h⟩ : ℚ≥0) : ℝ) else 0)
      = (0 : Matrix (Fin G.n) (Fin G.n) ℝ) := by
  ext i j
  by_cases h : i < j
  · simp [h, hw]
  · by_cases h' : j < i
    · simp [h, h', hw]
    · simp [h, h']

/-- **The leaf's per-input conclusion at `L := 0` on the zero-edge inputs.** -/
theorem leaf_at_zero_weight (G : Input) (hw : ∀ e : Edge G.n, G.weights e = 0) :
    ∃ S : ℝ,
      ModernConvex.Relaxations.IsMaxcutSDPValue
        (Matrix.of fun i j : Fin G.n =>
          if h : i < j then ((G.weights ⟨(i, j), h⟩ : ℚ≥0) : ℝ)
          else if h : j < i then ((G.weights ⟨(j, i), h⟩ : ℚ≥0) : ℝ) else 0) S ∧
      (0 : ℝ) ≤ S ∧
      S - 0 ≤ (∑ e, ((G.weights e : ℚ≥0) : ℝ)) / 10000 := by
  have hmat := weightMatrix_eq_zero G hw
  have hsum : (∑ e, ((G.weights e : ℚ≥0) : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    rw [hw e]
    simp
  refine ⟨0, ?_, le_refl _, ?_⟩
  · rw [hmat]
    exact isMaxcutSDPValue_zero G.n
  · rw [hsum]
    norm_num

/-- **The interior bracket is empty on the degenerate inputs.**  If `Rq G ≤ 0` there is no `t` with
`-Rq G ≤ t` and `t < -Rq G/40000`. -/
theorem bracket_empty_of_Rq_nonpos (G : Input)
    (hRq : QMCLeafB.EngineRuntime.Rq G ≤ 0) :
    ¬ ∃ t : ℚ, -QMCLeafB.EngineRuntime.Rq G ≤ t ∧
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
  rintro ⟨t, hlo, hhi⟩
  have hRqR : ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) ≤ 0 := by exact_mod_cast hRq
  have htR : -(((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ)) ≤ ((t : ℚ) : ℝ) := by exact_mod_cast hlo
  have heps : (0 : ℚ) ≤ QMCLeafB.EngineRuntime.Rq G / 40000 := by
    have := QMCLeafB.RundataArith.Rq_nonneg G
    linarith
  have hepsR : (0 : ℝ) ≤ (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by exact_mod_cast heps
  linarith

/-! ## Axiom audit -/

#print axioms QMCLeafB.ZeroEdge.isMaxcutSDPValue_zero
#print axioms QMCLeafB.ZeroEdge.weightMatrix_eq_zero
#print axioms QMCLeafB.ZeroEdge.leaf_at_zero_weight
#print axioms QMCLeafB.ZeroEdge.bracket_empty_of_Rq_nonpos

end QMCLeafB.ZeroEdge


