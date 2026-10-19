-- Prove2me | Definitions.Def_QAlgorithms_Defs_SchurShapes
-- name    : QAlgorithms_Defs_SchurShapes
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:37:15.796531+00:00
-- url     : https://prove2.me/theorems/b5a51c72-3d2a-43aa-a3d8-2c4abd30b90d
-- title:
--   SchurShapes
-- statement:
--   SchurShapes
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\SchurShapes.lean

import Definitions.Def_QAlgorithms_Defs_Information
import Mathlib.Combinatorics.Young.YoungDiagram

noncomputable section

namespace QAlgorithms.Schur

/-- Young shapes of size n and height at most d, shared by both Schur estimators
(1508.01797 pp.4-6; 1508.01907 p.4). -/
abbrev Partition (d n : ℕ) := {lambda : YoungDiagram // lambda.card = n ∧ lambda.colLen 0 ≤ d}

/-- Padded normalized row vector, with positive copy count
(1508.01907 p.2 and p.8). -/
def normalizedRows {d n : ℕ} (_hd : 0 < d) (hn : 0 < n) (lambda : Partition d n) :
    Fin d → ℝ := fun i => (lambda.val.rowLen i.val : ℝ)/n

/-- Complex diagonal lambda/n, with no truncation renormalization
(1508.01797 pp.5-6, Eqs.(9)-(10)). -/
def normalizedDiagram {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (lambda : Partition d n) :
    Matrix (Fin d) (Fin d) ℂ := Matrix.diagonal fun i => (normalizedRows hd hn lambda i : ℂ)

/-- Public decoder U diag(lambda/n) U dagger, independent of the true state
(1508.01797 p.6, Eq.(10); 1508.01907 p.8). -/
def estimate {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (lambda : Partition d n)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  (U : Matrix _ _ ℂ)*normalizedDiagram hd hn lambda*star (U : Matrix _ _ ℂ)

example {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (lambda : Partition d n) :
    estimate hd hn lambda 1 = normalizedDiagram hd hn lambda := by simp [estimate]

example {n : ℕ} (hn : 0 < n) (lambda : Partition 1 n)
    (hrow : lambda.val.rowLen 0 = n) :
    normalizedRows (by omega) hn lambda 0 = 1 := by
  simp [normalizedRows, hrow, (Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne']

end QAlgorithms.Schur


