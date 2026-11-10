-- Prove2me | Definitions.Def_MovementSorting_Exponent_Geometry
-- name    : MovementSorting_Exponent_Geometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:01:19.620841+00:00
-- url     : https://prove2.me/theorems/3378f7ba-b87d-4b4e-ae24-d1ce069398d9
-- title:
--   Cells, the cell metric, co-blocked cells C_b, and lengths of sequences
-- statement:
--   A cell is an unordered pair of positions (`Sym2`); genuine cells are the non-diagonal ones. The metric on cells is $\mathrm{dist}(\{x,y\},\{x',y'\}) = \min(\|x-x'\|_1+\|y-y'\|_1, \|x-y'\|_1+\|y-x'\|_1)$. Two positions are co-blocked at the integer scale $b$ when their (0-based) ranks lie in the same scale-$b$ block, i.e. have the same quotient by $b$ (the paper's 1-based blocks $\{(i-1)b+1,\dots,ib\}$); $C_b$ (`coBlocked π b`) is the set of genuine cells co-blocked at scale $b$. A route visits a cell when it visits one of its two orientations, and `visitedCount ρ W` counts the cells of $W$ a route visits. For a metric space, `pathLength` is the sum of the distances between consecutive points of a finite sequence, and `nnDist W w` is $\nu_W(w) = \min_{w' \in W\setminus\{w\}} \mathrm{dist}(w,w')$ (set to $0$ when $W\setminus\{w\}$ is empty, a case excluded wherever it is used).
-- source:
--   Wang (2026), The Movement Complexity of Sorting, arXiv:2611.01157 (held copy SHA-256 90e3d9df…), Definitions 2.2, 2.4 and 3.1, pp. 7–9; Fact 3.2, p. 10

import Definitions.Def_MovementSorting_Exponent_Model

set_option autoImplicit false

namespace MovementSorting.Exponent

/-! # Cells, blocks and co-blocked cells (Wang 2026, Definitions 2.2, 2.4, 3.1, pp. 7–9);
lengths of sequences in a metric space (Fact 3.2, p. 10) -/

/-- A cell `{x, y}`: an unordered pair of positions (`Sym2`); a genuine cell has `x ≠ y`. -/
abbrev Cell (d m : ℕ) := Sym2 (Pos d m)

/-- `dist({x,y},{x',y'}) = min(‖x-x'‖₁ + ‖y-y'‖₁, ‖x-y'‖₁ + ‖y-x'‖₁)`. -/
def cellDist {d m : ℕ} : Cell d m → Cell d m → ℕ :=
  Sym2.lift₂ ⟨fun x y x' y' => min (posL1 x x' + posL1 y y') (posL1 x y' + posL1 y x'),
    fun x y x' y' => by
      refine ⟨?_, ?_⟩
      · dsimp only
        rw [add_comm (posL1 y x') (posL1 x y'), add_comm (posL1 y y') (posL1 x x'), min_comm]
      · dsimp only
        rw [min_comm]⟩

/-- Two positions are co-blocked at the integer scale `b`: their (0-based) ranks lie in the same
scale-`b` block `{ib, …, ib + b - 1}` (the paper's 1-based block `{(i-1)b+1, …, ib}`). -/
def coBlockedPair {d m : ℕ} (π : Input d m) (b : ℕ) : Cell d m → Bool :=
  Sym2.lift ⟨fun x y => decide ((π x : ℕ) / b = (π y : ℕ) / b),
    fun x y => by simp only [eq_comm]⟩

/-- `C_b`: the cells (unordered pairs of distinct positions) co-blocked at scale `b`. -/
def coBlocked {d m : ℕ} (π : Input d m) (b : ℕ) : Finset (Cell d m) :=
  Finset.univ.filter (fun c => ¬ c.IsDiag ∧ coBlockedPair π b c = true)

/-- A route visits a cell if it visits one of its orientations. -/
def visitsCell {d m : ℕ} (ρ : List (Config d m)) (c : Cell d m) : Bool :=
  ρ.any (fun z => decide (s(z.1, z.2) = c))

/-- The number of cells of a set `W` that a route visits. -/
def visitedCount {d m : ℕ} (ρ : List (Config d m)) (W : Finset (Cell d m)) : ℕ :=
  (W.filter (fun c => visitsCell ρ c = true)).card

/-- The length of a finite sequence of points of a metric space: the sum of the distances between
consecutive points. -/
noncomputable def pathLength {Y : Type*} [MetricSpace Y] (s : List Y) : ℝ :=
  ((s.zip s.tail).map (fun p => dist p.1 p.2)).sum

/-- `ν_W(w) = min_{w' ∈ W ∖ {w}} dist(w, w')` (set to `0` when `W ∖ {w}` is empty, a case the
statements exclude by `|W| ≥ 2`). -/
noncomputable def nnDist {Y : Type*} [MetricSpace Y] [DecidableEq Y] (W : Finset Y) (w : Y) : ℝ :=
  if h : (W.erase w).Nonempty then (W.erase w).inf' h (dist w) else 0

end MovementSorting.Exponent


