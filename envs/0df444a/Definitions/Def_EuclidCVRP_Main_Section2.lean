-- Prove2me | Definitions.Def_EuclidCVRP_Main_Section2
-- name    : EuclidCVRP_Main_Section2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:06:41.945635+00:00
-- url     : https://prove2.me/theorems/06510cd3-86f0-4540-80af-3eaca1cdf9d7
-- title:
--   The setting of Section 2: big clients, grid cells, preassignment, dense cells, closed walks
-- statement:
--   Fix $\varepsilon>0$, $D\ge1$, a valid $D$-bounded instance and an optimal solution $\mathrm{OPT}$ with at most $\Gamma$ tours, all nonempty (the **setting of Section 2**).
--
--   1. A client $v$ is **big** if $d(v)\ge\delta Q$ with $\delta=\varepsilon/D$, and small otherwise.
--   2. The plane is cut into square **cells** of side $\tau=\varepsilon^2/D$; the depot is a grid vertex and cells are half-open, $[a,a+\tau)\times[b,b+\tau)$. The $K=(2\lceil D/\tau\rceil+1)^2$ cells around the depot contain every client, and $K$ depends only on $\varepsilon$ and $D$.
--   3. A tour **traverses** a cell if its closed polygonal curve meets the cell.
--   4. **Preassignment.** $V_{\mathrm{fixed}}(T)$ is the set of clients of $T$ that are big or lie in a cell traversed by exactly one tour of $\mathrm{OPT}$; $V_{\mathrm{left}}(T)=V(T)\setminus V_{\mathrm{fixed}}(T)$; the leftover capacity is $Q_T=Q-\sum_{v\in V_{\mathrm{fixed}}(T)}d(v)$.
--   5. The slack parameter is $\eta_{\mathrm{slack}}=\min\{\varepsilon/D,\,1/K\}$.
--   6. A cell $C$ is an admissible **dense cell** $\mathrm{Cell}(T)$ of $T$ if the clients of $V_{\mathrm{left}}(T)$ in $C$ have total demand at least $d(V_{\mathrm{left}}(T))/K$.
--   7. A **closed walk** is a closed polygonal walk through arbitrary points of the plane, with a set $V(P)$ of clients it serves; it is well formed if it passes through the depot and through the location of every client it serves. Its cost $c(P)$ is its length.
--
--   These are the objects of Lemmas 6, 7 and 9 and Claim 8.
--
--   **Formalization Note** The grid's exact construction is not fixed by the source ("the exact construction of the cells is not important", p. 7); half-open cells aligned at the depot partition the plane, so every client lies in exactly one cell.
-- source:
--   Jannis Blauth, Fabrizio Grandoni, Bence Mátravölgyi, Ramin Mousavi, Kinter Ren, Mohammad R. Salavatipour, STOC 2027 submission #1236 (October 2026), §2, pp. 6–8 (δ = ε/D, τ = ε²/D, K, traversal, V_fixed, V_left, Q_T, Cell(T)); Lemma 6, p. 7 (η_slack); Lemma 9, p. 10 (closed walks)

import Mathlib
import Definitions.Def_EuclidCVRP_Main_Instance

set_option autoImplicit false

namespace EuclidCVRP.Main

/-!
# The setting of Section 2 (bounded number of tours)

Blauth, Grandoni, Mátravölgyi, Mousavi, Ren, Salavatipour, STOC 2027 submission #1236 (October 2026),
§2, pp. 6–8: big clients (`δ = ε/D`), the square grid of side `τ = ε²/D` with `K` cells, traversal,
the preassignment (`V_fixed(T)`, `V_left(T)`, `Q_T`), `η_slack = min{ε/D, 1/K}` (Lemma 6), the
dense cell `Cell(T)` (p. 8), and closed walks serving clients (Lemma 9, p. 10).
-/

namespace Sec2

variable (I : Instance) (ε D : ℝ)

/-- The big-client threshold `δ = ε/D` (p. 6). -/
noncomputable def δ : ℝ := ε / D

/-- The cell side length `τ = ε²/D` (p. 7). -/
noncomputable def τ : ℝ := ε ^ 2 / D

/-- The grid cell containing a point: the grid of squares of side `τ` with the depot at a grid
vertex; cells are half-open, `[a, a+τ) × [b, b+τ)`, so they partition the plane. -/
noncomputable def cellOf (p : Pt) : ℤ × ℤ :=
  (⌊(p.ofLp 0 - I.depot.ofLp 0) / τ ε D⌋, ⌊(p.ofLp 1 - I.depot.ofLp 1) / τ ε D⌋)

/-- The points of the cell with index `c`. -/
def cellSet (c : ℤ × ℤ) : Set Pt := {p | cellOf I ε D p = c}

/-- The number of cells per half-row covering the disc of radius `D` around the depot. -/
noncomputable def gridRadius : ℕ := ⌈D / τ ε D⌉₊

/-- The number `K` of grid cells covering the disc of radius `D` around the depot (the cells with
indices in `[-gridRadius, gridRadius]²`); it depends only on `ε` and `D`. -/
noncomputable def K : ℕ := (2 * gridRadius ε D + 1) ^ 2

/-- The slack parameter `η_slack = min{ε/D, 1/K}` (Lemma 6, p. 7). -/
noncomputable def ηslack : ℝ := min (ε / D) (1 / (K ε D : ℝ))

variable (OPT : List (List (Fin I.n)))

/-- A client is **big** if `d(v) ≥ δ Q` (p. 6), and small otherwise. -/
def Big (v : Fin I.n) : Prop := δ ε D * I.Q ≤ I.dem v

/-- The tour of `OPT` with index `j` traverses the cell `c`. -/
def TraversedBy (j : Fin OPT.length) (c : ℤ × ℤ) : Prop :=
  Traverses (I.tourPts OPT[j]) (cellSet I ε D c)

/-- The number of tours of `OPT` traversing the cell `c`. -/
noncomputable def numTraversing (c : ℤ × ℤ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j : Fin OPT.length => TraversedBy I ε D OPT j c)).card

/-- `V_fixed(T)` (pp. 6–7): the clients of the tour `T` preassigned to it, namely its big clients and
its clients lying in a cell traversed by exactly one tour of `OPT`. -/
noncomputable def Vfixed (j : Fin OPT.length) : Finset (Fin I.n) := by
  classical
  exact (OPT[j]).toFinset.filter
    (fun v => Big I ε D v ∨ numTraversing I ε D OPT (cellOf I ε D (I.loc v)) = 1)

/-- `V_left(T) = V(T) \ V_fixed(T)` (p. 7). -/
noncomputable def Vleft (j : Fin OPT.length) : Finset (Fin I.n) := by
  classical
  exact (OPT[j]).toFinset \ Vfixed I ε D OPT j

/-- The leftover capacity `Q_T = Q − ∑_{v ∈ V_fixed(T)} d(v)` (p. 7). -/
noncomputable def QT (j : Fin OPT.length) : ℝ := (I.Q : ℝ) - I.demSet (Vfixed I ε D OPT j)

/-- `c` is an admissible dense cell `Cell(T)` of the tour `T` (p. 8): the clients of `V_left(T)` lying
in `c` have total demand at least `d(V_left(T))/K`. -/
def IsDenseCell (j : Fin OPT.length) (c : ℤ × ℤ) : Prop := by
  classical
  exact (I.demSet ((Vleft I ε D OPT j).filter (fun v => cellOf I ε D (I.loc v) = c)) : ℝ) ≥
    (I.demSet (Vleft I ε D OPT j) : ℝ) / (K ε D : ℝ)

/-- **The standing assumptions of Section 2** (p. 6, "We fix an optimum solution OPT with
|OPT| ≤ Γ"; Theorem 4): a valid `D`-bounded instance and an optimal solution `OPT` consisting of at
most `Γ` tours, all nonempty. -/
def Setting (Γ : ℕ) : Prop :=
  I.Valid ∧ I.DBounded D ∧ I.IsOptimal OPT ∧ (∀ T ∈ OPT, T ≠ []) ∧ OPT.length ≤ Γ

end Sec2

/-- **A closed walk serving clients** (Lemmas 7 and 9): a closed polygonal walk through the points
`pts` of the plane (arbitrary points, repetitions allowed), together with the set `serves` of the
clients it serves. -/
structure Walk (I : Instance) where
  /-- the vertices of the closed polygonal walk, in order -/
  pts : List Pt
  /-- the clients `V(P)` served by the walk -/
  serves : Finset (Fin I.n)

/-- A walk is well formed: it passes through the depot and through the location of every client it
serves. -/
def Walk.Valid {I : Instance} (w : Walk I) : Prop :=
  I.depot ∈ w.pts ∧ ∀ v ∈ w.serves, I.loc v ∈ w.pts

/-- The length `c(P)` of a walk. -/
noncomputable def Walk.cost {I : Instance} (w : Walk I) : ℝ := closedLen w.pts

end EuclidCVRP.Main


