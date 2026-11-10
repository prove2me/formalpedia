-- Prove2me | Definitions.Def_GEPPGrowth_Main_GEPP
-- name    : GEPPGrowth_Main_GEPP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T23:35:57.876474+00:00
-- url     : https://prove2.me/theorems/cbf136b4-14ce-4b5b-9aab-e74ce2798359
-- title:
--   Exact Gaussian elimination with partial pivoting and final-U growth
-- statement:
--   Starting from a real square matrix $A$, the state records its current entries and the original label of every row. At the source step $k$ select the smallest eligible maximizing row, swap it into row $k$, and call the swapped matrix $B$. The update is
--
--   $$l_i=\begin{cases}B_{ik}/B_{kk}&i>k,\\0&i\le k,\end{cases}\quad b_j=\begin{cases}B_{kj}&j\ge k,\\0&j<k,\end{cases}\quad A^{(k+1)}=B-lb^\top.$$
--
--   The matrix $U$ is the final upper triangular part. A redundant final one-row step changes nothing. With $\|A\|_{\max}=\max_{ij}|A_{ij}|$, the growth factor is
--
--   $$\rho(A)=\frac{\|U\|_{\max}}{\|A\|_{\max}}.$$
--
--   The residual is the actual trailing block. The selected pivot minor uses original input row labels in pivot order, rather than an independent minor. An alternate pivot-rule interface expresses all allowed tie resolutions. The regular-input predicate excludes zero pivots and ties in absolute residual entries; it is only used in a conclusion establishing an almost-sure property, never as a hypothesis of the goal. Zero division gives a total extension on singular inputs. Empty maxima equal zero. The source's 1-based coordinate $i$ is Lean's index $i-1$.
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), §2.1, printed pp.2–3, PDF pp.3–4; Definition 2.1, printed p.4, PDF p.5

import Definitions.Def_GEPPGrowth_Main_Covariance
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Full-size GEPP state, retaining the labels of the original input rows. -/
structure RunState (n : ℕ) where
  matrix : Mat n
  labels : Fin n → Fin n

/-- Smallest maximizing eligible row. k is zero-based; it is a valid pivot position. -/
noncomputable def rowPivot {n : ℕ} (A : Mat n) (k : Fin n) : Fin n :=
  (List.finRange n).foldl (fun b j =>
    if k ≤ j ∧ (|A b k| < |A j k| ∨ (|A b k| = |A j k| ∧ j < b))
    then j else b) k

/-- One exact §2.1 elimination step, including its row swap. -/
def stepAt {n : ℕ} (s : RunState n) (k i : Fin n) : RunState n :=
  let sw := Equiv.swap k i
  let B := s.matrix.submatrix sw id
  { matrix := fun a b => B a b -
      (if k < a then B a k / B k k else 0) * (if k ≤ b then B k b else 0)
    labels := fun a => s.labels (sw a) }

noncomputable def run {n : ℕ} (A : Mat n) : ℕ → RunState n
  | 0 => ⟨A, id⟩
  | t+1 => let s := run A t
           if h : t < n then stepAt s ⟨t,h⟩ (rowPivot s.matrix ⟨t,h⟩) else s

/-- Final U, rather than the largest intermediate elimination entry. The redundant final
one-row step makes no change to the matrix. -/
noncomputable def upper {n : ℕ} (A : Mat n) : Mat n :=
  fun i j => if i ≤ j then (run A n).matrix i j else 0

/-- Maximum of a finite real matrix's absolute entries; zero for an empty matrix. -/
noncomputable def maxEntry {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  (((Finset.univ : Finset (Fin n × Fin m)).sup (fun ij => ‖A ij.1 ij.2‖₊) : NNReal) : ℝ)

/-- Definition 2.1. On the zero matrix Lean division sets the ratio to zero. -/
noncomputable def growth {n : ℕ} (A : Mat n) : ℝ := maxEntry (upper A) / maxEntry A

/-- The actual trailing square block after t completed eliminations. -/
noncomputable def residual {n : ℕ} (A : Mat n) (t : ℕ) : Mat (n-t) :=
  (run A t).matrix.submatrix
    (fun i => ⟨i.val+t, by omega⟩) (fun j => ⟨j.val+t, by omega⟩)

/-- Original row labels of the first t pivots, in their selection order. -/
noncomputable def pivotMinor {n t : ℕ} (ht : t ≤ n) (A : Mat n) : Mat t :=
  fun i j => A ((run A t).labels ⟨i.val, by omega⟩) ⟨j.val, by omega⟩

def firstColumns {n t : ℕ} (ht : t ≤ n) (A : Mat n) : Matrix (Fin n) (Fin t) ℝ :=
  fun i j => A i ⟨j.val, by omega⟩

/-- Null exceptional inputs include a zero pivot and all nonunique absolute pivot maxima. -/
noncomputable def Regular {n : ℕ} (A : Mat n) : Prop :=
  ∀ (t : ℕ) (h : t < n),
    (run A t).matrix (rowPivot (run A t).matrix ⟨t,h⟩) ⟨t,h⟩ ≠ 0 ∧
    ∀ i j : Fin n, t ≤ i.val → t ≤ j.val →
      |(run A t).matrix i ⟨t,h⟩| = |(run A t).matrix j ⟨t,h⟩| → i = j

/-- Any allowed tie resolution, for the convention-equivalence assertion. -/
def IsPivotRule {n : ℕ} (p : Fin n → Mat n → Fin n) : Prop :=
  ∀ k B, k ≤ p k B ∧ ∀ j, k ≤ j → |B j k| ≤ |B (p k B) k|

noncomputable def runWith {n : ℕ} (p : Fin n → Mat n → Fin n) (A : Mat n) : ℕ → RunState n
  | 0 => ⟨A, id⟩
  | t+1 => let s := runWith p A t
           if h : t < n then stepAt s ⟨t,h⟩ (p ⟨t,h⟩ s.matrix) else s

noncomputable def upperWith {n : ℕ} (p : Fin n → Mat n → Fin n) (A : Mat n) : Mat n :=
  fun i j => if i ≤ j then (runWith p A n).matrix i j else 0

end GEPPGrowth.Main


