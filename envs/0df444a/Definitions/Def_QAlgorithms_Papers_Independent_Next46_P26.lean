-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P26
-- name    : QAlgorithms_Papers_Independent_Next46_P26
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T14:04:05.422711+00:00
-- url     : https://prove2.me/theorems/d13778e9-1c72-49d9-8b69-541ab997808d
-- title:
--   Definitions for The weighted hook length formula
-- statement:
--   The objects the formalized statements of *The weighted hook length formula* (arXiv:1006.0043) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Cell`
--   - `corners`: Occupied removable corners, in zero-based English coordinates (§1, p.3).
--   - `noncorners`: The noncorner cells, and the cells D_rs of equation (3) (p.4).
--   - `offCross`
--   - `oneBoxPredecessors`: Exactly the one-box predecessor diagrams of §1 (p.3).
--   - `tableauCount`: The accepted inverse filling predicate, restricted to the finite occupied-cell codomain. Labels and coordinates are zero-based; there is no dimension cutoff (p.3).
--   - `hook`: The accepted hook counts the occupied cell, its strict arm and strict leg (p.3).
--   - `hookProduct`: Hook products in the rational numbers; subtraction is subsequently in ℚ (pp.3–4).
--   - `strictHook`: Strict-hook linear weight, equation (4), p.4.
--   - `rowGap`: The two cross denominators in WHL; all bounds have been shifted from one-based source indices to zero-based indices (pp.2,6).
--   - `colGap`
--   - `totalWeight`: Total starting weight W (pp.2,8).
--   - `cornerWeight`: The named corner weight Π_rs of Theorem 2 (p.6), not a further product.
--   - `outsideA`: The two outside denominators of Theorem 2(b–d), p.6.
--   - `outsideB`
--   - `WeightPoly`: The polynomial ring on exactly the occupied rows and columns (pp.2,6).
--   - `WeightRat`
--   - `polyX`: Canonical tagged row/column indeterminates; unused out-of-range indices are extended by zero and are never used in the displayed formulas (p.4).
--   - `polyY`
--   - `ratX`
--   - `ratY`
--   - `polynomialTerm`: The single corner summand of the polynomial equation (4), p.4.
--   - `kerovPi`: Corrected Kerov corner factors, Corollary 3, p.7. X_i in Lean means source X_(i+1), whereas Y_i retains its source index.
--   - `kerovZ`: Z and S of Corollary 3, p.7.
--   - `kerovS`
--   - `successors`: Strict legal arm/leg successors of §4.1, p.8; diagonals are excluded.
--   - `modifiedSuccessors`: Modified hook of §4.2, p.8: skip the entire equal-length row or column block. Finset.min is +infinity if the eligible corner set is empty, so bad inputs yield no successors in that direction.
--   - `moveWeight`: Single transition mass, normalized over the entire strict or modified hook, not separately over its two directions (§4, p.8).
--   - `walkEval`: Finite evaluation of the actual stopped path law (§4, pp.8–9). At a terminal cell return the event on [z]; otherwise sum the normalized transition masses. At insufficient fuel return zero. On a valid diagram, card(lam) fuel covers every path, as every move strictly increases a coordinate.
--   - `terminalProb`: Probability of the actual terminal cell, including the random initial cell with probability x_i y_j/W (§4, pp.8–9).
--   - `PositiveWeights`: Strict positivity only on the occupied row/column ranges (p.8).
--   - `rowEnds`: Row and column block endpoints, sorted in increasing coordinate (§4.2, pp.8–9).
--   - `colEnds`
--   - `blockCorner`: Output corner of a terminal modified block (p.9, staircase proof). The raw cell need not be its block's southeast endpoint: on a rectangle every modified hook is empty. Identify its equal-row/equal-column block with that endpoint, as required by the source's staircase equivalence. On out-of-range raw inputs the find operations default to the given coordinate.
--   - `modifiedTerminalProb`: Terminal-corner output law of the modified process (pp.8–9). Sum the actual modified transition law on raw cells, and identify the final block with its corner, rather than requiring the last raw cell to be that corner.
--   - `blockX`: X_k is the sum of row weights, and Y_k the sum of column weights, over equal-length blocks (p.9, Figure 4 and proof of Theorem 5). The prose on p.9 mistakenly says elements of U for both sums; the example fixes the intended meaning.
--   - `blockY`
--   - `cornerRank`: Zero-based rank of an actual corner, from top right to bottom left (p.9).
--   - `staircaseWeight`: Corner factor for the c-row staircase in Theorem 5, p.9.
--   - `projectionProb`: Projection-event probability from a deterministic starting cell, equivalent to conditioning on that positive-probability start (§5, pp.9–10).
--   - `Label`: Tagged formal labels; row and column labels are distinct regardless of any later numerical specialization (§2.2, pp.4–5).
--   - `Arrangement`: Raw arrangement with canonical dummy labels at corners. The predicates below restrict exactly the labels used in F_lambda and G_lambda (pp.4–5).
--   - `oldLabel`: Read an old label, with a fixed dummy outside the occupied diagram (p.5).
--   - `StrictLabel`: Strict-hook admissibility of a tagged label (§2.2, p.4).
--   - `hookLabelInputs`: F_lambda, including the starting-square special labels (§2.2, p.4).
--   - `hookLabelOutputs`: G_lambda with the source's special rules on the terminal row and column; at a corner lambda'_s=r+1 and lambda_r=s+1 in zero-based coordinates (p.4).
--   - `arrowTarget`: Arrow encoded by a tagged label (p.5).
--   - `arrowPath`: Follow the old labels, stopping at the first corner (p.5). Fuel card(lam) suffices on hookLabelInputs because every strict-hook arrow advances a coordinate.
--   - `rearrangeHookLabels`: The p.5 rearrangement, evaluated from the old arrangement simultaneously. Projected visited rows get their own x-label and projected columns their own y-label. Other walk cells receive the old label from the shaded row/column. This also handles a walk that starts at a corner without reading a corner label.
-- source:
--   The weighted hook length formula, arXiv:1006.0043v1, https://arxiv.org/abs/1006.0043v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

abbrev Cell := ℕ × ℕ

/-- Occupied removable corners, in zero-based English coordinates (§1, p.3). -/
def corners (lam : YoungDiagram) : Finset Cell :=
  lam.cells.filter fun z => (z.1 + 1, z.2) ∉ lam ∧ (z.1, z.2 + 1) ∉ lam

/-- The noncorner cells, and the cells D_rs of equation (3) (p.4). -/
def noncorners (lam : YoungDiagram) : Finset Cell := lam.cells \ corners lam

def offCross (lam : YoungDiagram) (r s : ℕ) : Finset Cell :=
  (noncorners lam).filter fun z => z.1 ≠ r ∧ z.2 ≠ s

/-- Exactly the one-box predecessor diagrams of §1 (p.3). -/
def oneBoxPredecessors (lam : YoungDiagram) : Finset YoungDiagram :=
  ((lam.cells.powerset.filter fun a : Finset Cell => a.card + 1 = lam.card ∧
    IsLowerSet (a : Set Cell)).attach).image fun a =>
      (⟨a.val, (Finset.mem_filter.mp a.property).2.2⟩ : YoungDiagram)

/-- The accepted inverse filling predicate, restricted to the finite occupied-cell
codomain. Labels and coordinates are zero-based; there is no dimension cutoff (p.3). -/
def tableauCount (lam : YoungDiagram) : ℕ :=
  Fintype.card {t : Fin lam.card → {z : Cell // z ∈ lam.cells} //
    QAlgorithms.Papers.Independent.Dependency50.P31.IsTableau lam (fun i => (t i).val)}

/-- The accepted hook counts the occupied cell, its strict arm and strict leg (p.3). -/
abbrev hook (lam : YoungDiagram) (z : Cell) : ℕ :=
  QAlgorithms.Papers.Independent.Dependency50.P31.cellHook lam.cells z

/-- Hook products in the rational numbers; subtraction is subsequently in ℚ (pp.3–4). -/
def hookProduct (lam : YoungDiagram) : ℚ := ∏ z ∈ lam.cells, (hook lam z : ℚ)

/-- Strict-hook linear weight, equation (4), p.4. -/
def strictHook {K : Type*} [CommSemiring K] (lam : YoungDiagram)
    (x y : ℕ → K) (i j : ℕ) : K :=
  (∑ k ∈ Finset.Ico (i + 1) (lam.colLen j), x k) +
    ∑ l ∈ Finset.Ico (j + 1) (lam.rowLen i), y l

/-- The two cross denominators in WHL; all bounds have been shifted from
one-based source indices to zero-based indices (pp.2,6). -/
def rowGap {K : Type*} [CommSemiring K] (lam : YoungDiagram)
    (x y : ℕ → K) (i r s : ℕ) : K :=
  (∑ k ∈ Finset.Ico (i + 1) (r + 1), x k) +
    ∑ l ∈ Finset.Ico (s + 1) (lam.rowLen i), y l

def colGap {K : Type*} [CommSemiring K] (lam : YoungDiagram)
    (x y : ℕ → K) (j r s : ℕ) : K :=
  (∑ k ∈ Finset.Ico (r + 1) (lam.colLen j), x k) +
    ∑ l ∈ Finset.Ico (j + 1) (s + 1), y l

/-- Total starting weight W (pp.2,8). -/
def totalWeight {K : Type*} [CommSemiring K] (lam : YoungDiagram)
    (x y : ℕ → K) : K := ∑ z ∈ lam.cells, x z.1 * y z.2

/-- The named corner weight Π_rs of Theorem 2 (p.6), not a further product. -/
def cornerWeight {K : Type*} [Field K] (lam : YoungDiagram)
    (x y : ℕ → K) (r s : ℕ) : K :=
  x r * y s * (∏ i ∈ Finset.range r, (1 + x i / rowGap lam x y i r s)) *
    ∏ j ∈ Finset.range s, (1 + y j / colGap lam x y j r s)

/-- The two outside denominators of Theorem 2(b–d), p.6. -/
def outsideA {K : Type*} [CommSemiring K] (lam : YoungDiagram)
    (x y : ℕ → K) (r s : ℕ) : K :=
  (∑ k ∈ Finset.Ico (r + 1) (lam.colLen 0), x k) +
    ∑ l ∈ Finset.range (s + 1), y l

def outsideB {K : Type*} [CommSemiring K] (lam : YoungDiagram)
    (x y : ℕ → K) (r s : ℕ) : K :=
  (∑ k ∈ Finset.range (r + 1), x k) +
    ∑ l ∈ Finset.Ico (s + 1) (lam.rowLen 0), y l

/-- The polynomial ring on exactly the occupied rows and columns (pp.2,6). -/
abbrev WeightPoly (lam : YoungDiagram) :=
  MvPolynomial (Sum (Fin (lam.colLen 0)) (Fin (lam.rowLen 0))) ℚ

abbrev WeightRat (lam : YoungDiagram) := FractionRing (WeightPoly lam)

/-- Canonical tagged row/column indeterminates; unused out-of-range indices
are extended by zero and are never used in the displayed formulas (p.4). -/
def polyX (lam : YoungDiagram) (i : ℕ) : WeightPoly lam :=
  if h : i < lam.colLen 0 then MvPolynomial.X (Sum.inl ⟨i, h⟩) else 0

def polyY (lam : YoungDiagram) (j : ℕ) : WeightPoly lam :=
  if h : j < lam.rowLen 0 then MvPolynomial.X (Sum.inr ⟨j, h⟩) else 0

def ratX (lam : YoungDiagram) (i : ℕ) : WeightRat lam :=
  algebraMap (WeightPoly lam) (WeightRat lam) (polyX lam i)

def ratY (lam : YoungDiagram) (j : ℕ) : WeightRat lam :=
  algebraMap (WeightPoly lam) (WeightRat lam) (polyY lam j)

/-- The single corner summand of the polynomial equation (4), p.4. -/
def polynomialTerm (lam : YoungDiagram) (r s : ℕ) : WeightPoly lam :=
  polyX lam r * polyY lam s *
    (∏ z ∈ offCross lam r s, strictHook lam (polyX lam) (polyY lam) z.1 z.2) *
    (∏ i ∈ Finset.range r, (polyX lam i + rowGap lam (polyX lam) (polyY lam) i r s)) *
    ∏ j ∈ Finset.range s, (polyY lam j + colGap lam (polyX lam) (polyY lam) j r s)

/-- Corrected Kerov corner factors, Corollary 3, p.7. X_i in Lean means
source X_(i+1), whereas Y_i retains its source index. -/
def kerovPi (d : ℕ) (q : ℝ) (X Y : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∏ i ∈ Finset.range k,
    (q ^ Y (i + 1) - q ^ X k) / (q ^ X i - q ^ X k)) *
  ∏ i ∈ Finset.Ico (k + 1) d,
    (q ^ X k - q ^ Y i) / (q ^ X k - q ^ X i)

/-- Z and S of Corollary 3, p.7. -/
def kerovZ (d : ℕ) (q : ℝ) (X Y : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range d, q ^ X i) - ∑ i ∈ Finset.Ico 1 d, q ^ Y i

def kerovS (d : ℕ) (q : ℝ) (X Y : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range d, ∑ j ∈ Finset.Ico i d,
    (q ^ Y i - q ^ X i) * (q ^ X j - q ^ Y (j + 1))

/-- Strict legal arm/leg successors of §4.1, p.8; diagonals are excluded. -/
def successors (lam : YoungDiagram) (z : Cell) : Finset Cell :=
  lam.cells.filter fun t => (t.2 = z.2 ∧ z.1 < t.1) ∨ (t.1 = z.1 ∧ z.2 < t.2)

/-- Modified hook of §4.2, p.8: skip the entire equal-length row or column
block. Finset.min is +infinity if the eligible corner set is empty, so bad
inputs yield no successors in that direction. -/
def modifiedSuccessors (lam : YoungDiagram) (z : Cell) : Finset Cell :=
  lam.cells.filter fun t =>
    (t.2 = z.2 ∧
      (((corners lam).filter fun c => z.1 ≤ c.1).image Prod.fst).min < (t.1 : WithTop ℕ)) ∨
    (t.1 = z.1 ∧
      (((corners lam).filter fun c => z.2 ≤ c.2).image Prod.snd).min < (t.2 : WithTop ℕ))

/-- Single transition mass, normalized over the entire strict or modified hook,
not separately over its two directions (§4, p.8). -/
def moveWeight (x y : ℕ → ℝ) (z t : Cell) : ℝ :=
  if t.2 = z.2 then x t.1 else y t.2

/-- Finite evaluation of the actual stopped path law (§4, pp.8–9).
At a terminal cell return the event on [z]; otherwise sum the normalized
transition masses. At insufficient fuel return zero. On a valid diagram,
card(lam) fuel covers every path, as every move strictly increases a coordinate. -/
def walkEval (next : Cell → Finset Cell) (x y : ℕ → ℝ) :
    ℕ → Cell → (List Cell → ℝ) → ℝ
  | 0, z, event => if next z = ∅ then event [z] else 0
  | fuel + 1, z, event =>
    if next z = ∅ then event [z] else
      ∑ t ∈ next z, moveWeight x y z t /
        (∑ u ∈ next z, moveWeight x y z u) *
          walkEval next x y fuel t (fun tail => event (z :: tail))

/-- Probability of the actual terminal cell, including the random initial cell
with probability x_i y_j/W (§4, pp.8–9). -/
def terminalProb (lam : YoungDiagram) (next : Cell → Finset Cell)
    (x y : ℕ → ℝ) (c : Cell) : ℝ :=
  ∑ z ∈ lam.cells, (x z.1 * y z.2 / totalWeight lam x y) *
    walkEval next x y lam.card z (fun p => if p.getLast? = some c then 1 else 0)

/-- Strict positivity only on the occupied row/column ranges (p.8). -/
def PositiveWeights (lam : YoungDiagram) (x y : ℕ → ℝ) : Prop :=
  (∀ i < lam.colLen 0, 0 < x i) ∧ (∀ j < lam.rowLen 0, 0 < y j)

/-- Row and column block endpoints, sorted in increasing coordinate (§4.2, pp.8–9). -/
def rowEnds (lam : YoungDiagram) : List ℕ := ((corners lam).image Prod.fst).sort (· ≤ ·)

def colEnds (lam : YoungDiagram) : List ℕ := ((corners lam).image Prod.snd).sort (· ≤ ·)

/-- Output corner of a terminal modified block (p.9, staircase proof).
The raw cell need not be its block's southeast endpoint: on a rectangle
every modified hook is empty. Identify its equal-row/equal-column block
with that endpoint, as required by the source's staircase equivalence.
On out-of-range raw inputs the find operations default to the given coordinate. -/
def blockCorner (lam : YoungDiagram) (z : Cell) : Cell :=
  (((rowEnds lam).find? (fun r => decide (z.1 ≤ r))).getD z.1,
    ((colEnds lam).find? (fun s => decide (z.2 ≤ s))).getD z.2)

/-- Terminal-corner output law of the modified process (pp.8–9).
Sum the actual modified transition law on raw cells, and identify the final
block with its corner, rather than requiring the last raw cell to be that corner. -/
def modifiedTerminalProb (lam : YoungDiagram) (x y : ℕ → ℝ) (c : Cell) : ℝ :=
  ∑ z ∈ lam.cells, (x z.1 * y z.2 / totalWeight lam x y) *
    walkEval (modifiedSuccessors lam) x y lam.card z (fun p =>
      if p.getLast?.map (blockCorner lam) = some c then 1 else 0)

/-- X_k is the sum of row weights, and Y_k the sum of column weights, over
equal-length blocks (p.9, Figure 4 and proof of Theorem 5). The prose on p.9
mistakenly says elements of U for both sums; the example fixes the intended meaning. -/
def blockX (lam : YoungDiagram) (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (lam.colLen 0),
    if lam.rowLen i = lam.rowLen ((rowEnds lam).getD k 0) then x i else 0

def blockY (lam : YoungDiagram) (y : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (lam.rowLen 0),
    if lam.colLen j = lam.colLen ((colEnds lam).getD k 0) then y j else 0

/-- Zero-based rank of an actual corner, from top right to bottom left (p.9). -/
def cornerRank (lam : YoungDiagram) (c : Cell) : ℕ :=
  ((corners lam).filter fun t => t.1 < c.1).card

/-- Corner factor for the c-row staircase in Theorem 5, p.9. -/
def staircaseWeight (c : ℕ) (X Y : ℕ → ℝ) (r s : ℕ) : ℝ :=
  X r * Y s *
    (∏ i ∈ Finset.range r, (1 + X i /
      ((∑ k ∈ Finset.Ico (i + 1) (r + 1), X k) +
        ∑ l ∈ Finset.Ico (s + 1) (c - i), Y l))) *
    ∏ j ∈ Finset.range s, (1 + Y j /
      ((∑ k ∈ Finset.Ico (r + 1) (c - j), X k) +
        ∑ l ∈ Finset.Ico (j + 1) (s + 1), Y l))

/-- Projection-event probability from a deterministic starting cell, equivalent
to conditioning on that positive-probability start (§5, pp.9–10). -/
def projectionProb (lam : YoungDiagram) (x y : ℕ → ℝ) (start : Cell)
    (I J : Finset ℕ) : ℝ :=
  walkEval (successors lam) x y lam.card start (fun p =>
    if p.toFinset.image Prod.fst = I ∧ p.toFinset.image Prod.snd = J then 1 else 0)

/-- Tagged formal labels; row and column labels are distinct regardless of
any later numerical specialization (§2.2, pp.4–5). -/
abbrev Label := Sum ℕ ℕ

/-- Raw arrangement with canonical dummy labels at corners. The predicates
below restrict exactly the labels used in F_lambda and G_lambda (pp.4–5). -/
abbrev Arrangement (lam : YoungDiagram) := Cell × ({z : Cell // z ∈ lam.cells} → Label)

/-- Read an old label, with a fixed dummy outside the occupied diagram (p.5). -/
def oldLabel (lam : YoungDiagram) (a : Arrangement lam) (z : Cell) : Label :=
  if h : z ∈ lam.cells then a.2 ⟨z, h⟩ else Sum.inl 0

/-- Strict-hook admissibility of a tagged label (§2.2, p.4). -/
def StrictLabel (lam : YoungDiagram) (z : Cell) : Label → Prop
  | Sum.inl k => z.1 < k ∧ k < lam.colLen z.2
  | Sum.inr l => z.2 < l ∧ l < lam.rowLen z.1

/-- F_lambda, including the starting-square special labels (§2.2, p.4). -/
def hookLabelInputs (lam : YoungDiagram) : Set (Arrangement lam) :=
  {a | a.1 ∈ lam.cells ∧ ∀ z : {z : Cell // z ∈ lam.cells},
    if z.val ∈ corners lam then a.2 z = Sum.inl 0 else StrictLabel lam z.val (a.2 z)}

/-- G_lambda with the source's special rules on the terminal row and column;
at a corner lambda'_s=r+1 and lambda_r=s+1 in zero-based coordinates (p.4). -/
def hookLabelOutputs (lam : YoungDiagram) : Set (Arrangement lam) :=
  {a | a.1 ∈ corners lam ∧ ∀ z : {z : Cell // z ∈ lam.cells},
    if z.val ∈ corners lam then a.2 z = Sum.inl 0 else
      if z.val.2 = a.1.2 then
        match a.2 z with
        | Sum.inl k => z.val.1 ≤ k ∧ k ≤ a.1.1
        | Sum.inr l => a.1.2 < l ∧ l < lam.rowLen z.val.1
      else if z.val.1 = a.1.1 then
        match a.2 z with
        | Sum.inl k => a.1.1 < k ∧ k < lam.colLen z.val.2
        | Sum.inr l => z.val.2 ≤ l ∧ l ≤ a.1.2
      else StrictLabel lam z.val (a.2 z)}

/-- Arrow encoded by a tagged label (p.5). -/
def arrowTarget (z : Cell) : Label → Cell
  | Sum.inl k => (k, z.2)
  | Sum.inr l => (z.1, l)

/-- Follow the old labels, stopping at the first corner (p.5). Fuel card(lam)
suffices on hookLabelInputs because every strict-hook arrow advances a coordinate. -/
def arrowPath (lam : YoungDiagram) (a : Arrangement lam) : ℕ → Cell → List Cell
  | 0, z => [z]
  | fuel + 1, z => if z ∈ corners lam then [z] else
    z :: arrowPath lam a fuel (arrowTarget z (oldLabel lam a z))

/-- The p.5 rearrangement, evaluated from the old arrangement simultaneously.
Projected visited rows get their own x-label and projected columns their own
y-label. Other walk cells receive the old label from the shaded row/column.
This also handles a walk that starts at a corner without reading a corner label. -/
def rearrangeHookLabels (lam : YoungDiagram) (a : Arrangement lam) : Arrangement lam :=
  let path := arrowPath lam a lam.card a.1
  let c := path.getLast?.getD a.1
  (c, fun z =>
    if z.val ∈ corners lam then Sum.inl 0 else
    if z.val.2 = c.2 ∧ z.val.1 ∈ path.toFinset.image Prod.fst then Sum.inl z.val.1 else
    if z.val.1 = c.1 ∧ z.val.2 ∈ path.toFinset.image Prod.snd then Sum.inr z.val.2 else
    if z.val ∈ path then
      match oldLabel lam a z.val with
      | Sum.inl _ => oldLabel lam a (z.val.1, c.2)
      | Sum.inr _ => oldLabel lam a (c.1, z.val.2)
    else a.2 z)

/-- Sanity: the strict hook has no labels in the empty diagram. -/
example : corners (⊥ : YoungDiagram) = ∅ := by simp [corners]

/-- Sanity: arrow tags retain the intended axis and target. -/
example (i j k : ℕ) : arrowTarget (i, j) (Sum.inl k) = (k, j) := by rfl

/-- Sanity: an already terminal starting cell is evaluated exactly once. -/
example (x y : ℕ → ℝ) (z : Cell) (event : List Cell → ℝ) :
    walkEval (fun _ => ∅) x y 0 z event = event [z] := by
  simp [walkEval]

/-- Sanity: both products in the one-corner q-factor are empty. -/
example (q : ℝ) (X Y : ℕ → ℝ) : kerovPi 1 q X Y 0 = 1 := by
  simp [kerovPi]

/-- Sanity: the empty shape has no one-box oneBoxPredecessors. -/
example : oneBoxPredecessors (⊥ : YoungDiagram) = ∅ := by
  simp [oneBoxPredecessors, YoungDiagram.card]

/-- Sanity: the empty hook product is one. -/
example : hookProduct (⊥ : YoungDiagram) = 1 := by
  simp [hookProduct]

/-- Sanity: zero weights make every strict-hook sum and total weight zero. -/
example (lam : YoungDiagram) (i j : ℕ) :
    strictHook lam (fun _ => (0 : ℚ)) (fun _ => 0) i j = 0 ∧
      totalWeight lam (fun _ => (0 : ℚ)) (fun _ => 0) = 0 := by
  simp [strictHook, totalWeight]

/-- Sanity: the first unused row/column is not a formal variable. -/
example (lam : YoungDiagram) :
    polyX lam (lam.colLen 0) = 0 ∧ polyY lam (lam.rowLen 0) = 0 := by
  simp [polyX, polyY]

/-- Sanity: singleton-corner factors have two empty products. -/
example (lam : YoungDiagram) (x y : ℕ → ℚ) :
    cornerWeight lam x y 0 0 = x 0 * y 0 := by
  simp [cornerWeight]

/-- Sanity: the ordinary hook cannot contain its own starting cell. -/
example (lam : YoungDiagram) (z : Cell) : z ∉ successors lam z := by
  simp [successors]

/-- Sanity: the empty diagram has no modified successors or terminal mass. -/
example (z c : Cell) (x y : ℕ → ℝ) :
    modifiedSuccessors (⊥ : YoungDiagram) z = ∅ ∧
      terminalProb (⊥ : YoungDiagram) (successors ⊥) x y c = 0 := by
  simp [modifiedSuccessors, terminalProb]

/-- Sanity: a vertical transition carries the target row weight. -/
example (x y : ℕ → ℝ) (i j k : ℕ) :
    moveWeight x y (i, j) (k, j) = x k := by
  simp [moveWeight]

/-- Sanity: a one-block staircase has no nontrivial product factors. -/
example (X Y : ℕ → ℝ) : staircaseWeight 1 X Y 0 0 = X 0 * Y 0 := by
  simp [staircaseWeight]

/-- Sanity: a one-term Z and S use the two outside endpoints. -/
example (q : ℝ) (X Y : ℕ → ℝ) :
    kerovZ 1 q X Y = q ^ X 0 ∧
      kerovS 1 q X Y = (q ^ Y 0 - q ^ X 0) * (q ^ X 0 - q ^ Y 1) := by
  simp [kerovZ, kerovS]

/-- Sanity: reading outside the empty diagram is the canonical dummy. -/
example (a : Arrangement ⊥) (z : Cell) : oldLabel ⊥ a z = Sum.inl 0 := by
  simp [oldLabel]

/-- Sanity: the arrow path stops at a corner before reading any label. -/
example (lam : YoungDiagram) (a : Arrangement lam) (z : Cell)
    (hz : z ∈ corners lam) : arrowPath lam a 1 z = [z] := by
  simp [arrowPath, hz]

/-- Sanity: a single modified block outputs its southeast corner even when
its raw starting cell is interior, as on every rectangular diagram. -/
example (lam : YoungDiagram) (z : Cell) (r s : ℕ)
    (hr : rowEnds lam = [r]) (hs : colEnds lam = [s])
    (hrow : z.1 ≤ r) (hcol : z.2 ≤ s) : blockCorner lam z = (r, s) := by
  simp [blockCorner, hr, hs, hrow, hcol]

end QAlgorithms.Papers.Independent.Next46.P26


