-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P91
-- name    : QAlgorithms_Papers_Independent_Intake100_P91
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T11:08:51.857435+00:00
-- url     : https://prove2.me/theorems/0c7f417e-44e7-4a6b-ac3b-23fce29d35e2
-- title:
--   Definitions for A Multigraph Approach for Performing the Quantum Schur Transform
-- statement:
--   The objects the formalized statements of *A Multigraph Approach for Performing the Quantum Schur Transform* (arXiv:2204.10694) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `WeylTableau`: Standard Weyl tableaux, PDF pp.6-7: source letter j is Fin value j-1. For d=2 these values are the source's qubit letters 0 and 1.
--   - `ShapedYoungTableau`: Standard Young tableaux of a fixed shape, PDF pp.3,5. Reuse the frozen label-to-box tableau: Fin value i denotes source label i+1, and every prefix is a lower ideal. Only the endpoint shape is restricted here; tableau standardness is reused unchanged.
--   - `ShapePath`: A path of SHAPES from the unique empty diagram to lambda, PDF p.8, (13). Consecutive sizes differ by one, so cell inclusion adds exactly one box.
--   - `youngPrefixCells`: The occupied cells of the first k Young labels, PDF pp.3,5. The canonical path is computed from these exact prefixes.
--   - `IsYoungPath`: The path associated to a Young tableau keeps exactly its first i boxes, PDF pp.5,8. This pins the bijection, rather than just equating cardinalities.
--   - `SchurLabels`: Triples with the paper's ordering: shape, Weyl tableau, Young tableau (PDF p.7). At level zero all three components have exactly one possibility.
--   - `GraphLabels`: A Weyl ENDPOINT paired with a Young shape path, PDF pp.8,11. This deliberately does not count individual paths of Weyl vertices.
--   - `LabelsCorrespond`: The simultaneous labelling preserves the actual Weyl endpoint and assigns the Young tableau its own prefix path, PDF pp.8,11. HEq only transports the Weyl tableau across the equality of its shape, without changing any entry.
--   - `tableauGT`: The source GT entry m_(i,j), PDF pp.6-7: count row-i boxes with source letter at most j. Indices i,j are one-based; the empty subalphabet is j=0.
--   - `GTStep`: Exact GT addition (16), PDF p.11. Starting at the inserted symbol k, one entry tau(j) increases in each row j; all rows below k stay fixed. This allows rearrangement of entries in a Weyl tableau, not just cell deletion.
--   - `WeylEdge`: The graph edge of PDF pp.8,11, with addition/removal pinned to (16).
--   - `HasWeylLift`: A multipath label has at least one compatible Weyl-vertex history. All histories are retained by the predicate; none is selected as a basis label.
--   - `partialHook`: Lower-pattern partial hook p_(i,j)=m_(i,j)+j-i, PDF p.11 and (32), p.18. All differences are in the reals, with no truncated natural subtraction.
--   - `comparisonSign`: Comparison sign in (17), PDF p.11. Equality has sign +1, as fixed by Appendix A, Rule 1b, p.18; Lean's sign(0) would give the wrong amplitude.
--   - `louck`: Louck's independent product (17) times (18), PDF p.11. The original PDF has an absolute value around EACH quotient under a square root. Both products use the lower pattern. Empty first product (k=d) and second factor (k=1) are exactly 1. Only valid GT edges are used in the statements below.
--   - `qubitGT`: A two-level GT array with top row (r,s) and lower entry a (PDF pp.12-13). All other entries are padding and are never used by the d=2 product.
--   - `QubitPattern`: Interlacing for a qubit GT array, PDF (5), p.6. This also forces r≥s.
--   - `QubitEdge`: All qubit graph edges, using (16), rather than content change alone. The two endpoint arrays must both interlace (PDF pp.11-13).
--   - `qubitLouck`: The d=2 specialization of the independent product, not a Pattern Rule. On a valid edge b=a inserts letter 1 (k=2), while b=a+1 inserts 0 (k=1). The changed top-row entry is read from the two shapes (PDF pp.11,18-20).
--   - `patternAmplitude`: The coefficient obtained from the four Pattern Rules: remove all shared full columns, then use Rule 1 or Rule 2. This independent short expression is compared to louck, never used to define it (PDF pp.12-13).
-- source:
--   A Multigraph Approach for Performing the Quantum Schur Transform, arXiv:2204.10694v1, https://arxiv.org/abs/2204.10694v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P91

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Standard Weyl tableaux, PDF pp.6-7: source letter j is Fin value j-1.
For d=2 these values are the source's qubit letters 0 and 1. -/
def WeylTableau {d n : ℕ} (lambda : QAlgorithms.Schur.Partition d n) :=
  {t : lambda.val.cells → Fin d // QAlgorithms.Schur.IsSemistandardFilling lambda t}

/-- Standard Young tableaux of a fixed shape, PDF pp.3,5. Reuse the frozen
label-to-box tableau: Fin value i denotes source label i+1, and every prefix
is a lower ideal. Only the endpoint shape is restricted here; tableau
standardness is reused unchanged. -/
abbrev ShapedYoungTableau {d n : ℕ} (lambda : QAlgorithms.Schur.Partition d n) :=
  {y : QAlgorithms.Papers.Independent.Renew46.P26.YoungTableau n //
    QAlgorithms.Papers.Independent.Renew46.P26.tableauShape y = lambda.val}

/-- A path of SHAPES from the unique empty diagram to lambda, PDF p.8, (13).
Consecutive sizes differ by one, so cell inclusion adds exactly one box. -/
def ShapePath {d n : ℕ} (lambda : QAlgorithms.Schur.Partition d n) :=
  {p : (i : Fin (n+1)) → QAlgorithms.Schur.Partition d i.val //
    (∀ i : Fin n, (p i.castSucc).val.cells ⊆ (p i.succ).val.cells) ∧
    (p (Fin.last n)).val = lambda.val}

/-- The occupied cells of the first k Young labels, PDF pp.3,5.
The canonical path is computed from these exact prefixes. -/
def youngPrefixCells {d n : ℕ} {lambda : QAlgorithms.Schur.Partition d n}
    (y : ShapedYoungTableau lambda) (k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.univ.filter fun i : Fin n => i.val < k).image y.val.val

/-- The path associated to a Young tableau keeps exactly its first i boxes,
PDF pp.5,8. This pins the bijection, rather than just equating cardinalities. -/
def IsYoungPath {d n : ℕ} {lambda : QAlgorithms.Schur.Partition d n}
    (y : ShapedYoungTableau lambda) (p : ShapePath lambda) : Prop :=
  ∀ i : Fin (n+1), (p.val i).val.cells = youngPrefixCells y i.val

/-- Triples with the paper's ordering: shape, Weyl tableau, Young tableau
(PDF p.7). At level zero all three components have exactly one possibility. -/
abbrev SchurLabels (d n : ℕ) :=
  (lambda : QAlgorithms.Schur.Partition d n) × (WeylTableau lambda × ShapedYoungTableau lambda)

/-- A Weyl ENDPOINT paired with a Young shape path, PDF pp.8,11.
This deliberately does not count individual paths of Weyl vertices. -/
abbrev GraphLabels (d n : ℕ) :=
  (lambda : QAlgorithms.Schur.Partition d n) × (WeylTableau lambda × ShapePath lambda)

/-- The simultaneous labelling preserves the actual Weyl endpoint and assigns
the Young tableau its own prefix path, PDF pp.8,11. HEq only transports the
Weyl tableau across the equality of its shape, without changing any entry. -/
def LabelsCorrespond {d n : ℕ} (a : SchurLabels d n) (b : GraphLabels d n) : Prop :=
  a.1 = b.1 ∧ HEq a.2.1 b.2.1 ∧
    ∀ i : Fin (n+1), (b.2.2.val i).val.cells = youngPrefixCells a.2.2 i.val

/-- The source GT entry m_(i,j), PDF pp.6-7: count row-i boxes with source
letter at most j. Indices i,j are one-based; the empty subalphabet is j=0. -/
def tableauGT {d n : ℕ} {lambda : QAlgorithms.Schur.Partition d n}
    (t : WeylTableau lambda) (i j : ℕ) : ℕ :=
  (Finset.univ.filter fun c : lambda.val.cells =>
    c.val.1 + 1 = i ∧ (t.val c).val < j).card

/-- Exact GT addition (16), PDF p.11. Starting at the inserted symbol k,
one entry tau(j) increases in each row j; all rows below k stay fixed.
This allows rearrangement of entries in a Weyl tableau, not just cell deletion. -/
def GTStep (d : ℕ) (lower upper : ℕ → ℕ → ℕ) (k : ℕ) (tau : ℕ → ℕ) : Prop :=
  1 ≤ k ∧ k ≤ d ∧ ∀ j, 1 ≤ j → j ≤ d →
    (j < k → ∀ i, 1 ≤ i → i ≤ j → upper i j = lower i j) ∧
    (k ≤ j → 1 ≤ tau j ∧ tau j ≤ j ∧ ∀ i, 1 ≤ i → i ≤ j →
      upper i j = lower i j + if i = tau j then 1 else 0)

/-- The graph edge of PDF pp.8,11, with addition/removal pinned to (16). -/
def WeylEdge {d m n : ℕ} {mu : QAlgorithms.Schur.Partition d m}
    {lambda : QAlgorithms.Schur.Partition d n}
    (t : WeylTableau mu) (u : WeylTableau lambda) : Prop :=
  n = m+1 ∧ mu.val.cells ⊆ lambda.val.cells ∧
    ∃ k tau, GTStep d (tableauGT t) (tableauGT u) k tau

/-- A multipath label has at least one compatible Weyl-vertex history.
All histories are retained by the predicate; none is selected as a basis label. -/
def HasWeylLift {d n : ℕ} (label : GraphLabels d n) : Prop :=
  ∃ v : (i : Fin (n+1)) →
      (lambda : QAlgorithms.Schur.Partition d i.val) × WeylTableau lambda,
    (∀ i, (v i).1.val = (label.2.2.val i).val) ∧
    v (Fin.last n) = ⟨label.1, label.2.1⟩ ∧
    ∀ i : Fin n, WeylEdge (v i.castSucc).2 (v i.succ).2

/-- Empty Young prefix, including the unique vacuum tableau. -/
example {d n : ℕ} {lambda : QAlgorithms.Schur.Partition d n}
    (y : ShapedYoungTableau lambda) : youngPrefixCells y 0 = ∅ := by
  simp [youngPrefixCells]

/-- The zero-letter subtableau has no occupied cells. -/
example {d n : ℕ} {lambda : QAlgorithms.Schur.Partition d n}
    (t : WeylTableau lambda) (i : ℕ) : tableauGT t i 0 = 0 := by
  simp [tableauGT]

/-- The path and tableau types are actually finite; Nat.card has no infinite
fallback on these concrete labels. -/
example (d n : ℕ) : Finite (GraphLabels d n) := by
  unfold GraphLabels WeylTableau ShapePath
  infer_instance

/-- Lower-pattern partial hook p_(i,j)=m_(i,j)+j-i, PDF p.11 and (32), p.18.
All differences are in the reals, with no truncated natural subtraction. -/
def partialHook (m : ℕ → ℕ → ℕ) (i j : ℕ) : ℝ :=
  (m i j : ℝ) + (j : ℝ) - (i : ℝ)

/-- Comparison sign in (17), PDF p.11. Equality has sign +1, as fixed by
Appendix A, Rule 1b, p.18; Lean's sign(0) would give the wrong amplitude. -/
def comparisonSign (a b : ℕ) : ℝ := if b ≤ a then 1 else -1

/-- Louck's independent product (17) times (18), PDF p.11. The original PDF
has an absolute value around EACH quotient under a square root. Both products
use the lower pattern. Empty first product (k=d) and second factor (k=1)
are exactly 1. Only valid GT edges are used in the statements below. -/
def louck (d : ℕ) (m : ℕ → ℕ → ℕ) (k : ℕ) (tau : ℕ → ℕ) : ℝ :=
  Finset.prod (Finset.Icc (k+1) d) (fun j =>
    comparisonSign (tau (j-1)) (tau j) *
    Real.sqrt (abs (
      ((Finset.prod ((Finset.Icc 1 (j-1)).erase (tau (j-1))) (fun i =>
          partialHook m (tau j) j - partialHook m i (j-1))) *
       (Finset.prod ((Finset.Icc 1 j).erase (tau j)) (fun i =>
          partialHook m (tau (j-1)) (j-1) - partialHook m i j + 1))) /
      ((Finset.prod ((Finset.Icc 1 j).erase (tau j)) (fun i =>
          partialHook m (tau j) j - partialHook m i j)) *
       (Finset.prod ((Finset.Icc 1 (j-1)).erase (tau (j-1))) (fun i =>
          partialHook m (tau (j-1)) (j-1) - partialHook m i (j-1) + 1)))))) *
  (if k = 1 then 1 else
    Real.sqrt (abs (
      (Finset.prod (Finset.Icc 1 (k-1)) (fun i =>
        partialHook m (tau k) k - partialHook m i (k-1))) /
      (Finset.prod ((Finset.Icc 1 k).erase (tau k)) (fun i =>
        partialHook m (tau k) k - partialHook m i k)))))

/-- A two-level GT array with top row (r,s) and lower entry a (PDF pp.12-13).
All other entries are padding and are never used by the d=2 product. -/
def qubitGT (r s a : ℕ) (i j : ℕ) : ℕ :=
  if j = 1 ∧ i = 1 then a
  else if j = 2 ∧ i = 1 then r
  else if j = 2 ∧ i = 2 then s
  else 0

/-- Interlacing for a qubit GT array, PDF (5), p.6. This also forces r≥s. -/
def QubitPattern (r s a : ℕ) : Prop := s ≤ a ∧ a ≤ r

/-- All qubit graph edges, using (16), rather than content change alone.
The two endpoint arrays must both interlace (PDF pp.11-13). -/
def QubitEdge (r s a R S b : ℕ) : Prop :=
  QubitPattern r s a ∧ QubitPattern R S b ∧
    ∃ k tau, GTStep 2 (qubitGT r s a) (qubitGT R S b) k tau

/-- The d=2 specialization of the independent product, not a Pattern Rule.
On a valid edge b=a inserts letter 1 (k=2), while b=a+1 inserts 0 (k=1).
The changed top-row entry is read from the two shapes (PDF pp.11,18-20). -/
def qubitLouck (r s a R S b : ℕ) : ℝ :=
  louck 2 (qubitGT r s a) (if b = a then 2 else 1)
    (fun j => if j = 1 then 1 else if R = r+1 ∧ S = s then 1 else 2)

/-- The coefficient obtained from the four Pattern Rules: remove all shared
full columns, then use Rule 1 or Rule 2. This independent short expression
is compared to louck, never used to define it (PDF pp.12-13). -/
def patternAmplitude (r s a R S b : ℕ) : ℝ :=
  if S = s then
    if a = b then Real.sqrt (((R : ℝ) - b) / ((R : ℝ) - s))
    else Real.sqrt (((b : ℝ) - s) / ((R : ℝ) - s))
  else
    if a = b then Real.sqrt (((b : ℝ) - S + 1) / ((R : ℝ) - S + 2))
    else -Real.sqrt (((R : ℝ) - b + 1) / ((R : ℝ) - S + 2))

/-- Equality in the comparison sign is positive (Appendix A, Rule 1b). -/
example : comparisonSign 1 1 = 1 := by norm_num [comparisonSign]

/-- With a one-letter alphabet, both coefficient factors are empty/one. -/
example (m : ℕ → ℕ → ℕ) (tau : ℕ → ℕ) : louck 1 m 1 tau = 1 := by
  norm_num [louck]

/-- The empty two-row pattern interlaces; no positive tensor degree is required. -/
example : QubitPattern 0 0 0 := by norm_num [QubitPattern]

/-- Padding, top row and zero count of a two-row array are independent entries. -/
example (r s a : ℕ) :
    qubitGT r s a 1 1 = a ∧ qubitGT r s a 1 2 = r ∧ qubitGT r s a 2 2 = s := by
  simp [qubitGT]

end QAlgorithms.Papers.Independent.Intake100.P91


