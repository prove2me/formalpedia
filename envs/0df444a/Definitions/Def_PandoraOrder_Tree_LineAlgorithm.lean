-- Prove2me | Definitions.Def_PandoraOrder_Tree_LineAlgorithm
-- name    : PandoraOrder_Tree_LineAlgorithm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T21:59:12.421196+00:00
-- url     : https://prove2.me/theorems/4a3da7a4-f86a-4b93-a544-b24df2d21f52
-- title:
--   Exact line dynamic programming and computeThreshold
-- statement:
--   The line program processes suffixes backwards. The empty suffix has value $x$. For a box prefixed to a computed suffix table, it explicitly evaluates
--   $$C(x)=-c+\sum_a p_a\Phi(\max(x,r_a),L).$$
--   The continuation column's knots are the previous column's knots, this box's reward atoms, and zero. Duplicate knots are removed by comparisons. Affine coefficients between consecutive knots are obtained from two evaluations; on the final infinite interval the evaluations are at its left endpoint and one unit farther right.
--
--   The program scans for the first point where $C(x)\le x$, using guarded division to solve an affine crossing inside an interval. It retains the continuation column below that point and uses the identity column from there onward. It records the threshold and repeats for the preceding box. In particular, the root need not be a reward atom: a deterministic reward two with cost one has root one.
--
--   The procedure computeThreshold prefixes its input box to the input list and runs this explicit line program. A missing root or failed division returns failure, rather than a silently chosen threshold. Success, equality with the semantic generalized threshold, and polynomial time and space remain theorem conclusions. Recomputing a suffix table at a tree node retains the descendant annotations rather than replacing them.
--
--   Formalization Note: all expectations are finite weighted sums. No regularity, rationality, separation of atoms, or bound on reward magnitudes is assumed. The piecewise-affine interpolation fills in the off-support values needed by Definition 3 and Appendix C.
-- source:
--   Boodaghians et al., arXiv:2002.06968v2, §3.1, Theorem 5 proof and computeThreshold, p. 8 (PDF p. 8); https://arxiv.org/abs/2002.06968v2

import Definitions.Def_PandoraOrder_Tree_Model
import Definitions.Def_PandoraOrder_Tree_Arithmetic

namespace PandoraOrder.Tree

/-- Explicit weighted sum of the already computed suffix table. -/
noncomputable def continuationTable {n : ℕ} (I : Instance n) (b : Fin n)
    (rows : Table) (x : ℝ) : Calc ℝ := do
  let _ ← readCell (I.size b)
  let atoms ← finCells (I.size b)
  let v ← foldCells (fun total a => do
    let r ← readCell (I.reward b a)
    let p ← readCell ((I.law b).prob a)
    let y ← maximum x r
    let f ← tableEval rows y
    let term ← times p f
    plus total term) 0 atoms
  let c ← readCell (I.cost b)
  minus v c

/-- Knots of a continuation column are the old knots and this box's reward atoms. -/
noncomputable def columnKnots {n : ℕ} (I : Instance n) (b : Fin n)
    (rows : Table) : Calc (List ℝ) := do
  let zero ← consCell 1 (0 : ℝ) []
  let old ← foldCells (fun ks r => do let a ← readCell r.left; insertKnot a ks) zero rows
  let atoms ← finCells (I.size b)
  foldCells (fun ks a => do let r ← readCell (I.reward b a); insertKnot r ks) old atoms

/-- Interpolate each affine interval; the final interval is sampled at a and a+1,
not at an arbitrary truncation of the reward domain. Duplicate knots were removed. -/
noncomputable def continuationRows {n : ℕ} (I : Instance n) (b : Fin n)
    (rows : Table) : List ℝ → Calc Table
  | [] => do charge 1 16; pure []
  | a :: ks => do
      charge 1 16
      let right ← match ks with
        | [] => plus a 1
        | c :: _ => readCell c
      let va ← continuationTable I b rows a
      let vb ← continuationTable I b rows right
      let dy ← minus vb va
      let dx ← minus right a
      let slope ← divide dy dx
      let ma ← times slope a
      let intercept ← minus va ma
      let tail ← continuationRows I b rows ks
      consCell 3 ⟨a, slope, intercept⟩ tail

/-- First zero of max(x,C(x))-x. A zero need not be a reward atom.
Failure is explicit, and successful computation for all source inputs is a theorem. -/
noncomputable def firstRoot : Table → Calc ℝ
  | [] => failure
  | r :: rs => do
      charge 1 16
      let a ← readCell r.left
      let v ← affineEval r a
      if !(← less a v) then pure a else
        let m ← readCell r.slope
        if ← less m 1 then
          let den ← minus 1 m
          let intercept ← readCell r.intercept
          let root ← divide intercept den
          match rs with
          | [] => pure root
          | next :: _ =>
              let right ← readCell next.left
              if !(← less right root) then pure root else firstRoot rs
        else firstRoot rs

/-- After the first root the value column is the identity. No implicit maximization
or unbounded search is used in this table update. -/
noncomputable def stopColumn (z : ℝ) : Table → Calc Table
  | [] => consCell 3 ⟨z, 1, 0⟩ []
  | r :: rs => do
      charge 1 16
      let a ← readCell r.left
      if ← less a z then
        let tail ← stopColumn z rs
        consCell 3 r tail
      else consCell 3 ⟨z, 1, 0⟩ []

abbrev Annotated (n : ℕ) := List (Fin n × ℝ)

/-- Compute all suffix columns backwards; only the current column is read, though
the allocation arena also retains old storage until the run ends. -/
noncomputable def lineProgram {n : ℕ} (I : Instance n) :
    List (Fin n) → Calc (Table × Annotated n)
  | [] => do
      let rows ← consCell 3 (⟨0, 1, 0⟩ : AffineRow) []
      pure (rows, [])
  | b :: L => do
      charge 1 16
      let (old, ann) ← lineProgram I L
      let knots ← columnKnots I b old
      let rows ← continuationRows I b old knots
      let z ← firstRoot rows
      let new ← stopColumn z rows
      let out ← consCell 2 (b, z) ann
      pure (new, out)

/-- Source computeThreshold: recomputing the suffix table is allowed, and is still
polynomial if the line-program bound holds. Descendant thresholds are not overwritten. -/
noncomputable def computeThreshold {n : ℕ} (I : Instance n) (b : Fin n)
    (L : List (Fin n)) : Calc ℝ := do
  let full ← consCell 1 b L
  let (_, ann) ← lineProgram I full
  match ann with
  | [] => failure
  | (_, z) :: _ => readCell z

end PandoraOrder.Tree


