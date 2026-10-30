-- Prove2me | Definitions.Def_LSWNewArcAudit_NewArc_RepresentedInput
-- name    : LSWNewArcAudit_NewArc_RepresentedInput
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T13:42:25.992877+00:00
-- url     : https://prove2.me/theorems/2baa4ee1-39c0-4448-b0ae-0d7bfe4d4570
-- title:
--   Supplied consistent BFS arrays, defining permutations and the RAM input layout
-- statement:
--   Let $V=\{0,\ldots,n-1\}$ and let $m$ be the number of supplied bases. The input consists of an adjacency matrix, a specified vertex $p$, real weights $\lambda_k$, explicit vectors $y^{(k)}\in\mathbb R^V$, and their defining permutations. A permutation is a position map, so $j$ precedes $i$ exactly when its position is smaller. The source promise is that these are consistent defining permutations and
--
--   $$\lambda_k\ge0,\qquad\sum_k\lambda_k=1,\qquad y^{(k)}_j=f(P_{k,j}\cup\{j\})-f(P_{k,j}),$$
--
--   where $P_{k,j}$ is the set of elements preceding $j$ in permutation $k$. The specified vector is $y_j=\sum_k\lambda_k y^{(k)}_j$.
--
--   The integer input tape holds $n,m,p$ in cells $0,1,2$, then the $n^2$ adjacency bits in row order, then $mn$ permutation-position entries in basis order. The real tape holds the $m$ weights followed by the $mn$ supplied BFS entries. Unused and negative cells are zero. The machine reads one cell per charged load; the representation exposes no inverse permutation, combined vector, descendant set, upper marginal, minimizer, or output advice. The defining permutations are supplied even when a vector has several such permutations.
--
--   These are data and specification definitions. Submodularity, normalization, acyclicity, support size, mixed-sign nondegeneracy and the trigger are hypotheses of the goal, not structure fields. No correctness or cost assertion is an input promise.
-- source:
--   Lee, Sidford, Wong, A Faster Cutting Plane Method and its Implications for Combinatorial and Convex Optimization, arXiv:1508.04874v2 (5 Nov 2015), https://arxiv.org/pdf/1508.04874v2, §13.1 p. 74; §13.3 Theorem 62 p. 76; §15.2.1 Definition 74 p. 82; §15.2.2 Lemma 79 pp. 84–86; every page is both printed and PDF.

import Mathlib
import Definitions.Def_LSWCuttingPlane_SFMArcs_Setting
import Definitions.Def_LSWNewArcAudit_NewArc_OracleRAM

namespace LSWNewArcAudit.NewArc

open LSWCuttingPlane.SFMArcs

/-! Lee--Sidford--Wong, arXiv:1508.04874v2, §13.1 p. 74, Theorem 62
p. 76, Definition 74 p. 82, Lemma 79 pp. 84--86. Supplied BFS coordinates
and their defining permutations are input data, not oracle preprocessing. -/

/-- Source data only; no correctness, cost or output property is a field.
A permutation is a position map: j precedes i iff order k j < order k i.
The machine sees only its explicit n position entries, never its inverse or proofs. -/
structure ArcInput (n m : ℕ) where
  graph : Fin n → Fin n → Bool
  point : Fin n
  weight : Fin m → ℝ
  basis : Fin m → Fin n → ℝ
  order : Fin m → Equiv.Perm (Fin n)

def inputArcs {n m : ℕ} (I : ArcInput n m) (i j : Fin n) : Prop :=
  I.graph i j = true

/-- Only the source's supplied-BFS and convex-combination promise. No conclusion
of the new-arc proof or algorithm invariant is assumed. -/
def RepresentedCombination {n m : ℕ} (f : Finset (Fin n) → ℤ)
    (I : ArcInput n m) : Prop :=
  IsConsistentComb (inputArcs I) I.weight I.order ∧
  ∀ k j, I.basis k j = bfs f (I.order k) j

/-- Specification only: the weighted vector. Forming it is not a RAM primitive. -/
noncomputable def inputVector {n m : ℕ} (I : ArcInput n m) (j : Fin n) : ℝ :=
  ∑ k, I.weight k * I.basis k j

/-- Integer input cells. Addresses 0,1,2 hold n,m,p. Next come the n² graph
bits (row-major), then mn permutation positions (basis-major).
Each machine load reads one cell; the mathematical encoding is not a machine
instruction, preprocessing computation, or access to the oracle. There is no
stored descendant set, combined vector, maximum, upper(p), minimizer or valid q. -/
def inputIntegerCell {n m : ℕ} (I : ArcInput n m) (address : ℤ) : ℤ := by
  classical
  exact if address = 0 then n else if address = 1 then m else
    if address = 2 then I.point.val else
    if address < 3 then 0 else
    let a := (address - 3).toNat
    if h : a < n * n then
      if hij : a / n < n ∧ a % n < n then
        if I.graph ⟨a / n, hij.1⟩ ⟨a % n, hij.2⟩ then 1 else 0
      else 0
    else
      let b := a - n * n
      if h : b < m * n then
        if hkj : b / n < m ∧ b % n < n then
          (I.order ⟨b / n, hkj.1⟩ ⟨b % n, hkj.2⟩).val
        else 0
      else 0

/-- Real input cells: m weights followed by mn supplied BFS coordinates
(basis-major). Negative and all unused addresses in both tapes are zero. -/
noncomputable def inputRealCell {n m : ℕ} (I : ArcInput n m) (address : ℤ) : ℝ := by
  classical
  exact if address < 0 then 0 else
    let a := address.toNat
    if h : a < m then I.weight ⟨a, h⟩ else
      let b := a - m
      if h : b < m * n then
        if hkj : b / n < m ∧ b % n < n then
          I.basis ⟨b / n, hkj.1⟩ ⟨b % n, hkj.2⟩
        else 0
      else 0

/-- A representation only: machine access to these cells is charged by load
instructions. Encoding exposes no inverse permutation or computed aggregate. -/
noncomputable def inputMemory {n m : ℕ} (I : ArcInput n m) : RAMInput :=
  ⟨inputIntegerCell I, inputRealCell I⟩

end LSWNewArcAudit.NewArc


