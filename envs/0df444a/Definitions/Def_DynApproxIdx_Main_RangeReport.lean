-- Prove2me | Definitions.Def_DynApproxIdx_Main_RangeReport
-- name    : DynApproxIdx_Main_RangeReport
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:51:59.408406+00:00
-- url     : https://prove2.me/theorems/6cda5ef4-2fba-45da-92da-7a9c10578f47
-- title:
--   Orthogonal range reporting under deletions: the protocol of Fact 8.3
-- statement:
--   The input is a list of $n$ points $(x_i,y_i)$ in the plane, each with a value $v_i$, identified by its index $i\in[0..n)$; the preprocessing receives the words $n,x_0,y_0,v_0,\dots,x_{n-1},y_{n-1},v_{n-1}$ (operation $0$). The operations are
--   - $\mathrm{delete}(i)$, words $0,i$, valid when point $i$ is still present;
--   - $\mathrm{report}(a,b,c,d)$, words $1,a,b,c,d$: report the present points in the axis-parallel rectangle $[a,b]\times[c,d]$.
--
--   A report is answered correctly when it writes the identifier of every present point $(x_i,y_i)$ with $a\le x_i\le b$ and $c\le y_i\le d$, each exactly once, in any order. The word size is measured against $\lceil\log_2(\sigma_{\max}+3)\rceil$, where $\sigma_{\max}$ is the largest input or operation word. Times are those of the online run (`Run`).
--
--   This is the setting of Fact 8.3, the range-reporting structure behind the paper's dynamic $k$-errata trees.
--
--   **Formalization Note.** Coordinates and values are natural numbers (words of the machine); a reported identifier gives the point's value. Deletions may write anything.
-- source:
--   Charalampopoulos, Ellert, Radoszewski, Dynamic Approximate Text Indexing, STOC 2027 submission (manuscript sha256 7f902057…), Fact 8.3, p. 44 (PDF 46)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynApproxIdx_Main_Run

namespace DynApproxIdx.Main

/-! # Orthogonal range reporting under deletions (Fact 8.3)

Charalampopoulos, Ellert, Radoszewski, *Dynamic Approximate Text Indexing*, STOC 2027 submission
(manuscript sha256 7f902057…): Fact 8.3, p. 44 (PDF 46).

**Formalization Note.**
* The input is a list of `n` points `(x_i, y_i)` with values `v_i` (all natural numbers),
  identified by their index `i ∈ [0..n)`; it is delivered as the words `n, x_0, y_0, v_0, …`
  (operation `0`, the preprocessing).
* An operation is `delete i` (words `0, i`; valid when point `i` is still present) or
  `report a b c d` (words `1, a, b, c, d`): report the remaining points with `a ≤ x ≤ b` and
  `c ≤ y ≤ d`. The answer is the list of their identifiers, each exactly once, in any order (a
  point's value is read off its identifier). Deletions may write anything.
* The word size must be at least a constant times `⌈log₂(σ_max + 3)⌉`, where `σ_max` is the largest
  input or operation word. -/

/-- An operation on the point set. -/
inductive RROp where
  /-- delete point `i` -/
  | del (i : ℕ)
  /-- report the remaining points in `[a..b] × [c..d]` -/
  | report (a b c d : ℕ)

/-- The words of an operation. -/
def RROp.words : RROp → List ℕ
  | .del i => [0, i]
  | .report a b c d => [1, a, b, c, d]

/-- The set of present identifiers after an operation. -/
def RROp.apply : RROp → Set ℕ → Set ℕ
  | .del i, S => S \ {i}
  | .report _ _ _ _, S => S

/-- An operation is valid for the present set `S`: a deleted point is present. -/
def RROp.Valid : RROp → Set ℕ → Prop
  | .del i, S => i ∈ S
  | .report _ _ _ _, _ => True

/-- Every operation is valid for the present set it meets, starting from `S`. -/
def RRValidFrom : Set ℕ → List RROp → Prop
  | _, [] => True
  | S, o :: ops => o.Valid S ∧ RRValidFrom (o.apply S) ops

/-- The identifiers present after the first `j` operations, starting from all of `[0..n)`. -/
def presentAt (n : ℕ) (ops : List RROp) (j : ℕ) : Set ℕ :=
  (ops.take j).foldl (fun S o => o.apply S) {i | i < n}

/-- The preprocessing words `n, x_0, y_0, v_0, …, x_{n−1}, y_{n−1}, v_{n−1}`. -/
def pointWords (pts : List (ℕ × ℕ × ℕ)) : List ℕ :=
  pts.length :: pts.flatMap fun p => [p.1, p.2.1, p.2.2]

/-- The identifiers of the present points (set `S`) in the rectangle `[a..b] × [c..d]`. -/
def inRect (pts : List (ℕ × ℕ × ℕ)) (S : Set ℕ) (a b c d : ℕ) : Set ℕ :=
  {i | i ∈ S ∧ ∃ p, pts[i]? = some p ∧ a ≤ p.1 ∧ p.1 ≤ b ∧ c ≤ p.2.1 ∧ p.2.1 ≤ d}

/-- The word-size unit `⌈log₂(σ_max + 3)⌉`, `σ_max` the largest input or operation word. -/
def rrWidth (pts : List (ℕ × ℕ × ℕ)) (ops : List RROp) : ℕ :=
  Nat.clog 2 ((pointWords pts ++ ops.flatMap RROp.words).foldl max 0 + 3)

end DynApproxIdx.Main


