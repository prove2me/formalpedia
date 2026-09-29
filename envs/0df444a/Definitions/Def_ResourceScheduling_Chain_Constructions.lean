-- Prove2me | Definitions.Def_ResourceScheduling_Chain_Constructions
-- name    : ResourceScheduling_Chain_Constructions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:25:04.372996+00:00
-- url     : https://prove2.me/theorems/be2f0ce0-6238-499a-b0bb-5053483be9c9
-- title:
--   The scheduling instances built from a 3-PARTITION instance (proofs of Theorems 4 and 7)
-- statement:
--   Given a 3-PARTITION instance $t, b, a_1,\dots,a_{3t}$, this file builds two scheduling instances.
--
--   **The instance of Theorem 4.** It has $3t$ unit-time jobs, three identical machines, one resource of size $b$, job $J_j$ requiring $a_j$ units of it, and no precedence constraints. When $\sum_j a_j = tb$, a schedule with $C_{\max}\le t$ saturates both the machines and the resource. This is the instance under which the page's "When the machines and resources are all saturated, $P3\mid res1\cdot\cdot, p_j = 1\mid C_{\max}$ is equivalent to the following problem: 3-PARTITION" holds.
--
--   **The instance of Theorem 7.** In the paper's words:
--
--   > Given any instance of this problem, we construct an instance of $P2\mid res111, chain, p_j=1\mid C_{\max}$ in the following way:
--   > – There is a single chain $L$ of $2tb$ jobs:
--   > $L = J'_1 \to J'_2 \to \cdots \to J'_b \to J_1 \to J_2 \to \cdots \to J_b \to J'_{b+1} \to J'_{b+2} \to \cdots \to J'_{2b} \to J_{b+1} \to J_{b+2} \to \cdots \to J_{2b} \to \cdots \to J'_{(t-1)b+1} \to J'_{(t-1)b+2} \to \cdots \to J'_{tb} \to J_{(t-1)b+1} \to J_{(t-1)b+2} \to \cdots \to J_{tb}$.
--   > – For each $j \in S$, there are two chains $K_j$ and $K'_j$, each of $a_j$ jobs:
--   > $K_j = J_{j1} \to J_{j2} \to \cdots \to J_{ja_j}$, $K'_j = J'_{j1} \to J'_{j2} \to \cdots \to J'_{ja_j}$;
--   > moreover, it is required that $K_j$ precedes $K'_j$, i.e., $J_{ja_j} \to J'_{j1}$.
--   > – The primed jobs do require the resource, the unprimed jobs do not.
--
--   There are two identical machines and one resource of size one; a primed job requires one unit and an unprimed job none. The jobs are numbered in the order: the $2tb$ jobs of $L$ along the chain, then for $j = 1,\dots,3t$ the $a_j$ jobs of $K_j$ followed by the $a_j$ jobs of $K'_j$. Along $L$, positions $2ib+1,\dots,(2i+1)b$ are primed and positions $(2i+1)b+1,\dots,(2i+2)b$ unprimed ($i = 0,\dots,t-1$). The arcs join consecutive positions inside $L$ and inside each combined chain $K_j K'_j$ (which contains the arc $J_{ja_j}\to J'_{j1}$). For a valid instance there are $2tb + 2\sum_j a_j = 4tb$ jobs.
--
--   **Formalization Note.** The requirements are the list `chainReqs` in position order; the arcs are generated as pairs of positions from the chain lengths $2tb, 2a_1, \dots, 2a_{3t}$ and converted to job indices (every generated position is below the number of jobs, so the conversion drops nothing). The instances are defined for every 3-PARTITION instance; the theorems about them state the hypotheses they need.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), p. 16, proof of Theorem 4; pp. 18–19, proof of Theorem 7 (construction)

import Mathlib
import Definitions.Def_ResourceScheduling_Chain_Model
import Definitions.Def_ResourceScheduling_Chain_ThreePartition

/-!
# The scheduling instances built from a 3-PARTITION instance

* `p3Instance`: the `P3 | res1··, p_j = 1` instance of the proof of Theorem 4 (p. 16).
* `chainInstance`: the `P2 | res111, chain, p_j = 1` instance of the proof of Theorem 7
  (pp. 18–19).
-/

namespace ResourceScheduling.Chain

/-- The arcs of consecutive chains of the given lengths laid out one after another from
position `off`: a chain of length `len` starting at `off` has arcs `(off + c, off + c + 1)` for
`c + 1 < len`. -/
def chainArcsFrom : List ℕ → ℕ → List (ℕ × ℕ)
  | [], _ => []
  | len :: rest, off =>
      (List.range (len - 1)).map (fun c => (off + c, off + c + 1)) ++ chainArcsFrom rest (off + len)

/-- A pair of positions as a pair of job indices in `Fin n`, when both are below `n`. -/
def toFinArc (n : ℕ) (e : ℕ × ℕ) : Option (Fin n × Fin n) :=
  if h : e.1 < n ∧ e.2 < n then some (⟨e.1, h.1⟩, ⟨e.2, h.2⟩) else none

namespace ThreePartition

variable (P : ThreePartition)

/-- The instance of the proof of Theorem 4: `3t` unit jobs, three machines, one resource of size
`b`, job `j` requiring `a_j`, and no precedence constraints. -/
def p3Instance : Instance where
  n := 3 * P.t
  m := 3
  l := 1
  s := fun _ => P.b
  r := fun _ j => P.a j
  arcs := []

/-- Requirements along the chain `L`: `2t` blocks of `b` jobs, the even-numbered blocks
(`J'_{ib+1}, …, J'_{(i+1)b}`) primed (requirement 1), the odd-numbered blocks
(`J_{ib+1}, …, J_{(i+1)b}`) unprimed (requirement 0). -/
def chainLReqs : List ℕ :=
  (List.range (2 * P.t)).flatMap fun k => List.replicate P.b (if k % 2 = 0 then 1 else 0)

/-- Requirements along the chains `K_j K'_j` for `j = 0, …, 3t − 1`: `a_j` unprimed jobs followed
by `a_j` primed jobs. -/
def chainKReqs : List ℕ :=
  (List.ofFn fun j => List.replicate (P.a j) 0 ++ List.replicate (P.a j) 1).flatten

/-- Requirements of all jobs, in position order: the chain `L`, then `K_0 K'_0`, `K_1 K'_1`, …. -/
def chainReqs : List ℕ := P.chainLReqs ++ P.chainKReqs

/-- The lengths of the chains in position order: `2tb` for `L`, then `2a_j` for `K_j K'_j`. -/
def chainLengths : List ℕ := (2 * P.t * P.b) :: List.ofFn fun j => 2 * P.a j

/-- The instance of the proof of Theorem 7: two machines, one resource of size one, primed jobs
requiring it and unprimed jobs not, precedence arcs along the chain `L` and along each chain
`K_j → K'_j`. -/
def chainInstance : Instance where
  n := P.chainReqs.length
  m := 2
  l := 1
  s := fun _ => 1
  r := fun _ j => P.chainReqs.get j
  arcs := (chainArcsFrom P.chainLengths 0).filterMap (toFinArc P.chainReqs.length)

end ThreePartition

end ResourceScheduling.Chain


