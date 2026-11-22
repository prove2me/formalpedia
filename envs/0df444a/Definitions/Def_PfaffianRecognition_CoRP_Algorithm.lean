-- Prove2me | Definitions.Def_PfaffianRecognition_CoRP_Algorithm
-- name    : PfaffianRecognition_CoRP_Algorithm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-22T21:17:57.877728+00:00
-- url     : https://prove2.me/theorems/8535d46d-c9a8-4020-b682-f53a0add8b79
-- title:
--   Randomized Pfaffian recognition algorithm on bit strings
-- statement:
--   The randomized recognition algorithm $\mathcal A(\rho,w)$ on a random bit string $\rho$ and a graph encoding $w$ (unary vertex count $N$, a $0$, then the $N^2$ row-major adjacency bits).
--
--   Edges are pairs $(i,j)$ with $i<j$. A vector $d\in\mathbb F_2^{E}$ ($d_e=1$ meaning that $e$ points from its larger to its smaller endpoint) together with a bit $s$ is *consistent* with a perfect matching $M$ when
--   $$\sum_{e\in M} d_e + s = \operatorname{cr}(M)\quad\text{in }\mathbb F_2 ,$$
--   where $\operatorname{cr}(M)$ counts crossing pairs. By Lemma 2.1 of the source, $G$ is Pfaffian iff some $(d,s)$ is consistent with every perfect matching. The algorithm:
--
--   1. Rejects strings that do not encode a simple graph.
--   2. Runs $|E|+3$ rounds. Each round solves the collected equations over $\mathbb F_2$; inconsistency means rejection. Otherwise it takes a solution $(d,s)$, reads a point $\alpha\in K_m^{E}$ from fresh bits of $\rho$ (with $m=3^{\lceil\log_2(N+1)\rceil}$), and evaluates
--   $$Q(\beta)=s\,\Phi(\beta)+\sum_{d_e=1}\Phi(\beta^{(e)})+\sum_{\{e,f\}\text{ crossing}}\Phi(\beta^{(e,f)}),$$
--   where $\Phi(\beta)$ is the determinant of the symmetric $\beta$-weighted adjacency matrix and $\beta^{(S)}$ zeroes every edge that meets $S$ without belonging to $S$. If $Q(\alpha)=0$ the algorithm accepts.
--   3. Otherwise a greedy search extends a partial matching $S$ at its smallest uncovered vertex by the first edge keeping $Q(\alpha^{(S)})\ne0$; the result is verified to be a perfect matching inconsistent with $(d,s)$ and its equation is added. A failed verification means acceptance, as does completing all rounds.
--
--   This is the source's orientation test (Theorem 3.2 with the minor expression of Lemma 2.3) with the reference parity treated as an unknown, iterated with exact linear algebra in place of the orientation constructor of Lemma 3.3.
--
--   **Formalization Note** In characteristic two the skew-adjacency matrix coincides with the symmetric weighted adjacency matrix, and $\Phi(\beta^{(S)})$ replaces the principal minors of the source by kill substitutions.
-- source:
--   Priyanshu Pant, Ranveer Singh, Pfaffian Recognition is in coRP, STOC 2027 submission #858 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/858.pdf, Theorem 1.1 (p. 3), §2 Lemmas 2.1, 2.3 and Proposition 2.2 (pp. 5-6), §3.1 Theorem 3.2 (p. 7), §3.2 (p. 8)

import Mathlib
import Definitions.Def_PfaffianRecognition_CoRP_GF2Bits

/-!
The randomized Pfaffian-graph recognition algorithm, written with plain list operations.

Input: a random bit string `ρ` and a graph encoding `w` (unary vertex count `N`, a `0`, then the
`N²` row-major adjacency bits). Edges are pairs `(i, j)` with `i < j`. An orientation is described by
`d`, one bit per edge (`true` = the edge points from its larger to its smaller endpoint), and a sign
bit `s`; `(d, s)` is consistent with a perfect matching `M` when `Σ_{e∈M} d_e + s = cr(M)` in `𝔽₂`,
`cr(M)` the number of crossing pairs of `M`. The graph is Pfaffian iff some `(d, s)` is consistent
with every perfect matching.

Each round solves the collected equations over `𝔽₂` (inconsistency ⇒ reject), samples a point
`α ∈ GF(2^{2m})^E` from the random string, and evaluates
`Q(β) = s·Φ(β) + Σ_{d_e = 1} Φ(β^{(e)}) + Σ_{crossing e,f} Φ(β^{(e,f)})`, where `Φ(β)` is the
determinant of the symmetric edge-weighted adjacency matrix and `β^{(S)}` zeroes every edge that meets
`S` without belonging to `S`. If `Q(α) = 0` the algorithm accepts; otherwise a greedy search extracts a
perfect matching inconsistent with `(d, s)`, which is verified and added as a new equation.
-/

namespace PfaffianRecognition.CoRP

/-! ### Parsing -/

/-- Number of leading `true` bits (the unary vertex count). -/
def hdrN (w : List Bool) : ℕ := w.findIdx (fun b => !b)

/-- The adjacency bits following the header and its terminating `false`. -/
def encBody (w : List Bool) : List Bool := w.drop (hdrN w + 1)

/-- The adjacency bit of `(i, j)` (row-major). -/
def adjBit (w : List Bool) (i j : ℕ) : Bool := (encBody w).getD (i * hdrN w + j) false

/-- All index pairs `(i, j)` with `i, j < N`, row-major. -/
def idxPairs (N : ℕ) : List (ℕ × ℕ) :=
  (List.range N).flatMap (fun i => (List.range N).map (fun j => (i, j)))

/-- `w` encodes a simple graph: a terminated header, exactly `N²` adjacency bits, a symmetric
adjacency relation and no loops. -/
def validEnc (w : List Bool) : Bool :=
  decide (hdrN w < w.length) && (encBody w).length == hdrN w * hdrN w &&
    (idxPairs (hdrN w)).all (fun ij => adjBit w ij.1 ij.2 == adjBit w ij.2 ij.1 &&
      !(ij.1 == ij.2 && adjBit w ij.1 ij.2))

/-- The edges `(i, j)`, `i < j`, in row-major order. -/
def encEdges (w : List Bool) : List (ℕ × ℕ) :=
  (idxPairs (hdrN w)).filter (fun ij => decide (ij.1 < ij.2) && adjBit w ij.1 ij.2)

/-- The field parameter `m = 3^{size N}`; the field has `2^{2m}` elements. -/
def fieldM (N : ℕ) : ℕ := 3 ^ Nat.size N

/-! ### Edge sets, kills, matrices -/

/-- `e` shares an endpoint with some edge of `S`. -/
def touches (S : List (ℕ × ℕ)) (e : ℕ × ℕ) : Bool :=
  S.any (fun f => f.1 == e.1 || f.1 == e.2 || f.2 == e.1 || f.2 == e.2)

/-- `β^{(S)}`: keep the weights of edges in `S`, zero the edges meeting `S` outside `S`, keep the
rest. Weights are aligned with the edge list `E`. -/
def kill (m : ℕ) (E S : List (ℕ × ℕ)) (β : List (List Bool)) : List (List Bool) :=
  (E.zip β).map (fun eb => if S.contains eb.1 then eb.2
    else if touches S eb.1 then gfZero m else eb.2)

/-- The symmetric weighted adjacency matrix: entry `(i, j)` is the weight of the edge
`(min i j, max i j)` if it is an edge, and zero otherwise. -/
def weightMatrix (m N : ℕ) (E : List (ℕ × ℕ)) (β : List (List Bool)) : List (List (List Bool)) :=
  (List.range N).map (fun i => (List.range N).map (fun j =>
    β.getD (E.findIdx (fun e => e == (min i j, max i j))) (gfZero m)))

/-- `Φ(β)`: the determinant of the weighted adjacency matrix over `GF(2^{2m})`. -/
def phiVal (m N : ℕ) (E : List (ℕ × ℕ)) (β : List (List Bool)) : List Bool :=
  detAlg (gfOps m) (weightMatrix m N E β)

/-- Crossing pairs `(e, f)` of a list of edges: `e.1 < f.1 < e.2 < f.2` (each unordered crossing
pair once). -/
def crossPairs (E : List (ℕ × ℕ)) : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (E.flatMap (fun e => E.map (fun f => (e, f)))).filter
    (fun ef => decide (ef.1.1 < ef.2.1) && decide (ef.2.1 < ef.1.2) && decide (ef.1.2 < ef.2.2))

/-- `Q(β) = s·Φ(β) + Σ_{d_e = 1} Φ(β^{(e)}) + Σ_{crossing (e,f)} Φ(β^{(e,f)})`. -/
def qVal (m N : ℕ) (E : List (ℕ × ℕ)) (d : List Bool) (s : Bool) (β : List (List Bool)) :
    List Bool :=
  listSum (gfOps m)
    ([if s then phiVal m N E β else gfZero m] ++
      ((E.zip d).filter (fun ed => ed.2)).map (fun ed => phiVal m N E (kill m E [ed.1] β)) ++
      (crossPairs E).map (fun ef => phiVal m N E (kill m E [ef.1, ef.2] β)))

/-! ### Greedy extraction of an inconsistent perfect matching -/

/-- Extend the partial matching `S` at its smallest uncovered vertex `v` by the first edge `e ∋ v`
disjoint from `S` with `Q(α^{(S ∪ e)}) ≠ 0` (unchanged if there is none). -/
def searchStep (m N : ℕ) (E : List (ℕ × ℕ)) (d : List Bool) (s : Bool) (α : List (List Bool))
    (S : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  if ((E.filter (fun e => (e.1 == (List.range N).findIdx (fun u => !touches S (u, u)) ||
        e.2 == (List.range N).findIdx (fun u => !touches S (u, u))) && !touches S e)).findIdx
      (fun e => !gfIsZero m (qVal m N E d s (kill m E (S ++ [e]) α)))) <
      (E.filter (fun e => (e.1 == (List.range N).findIdx (fun u => !touches S (u, u)) ||
        e.2 == (List.range N).findIdx (fun u => !touches S (u, u))) && !touches S e)).length then
    S ++ [(E.filter (fun e => (e.1 == (List.range N).findIdx (fun u => !touches S (u, u)) ||
        e.2 == (List.range N).findIdx (fun u => !touches S (u, u))) && !touches S e)).getD
      ((E.filter (fun e => (e.1 == (List.range N).findIdx (fun u => !touches S (u, u)) ||
        e.2 == (List.range N).findIdx (fun u => !touches S (u, u))) && !touches S e)).findIdx
        (fun e => !gfIsZero m (qVal m N E d s (kill m E (S ++ [e]) α)))) (0, 0)]
  else S

/-- `N` greedy steps from the empty matching. -/
def greedySearch (m N : ℕ) (E : List (ℕ × ℕ)) (d : List Bool) (s : Bool) (α : List (List Bool)) :
    List (ℕ × ℕ) :=
  (List.range N).foldl (fun S _ => searchStep m N E d s α S) []

/-- `S` is a perfect matching of the graph with edge list `E` on vertices `0, …, N-1`. -/
def isPMList (N : ℕ) (E S : List (ℕ × ℕ)) : Bool :=
  (List.range N).all (fun v => (S.filter (fun f => f.1 == v || f.2 == v)).length == 1) &&
    S.all (fun f => E.contains f)

/-- The number of crossing pairs of `S`. -/
def crossCount (S : List (ℕ × ℕ)) : ℕ := (crossPairs S).length

/-- The number of edges of `S` marked by `d`. -/
def dCount (E : List (ℕ × ℕ)) (d : List Bool) (S : List (ℕ × ℕ)) : ℕ :=
  ((E.zip d).filter (fun ed => ed.2 && S.contains ed.1)).length

/-- `S` is inconsistent with `(d, s)`: `Σ_{e∈S} d_e + s ≠ cr(S)` in `𝔽₂`. -/
def violates (E : List (ℕ × ℕ)) (d : List Bool) (s : Bool) (S : List (ℕ × ℕ)) : Bool :=
  (crossCount S + dCount E d S + (if s then 1 else 0)) % 2 == 1

/-- The equation `Σ_{e∈S} d_e + s = cr(S)` in the unknowns `(d, s)` (coefficient list `|E| + 1`). -/
def matchEqn (E S : List (ℕ × ℕ)) : Eqn :=
  (E.map (fun e => S.contains e) ++ [true], crossCount S % 2 == 1)

/-! ### Rounds -/

/-- The random point of round `r`: `|E|` consecutive blocks of `2m` bits, starting at bit
`r · |E| · 2m`. -/
def roundPoint (m : ℕ) (E : List (ℕ × ℕ)) (ρ : List Bool) (r : ℕ) : List (List Bool) :=
  (List.range E.length).map (fun i => (ρ.drop ((r * E.length + i) * (2 * m))).take (2 * m))

/-- One round on the state `(equations, (done, verdict))`. -/
def roundStep (m N : ℕ) (E : List (ℕ × ℕ)) (ρ : List Bool) (st : List Eqn × (Bool × Bool))
    (r : ℕ) : List Eqn × (Bool × Bool) :=
  if st.2.1 then st
  else if !(solveF2 (E.length + 1) st.1).1 then (st.1, (true, false))
  else if gfIsZero m (qVal m N E ((solveF2 (E.length + 1) st.1).2.take E.length)
      ((solveF2 (E.length + 1) st.1).2.getD E.length false) (roundPoint m E ρ r)) then
    (st.1, (true, true))
  else if isPMList N E (greedySearch m N E ((solveF2 (E.length + 1) st.1).2.take E.length)
        ((solveF2 (E.length + 1) st.1).2.getD E.length false) (roundPoint m E ρ r)) &&
      violates E ((solveF2 (E.length + 1) st.1).2.take E.length)
        ((solveF2 (E.length + 1) st.1).2.getD E.length false)
        (greedySearch m N E ((solveF2 (E.length + 1) st.1).2.take E.length)
          ((solveF2 (E.length + 1) st.1).2.getD E.length false) (roundPoint m E ρ r)) then
    (st.1 ++ [matchEqn E (greedySearch m N E ((solveF2 (E.length + 1) st.1).2.take E.length)
        ((solveF2 (E.length + 1) st.1).2.getD E.length false) (roundPoint m E ρ r))],
      (false, false))
  else (st.1, (true, true))

/-- Run `|E| + 3` rounds; accept unless some round rejected. -/
def runRounds (m N : ℕ) (E : List (ℕ × ℕ)) (ρ : List Bool) : Bool :=
  !((List.range (E.length + 3)).foldl (roundStep m N E ρ) ([], (false, false))).2.1 ||
    ((List.range (E.length + 3)).foldl (roundStep m N E ρ) ([], (false, false))).2.2

/-- The algorithm on random string `ρ` and input `w`: reject invalid encodings, otherwise run the
rounds. -/
def pfAlg (x : List Bool × List Bool) : Bool :=
  validEnc x.2 && runRounds (fieldM (hdrN x.2)) (hdrN x.2) (encEdges x.2) x.1

end PfaffianRecognition.CoRP


