-- Prove2me | Definitions.Def_LubyMIS_Derandomized_AlgorithmD
-- name    : LubyMIS_Derandomized_AlgorithmD
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T22:54:38.328566+00:00
-- url     : https://prove2.me/theorems/f05b7828-3474-45b9-89cb-fe55e497038c
-- title:
--   Algorithm D: its coins, one execution of the loop body, runs, and Case 1 (§4.4)
-- statement:
--   The input is a graph $G$ on the vertices $\{0, \dots, n-1\}$ and a prime $q$ with $n \le q \le 2n$. The algorithm keeps a set $I$ and the vertex set $V'$ of the current graph $G'$, the subgraph of $G$ induced on $V'$; initially $I = \emptyset$ and $V' = V$. While $V' \ne \emptyset$ it executes the loop body:
--
--   1. every vertex of degree $0$ in $G'$ is added to $I$ and deleted from $V'$; call the remaining vertex set $V_1$;
--   2. **Case 1.** If a vertex $i \in V_1$ of maximum degree has $d(i) \ge n/16$, then $i$ is added to $I$ and $\{i\} \cup N(\{i\})$ is deleted;
--   3. **Case 2.** Otherwise every $i \in V_1$ has $d(i) < n/16$. For a sample point $(x,y)$, $0 \le x,y \le q-1$, the coin of vertex $i$ is
--   $$\mathrm{coin}(i) = 1 \iff (x + y\cdot i) \bmod q < n(i), \qquad n(i) = \lfloor q / 2d(i) \rfloor,$$
--   and $I'$ is Algorithm B's selection for these coins on the graph induced on $V_1$. Algorithm D uses a sample point $(x,y)$ that maximizes the number of edges eliminated, adds $I'$ to $I$ and deletes $I' \cup N(I')$.
--
--   One execution of the loop body is a relation between the state $(I, V')$ before and the state after it; the maximizing vertex in Case 1 and the maximizing sample point in Case 2 are left free, as on the page. A run is a sequence of states starting at $(\emptyset, V)$ in which every step taken while $V' \ne \emptyset$ is an execution of the loop body. A state is in Case 1 when, after the deletion of the isolated vertices, some vertex has degree at least $n/16$.
--
--   **Formalization Note** The induced subgraph on $U$ is kept on the full vertex type `Fin n`, with the vertices outside $U$ isolated. The condition $d(i) \ge n/16$ is written $n \le 16\,d(i)$ in $\mathbb{N}$, and $d(i) < n/16$ as $16\,d(i) < n$, both exact. The printed code tests $l(i) \le n(i)$; that places $n(i)+1$ residues in $X$ and gives $\Pr[\mathrm{coin}(i) = 1] = (n(i)+1)/q$, which can exceed $1/2d(i)$. The prose on p. 1046 ($p'_i = \lfloor p_i q\rfloor/q$) and §4.2 (row $i$ holds exactly $n_{ij}$ entries equal to $R_j$) fix the test as $l(i) < n(i)$, which is used here. A vertex of degree $0$ gets coin $0$ ($\lfloor q/0 \rfloor = 0$ in Lean); Algorithm D has already deleted such vertices from $V'$. Vertices are labelled $0,\dots,n-1$ (the page's §3.2 writes $V' = \{1, \dots, n'\}$; §4.2 indexes $X_0, \dots, X_{n-1}$).
-- source:
--   Luby, A Simple Parallel Algorithm for the Maximal Independent Set Problem, SIAM J. Comput. 15(4), 1986, pp. 1046–1048, §4.4 (p′_i, Cases 1–2, Algorithm D, code of Algorithm C); p. 1039, §3.1 (loop)

import Mathlib
import Definitions.Def_LubyMIS_Derandomized_Basic

namespace LubyMIS.Derandomized

/-- The subgraph of `G` induced on the vertex set `U`, kept on the full vertex type: vertices outside
`U` are isolated. -/
def restrict {V : Type*} (G : SimpleGraph V) (U : Finset V) : SimpleGraph V where
  Adj a b := a ∈ U ∧ b ∈ U ∧ G.Adj a b
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  loopless := ⟨fun a h => G.loopless.irrefl a h.2.2⟩

instance restrictDecidableRel {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) : DecidableRel (restrict G U).Adj :=
  fun a b => inferInstanceAs (Decidable (a ∈ U ∧ b ∈ U ∧ G.Adj a b))

/-- Algorithm D's coin of vertex `i` at the sample point `(x, y)` (§4.4, pp. 1046–1047): with
`n(i) = ⌊q / 2d(i)⌋` and `l(i) = (x + y·i) mod q`, `coin(i) = 1` iff `l(i) < n(i)`. The printed code
reads `l(i) ≦ n(i)`; the strict test is the one that gives `Pr[coin(i) = 1] = ⌊p_i·q⌋/q = p′_i`
(p. 1046, and §4.2: row `i` holds exactly `n_{ij}` entries equal to `R_j`). At `d(i) = 0`,
`q / 0 = 0` and the coin is `0`. -/
def coinD {n : ℕ} (q : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (x y : ZMod q)
    (i : Fin n) : Bool :=
  decide ((x + y * ((i : ℕ) : ZMod q)).val < q / (2 * H.degree i))

/-- The vertices of `V′ = U` that are isolated in the current graph `G′` (the induced subgraph on
`U`); Algorithm D adds them to `I` and deletes them from `V′`. -/
def zeroSet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (U : Finset (Fin n)) :
    Finset (Fin n) :=
  U.filter (fun v => (restrict G U).degree v = 0)

/-- `V′` after the deletion of its isolated vertices. -/
def V1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (U : Finset (Fin n)) :
    Finset (Fin n) :=
  U \ zeroSet G U

/-- One execution of the body of Algorithm D's `while` loop (§4.4, pp. 1046–1048), from the state
`s = (I, V′)` to the state `t`, for the input graph `G` on `Fin n` and the prime `q`. The current graph
is `H = restrict G V′`; its isolated vertices `Z` go to `I`; on `V₁ = V′ − Z`:
* **Case 1**: a vertex `i ∈ V₁` of maximum degree with `d(i) ≥ n/16` joins `I`, and `{i} ∪ N({i})`
  is deleted;
* **Case 2**: all of `V₁` has `d(i) < n/16`; a sample point `(x, y) ∈ (ZMod q)²` maximizing the number
  of eliminated edges is used, `I′ = selectB` of its coins joins `I`, and `I′ ∪ N(I′)` is deleted. -/
def DStep {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q : ℕ)
    (s t : Finset (Fin n) × Finset (Fin n)) : Prop :=
  let H := restrict G s.2
  let I₁ := s.1 ∪ zeroSet G s.2
  let V₁ := V1 G s.2
  let H₁ := restrict G V₁
  let S : ZMod q → ZMod q → Finset (Fin n) := fun x y => selectB H₁ (coinD q H₁ x y)
  (∃ i ∈ V₁, (∀ j ∈ V₁, H.degree j ≤ H.degree i) ∧ n ≤ 16 * H.degree i ∧
      t = (I₁ ∪ {i}, V₁ \ ({i} ∪ H.neighborFinset i))) ∨
    ((∀ i ∈ V₁, 16 * H.degree i < n) ∧
      ∃ x y : ZMod q, (∀ x' y' : ZMod q, eliminated H₁ (S x' y') ≤ eliminated H₁ (S x y)) ∧
        t = (I₁ ∪ S x y, V₁ \ (S x y ∪ nbhd H₁ (S x y))))

/-- A run of Algorithm D: it starts from `I = ∅`, `V′ = V`, and every execution of the loop body
while `G′ ≠ ∅` (i.e. `V′` nonempty) is a `DStep`. -/
def IsRun {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q : ℕ)
    (s : ℕ → Finset (Fin n) × Finset (Fin n)) : Prop :=
  s 0 = (∅, Finset.univ) ∧ ∀ k, (s k).2.Nonempty → DStep G q (s k) (s (k + 1))

/-- The state `s` is in Case 1 of §4.4: after the isolated vertices are deleted, some vertex has
degree `d(i) ≥ n/16` in the current graph. -/
def Case1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Finset (Fin n) × Finset (Fin n)) : Prop :=
  ∃ i ∈ V1 G s.2, n ≤ 16 * (restrict G s.2).degree i

instance case1Decidable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    DecidablePred (Case1 G) :=
  fun s => inferInstanceAs (Decidable (∃ i ∈ V1 G s.2, n ≤ 16 * (restrict G s.2).degree i))

end LubyMIS.Derandomized


