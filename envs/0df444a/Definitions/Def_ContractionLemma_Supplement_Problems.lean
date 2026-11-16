-- Prove2me | Definitions.Def_ContractionLemma_Supplement_Problems
-- name    : ContractionLemma_Supplement_Problems
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:20:24.200714+00:00
-- url     : https://prove2.me/theorems/7748805f-32ff-4162-9a57-326151f23c17
-- title:
--   The problems of Part I: Max-Cut, graphical games, End-of-Line, DNF minimization, Hamiltonicity, Common Matching Weight, sparse CSPs, TQBF
-- statement:
--   The problems of Part I, with their input encodings (binary throughout).
--
--   1. **Weighted Max-Cut** (§3): a graph on $n$ vertices with rational edge weights; a cut $x\in\{0,1\}^V$ is a **local maximum** if flipping the side of any single vertex does not increase its weight; local maxima are counted as assignments.
--   2. **Graphical games** (§3): $n$ players with actions in $\{0,1\}$, player $i$ with a set $N_i$ of neighbours and a payoff table $u_i:\{0,1\}^{\{i\}\cup N_i}\to[0,1]\cap\mathbb Q$. For a mixed profile $p\in[0,1]^n$, $U_i(p)$ is the expected payoff and $r_i(p)=\max_a U_i(a,p_{-i})-U_i(p)$ the regret; $p$ is an **$\varepsilon$-Nash equilibrium** if $r_i(p)\le\varepsilon$ for every $i$.
--   3. **End-of-Line** (§3): circuits $S,P:\{0,1\}^n\to\{0,1\}^n$ with $P(0^n)=0^n$, $S(0^n)\ne0^n$, $P(S(0^n))=0^n$; a solution is $x\ne0^n$ with $[P(S(x))=x]\ne[S(P(x))=x]$.
--   4. **DNF minimization** (§4.2): a term is a pattern in $\{0,1,*\}^k$; an implicant covers only positive rows; a prime implicant has no fixed position that can be starred; $I=\sum_j|P_j^{-1}(1)|$ counts the pairs of a prime implicant and a row it covers.
--   5. **Hamiltonicity** (§6): simple directed or undirected graphs with integer arc costs; Hamiltonian paths and cycles; $\sigma(n,m)=n\max\{1,\log(m/n)\}$.
--   6. **Common Matching Weight** (p.7): $A\in\mathbb N^{a\times a}$, $B\in\mathbb N^{b\times b}$, $N=2a+2b$; the support of a row is the set of binary positions nonzero in some entry of the row; the count is the number of pairs $(\pi,\sigma)$ of permutations with $\sum_iA_{i,\pi(i)}=\sum_jB_{j,\sigma(j)}$.
--   7. **CSPs with all-different** (§7.3): $n$ variables over $[n]$, $m$ constraints given by their scopes; the count is the number of injective assignments satisfying every constraint.
--   8. **TQBF** (Definition 2.11): the true closed quantified Boolean formulas.
--
--   **Formalization Note** Max-Cut instances may have parallel edges, counted in the degree. An undirected Hamiltonian cycle has at least three vertices, a directed one at least two. A truth table lists row $x$ at index $\sum_ix_i2^i$.
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), §3, pp.23–24; §4.2, pp.25–26; §6, p.29; p.7; §7.3, p.35; Definition 2.11, p.21

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_Supplement_Common

set_option autoImplicit false

namespace ContractionLemma.Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-! The problems of Part I of Gajulapalli, *The Contraction Lemma Beyond ETH* (manuscript, sha256
049caea1…), pp.22–35, and TQBF (Definition 2.11, p.21), with their input encodings. -/

/-- **Weighted Max-Cut instance** (§3, p.23): a graph on vertices `Fin n` given by its edge list,
each edge with a rational weight (written in binary).

**Formalization Note.** The edge list may contain parallel edges (each counted in the degree and in
the cut weight); loops are excluded. -/
structure MaxCutInst where
  /-- number of vertices -/
  n : ℕ
  /-- edges `(u, v, w_uv)` -/
  edges : List (Fin n × Fin n × ℚ)
  /-- no loops -/
  loopless : ∀ e ∈ edges, e.1 ≠ e.2.1

namespace MaxCutInst

/-- The weight of the cut `x`: the total weight of the edges whose endpoints lie on different sides. -/
def cutWeight (H : MaxCutInst) (x : Fin H.n → Bool) : ℚ :=
  (H.edges.map fun e => if x e.1 ≠ x e.2.1 then e.2.2 else 0).sum

/-- The cut `x` with the side of `v` flipped. -/
def flip (H : MaxCutInst) (x : Fin H.n → Bool) (v : Fin H.n) : Fin H.n → Bool :=
  Function.update x v (!x v)

/-- A local maximum under single flips: no single flip increases the cut weight. -/
def IsLocalMax (H : MaxCutInst) (x : Fin H.n → Bool) : Prop :=
  ∀ v, H.cutWeight (H.flip x v) ≤ H.cutWeight x

/-- The degree of `v` (incident edges with multiplicity). -/
def deg (H : MaxCutInst) (v : Fin H.n) : ℕ := (H.edges.filter fun e => e.1 = v ∨ e.2.1 = v).length

open scoped Classical in
/-- The number of local maxima, counted as assignments (a cut and its complement separately). -/
noncomputable def numLocalMax (H : MaxCutInst) : ℕ :=
  (Finset.univ.filter fun x : Fin H.n → Bool => H.IsLocalMax x).card

/-- The encoding: `n`, then each edge as its endpoints and weight in binary. -/
def encode (H : MaxCutInst) : List Bool :=
  Encoding.encodeList id
    [countWord H.n, Encoding.encodeList (fun e : Fin H.n × Fin H.n × ℚ =>
      Encoding.encodeList id [countWord e.1, countWord e.2.1, ratWord e.2.2]) H.edges]

end MaxCutInst

/-- The encoding of a vertex assignment `x : Fin n → Bool` (output of Theorem 2(a), (c)). -/
def vecWord {n : ℕ} (x : Fin n → Bool) : List Bool := bitsWord (List.ofFn x)

/-- **A graphical game with binary actions** (§3, p.23): `n` players; player `i` has the neighbour
list `nbrs i` (distinct players other than `i`) and the payoff table `pay i` on the actions of `i`
(index `0`) and of its neighbours (indices `1, …`, in list order), with values in `[0, 1] ∩ ℚ`. -/
structure GameInst where
  /-- number of players -/
  n : ℕ
  /-- neighbours of each player -/
  nbrs : Fin n → List (Fin n)
  /-- neighbours are distinct -/
  nodup : ∀ i, (nbrs i).Nodup
  /-- a player is not its own neighbour -/
  irrefl : ∀ i, i ∉ nbrs i
  /-- payoff tables -/
  pay : (i : Fin n) → (Fin ((nbrs i).length + 1) → Bool) → ℚ
  /-- payoffs lie in `[0, 1]` -/
  pay_mem : ∀ i a, 0 ≤ pay i a ∧ pay i a ≤ 1

namespace GameInst

/-- The local view of an action profile `a` by player `i`: its own action, then its neighbours'. -/
def view (G : GameInst) (i : Fin G.n) (a : Fin G.n → Bool) : Fin ((G.nbrs i).length + 1) → Bool :=
  fun k => Fin.cases (a i) (fun j => a ((G.nbrs i).get j)) k

/-- The expected payoff `U_i(p)` of player `i` under the mixed profile `p` (player `j` plays `1` with
probability `p_j`, independently). -/
noncomputable def U (G : GameInst) (i : Fin G.n) (p : Fin G.n → ℝ) : ℝ :=
  ∑ a : Fin G.n → Bool, (∏ j, if a j then p j else 1 - p j) * (G.pay i (G.view i a) : ℝ)

/-- The regret `r_i(p) = max_a U_i(a, p_{−i}) − U_i(p)`. -/
noncomputable def regret (G : GameInst) (i : Fin G.n) (p : Fin G.n → ℝ) : ℝ :=
  max (G.U i (Function.update p i 1)) (G.U i (Function.update p i 0)) - G.U i p

/-- An `ε`-Nash equilibrium: a mixed profile in `[0,1]^n` with every regret at most `ε`. -/
def IsEpsNash (G : GameInst) (ε : ℝ) (p : Fin G.n → ℝ) : Prop :=
  (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧ ∀ i, G.regret i p ≤ ε

/-- The encoding: `n`, each player's neighbour list, and each payoff table listed over the codes
`c < 2^{|N_i|+1}` (bit `k` of `c` is the action of local index `k`), payoffs in binary. -/
def encode (G : GameInst) : List Bool :=
  Encoding.encodeList id
    [countWord G.n,
      Encoding.encodeList (fun i => Encoding.encodeList (fun j : Fin G.n => countWord j) (G.nbrs i))
        (List.finRange G.n),
      Encoding.encodeList (fun i => Encoding.encodeList
        (fun c => ratWord (G.pay i (fun k => c.testBit k))) (List.range (2 ^ ((G.nbrs i).length + 1))))
        (List.finRange G.n)]

end GameInst

/-- The encoding of a rational mixed profile (output of Theorem 2(b)). -/
def ratVecWord {n : ℕ} (p : Fin n → ℚ) : List Bool := Encoding.encodeList ratWord (List.ofFn p)

/-- **An End-of-Line instance** (§3, p.24): successor and predecessor circuits `S, P` on `n`-bit
labels with `P(0^n) = 0^n`, `S(0^n) ≠ 0^n`, `P(S(0^n)) = 0^n`. -/
structure EoLInst where
  /-- label length -/
  n : ℕ
  /-- successor circuit -/
  S : FCircuit
  /-- predecessor circuit -/
  P : FCircuit
  /-- `S` is a well-formed map `{0,1}^n → {0,1}^n` -/
  hS : S.WellFormed ∧ S.nIn = n ∧ S.outs.length = n
  /-- `P` is a well-formed map `{0,1}^n → {0,1}^n` -/
  hP : P.WellFormed ∧ P.nIn = n ∧ P.outs.length = n

namespace EoLInst

/-- The all-zero label. -/
def zero (I : EoLInst) : List Bool := List.replicate I.n false

/-- The promise `P(0^n) = 0^n`, `S(0^n) ≠ 0^n`, `P(S(0^n)) = 0^n`. -/
def Promise (I : EoLInst) : Prop :=
  I.P.eval I.zero = I.zero ∧ I.S.eval I.zero ≠ I.zero ∧ I.P.eval (I.S.eval I.zero) = I.zero

/-- `out(x) = [P(S(x)) = x]`. -/
def outB (I : EoLInst) (x : List Bool) : Bool := decide (I.P.eval (I.S.eval x) = x)

/-- `in(x) = [S(P(x)) = x]`. -/
def inB (I : EoLInst) (x : List Bool) : Bool := decide (I.S.eval (I.P.eval x) = x)

/-- A solution: `x ≠ 0^n` whose in-degree and out-degree differ, i.e. `out(x) ≠ in(x)`. -/
def IsSolution (I : EoLInst) (x : Fin I.n → Bool) : Prop :=
  List.ofFn x ≠ I.zero ∧ I.outB (List.ofFn x) ≠ I.inB (List.ofFn x)

/-- The total number of gates `G`. -/
def gates (I : EoLInst) : ℕ := I.S.size + I.P.size

/-- The encoding: `n` and the two circuits. -/
def encode (I : EoLInst) : List Bool := Encoding.encodeList id [countWord I.n, I.S.encode, I.P.encode]

end EoLInst

/-- **A term** on `k` variables (§4.2, p.25): a pattern in `{0, 1, ∗}^k` (`none` is `∗`). -/
abbrev Term (k : ℕ) := Fin k → Option Bool

/-- The function `f : {0,1}^k → {0,1}` of a truth table: row `x` has index `∑_i x_i 2^i`. -/
def ttFun (tt : List Bool) (k : ℕ) (x : Fin k → Bool) : Bool :=
  tt.getD (∑ i : Fin k, if x i then 2 ^ (i : ℕ) else 0) false

namespace Term

variable {k : ℕ}

/-- The term covers the row `x` if `x` agrees with it on every fixed position. -/
def Covers (t : Term k) (x : Fin k → Bool) : Prop := ∀ i b, t i = some b → x i = b

/-- An implicant of `f`: it covers only positive rows. -/
def IsImplicant (f : (Fin k → Bool) → Bool) (t : Term k) : Prop := ∀ x, t.Covers x → f x = true

/-- A prime implicant: an implicant in which no fixed position can be starred. -/
def IsPrime (f : (Fin k → Bool) → Bool) (t : Term k) : Prop :=
  IsImplicant f t ∧ ∀ i, t i ≠ none → ¬ IsImplicant f (Function.update t i none)

open scoped Classical in
/-- The number of literals (fixed positions). -/
noncomputable def literals (t : Term k) : ℕ := (Finset.univ.filter fun i => t i ≠ none).card

open scoped Classical in
/-- The number of rows the term covers. -/
noncomputable def coverCount (t : Term k) : ℕ := (Finset.univ.filter fun x => t.Covers x).card

end Term

/-- A DNF (a list of terms) computes `f`. -/
def DNFComputes {k : ℕ} (f : (Fin k → Bool) → Bool) (D : List (Term k)) : Prop :=
  ∀ x, f x = true ↔ ∃ t ∈ D, t.Covers x

/-- The literal count of a DNF. -/
noncomputable def litCount {k : ℕ} (D : List (Term k)) : ℕ := (D.map Term.literals).sum

open scoped Classical in
/-- `I = ∑_j |P_j^{−1}(1)|`: the number of pairs of a prime implicant and a row it covers (Theorem 4). -/
noncomputable def primeIncidence {k : ℕ} (f : (Fin k → Bool) → Bool) : ℕ :=
  ∑ t ∈ Finset.univ.filter (fun t : Term k => t.IsPrime f), t.coverCount

/-- The encoding of a DNF: each term as its `k` positions, `∗ ↦ 00`, `0 ↦ 10`, `1 ↦ 11`. -/
def dnfWord {k : ℕ} (D : List (Term k)) : List Bool :=
  Encoding.encodeList (fun t : Term k => (List.ofFn t).flatMap fun
    | none => [false, false] | some b => [true, b]) D

/-- **A Hamiltonicity instance** (§6, p.29 and p.7): a simple directed (`directed = true`) or
undirected graph on `Fin n` given by its list of arcs or edges, with an integer cost on each. -/
structure HamInst where
  /-- number of vertices -/
  n : ℕ
  /-- directed or undirected -/
  directed : Bool
  /-- arcs (directed) or edges (undirected) -/
  arcs : List (Fin n × Fin n)
  /-- integer costs, one per arc or edge -/
  cost : List ℤ
  /-- one cost per arc -/
  cost_len : cost.length = arcs.length
  /-- no loops -/
  loopless : ∀ e ∈ arcs, e.1 ≠ e.2
  /-- no repeated arcs -/
  nodup : arcs.Nodup
  /-- an undirected edge is listed once -/
  undirected_once : directed = false → ∀ u v, (u, v) ∈ arcs → (v, u) ∉ arcs

namespace HamInst

/-- The number of arcs or edges `m`. -/
def m (H : HamInst) : ℕ := H.arcs.length

/-- `u → v` is an arc (or `{u, v}` an edge) of the graph. -/
def Adj (H : HamInst) (u v : Fin H.n) : Prop :=
  (u, v) ∈ H.arcs ∨ (H.directed = false ∧ (v, u) ∈ H.arcs)

/-- The cost of the arc `u → v` (or edge `{u, v}`); `0` if absent. -/
def arcCost (H : HamInst) (u v : Fin H.n) : ℤ :=
  match H.arcs.idxOf? (u, v) with
  | some i => H.cost.getD i 0
  | none => match H.arcs.idxOf? (v, u) with
    | some i => if H.directed then 0 else H.cost.getD i 0
    | none => 0

/-- A Hamiltonian path: a list of all `n` vertices, each once, consecutive ones adjacent. -/
def IsHamPath (H : HamInst) (P : List (Fin H.n)) : Prop :=
  P.Nodup ∧ P.length = H.n ∧ P.IsChain H.Adj

/-- A Hamiltonian cycle: a Hamiltonian path whose last vertex is adjacent to its first, with at least
two vertices (directed) or three (undirected). -/
def IsHamCycle (H : HamInst) (P : List (Fin H.n)) : Prop :=
  H.IsHamPath P ∧ (if H.directed then 2 else 3) ≤ H.n ∧
    ∃ (u v : Fin H.n), P.head? = some u ∧ P.getLast? = some v ∧ H.Adj v u

/-- The cost of a path (`closed = false`) or of the cycle it closes (`closed = true`). -/
def pathCost (H : HamInst) (closed : Bool) (P : List (Fin H.n)) : ℤ :=
  (List.zipWith (fun u v => H.arcCost u v) P P.tail).sum +
    (if closed then
      match P.getLast?, P.head? with
      | some v, some u => H.arcCost v u
      | _, _ => 0
    else 0)

/-- Hamiltonian path (`closed = false`) or cycle (`closed = true`). -/
def IsHam (H : HamInst) (closed : Bool) (P : List (Fin H.n)) : Prop :=
  if closed then H.IsHamCycle P else H.IsHamPath P

/-- `σ(n, m) = n · max{1, log(m/n)}` (Theorem 7). -/
noncomputable def sigma (H : HamInst) : ℝ := H.n * max 1 (Real.logb 2 ((H.m : ℝ) / H.n))

/-- The encoding: `n`, the direction bit, and each arc with its cost in binary. -/
def encode (H : HamInst) : List Bool :=
  Encoding.encodeList id
    [countWord H.n, [H.directed],
      Encoding.encodeList (fun e : (Fin H.n × Fin H.n) × ℤ =>
        Encoding.encodeList id [countWord e.1.1, countWord e.1.2, intWord e.2]) (H.arcs.zip H.cost)]

end HamInst

/-- The encoding of a vertex list (a path or cycle). -/
def pathWord {n : ℕ} (P : List (Fin n)) : List Bool := Encoding.encodeList (fun v : Fin n => countWord v) P

/-- **A Common Matching Weight instance** (p.7, §7.2): `A ∈ ℕ^{a×a}`, `B ∈ ℕ^{b×b}`; `N = 2a + 2b`. -/
structure CMWInst where
  /-- order of `A` -/
  a : ℕ
  /-- order of `B` -/
  b : ℕ
  /-- the matrix `A` -/
  A : Fin a → Fin a → ℕ
  /-- the matrix `B` -/
  B : Fin b → Fin b → ℕ

namespace CMWInst

/-- `N = 2a + 2b`. -/
def N (I : CMWInst) : ℕ := 2 * I.a + 2 * I.b

/-- The support of a row: the binary positions that are nonzero in some entry of the row. -/
def rowSupport {k : ℕ} (row : Fin k → ℕ) : Finset ℕ :=
  Finset.univ.biUnion fun j => (Finset.range (row j + 1)).filter fun i => (row j).testBit i

open scoped Classical in
/-- The number of pairs `(π, σ)` of permutations with `∑_i A_{i,π(i)} = ∑_j B_{j,σ(j)}`. -/
noncomputable def count (I : CMWInst) : ℕ :=
  (Finset.univ.filter fun πσ : Equiv.Perm (Fin I.a) × Equiv.Perm (Fin I.b) =>
    ∑ i, I.A i (πσ.1 i) = ∑ j, I.B j (πσ.2 j)).card

/-- Every row support has size at most `c·log(N+2)`. -/
def SparseRows (I : CMWInst) (c : ℝ) : Prop :=
  (∀ i, ((rowSupport (I.A i)).card : ℝ) ≤ c * Real.logb 2 (I.N + 2)) ∧
  ∀ j, ((rowSupport (I.B j)).card : ℝ) ≤ c * Real.logb 2 (I.N + 2)

/-- The encoding: `a`, `b`, and the rows of `A` and of `B`, entries in binary. -/
def encode (I : CMWInst) : List Bool :=
  Encoding.encodeList id
    [countWord I.a, countWord I.b,
      Encoding.encodeList (fun i => Encoding.encodeList (fun j => countWord (I.A i j))
        (List.finRange I.a)) (List.finRange I.a),
      Encoding.encodeList (fun i => Encoding.encodeList (fun j => countWord (I.B i j))
        (List.finRange I.b)) (List.finRange I.b)]

end CMWInst

/-- **A CSP instance with domain `[n]`** (§7.3, p.35): `n` variables with values in `Fin n`, the
scopes of `m` constraints (lists of variables), and further data `data` read by the constraint
predicates. The predicates themselves are given by a machine (Theorem 7.3). -/
structure CSPInst where
  /-- data read by the predicates -/
  data : List Bool
  /-- number of variables, also the domain size -/
  n : ℕ
  /-- the scopes of the constraints -/
  scopes : List (List (Fin n))

namespace CSPInst

/-- The number of constraints `m`. -/
def m (I : CSPInst) : ℕ := I.scopes.length

/-- The encoding: the data, `n`, and the scopes. -/
def encode (I : CSPInst) : List Bool :=
  Encoding.encodeList id
    [I.data, countWord I.n, Encoding.encodeList (fun sc : List (Fin I.n) =>
      Encoding.encodeList (fun v : Fin I.n => countWord v) sc) I.scopes]

/-- The input of the predicate machine for constraint `j` on the values `vals` of its scope. -/
def predInput (I : CSPInst) (j : ℕ) (vals : List (Fin I.n)) : List Bool :=
  Encoding.encodeList id [I.encode, countWord j, Encoding.encodeList (fun v : Fin I.n => countWord v) vals]

open scoped Classical in
/-- The number of solutions with all-different: injective assignments `x : [n] → [n]` (permutations)
satisfying every constraint `pred j`. -/
noncomputable def count (I : CSPInst) (pred : Fin I.m → List (Fin I.n) → Bool) : ℕ :=
  (Finset.univ.filter fun x : Fin I.n → Fin I.n => Function.Injective x ∧
    ∀ j : Fin I.m, pred j ((I.scopes.get j).map x) = true).card

end CSPInst

/-- **Quantified Boolean formulas** (Definition 2.11): variables, negation, conjunction, disjunction,
universal and existential quantification of a variable. -/
inductive QBF
  | var (i : ℕ)
  | neg (φ : QBF)
  | conj (φ ψ : QBF)
  | disj (φ ψ : QBF)
  | all (i : ℕ) (φ : QBF)
  | ex (i : ℕ) (φ : QBF)

namespace QBF

/-- The truth value under an assignment. -/
def eval : QBF → (ℕ → Bool) → Bool
  | var i, a => a i
  | neg φ, a => !(φ.eval a)
  | conj φ ψ, a => φ.eval a && ψ.eval a
  | disj φ ψ, a => φ.eval a || ψ.eval a
  | all i φ, a => φ.eval (Function.update a i false) && φ.eval (Function.update a i true)
  | ex i φ, a => φ.eval (Function.update a i false) || φ.eval (Function.update a i true)

/-- The free variables. -/
def free : QBF → Finset ℕ
  | var i => {i}
  | neg φ => φ.free
  | conj φ ψ => φ.free ∪ ψ.free
  | disj φ ψ => φ.free ∪ ψ.free
  | all i φ => φ.free.erase i
  | ex i φ => φ.free.erase i

/-- A prefix-free encoding: a 3-bit tag, then the variable in binary and the subformulas, framed. -/
def encode : QBF → List Bool
  | var i => Encoding.encodeList id [[false, false, false], countWord i]
  | neg φ => Encoding.encodeList id [[false, false, true], φ.encode]
  | conj φ ψ => Encoding.encodeList id [[false, true, false], φ.encode, ψ.encode]
  | disj φ ψ => Encoding.encodeList id [[false, true, true], φ.encode, ψ.encode]
  | all i φ => Encoding.encodeList id [[true, false, false], countWord i, φ.encode]
  | ex i φ => Encoding.encodeList id [[true, false, true], countWord i, φ.encode]

end QBF

/-- **TQBF** (Definition 2.11, p.21): the encodings of true closed quantified Boolean formulas. -/
def TQBF : List Bool → Prop := fun w =>
  ∃ φ : QBF, w = φ.encode ∧ φ.free = ∅ ∧ φ.eval (fun _ => false) = true

end ContractionLemma.Supplement


