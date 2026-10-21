-- Prove2me | Definitions.Def_MatrixAnalytic_Tree_Model
-- name    : MatrixAnalytic_Tree_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:47:19.691675+00:00
-- url     : https://prove2.me/theorems/de1d98c8-44b9-4565-a871-9b8fe57d356f
-- title:
--   The tree process of §14.2 — generator (14.2)–(14.3) on stacks, the matrices N, R(i), R, U and the marginals p_n
-- statement:
--   Fix a countable set of **phases** $\{1, \dots, m\}$ ($m$ possibly infinite). The state space is the empty stack $\emptyset$ together with all stacks $(i_1, \dots, i_k)$, $k \ge 1$, of phases. The states $(i_1, \dots, i_k, j)$, $j$ ranging over the phases, form the **stack descriptor** (node) $s\{i_1, \dots, i_k\}$; the nodes form an $m$-ary tree whose root $s\{\cdot\}$ holds the stacks of size one, and whose parent of $s\{\cdot\}$ is $\emptyset$.
--
--   The data are vectors $\boldsymbol a, \boldsymbol d$ and matrices $C, A_1, \dots, A_m, D_1, \dots, D_m$ indexed by the phases. The generator $Q$ of (14.2)–(14.3) has the transitions
--   - $(i_1, \dots, i_{k-1}, i) \to (i_1, \dots, i_{k-1}, j)$ with rate $C_{ij}$ (and diagonal entry $C_{ii}$);
--   - $\emptyset \to (j)$ with rate $a_j$, and $Q_{\emptyset\emptyset} = \lambda = -\sum_j a_j$;
--   - $(i_1, \dots, i_{k-1}, i) \to (i_1, \dots, i_{k-1}, j, i')$ with rate $[A_j]_{ii'}$;
--   - $(i) \to \emptyset$ with rate $d_i$;
--   - $(i_1, \dots, i_{k-1}, j, i) \to (i_1, \dots, i_{k-1}, i')$ with rate $[D_j]_{ii'}$;
--
--   and no others. The standing assumption (p. 289) is that the data make $Q$ an **irreducible generator**; they are otherwise arbitrary.
--
--   For a vector $\pi$ on the states, $\pi\{i_1, \dots, i_k\}$ is its subvector on the node $s\{i_1, \dots, i_k\}$, $\pi_0$ its value at $\emptyset$, and $p_{n,j}$ the total mass of the states of stack size $n$ with phase $j$ at the top, i.e. $p_{n,j} = \sum_{i_1, \dots, i_{n-1}} \pi\{i_1, \dots, i_{n-1}\}_j$.
--
--   The matrix $N$ has entries $N_{ij}$ = the expected total time spent in the state $(j)$ of the node $s\{\cdot\}$, starting from $(i)$ at time $0$, before the first visit to $\emptyset$. Further $R(i) = A_iN$ and $R = \sum_i R(i)$. The matrix $U$ is the generator of the process in the local time of $s\{\cdot\}$ before the first passage to $\emptyset$: $U_{ij}$ is the rate $C_{ij}$ of a direct transition $(i) \to (j)$ plus, for every transition from $(i)$ to a state $z$ outside $s\{\cdot\} \cup \{\emptyset\}$, its rate times the probability that the process started from $z$ enters $s\{\cdot\} \cup \{\emptyset\}$ for the first time in $(j)$.
--
--   **Formalization Note** Phases are an arbitrary countable type $\iota$; a stack $(i_1, \dots, i_k, j)$ is the pair of the list $[i_1, \dots, i_k]$ (bottom of the stack first) and the top phase $j$, and $\emptyset$ is `none`. $N$, $R(i)$ and $R$ are expected times and products of nonnegative matrices, computed in $[0, \infty]$ with `tsum` products; $U$ is real (its diagonal is negative), with the first-entry probabilities read as reals. None of $N$, $R$, $U$ is defined through (14.4), (14.6) or a "minimal solution": they are defined by what the book says they mean.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 288–292, §14.2 (a)–(c), (14.2), (14.3), and the definitions of N (pp. 289–290), π₀, π{n}, p_n (p. 290), R(i) (p. 290), R (p. 291) and U (p. 291)

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process

namespace MatrixAnalytic.Tree

noncomputable section

open scoped ENNReal

/-!
The tree-structured Markov process of §14.2–14.3 of Latouche & Ramaswami (pp. 288–292). A state
is either the empty stack `∅` (`none`) or a stack `(i₁, …, i_k, j)`, `k ≥ 0`, written
`some (l, j)` with `l = [i₁, …, i_k]` (book order, bottom of the stack first) and `j` the index at
the top. The stack descriptor (node) `s{i₁, …, i_k}` is the set of the states `some (l, j)`,
`j` ranging over the phases. Phases form an arbitrary countable type `ι` (the book's
`{1, …, m}`, `m` possibly infinite). The quantities `N`, `R(i)`, `R`, `U` are defined by what they
mean (expected times and first-entry probabilities of the process), never by an equation of the
chapter.
-/

variable {ι : Type*} [Countable ι] [DecidableEq ι]

/-- The data of a tree process (p. 288–289): the vectors `a`, `d` and the matrices `C`, `A_j`,
`D_j` (`A j i i' = [A_j]_{ii'}`, `D j i i' = [D_j]_{ii'}`). -/
structure TreeData (ι : Type*) where
  a : ι → ℝ
  d : ι → ℝ
  C : ι → ι → ℝ
  A : ι → ι → ι → ℝ
  D : ι → ι → ι → ℝ

/-- The state space `∅ ∪ {(i₁, …, i_k) : k ≥ 1}`: `none` is `∅`, `some (l, j)` is the stack
`(l₁, …, l_k, j)`. -/
abbrev TreeState (ι : Type*) := Option (List ι × ι)

/-- The infinitesimal generator `Q` of (14.2)–(14.3), entry by entry (p. 288):
* `(i₁, …, i_{k−1}, i) → (i₁, …, i_{k−1}, j)` at rate `C_{ij}` (the diagonal entry is `C_{ii}`);
* `∅ → (j)` at rate `a_j`, and `Q_{∅∅} = λ = −Σ_j a_j`;
* `(i₁, …, i_{k−1}, i) → (i₁, …, i_{k−1}, j, i')` at rate `[A_j]_{ii'}`;
* `(i) → ∅` at rate `d_i`;
* `(i₁, …, i_{k−1}, j, i) → (i₁, …, i_{k−1}, i')` at rate `[D_j]_{ii'}`;
and `0` for every other pair. In the last entry the three summands are mutually exclusive (the
stacks have equal length, one more, or one less element), and each sum over `j` has at most one
nonzero term. -/
def gen (T : TreeData ι) : TreeState ι → TreeState ι → ℝ
  | none, none => -∑' j : ι, T.a j
  | none, some (l, j) => if l = [] then T.a j else 0
  | some (l, i), none => if l = [] then T.d i else 0
  | some (l, i), some (l', i') =>
      (if l' = l then T.C i i' else 0)
        + ∑' j : ι, (if l' = l ++ [j] then T.A j i i' else 0)
        + ∑' j : ι, (if l = l' ++ [j] then T.D j i i' else 0)

/-- The standing assumption of p. 289: the data are such that `Q` is an **irreducible
generator** (the data are otherwise arbitrary). -/
def IsTreeProcess (T : TreeData ι) : Prop :=
  IsGenerator (gen T) ∧ IsIrreducibleGen (gen T)

/-- The stack descriptor `s{l}` as a set of states. -/
def node (l : List ι) : Set (TreeState ι) :=
  {x | ∃ j : ι, x = some (l, j)}

/-- The subvector `π{l}` of a vector `π` on the states, for the stack descriptor `s{l}`. -/
def nodeVec (π : TreeState ι → ℝ) (l : List ι) : ι → ℝ :=
  fun j => π (some (l, j))

/-- `p_{n,j}`: the probability, under `π`, that the stack size is `n` and the index at the top is
`j` (p. 290); the states `(i₁, …, i_k, j)` have stack size `k + 1`. -/
def stackMarginal (π : TreeState ι → ℝ) (n : ℕ) (j : ι) : ℝ :=
  ∑' l : List ι, if l.length + 1 = n then π (some (l, j)) else 0

/-- A real matrix read in `ℝ≥0∞` (its entries are nonnegative wherever it is used). -/
def ennMat (M : ι → ι → ℝ) : ι → ι → ℝ≥0∞ :=
  fun i j => ENNReal.ofReal (M i j)

/-- Row vector times matrix, `(vM)_j = Σ_i v_i M_{ij}`, in `ℝ≥0∞`. -/
def vecMulE (v : ι → ℝ≥0∞) (M : ι → ι → ℝ≥0∞) : ι → ℝ≥0∞ :=
  fun j => ∑' i : ι, v i * M i j

/-- Matrix product `(MM')_{ij} = Σ_k M_{ik} M'_{kj}`, in `ℝ≥0∞`. -/
def matMulE (M M' : ι → ι → ℝ≥0∞) : ι → ι → ℝ≥0∞ :=
  fun i j => ∑' k : ι, M i k * M' k j

/-- Matrix powers in `ℝ≥0∞`: `M⁰ = I`, `M^{k+1} = M^k M`. -/
def matPowE (M : ι → ι → ℝ≥0∞) : ℕ → ι → ι → ℝ≥0∞
  | 0 => fun i j => if i = j then 1 else 0
  | k + 1 => matMulE (matPowE M k) M

/-- The matrix `N` (pp. 289–291): `N_{ij}` is the expected total time spent in the state `(j)` of
the node `s{·}`, starting from the state `(i)` at time `0`, before the first visit to the parent
of `s{·}`, the empty state `∅`. -/
def matN (T : TreeData ι) : ι → ι → ℝ≥0∞ :=
  fun i j => sojournAvoid (gen T) {none} (some ([], i)) (some ([], j))

/-- `N` read as a real matrix (its entries are finite wherever this is used). -/
def matNR (T : TreeData ι) : Matrix ι ι ℝ :=
  Matrix.of fun i j => (matN T i j).toReal

/-- `R(i) = A_i N` (Theorem 14.3.1, p. 290). -/
def matRi (T : TreeData ι) (i : ι) : ι → ι → ℝ≥0∞ :=
  matMulE (ennMat (T.A i)) (matN T)

/-- `R = Σ_{1 ≤ i ≤ m} R(i)` (Corollary 14.3.2, p. 291). -/
def matR (T : TreeData ι) : ι → ι → ℝ≥0∞ :=
  fun i j => ∑' k : ι, matRi T k i j

/-- The row vector `π₀ a` (`π₀` the probability of `∅` under `π`). -/
def rootVec (T : TreeData ι) (π : TreeState ι → ℝ) : ι → ℝ≥0∞ :=
  fun i => ENNReal.ofReal (π none * T.a i)

open Classical in
/-- The matrix `U` (p. 291): the infinitesimal generator of the process in the local time of the
node `s{·}` before the first passage to `∅`. Its `(i, j)` entry is the rate `Q_{(i)(j)}` of a
direct transition inside `s{·}`, plus, for every transition out of `s{·}` to a state `z ∉ s{·}`,
`z ≠ ∅`, its rate times the probability that the process, started from `z`, enters
`s{·} ∪ {∅}` for the first time in the state `(j)`. Transitions to `∅` end the local time. -/
def matU (T : TreeData ι) : ι → ι → ℝ :=
  fun i j => gen T (some ([], i)) (some ([], j)) +
    ∑' z : TreeState ι,
      if z ∈ node ([] : List ι) ∨ z = none then 0
      else gen T (some ([], i)) z *
        (firstEntryProb (jumpP (gen T)) (node ([] : List ι) ∪ {none}) z
          (some ([], j))).toReal

end

end MatrixAnalytic.Tree


