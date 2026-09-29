-- Prove2me | Definitions.Def_HarelTarjan_PointerLB_PointerMachine
-- name    : HarelTarjan_PointerLB_PointerMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:38:36.421155+00:00
-- url     : https://prove2.me/theorems/2caa56c6-b4ac-407b-8350-0edd2680ea0c
-- title:
--   List structures with two pointers per node, accessibility in $j$ steps, and answering nca queries in $k$ steps
-- statement:
--   The pointer-machine model of Harel and Tarjan's §2. The tree $T$ is represented by a list structure: a collection $N$ of nodes, each with two pointer fields. A pointer field of node $m$ contains either a node or nil. Every tree vertex $v$ is represented by a node $\mathrm{rep}(v)$; the structure may contain further nodes that represent no vertex.
--
--   1. **Accessibility.** The set $\mathrm{acc}_j(a)$ of nodes accessible from the node $a$ in $j$ steps or less is defined by
--   $$\mathrm{acc}_0(a) = \{a\}, \qquad \mathrm{acc}_{j+1}(a) = \mathrm{acc}_j(a) \cup \{\, b : b \text{ is the content of a pointer field of some } m \in \mathrm{acc}_j(a) \,\}.$$
--   2. **Runs.** On a query the machine is given pointers to two input nodes $a$ and $b$. A run of $t$ steps is a sequence of nodes $n_1, \dots, n_t$ such that each $n_s$ is the content of a pointer field of a node in $\{a, b, n_1, \dots, n_{s-1}\}$: each step follows one pointer out of a node the machine already holds. After the run the machine holds $\{a, b, n_1, \dots, n_t\}$.
--   3. **Answering.** A query with inputs $a, b$ and answer node $c$ is answered in $k$ steps if some run of at most $k$ steps from $a, b$ holds $c$. The representation answers every nca query on leaves in $k$ steps if, for all leaves $x, y$ of $T$, the query with inputs $\mathrm{rep}(x), \mathrm{rep}(y)$ and answer node $\mathrm{rep}(\operatorname{nca}(x,y))$ is answered in $k$ steps.
--   4. **The sets $A_x$.** For a leaf $x$, $A_x$ is the set of tree vertices $t$ whose node $\mathrm{rep}(t)$ is accessible from $\mathrm{rep}(x)$ in $k$ steps or less.
--
--   These are the objects of the proof of Theorem 1 at "the time just before a query".
--
--   **Formalization Note** Nodes form an arbitrary type `N` (not necessarily finite) and `ptr m i : Option N` for `i : Fin 2` is field `i` of node `m`; the paper allows any fixed number of pointers per node and reduces it to two "without loss of generality", and two is the model here. `Run ptr a b t held` is an inductive predicate; `AnsweredIn` asks only that *some* run of at most `k` steps reaches the answer, which is weaker than asking one algorithm to find it, so lower bounds proved against it are stronger. Mutation of the structure during a query, non-pointer fields and the other operations of the machine are not modelled: they do not let a machine hold a pointer to a node it has not reached by following pointers, and every step that follows a pointer costs at least one unit of time.
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), pp. 338–339, §1 (pointer machines); p. 340, §2, second paragraph (assumptions on the representation) and proof of Theorem 1 (accessibility, the sets A_x)

import Mathlib
import Definitions.Def_HarelTarjan_PointerLB_BinaryTree

namespace HarelTarjan.PointerLB

/-- The nodes accessible from the node `a` in `j` steps or less (proof of Theorem 1, p. 340), in a
list structure on the node type `N` in which every node has two pointer fields: `ptr m i` is the
content of field `i` of node `m`, either a node (`some b`) or nil (`none`).
`acc ptr 0 a = {a}`, and a node is accessible in `j + 1` steps or less if it is accessible in `j`
steps or less, or is the content of a pointer field of such a node. -/
def acc {N : Type*} (ptr : N → Fin 2 → Option N) : ℕ → N → Set N
  | 0, a => {a}
  | j + 1, a => acc ptr j a ∪ {b | ∃ m ∈ acc ptr j a, ∃ i : Fin 2, ptr m i = some b}

/-- A run of a pointer machine that answers a query (§2, p. 340). The machine is given pointers to
the two input nodes `a` and `b`; `Run ptr a b t held` says that after `t` steps it can hold
pointers to exactly the nodes in the list `held`. Each step dereferences one pointer field of a
node it already holds and adds the node found there. -/
inductive Run {N : Type*} (ptr : N → Fin 2 → Option N) (a b : N) : ℕ → List N → Prop
  | start : Run ptr a b 0 [a, b]
  | step {t : ℕ} {held : List N} {m n : N} (i : Fin 2) :
      Run ptr a b t held → m ∈ held → ptr m i = some n → Run ptr a b (t + 1) (n :: held)

/-- A query with input nodes `a`, `b` whose answer is the node `target` can be answered in `k`
steps: some run of at most `k` steps from `a`, `b` holds a pointer to `target`. -/
def AnsweredIn {N : Type*} (ptr : N → Fin 2 → Option N) (a b target : N) (k : ℕ) : Prop :=
  ∃ t ≤ k, ∃ held : List N, Run ptr a b t held ∧ target ∈ held

/-- The list structure `ptr`, in which the tree vertex `v` is represented by the node `rep v`,
answers every nca query on two leaves in `k` steps: for all leaves `x`, `y`, a run of at most `k`
steps from `rep x`, `rep y` reaches the node `rep (nca x y)` representing their nearest common
ancestor. -/
def AnswersLeafQueriesIn {N : Type*} {h : ℕ} (ptr : N → Fin 2 → Option N) (rep : Vertex h → N)
    (k : ℕ) : Prop :=
  ∀ x y : Vertex h, IsLeaf x → IsLeaf y → AnsweredIn ptr (rep x) (rep y) (rep (nca x y)) k

/-- `A_x` (proof of Theorem 1, p. 340): the tree vertices whose representing nodes are accessible
from the node representing `x` in `k` steps or less. -/
def A {N : Type*} {h : ℕ} (ptr : N → Fin 2 → Option N) (rep : Vertex h → N) (k : ℕ)
    (x : Vertex h) : Set (Vertex h) :=
  {t | rep t ∈ acc ptr k (rep x)}

end HarelTarjan.PointerLB


