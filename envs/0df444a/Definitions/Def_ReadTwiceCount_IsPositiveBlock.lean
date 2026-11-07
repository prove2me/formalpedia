-- Prove2me | Definitions.Def_ReadTwiceCount_IsPositiveBlock
-- name    : ReadTwiceCount_IsPositiveBlock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:41:41.687214+00:00
-- url     : https://prove2.me/theorems/07727b7b-d11a-45e3-a829-578bc1060b90
-- title:
--   Partial computation trees, positive blocks, the frozen evaluation and the stopping rule
-- statement:
--   Fix a positive dangling query $(H,h)$.
--
--   1. A **partial computation tree** of $(H,h)$ is a descriptor tree in which every node is the descriptor of its state, with its retained children in descriptor order and below the $j$-th child a partial computation tree of that child's state; every constant is the exact value of a recognized exact case; and every leaf is an unresolved frontier input, carrying the state reached along its path.
--   2. A **positive block** of $(H,h)$ is a partial computation tree in which every $\mathrm{EQ}$ child is a frontier leaf (an EQ boundary input).
--   3. The **frozen evaluation** puts each cut input $u$ at the upper value $s_u+1$, where $s_u$ is the clause count of its state, and each EQ boundary input at $1$. The **frozen weights** $D_u$ are the path derivatives at this evaluation.
--   4. With a global clause bound $n$, $B=n+1$ and $\delta=a/B^3$ (12), the block meets the **stopping rule** if every cut input has $D_u\le\delta^2$.
--   5. The **block value** with boundary values $\ell_i$ is the root value with every cut input at $s_u+1$ and every EQ boundary input $i$ at $\ell_i$. The true coordinate of a frontier input is $y_u=y(H_u,h_u)$.
--
--   These are the objects of the block error certificate (Lemma 6.1) and of the marginal procedure.
-- source:
--   He, A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments, STOC 2027 submission (manuscript sha256 7a2a9dcd…), §4, p.5; §5.1, pp.6–7, display (12); §6, p.9

import Mathlib
import Definitions.Def_ReadTwiceCount_stateDesc
import Definitions.Def_ReadTwiceCount_DTree

namespace ReadTwiceCount

variable {M : ℕ}

/-- The state reached from the query `(H, h)` along a path of child indices: at each step, the
`j`-th retained child `(Hⱼ, zⱼ)` of the current descriptor. (A path that leaves the descriptor
structure stops at the last state reached; it is never used on such paths.) -/
def stateAt : Formula M → Lit M → List ℕ → Formula M × Lit M
  | H, h, [] => (H, h)
  | H, h, j :: p =>
      match stateDesc H h with
      | .desc _ cs =>
          match cs[j]? with
          | some c => stateAt c.2.1 c.2.2 p
          | none => (H, h)
      | _ => (H, h)

/-- **A partial computation tree of the query `(H, h)`** (He, *A Deterministic Approximation Scheme
for Counting Read-Twice CNF Assignments*, STOC 2027 submission, manuscript sha256 7a2a9dcd…, §4, p.5
and §5.1, p.6): every node is the descriptor of its state, with its children in descriptor order and,
below each child, a tree of that child's state; every constant is the exact value of a recognized
exact case; a leaf is an unresolved frontier input carrying its state. -/
def IsPCT : Formula M → Lit M → DTree → Prop
  | _, _, .leaf => True
  | H, h, .const r => ∃ q : ℚ, exactValue H h = some q ∧ r = (q : ℝ)
  | H, h, .node t n label child =>
      ∃ cs : List (Label × Formula M × Lit M), stateDesc H h = .desc t cs ∧
        ∃ hn : cs.length = n, ∀ j : Fin n,
          (cs.get (j.cast hn.symm)).1 = label j ∧
            IsPCT (cs.get (j.cast hn.symm)).2.1 (cs.get (j.cast hn.symm)).2.2 (child j)

/-- **A positive block of `(H, h)`** (He, STOC 2027 submission, manuscript sha256 7a2a9dcd…, §5.1,
p.6: "A positive block is a partial computation tree whose internal edges are all NEQ"): a partial
computation tree of `(H, h)` in which every `EQ` child is a frontier leaf (an EQ boundary input). -/
def IsPositiveBlock (H : Formula M) (h : Lit M) (T : DTree) : Prop :=
  IsPCT H h T ∧ T.EqChildrenAreLeaves

/-- The clause count `s_u` of the state at the path `u`. -/
def clauseCountAt (H : Formula M) (h : Lit M) (u : List ℕ) : ℕ := (stateAt H h u).1.clauses.length

/-- **The frozen evaluation** of a block (§5.1, p.6): every cut input `u` at its upper value
`s_u + 1`, every EQ boundary input at the fixed lower value `1`. -/
noncomputable def frozenInput (H : Formula M) (h : Lit M) (T : DTree) (u : List ℕ) : ℝ :=
  if T.lastLabel u = some .EQ then 1 else (clauseCountAt H h u : ℝ) + 1

/-- **The frozen path derivative `D_u`** of a frontier input of a block: the path derivative at the
frozen evaluation (§5.1, p.7: "Boundary allocation and interpolation use the weights at the final
frozen evaluation"). -/
noncomputable def frozenD (H : Formula M) (h : Lit M) (T : DTree) (u : List ℕ) : ℝ :=
  T.pathDeriv (frozenInput H h T) u

/-- **The stopping rule** with the global parameters `B = n + 1` and `δ = a/B³`, display (12)
(§5.1, p.7): no unresolved cut input `u` has `D_u > δ²`. -/
def StoppingRule (n : ℕ) (a : ℝ) (H : Formula M) (h : Lit M) (T : DTree) : Prop :=
  ∀ u ∈ T.cuts, frozenD H h T u ≤ (a / ((n : ℝ) + 1) ^ 3) ^ 2

/-- The true coordinate `y_u = y(H_u, h_u)` of the state at the path `u`. -/
def trueInput (H : Formula M) (h : Lit M) (u : List ℕ) : ℝ :=
  (yCoord (stateAt H h u).1 (stateAt H h u).2 : ℝ)

/-- **The block value with given boundary values** (§5.3, p.8 and Lemma 6.1, p.9): the root value of
the block with every cut input at its upper value `s_u + 1` and every EQ boundary input `i` at the
value `ℓ i`. -/
noncomputable def blockValue (H : Formula M) (h : Lit M) (T : DTree) (ℓ : List ℕ → ℝ) : ℝ :=
  T.eval fun u => if T.lastLabel u = some .EQ then ℓ u else (clauseCountAt H h u : ℝ) + 1

end ReadTwiceCount


