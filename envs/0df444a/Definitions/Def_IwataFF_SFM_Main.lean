-- Prove2me | Definitions.Def_IwataFF_SFM_Main
-- name    : IwataFF_SFM_Main
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:41:31.997781+00:00
-- url     : https://prove2.me/theorems/f418a8a9-0841-488c-912f-f4d8706a6e36
-- title:
--   The strongly polynomial algorithm of Figure 3: $D = (V,F)$, $R(v)$, $f_v$, consistent orderings, $\eta$ (4.1), contraction, deletion, steps and runs (§4, pp. 12–14)
-- statement:
--   **Generic notions** on a ground set $V$ with arc set $F \subseteq V \times V$ (the digraph $D = (V, F)$):
--   - $R(v)$ = the vertices of $V$ reachable from $v$ in $D$, including $v$.
--   - $f_v(X) = f(X \cup R) - f(R)$ with $R = R(v)$.
--   - A linear ordering $(v_1, \dots, v_k)$ is **consistent** with $D$ if $i < j$ implies $(v_i, v_j) \notin F$.
--   - $\eta = \max\{f(R(v)) - f(R(v) \setminus \{v\}) \mid v \in V\}$ (4.1), and $0$ for $V = \emptyset$.
--   - $(u, v)$ is **compatible** with $f$ if $u \in X$ implies $v \in X$ for every minimizer $X$ of $f$.
--
--   **The algorithm of Figure 3** on $f : 2^{\{0,\dots,n-1\}} \to \mathbb{R}$. A state holds the current underlying set as a family of disjoint blocks of original elements (a contracted vertex is the union of what it represents), the arcs $F$ between blocks, the output set $X$ built so far, the current function $h$ on original subsets (the function on a set of blocks is $h$ of their union), and a control point: at the head of the loop, inside Fix (with the case, $u$, $\eta$ and the scaling state), or finished with an output.
--   - **Initial state**: every element its own block, $F = \emptyset$, $X = \emptyset$, $h = f$, at the loop head.
--   - **Finish**: at the loop head with $V = \emptyset$; or with $V \neq \emptyset$, after the cap "if $f(V) > 0$ then $f(V) \leftarrow 0$", when $\eta \le 0$. The output is $X \cup Q$ if $f(V) < 0$ ($Q$ the original set represented by $V$), else $X$.
--   - **Call**: at the loop head with $V \ne \emptyset$: apply the cap, require $\eta > 0$, let $u \in V$ attain (4.1); the case is *former* if $f(R(u)) \ge \eta/2$. Choose a linear ordering consistent with $D$ of $V \setminus R(u)$ (former) or $V$ (latter) and start Fix with the greedy base of $f_u$ (former) or $f$ (latter), $\delta = \eta$, $\varphi = 0$.
--   - **Fix step**: one Fix step (with $\kappa = \eta/2$) on that ground set and function.
--   - **Return** with a Fix output $w$: former case with $u \in R(w)$: contract $C = \{v \in R(w) \mid u \in R(v)\}$ to one vertex (arcs redirected, arcs inside $C$ dropped, $h$ unchanged); former case with $u \notin R(w)$: $F \leftarrow F \cup \{(u, w)\}$; latter case: $V \leftarrow V \setminus R(w)$, $h \leftarrow (S \mapsto h(S \cup Q) - h(Q))$, $X \leftarrow X \cup Q$ with $Q$ the original set represented by $R(w)$, arcs touching $R(w)$ dropped.
--   - A **step** is one of these four; a **run** of $k$ steps starts at the initial state; a state is **final** when it has an output. `callCount` counts the calls of Fix along a run.
--
--   **Formalization Note** Every push and every augmentation of every Fix call is a step of its own, so a bound on run lengths counts the paper's dominant operations. The arithmetic cost of a single step (O(1) or O(n) for a push, O(n³) for the reduction) is not modeled. Fix returns any element with $x(w) < -n^2\delta$, since the paper's Fix sees only $f$, $x$ and $\eta$. Where Figure 3 leaves a choice (the maximizer $u$, the consistent ordering, the active pair, the path, the subfamily, $w$), the step relation allows every choice.
-- source:
--   Iwata, Fleischer & Fujishige, A Combinatorial, Strongly Polynomial-Time Algorithm for Minimizing Submodular Functions, arXiv:math/0004089v1, pp. 12–14, (4.1), Figure 3 (p. 14)

import Mathlib
import Definitions.Def_IwataFF_SFM_Basic
import Definitions.Def_IwataFF_SFM_Phase

namespace IwataFF.SFM

/-! Iwata, Fleischer & Fujishige, arXiv:math/0004089v1, §4, pp. 12–14, Figure 3: the strongly
polynomial algorithm.

Part 1 (generic ground set `V : Finset α`): the digraph `D = (V, F)`, `R(v)`, `f_v`, consistent
orderings, `η` of (4.1), compatible pairs.

Part 2: the algorithm of Figure 3 on `f : Finset (Fin n) → ℝ`. The current underlying set is a
family `blocks` of pairwise disjoint nonempty subsets of the original set `Fin n` (a contracted
vertex is the union of the original elements it represents); the current function is
`h : Finset (Fin n) → ℝ`, read on a set of blocks through the union of its blocks. Contraction
merges blocks and keeps `h`; deletion of `R(w)` removes its blocks, adds their union to the
output `X`, and replaces `h` by `S ↦ h(S ∪ Q) − h(Q)`, `Q = ⋃ R(w)` (that is, `f ← f_w`). -/

section Generic

variable {α : Type} [DecidableEq α]

open Classical in
/-- p. 12: `R(v)`, the set of vertices of `V` reachable from `v` in `D = (V, F)` (including
`v` itself when `v ∈ V`). -/
noncomputable def reach (V : Finset α) (F : Finset (α × α)) (v : α) : Finset α :=
  V.filter (fun b => Relation.ReflTransGen (fun a c => (a, c) ∈ F) v b)

/-- p. 12: `f_v(X) = f(X ∪ R) − f(R)` for `X ⊆ V \ R`, with `R = R(v)`. -/
def restrictFun (f : Finset α → ℝ) (R : Finset α) : Finset α → ℝ :=
  fun X => f (X ∪ R) - f R

/-- p. 13: a linear ordering `(v₁, …, v_k)` is consistent with `D = (V, F)` if `i < j` implies
`(v_i, v_j) ∉ F`. -/
def IsConsistent (F : Finset (α × α)) (L : List α) : Prop :=
  ∀ i j : ℕ, i < j → ∀ a b : α, L[i]? = some a → L[j]? = some b → (a, b) ∉ F

/-- (4.1), p. 13: `η = max{f(R(v)) − f(R(v) \ {v}) | v ∈ V}` (`0` when `V = ∅`, a case the
algorithm never evaluates). -/
noncomputable def etaVal (V : Finset α) (F : Finset (α × α)) (f : Finset α → ℝ) : ℝ :=
  if h : V.Nonempty then
    V.sup' h (fun v => f (reach V F v) - f ((reach V F v).erase v))
  else 0

/-- p. 12: the ordered pair `(u, v)` is compatible with `f`: `u ∈ X` implies `v ∈ X` for every
minimizer `X` of `f`. -/
def Compatible (V : Finset α) (f : Finset α → ℝ) (u v : α) : Prop :=
  ∀ X, IsMinimizer V f X → u ∈ X → v ∈ X

end Generic

/-- The control point of Figure 3: at the head of the `While` loop; inside `Fix` (with the
case, the element `u` attaining (4.1), the value `η`, and the scaling-phase state); or
finished with output `X`. `former = true` is the case `f(R(u)) ≥ η/2`. -/
inductive Mode (n : ℕ) where
  | loop : Mode n
  | fix (former : Bool) (u : Finset (Fin n)) (eta : ℝ) (ph : PhaseState (Finset (Fin n))) :
      Mode n
  | done (out : Finset (Fin n)) : Mode n

/-- A state of the algorithm of Figure 3. -/
structure MainState (n : ℕ) where
  /-- the current underlying set `V`, each vertex a block of original elements -/
  blocks : Finset (Finset (Fin n))
  /-- the arc set `F` of `D` -/
  arcs : Finset (Finset (Fin n) × Finset (Fin n))
  /-- the set `X` built so far -/
  acc : Finset (Fin n)
  /-- the current function, read on unions of blocks -/
  h : Finset (Fin n) → ℝ
  /-- the control point -/
  mode : Mode n

namespace MainState

variable {n : ℕ}

/-- The current submodular function `f` on sets of blocks: `f(𝒳) = h(⋃ 𝒳)`. -/
def curFun (s : MainState n) : Finset (Finset (Fin n)) → ℝ :=
  fun X => s.h (X.biUnion id)

/-- `R(v)` in the current `D`. -/
noncomputable def R (s : MainState n) (v : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  reach s.blocks s.arcs v

/-- The ground set `Fix` is called on: `V \ R(u)` in the former case, `V` in the latter. -/
noncomputable def fixGround (s : MainState n) (former : Bool) (u : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  if former then s.blocks \ s.R u else s.blocks

/-- The function `Fix` is called on: `f_u` in the former case, `f` in the latter. -/
noncomputable def fixFun (s : MainState n) (former : Bool) (u : Finset (Fin n)) :
    Finset (Finset (Fin n)) → ℝ :=
  if former then restrictFun s.curFun (s.R u) else s.curFun

/-- Figure 3: "If `f(V) > 0` then `f(V) ← 0`". -/
noncomputable def cap (s : MainState n) : MainState n :=
  { s with h := fun S => if S = s.blocks.biUnion id ∧ 0 < s.h S then 0 else s.h S }

open Classical in
/-- Figure 3, after the loop: `X ∪ Q` with `Q` the original set represented by `V` if
`f(V) < 0`, else `X`. -/
noncomputable def finalOut (s : MainState n) : Finset (Fin n) :=
  s.acc ∪ (if s.h (s.blocks.biUnion id) < 0 then s.blocks.biUnion id else ∅)

open Classical in
/-- Figure 3: "Contract `{v | v ∈ R(w), u ∈ R(v)}` to a single vertex": the blocks of
`C = {v ∈ R(w) | u ∈ R(v)}` are merged into their union; arcs incident to `C` are redirected
to the new vertex and arcs inside `C` disappear. `h` is unchanged. -/
noncomputable def contract (s : MainState n) (u w : Finset (Fin n)) : MainState n :=
  let C := (s.R w).filter (fun v => u ∈ s.R v)
  let B := C.biUnion id
  let m : Finset (Fin n) → Finset (Fin n) := fun b => if b ∈ C then B else b
  { s with blocks := insert B (s.blocks \ C),
           arcs := (s.arcs.image (fun e => (m e.1, m e.2))).filter (fun e => e.1 ≠ e.2),
           mode := Mode.loop }

/-- Figure 3: `F ← F ∪ {(u, w)}`. -/
def addArc (s : MainState n) (u w : Finset (Fin n)) : MainState n :=
  { s with arcs := insert (u, w) s.arcs, mode := Mode.loop }

open Classical in
/-- Figure 3: `V ← V \ R(w)`, `f ← f_w`, `X ← X ∪ Q` with `Q` the original set represented by
`R(w)`; arcs with an endpoint in `R(w)` disappear with their endpoints. -/
noncomputable def delete (s : MainState n) (w : Finset (Fin n)) : MainState n :=
  let Rw := s.R w
  let Q := Rw.biUnion id
  { blocks := s.blocks \ Rw,
    arcs := s.arcs.filter (fun e => e.1 ∉ Rw ∧ e.2 ∉ Rw),
    acc := s.acc ∪ Q,
    h := fun S => s.h (S ∪ Q) - s.h Q,
    mode := Mode.loop }

end MainState

open MainState

/-- Figure 3, initialization: `V = Fin n` (each element its own block), `X ← ∅`, `F ← ∅`. -/
def initMain {n : ℕ} (f : Finset (Fin n) → ℝ) : MainState n :=
  { blocks := Finset.univ.image (fun a => ({a} : Finset (Fin n))), arcs := ∅, acc := ∅,
    h := f, mode := Mode.loop }

/-- Figure 3, the loop ends: either `V = ∅`, or (after the cap) `η ≤ 0` ("break"); the output
is `X ∪ Q` if `f(V) < 0`, else `X`. -/
def FinishStep {n : ℕ} (s s' : MainState n) : Prop :=
  s.mode = Mode.loop ∧
    ((s.blocks = ∅ ∧ s' = { s with mode := Mode.done (finalOut s) }) ∨
     (s.blocks.Nonempty ∧ etaVal s.cap.blocks s.cap.arcs s.cap.curFun ≤ 0 ∧
        s' = { s.cap with mode := Mode.done (finalOut s.cap) }))

/-- Figure 3, one loop iteration up to the call of `Fix`: cap `f(V)`, compute `η > 0`, let `u`
attain the maximum in (4.1), choose the case by `f(R(u)) ≥ η/2`, find a consistent extreme base
of `f_u` on `V \ R(u)` (former case) or of `f` on `V` (latter case) by the greedy algorithm on a
linear ordering consistent with `D`, and start `Fix` from it with `δ = η` and `ϕ = 0`. -/
def CallStep {n : ℕ} (s s' : MainState n) : Prop :=
  s.mode = Mode.loop ∧ s.blocks.Nonempty ∧
    0 < etaVal s.cap.blocks s.cap.arcs s.cap.curFun ∧
    ∃ (u : Finset (Fin n)) (L : List (Finset (Fin n))),
      u ∈ s.blocks ∧
      s.cap.curFun (s.cap.R u) - s.cap.curFun ((s.cap.R u).erase u) =
        etaVal s.cap.blocks s.cap.arcs s.cap.curFun ∧
      let η := etaVal s.cap.blocks s.cap.arcs s.cap.curFun
      let former := decide (η / 2 ≤ s.cap.curFun (s.cap.R u))
      IsOrdering (s.cap.fixGround former u) L ∧ IsConsistent s.arcs L ∧
      s' = { s.cap with mode := Mode.fix former u η (initPhase L η) }

/-- Figure 3 inside `Fix(f', x, η)` (§4, p. 12, with `κ = η/2`): one step of the scaling
algorithm on the ground set and function of the call. -/
def FixPhaseStep {n : ℕ} (s s' : MainState n) : Prop :=
  ∃ (former : Bool) (u : Finset (Fin n)) (η : ℝ) (ph ph' : PhaseState (Finset (Fin n))),
    s.mode = Mode.fix former u η ph ∧
    FixInnerStep (s.fixFun former u) (s.fixGround former u) (η / 2) ph ph' ∧
    s' = { s with mode := Mode.fix former u η ph' }

/-- Figure 3, `w ← Fix(…)` and the rest of the iteration: in the former case contract if
`u ∈ R(w)`, else add the arc `(u, w)`; in the latter case delete `R(w)`. -/
def ReturnStep {n : ℕ} (s s' : MainState n) : Prop :=
  ∃ (former : Bool) (u : Finset (Fin n)) (η : ℝ) (ph : PhaseState (Finset (Fin n)))
    (w : Finset (Fin n)),
    s.mode = Mode.fix former u η ph ∧
    FixOutput (s.fixFun former u) (s.fixGround former u) (η / 2) ph w ∧
    ((former = true ∧ u ∈ s.R w ∧ s' = s.contract u w) ∨
     (former = true ∧ u ∉ s.R w ∧ s' = s.addArc u w) ∨
     (former = false ∧ s' = s.delete w))

/-- One step of the algorithm of Figure 3 (with `Fix` and its scaling phases inlined): every
push and every augmentation is a step of its own. -/
def Step {n : ℕ} (s s' : MainState n) : Prop :=
  FinishStep s s' ∨ CallStep s s' ∨ FixPhaseStep s s' ∨ ReturnStep s s'

/-- The algorithm has stopped, with output `X`. -/
def IsFinal {n : ℕ} (s : MainState n) : Prop :=
  ∃ X, s.mode = Mode.done X

/-- A run of `k` steps of Figure 3 on `f` from its initial state. -/
def IsRun {n : ℕ} (f : Finset (Fin n) → ℝ) (s : ℕ → MainState n) (k : ℕ) : Prop :=
  s 0 = initMain f ∧ ∀ j < k, Step (s j) (s (j + 1))

open Classical in
/-- The number of calls of `Fix` among the steps `s j → s (j+1)`, `j < k`. -/
noncomputable def callCount {n : ℕ} (s : ℕ → MainState n) (k : ℕ) : ℕ :=
  ((Finset.range k).filter (fun j => CallStep (s j) (s (j + 1)))).card

end IwataFF.SFM


