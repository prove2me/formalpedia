-- Prove2me | Definitions.Def_ChaChaTree_DynOpt_ChaChaProcess
-- name    : ChaChaTree_DynOpt_ChaChaProcess
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:21:57.096189+00:00
-- url     : https://prove2.me/theorems/7a44878e-c120-434f-8add-04c079d568e5
-- title:
--   The abstract Cha-cha process of Figure 11 and its counts Flips₁, Flips₂ and M
-- statement:
--   Let $n = 2^H$, $T_1$ and $T_2$ as in `RefTrees`, and let $B$ be the full binary tree with left subtree $T_2$ and right subtree the leaf $H$ (`refB`), so its leaves are $0,\dots,H$.
--
--   **State.** Primary preferences $T(v) \in \{\mathrm{LEFT}, \mathrm{RIGHT}\}$ at the internal vertices of $T_1$; for every leaf $z$, the secondary tree $T_z$ of the primary path $P_z$, with an entry at each internal $u = [a,b)$ of $B$: nonexistent, or a preference $\eta \in \{\mathrm{UP}, \mathrm{DOWN}\}$ (split or active); the leaf $z$ of the active path; and the counters $\mathrm{Flips}_1$, $\mathrm{Flips}_2$, $M$.
--
--   **Initial state.** Every primary preference is LEFT, so the active path ends at leaf $1$. For each leaf $w$, with $a_w$ the top depth of its primary path and sentinel $s = a_w - 1$ (none for the active path): $u = [a,b)$ is active ($s < a$) with preference UP, split ($s \in [a,b)$) with preference toward the sentinel, or nonexistent ($b \le s$).
--
--   **Operations (Figure 11).**
--   * `ExposeDepth(d)`: in the active secondary tree $T_z$, set every ancestor $u$ of the leaf $d$ in $B$ toward $d$; each change is a secondary flip ($\mathrm{Flips}_2 \mathrel{+}= 1$). Every call counts toward $M$.
--   * `SwitchHead()`: with $d$ the exposed leaf of $T_z$, flip $T(v)$ at $v = \mathrm{anc}_d(z)$ ($\mathrm{Flips}_1 \mathrel{+}= 1$); let $z'$ be the new exposed leaf of $T$; swap $T_z(u) \leftrightarrow T_{z'}(u)$ for every internal $u = [a,b)$ of $B$ with $a \le d$ (the nonexistent and split vertices w.r.t. $d$); set $z \leftarrow z'$.
--   * `Access(x)`: while $z \neq x$: $d \leftarrow \mathrm{depth}(\mathrm{lca}(z,x))$, `ExposeDepth(d)`, `SwitchHead()`; then `ExposeDepth(H)`.
--
--   $\mathrm{Flips}_1(X)$, $\mathrm{Flips}_2(X)$ and $M(X)$ (the number of `ExposeDepth` calls, including `ExposeDepth(H)` for every access) are read off after running the accesses of $X$ in order from the initial state.
--
--   **Formalization Note.** The fragment identifiers $q$ stored at active entries are omitted: no step of Figure 11 reads them, so the three counts do not depend on them. The `while` loop runs with a budget of $H+1$ iterations; it never needs more than $H$, because each iteration strictly increases $\mathrm{depth}(\mathrm{lca}(z,x)) < H$ (the leaf exposed after `SwitchHead` lies below the child of $\mathrm{lca}(z,x)$ toward $x$; first sentence of Lemma 22).
-- source:
--   Čech, Haeupler, Roeyskoe, Rozhoň, Tarjan, Yingchareonthawornchai, Dynamic Optimality to within O(log log log n), STOC 2027 submission (manuscript, sha256 9316fbfd…7b9e), §5.2, pp. 22–25 (PDF 23–26), Figure 11 (p. 25, PDF 26); M(X) on p. 34 (PDF 35)

import Mathlib
import Definitions.Def_ChaChaTree_DynOpt_RefTrees

set_option autoImplicit false

namespace ChaChaTree.DynOpt

/-! # The abstract Cha-cha process (§5.2, Figure 11) and its counters `Flips₁`, `Flips₂`, `M`

Čech et al., *Dynamic Optimality to within O(log log log n)*, STOC 2027 submission (manuscript,
sha256 9316fbfd…), §5.2, pp. 22–25 (PDF 23–26), Figure 11 (p. 25, PDF 26); `M(X)` on p. 34
(PDF 35).

Setting: `n = 2^H`, `T₁` the perfect leaf-oriented tree on `[n]` (see `RefTrees`), `T₂` a full
binary tree with leaves `0, …, H − 1`, and `B = node T₂ leaf` the secondary reference tree with
leaves `0, …, H` (left subtree `T₂`, right subtree the leaf `H`). An internal vertex `u = [a, b)`
of `B` is keyed by the pair `(a, b)`.

**Encoding of the state.**
* Primary preferences `T(v) ∈ {LEFT, RIGHT}` at internal vertices `v = (j, i)` of `T₁`:
  `pref₁ (j, i) = true` means RIGHT.
* Secondary entries `T_z(u)` of the secondary tree of the primary path `P_z` (leaf key `z`):
  `sec z (a, b) = none` is `(⊥, ⊥)` (nonexistent), `some η` is a split or active entry with
  preference `η` (`true` = DOWN, `false` = UP). The fragment identifiers `q` of active entries
  are not stored: no step of Figure 11 reads them (they are carried along by the same swaps),
  so `Flips₁`, `Flips₂` and `M` do not depend on them.
* `z`, the leaf of the active path, and the counters `Flips₁`, `Flips₂`, `M` (the number of
  `ExposeDepth` calls). -/

/-- The state of the abstract Cha-cha process. -/
structure ChaChaState where
  /-- Primary preferred child `T(v)` of the internal vertex `v = (j, i)` of `T₁`; `true` = RIGHT. -/
  pref₁ : ℕ × ℕ → Bool
  /-- Secondary entry `T_z(u)` at `u = [a, b) ∈ B`: `none` = nonexistent, `some true` = DOWN,
  `some false` = UP. -/
  sec : ℕ → ℕ × ℕ → Option Bool
  /-- The leaf `z` whose primary path `P_z` is the active path. -/
  z : ℕ
  /-- Number of primary flips so far. -/
  flips₁ : ℕ
  /-- Number of secondary flips so far. -/
  flips₂ : ℕ
  /-- Number of `ExposeDepth` calls so far. -/
  exposeCalls : ℕ

/-- The secondary reference tree `B`: left subtree `T₂`, right subtree the leaf `H`. -/
def refB (T₂ : FBT) : FBT := .node T₂ .leaf

/-- The internal vertices `(a, c, b)` of `B` (interval `[a, b)`, children `[a, c)`, `[c, b)`). -/
def bInternals (T₂ : FBT) : List (ℕ × ℕ × ℕ) := (refB T₂).internals 0

/-- The exposed leaf of a secondary tree with entries `e`: follow the preferred children from the
root of the full binary tree `t` (leaves numbered from `a`): to `[a, c)` on UP, to `[c, b)` on
DOWN. -/
def exposedLeafSec : FBT → ℕ → (ℕ × ℕ → Option Bool) → ℕ
  | .leaf, a, _ => a
  | .node l r, a, e =>
      if e (a, a + l.numLeaves + r.numLeaves) = some true then
        exposedLeafSec r (a + l.numLeaves) e
      else exposedLeafSec l a e

/-- Descend `s` levels in `T₁` from the vertex `(j, i)` along the primary preferred children;
returns the position reached. -/
def descendPref (pref₁ : ℕ × ℕ → Bool) : ℕ → ℕ → ℕ → ℕ
  | 0, _, i => i
  | s + 1, j, i => descendPref pref₁ s (j + 1) (2 * i + if pref₁ (j, i) then 1 else 0)

/-- The exposed leaf of `T` (the leaf key at the bottom of the root primary path). -/
def exposedLeafT (H : ℕ) (pref₁ : ℕ × ℕ → Bool) : ℕ := descendPref pref₁ H 0 0 + 1

/-- **`ExposeDepth(d)`** (Figure 11): in the active secondary tree `T_z`, set the preferred child
of every ancestor `u = [a, b)` of the leaf `d` in `B` (`a ≤ d < b`) toward `d` (DOWN iff
`d ≥ c`); each change is one secondary flip. Also counts the call. -/
def exposeDepth (T₂ : FBT) (d : ℕ) (st : ChaChaState) : ChaChaState :=
  let st' := (bInternals T₂).foldl
    (fun s f =>
      if f.1 ≤ d ∧ d < f.2.2 then
        let want : Option Bool := some (decide (f.2.1 ≤ d))
        if s.sec s.z (f.1, f.2.2) = want then s
        else { s with
          sec := Function.update s.sec s.z (Function.update (s.sec s.z) (f.1, f.2.2) want),
          flips₂ := s.flips₂ + 1 }
      else s)
    st
  { st' with exposeCalls := st'.exposeCalls + 1 }

/-- **`SwitchHead()`** (Figure 11): with `d` the exposed leaf of `T_z`, flip the primary preference
`T(v)` at `v = anc_d(z)` (one primary flip); let `z'` be the new exposed leaf of `T`; swap
`T_z(u) ↔ T_{z'}(u)` for every internal `u = [a, b) ∈ B_{≤d}` (nonexistent or split w.r.t. `d`,
i.e. `a ≤ d`); set `z ← z'`. -/
def switchHead (H : ℕ) (T₂ : FBT) (st : ChaChaState) : ChaChaState :=
  let d := exposedLeafSec (refB T₂) 0 (st.sec st.z)
  let v : ℕ × ℕ := (d, ancIdx H d st.z)
  let pref₁' := Function.update st.pref₁ v (!st.pref₁ v)
  let z' := exposedLeafT H pref₁'
  let inBle : ℕ × ℕ → Bool := fun u =>
    decide (u ∈ (bInternals T₂).filterMap fun f => if f.1 ≤ d then some (f.1, f.2.2) else none)
  { st with
    pref₁ := pref₁'
    sec := fun w u =>
      if inBle u then
        (if w = st.z then st.sec z' u else if w = z' then st.sec st.z u else st.sec w u)
      else st.sec w u
    z := z'
    flips₁ := st.flips₁ + 1 }

/-- The `while z ≠ x` loop of `Access(x)` (Figure 11), run with a budget of `fuel` iterations:
`d ← depth(lca(z, x))`, `ExposeDepth(d)`, `SwitchHead()`. -/
def accessLoop (H : ℕ) (T₂ : FBT) (x : ℕ) : ℕ → ChaChaState → ChaChaState
  | 0, st => st
  | fuel + 1, st =>
      if st.z = x then st
      else accessLoop H T₂ x fuel (switchHead H T₂ (exposeDepth T₂ (lcaDepth H st.z x) st))

/-- **`Access(x)`** (Figure 11): the `while` loop, then `ExposeDepth(H)`. The loop is given a
budget of `H + 1` iterations; it never needs more than `H`, since each iteration strictly increases
`depth(lca(z, x)) < H` (the new exposed leaf lies below the child of `lca(z, x)` toward `x`). -/
def access (H : ℕ) (T₂ : FBT) (x : ℕ) (st : ChaChaState) : ChaChaState :=
  exposeDepth T₂ H (accessLoop H T₂ x (H + 1) st)

/-- Top depth `a_w` of the primary path `P_w` through the leaf `w`: climb from the leaf while the
current vertex is the preferred child of its parent. -/
def topDepthAux (H : ℕ) (pref₁ : ℕ × ℕ → Bool) (w : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 =>
      if decide (ancIdx H (j + 1) w % 2 = 1) = pref₁ (j, ancIdx H j w) then
        topDepthAux H pref₁ w j
      else j + 1

/-- `a_w`, the depth of the topmost vertex of the primary path ending at leaf `w`. -/
def topDepth (H : ℕ) (pref₁ : ℕ × ℕ → Bool) (w : ℕ) : ℕ := topDepthAux H pref₁ w H

/-- The **initial state** (§5.2, p. 23 and p. 34): every primary preference is LEFT; the active
path ends at the leftmost leaf `1`; for every leaf `w`, the secondary tree of `P_w` has entries
w.r.t. the sentinel `s = a_w − 1` (none for the active path, `a_w = 0`): an internal
`u = [a, b) ∈ B` is active (`s < a`) with preference UP, split (`s ∈ [a, b)`) with preference
toward the sentinel (DOWN iff `s ≥ c`), or nonexistent (`b ≤ s`). -/
def initState (H : ℕ) (T₂ : FBT) : ChaChaState :=
  let pref₀ : ℕ × ℕ → Bool := fun _ => false
  { pref₁ := pref₀
    sec := fun w u =>
      match (bInternals T₂).find? (fun f => decide ((f.1, f.2.2) = u)) with
      | none => none
      | some f =>
          if topDepth H pref₀ w = 0 then some false
          else
            let s := topDepth H pref₀ w - 1
            if s < f.1 then some false
            else if s < f.2.2 then some (decide (f.2.1 ≤ s))
            else none
    z := exposedLeafT H pref₀
    flips₁ := 0
    flips₂ := 0
    exposeCalls := 0 }

/-- The state after serving the whole access sequence `X` from the initial state. -/
def runChaCha (H : ℕ) (T₂ : FBT) (X : List ℕ) : ChaChaState :=
  X.foldl (fun st x => access H T₂ x st) (initState H T₂)

/-- `Flips₁(X)`: the total number of primary flips. -/
def flips1 (H : ℕ) (T₂ : FBT) (X : List ℕ) : ℕ := (runChaCha H T₂ X).flips₁

/-- `Flips₂(X)`: the total number of secondary flips over all `ExposeDepth` operations. -/
def flips2 (H : ℕ) (T₂ : FBT) (X : List ℕ) : ℕ := (runChaCha H T₂ X).flips₂

/-- `M(X)`: the number of `ExposeDepth` calls, including the completion call `ExposeDepth(H)` of
every access (p. 34). -/
def exposeCount (H : ℕ) (T₂ : FBT) (X : List ℕ) : ℕ := (runChaCha H T₂ X).exposeCalls

end ChaChaTree.DynOpt


