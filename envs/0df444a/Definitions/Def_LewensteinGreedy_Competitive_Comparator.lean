-- Prove2me | Definitions.Def_LewensteinGreedy_Competitive_Comparator
-- name    : LewensteinGreedy_Competitive_Comparator
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:31:59.338735+00:00
-- url     : https://prove2.me/theorems/2fc24d62-c2c3-4161-8899-e9bc7c4c7dcf
-- title:
--   Comparator executions and their budgets $R$, $E$, $H$, $G$ (§2.3–2.4, eqs. (2.2)–(2.3))
-- statement:
--   A **comparator** for $X$ on $[n]$ is a separately evolving BST execution by single rotations: BSTs $T^*_0,\dots,T^*_R$ on $[n]$, where $T^*_{i+1}$ is obtained from $T^*_i$ by one rotation promoting a non-root key $a_i$ (the published `SplayDynOpt.IsRotationAt`). Each request $x_t$ is served at a designated state at which $x_t$ is the root; the designated states are visited in request order (repeated states, i.e. no rotation between two requests, are allowed). The initial comparator tree is arbitrary and no height or depth bound is part of the notion.
--
--   $R$ is the number of rotations; $d_i$ is the depth of the promoted key in $T^*_i$, immediately before the rotation; $E=\sum_{i=1}^R(1+d_i)$ (2.2); $H$ is the maximum depth of any key over the whole execution; $G=1+\mathrm{bitlen}(H)=F(H)$ (2.3).
--
--   **Formalization Note.** `Comparator` stores `rotations` $=R$, `tree i` $=T^*_i$, `promoted i` $=a_i$ and `time j`, the designated state of the $j$-th request (0-based). `serves n X`: all states $0..R$ are BSTs on $[n]$, every step is `IsRotationAt (promoted i)`, `time j ≤ R` and the root of `tree (time j)` is `X[j]`, and `time` is nondecreasing on the requests. `energy` $=E$, `height n` $=H$ (maximum edge depth of a key of $[n]$ over states $0..R$), `levels n` $=G$.
-- source:
--   Lewenstein, Greedy BST is O(log log n)-Competitive, supplied 2026 artifact (STOC 2027 submission; no DOI/arXiv/URL), SHA-256 04ac49f62855387e9d720867c8d3ded88730274553ff2fb8473a7a53b6906c4f, §2.3–2.4, eqs. (2.2)–(2.3), printed p. 7–8 / PDF 8–9

import Mathlib
import Definitions.Def_SplayDynOpt_IsBSTOn
import Definitions.Def_SplayDynOpt_rotateAt
import Definitions.Def_LewensteinGreedy_Competitive_Greedy

set_option autoImplicit false

namespace LewensteinGreedy.Competitive

/-!
# Comparator executions and their budgets `R`, `E`, `H`, `G`

Lewenstein, *Greedy BST is O(log log n)-Competitive*, supplied 2026 artifact (SHA-256
04ac49f6…), §2.3 printed p.7 / PDF 8 and §2.4 printed p.8 / PDF 9, equations (2.2)–(2.3).

A comparator is a separately evolving BST execution by rotations: states
`tree 0, tree 1, …, tree R`, where `tree (i+1)` is obtained from `tree i` by one rotation promoting
the non-root key `promoted i` (`SplayDynOpt.IsRotationAt`). The `j`-th request (0-based) is served
at the designated state `time j`, at which the requested key `X[j]` is the root; designated states
are visited in request order (`time` nondecreasing on the requests; repeated states, i.e. zero
rotations between requests, are allowed). The initial comparator tree is arbitrary. No bound on
height or rotation depth is part of the notion (Theorem 2.4 holds for every comparator).

* `energy = E = ∑_{i<R} (1 + d_i)`, with `d_i = depth (promoted i) (tree i)`, the edge depth of the
  promoted key immediately before its rotation.
* `height n = H`: the maximum edge depth of a key of `[n]` over all states `0..R`.
* `levels n = G = 1 + bitlen H = F(H)`.
-/

/-- A finite rotation schedule with designated access states. -/
structure Comparator where
  /-- The number `R` of rotations. -/
  rotations : ℕ
  /-- The comparator BST after `i` rotations. -/
  tree : ℕ → BinaryTree ℕ
  /-- The key promoted by the `i`-th rotation. -/
  promoted : ℕ → ℕ
  /-- The designated state at which the `j`-th request is served. -/
  time : ℕ → ℕ

/-- The comparator serves `X` on `[n]`: all states are BSTs on `[n]`, consecutive states differ by
one rotation of a non-root key, and each request is at the root of its designated state, the
designated states being visited in request order. -/
def Comparator.serves (e : Comparator) (n : ℕ) (X : List ℕ) : Prop :=
  (∀ i ≤ e.rotations, SplayDynOpt.IsBSTOn n (e.tree i)) ∧
  (∀ i < e.rotations, SplayDynOpt.IsRotationAt (e.promoted i) (e.tree i) (e.tree (i + 1))) ∧
  (∀ j : Fin X.length, e.time j.val ≤ e.rotations ∧
    SplayDynOpt.root (e.tree (e.time j.val)) = some X[j]) ∧
  (∀ i j, i ≤ j → j < X.length → e.time i ≤ e.time j)

/-- `E = ∑_{i=1}^{R} (1 + d_i)` of (2.2). -/
def Comparator.energy (e : Comparator) : ℕ :=
  ∑ i ∈ Finset.range e.rotations, (1 + SplayDynOpt.depth (e.promoted i) (e.tree i))

/-- `H`: the maximum edge depth of a key of `[n]` over the whole execution. -/
def Comparator.height (e : Comparator) (n : ℕ) : ℕ :=
  (Finset.range (e.rotations + 1)).sup fun i =>
    (Finset.Icc 1 n).sup fun v => SplayDynOpt.depth v (e.tree i)

/-- `G = 1 + bitlen H` of (2.3). -/
def Comparator.levels (e : Comparator) (n : ℕ) : ℕ := label (e.height n)

end LewensteinGreedy.Competitive


