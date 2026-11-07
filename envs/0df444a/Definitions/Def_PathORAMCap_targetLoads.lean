-- Prove2me | Definitions.Def_PathORAMCap_targetLoads
-- name    : PathORAMCap_targetLoads
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:49:16.954362+00:00
-- url     : https://prove2.me/theorems/88b0f2e2-e196-4fb7-948b-0d433e571890
-- title:
--   Targets $d_t(b)$ and target loads $A(t)$
-- statement:
--   Fix an instance $(s,\alpha)$ and a realization of the labels. Let $x_j$ be the old label read at access $j$, $I_t=\{a_1,\dots,a_t\}$ the blocks created by time $t$, $\tau_t(b)$ the last access time of $b\in I_t$ at or before $t$, and $y_b$ the current label of $b$. The **target** of $b$ after access $t$ is
--
--   $$d_t(b)=\text{the deepest node among }\{\mathrm{lcp}(y_b,x_j):\tau_t(b)\le j\le t\},$$
--
--   the deepest bucket in which the paths read since its last access (including that access, whose refill follows the relabeling) have offered $b$ a place. The **target loads** are
--
--   $$A_v(t)=\bigl|\{b\in I_t:d_t(b)=v\}\bigr|,\qquad A(t)=(A_v(t))_v.$$
--
--   They depend on the access sequence and the labels, not on the bucket capacity, and they turn the stash into the root overflow of upward packing (Lemma 5.1).
--
--   **Formalization Note** Accesses are indexed from $0$ in Lean, so the times $\tau_t(b)\le j\le t$ are the indices from the last access of $b$ to $t-1$. All candidate nodes lie on $\mathrm{path}(y_b)$, so the deepest is the prefix of $y_b$ of the largest candidate length.
-- source:
--   Chang, Au, The Minimum Bucket Capacity for Reliable Path ORAM, STOC 2027 submission (manuscript sha256 1762f048…), §4.3.1, p.16 (PDF p.19), eq. (19); §5.2.1, p.37 (PDF p.40); App. A.1, p.50 (PDF p.53), eq. (59)

import Mathlib
import Definitions.Def_PathORAMCap_stashSize

set_option autoImplicit false

namespace PathORAMCap

/-- The position map after `t` accesses (labels only; it does not depend on the bucket capacity):
initial labels `ω.1`, and access `j + 1` relabels `α j` with `ω.2 j` (Chang, Au, *The Minimum Bucket
Capacity for Reliable Path ORAM*, STOC 2027 submission (manuscript sha256 1762f048…), §4.3.1, p.16
(PDF p.19)). -/
def posAfter {N s : ℕ} (α : Fin s → Fin N) (ω : Labels N s) : ℕ → Fin N → Leaf (treeDepth N)
  | 0 => ω.1
  | t + 1 => if h : t < s then Function.update (posAfter α ω t) (α ⟨t, h⟩) (ω.2 ⟨t, h⟩)
      else posAfter α ω t

/-- The old label `x_j` of access `j` (0-indexed: the access to `α j`): the label of `α j` before the
access; it determines the read and refill path. -/
def oldLabel {N s : ℕ} (α : Fin s → Fin N) (ω : Labels N s) (j : Fin s) : Leaf (treeDepth N) :=
  posAfter α ω j (α j)

/-- `b ∈ I_t = {a₁, …, a_t}`: block `b` has been accessed among the first `t` accesses. -/
def IsCreated {N s : ℕ} (α : Fin s → Fin N) (t : ℕ) (b : Fin N) : Prop :=
  ∃ j : Fin s, j.val < t ∧ α j = b

instance {N s : ℕ} (α : Fin s → Fin N) (t : ℕ) : DecidablePred (IsCreated α t) :=
  fun b => by unfold IsCreated; infer_instance

/-- The 0-indexed time of the last access to `b` among the first `t` accesses (`τ_t(b) − 1`;
`0` if `b` was not accessed). -/
def lastAccess {N s : ℕ} (α : Fin s → Fin N) (t : ℕ) (b : Fin N) : ℕ :=
  (Finset.univ.filter (fun j : Fin s => j.val < t ∧ α j = b)).sup (fun j => j.val)

/-- The target `d_t(b)`, (19) p.16 (PDF p.19) and (59) p.50 (PDF p.53): "the deepest node among
{lcp(yb, xj) : τt(b) ≤ j ≤ t}", where `y_b` is the current label of `b` and `x_j` the old label of
access `j`. All candidates lie on `path(y_b)`, so the deepest is the prefix of `y_b` of the largest
candidate length.

**Formalization Note.** Accesses are 0-indexed: the access times `τ_t(b) ≤ j ≤ t` are the indices
`lastAccess α t b ≤ j < t`. The value is meaningful for created blocks (`IsCreated α t b`), the only
ones counted by `targetLoads`. -/
def target {N s : ℕ} (α : Fin s → Fin N) (ω : Labels N s) (t : ℕ) (b : Fin N) : List Bool :=
  let y := (posAfter α ω t b).toList
  y.take ((Finset.univ.filter (fun j : Fin s => lastAccess α t b ≤ j.val ∧ j.val < t)).sup
    (fun j => (commonPrefix y (oldLabel α ω j).toList).length))

/-- The target-load vector `A(t)`: `A_v(t) = |{b ∈ I_t : d_t(b) = v}|`, §4.3.1, p.16 (PDF p.19);
§5.2.1, p.37 (PDF p.40). -/
def targetLoads {N s : ℕ} (α : Fin s → Fin N) (ω : Labels N s) (t : ℕ)
    (v : List Bool) : ℕ :=
  (Finset.univ.filter (fun b => IsCreated α t b ∧ target α ω t b = v)).card

end PathORAMCap


