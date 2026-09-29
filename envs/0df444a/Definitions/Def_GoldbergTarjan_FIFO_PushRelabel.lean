-- Prove2me | Definitions.Def_GoldbergTarjan_FIFO_PushRelabel
-- name    : GoldbergTarjan_FIFO_PushRelabel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:32:10.810851+00:00
-- url     : https://prove2.me/theorems/4593d4c4-73e3-4693-ae48-48ea9b78679c
-- title:
--   Push and relabel operations (Fig. 1) and the initial preflow and simple labeling (Fig. 2)
-- statement:
--   This file defines the two basic operations of the generic push–relabel algorithm (Fig. 1 of Goldberg and Tarjan) and its initialization (Fig. 2).
--
--   Let $f$ be a function on vertex pairs, $d$ a labeling with values in $\mathbb{N}\cup\{\infty\}$, and $e$, $r_f$ the excess and residual capacity.
--
--   1. **Push$(v,w)$** is applicable when $v$ is active, $r_f(v,w) > 0$ and $d(v) = d(w) + 1$. It sends $\delta = \min(e(v), r_f(v,w))$ units of flow from $v$ to $w$: $$f(v,w) \leftarrow f(v,w) + \delta, \qquad f(w,v) \leftarrow f(w,v) - \delta,$$ all other values of $f$ unchanged.
--   2. **Relabel$(v)$** is applicable when $v$ is active and $d(v) \le d(w)$ for every $w$ with $r_f(v,w) > 0$. Its action sets $$d(v) \leftarrow \min\{ d(w) + 1 : r_f(v,w) > 0 \},$$ with $d(v) \leftarrow \infty$ when there is no residual edge leaving $v$.
--   3. The **initial preflow** saturates every edge leaving the source: $f(s,v) = c(s,v)$, $f(v,s) = -c(s,v)$ for every $v$, and $f(v,w) = 0$ when neither $v$ nor $w$ is $s$.
--   4. The **simple initial labeling** is $d(s) = n$ and $d(v) = 0$ for $v \neq s$.
--
--   Every algorithm of the paper is built from these operations; the first-in, first-out algorithm of §4 applies them through the push/relabel operation of Fig. 3.
--
--   **Formalization Note** The push action is given as the new function `pushFlow`; the excess updates $e(v) \leftarrow e(v) - \delta$, $e(w) \leftarrow e(w) + \delta$ of Fig. 1 follow from recomputing the excess. The relabel action is `relabelLabel`, an infimum in `ℕ∞`, whose empty infimum is $\infty$. Applicability of each operation is a separate predicate.
-- source:
--   Goldberg, Tarjan, A New Approach to the Maximum-Flow Problem, J. ACM 35(4), 1988, p. 925, Fig. 1 and Fig. 2; p. 926 (simple labeling)

import Mathlib
import Definitions.Def_GoldbergTarjan_FIFO_Network

namespace GoldbergTarjan.FIFO

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Applicability of `push(v, w)` (Fig. 1, p. 925): `v` is active, `r_f(v, w) > 0` and
`d(v) = d(w) + 1`. -/
def PushApplicable (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (v w : V) : Prop :=
  IsActive N f d v ∧ 0 < residual N f v w ∧ d v = d w + 1

/-- The amount `δ = min(e(v), r_f(v, w))` sent by `push(v, w)` (Fig. 1). -/
def pushAmount (N : Network V) (f : V → V → ℝ) (v w : V) : ℝ :=
  min (excess f v) (residual N f v w)

/-- The preflow after the action of `push(v, w)` (Fig. 1): `f(v, w) ← f(v, w) + δ`,
`f(w, v) ← f(w, v) − δ`, every other pair unchanged, with `δ = min(e(v), r_f(v, w))`. The
excesses `e(v) ← e(v) − δ`, `e(w) ← e(w) + δ` are not stored: `excess` is recomputed from the new
function. (The action is only used when the push is applicable, where `v ≠ w`.) -/
def pushFlow (N : Network V) (f : V → V → ℝ) (v w : V) : V → V → ℝ :=
  fun x y =>
    if x = v ∧ y = w then f v w + pushAmount N f v w
    else if x = w ∧ y = v then f w v - pushAmount N f v w
    else f x y

/-- Applicability of `relabel(v)` (Fig. 1): `v` is active and for every `w ∈ V`,
`r_f(v, w) > 0 ⇒ d(v) ≤ d(w)`. -/
def RelabelApplicable (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (v : V) : Prop :=
  IsActive N f d v ∧ ∀ w, 0 < residual N f v w → d v ≤ d w

/-- The new label set by `relabel(v)` (Fig. 1): `min{d(w) + 1 | (v, w) ∈ E_f}`, the minimum over
the residual edges leaving `v`. In `ℕ∞` the infimum of the empty family is `⊤ = ∞`, which is the
paper's "(If this minimum is over an empty set, `d(v) ← ∞`.)" -/
noncomputable def relabelLabel (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (v : V) : ℕ∞ :=
  ⨅ (w : V) (_ : 0 < residual N f v w), d w + 1

/-- The initial preflow of Fig. 2 (p. 925): `f(v, w) = 0` for `(v, w) ∈ (V − {s}) × (V − {s})`,
and `f(s, v) = c(s, v)`, `f(v, s) = −c(s, v)` for every `v` (so `f(s, s) = 0`, as `c(s, s) = 0`). -/
def initFlow (N : Network V) : V → V → ℝ :=
  fun v w =>
    if v = N.s then N.c N.s w
    else if w = N.s then -N.c N.s v
    else 0

/-- The simple initial labeling (Fig. 2 and p. 926): `d(s) = n = |V|` and `d(v) = 0` for
`v ∈ V − {s}`. -/
def initLabel (N : Network V) : V → ℕ∞ :=
  fun v => if v = N.s then (Fintype.card V : ℕ∞) else 0

end GoldbergTarjan.FIFO


