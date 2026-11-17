-- Prove2me | Definitions.Def_StreamRot_Supplement_detRun
-- name    : StreamRot_Supplement_detRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:23:40.367399+00:00
-- url     : https://prove2.me/theorems/a141acfc-19eb-4488-b659-f4253689ff70
-- title:
--   Run of a deterministic table on a word
-- statement:
--   Let $S_0,\dots,S_N$ be finite label sets. A **deterministic table** consists of an initial label $s_0\in S_0$ and, for every time $0\le t<N$, every letter $a$ and every label $s\in S_t$, one next label $\mathrm{next}_t(a,s)\in S_{t+1}$. Its **run** on a word $w=a_1\cdots a_N$ is the sequence of labels
--   $$
--   s_0,\qquad s_{t+1}=\mathrm{next}_t(a_{t+1},s_t)\quad(0\le t<N).
--   $$
--   This is the object produced by the same-width deterministic selection of Theorem B.4: the table lives on the same label sets as the stochastic controller, and the time $t$ is an argument of the table.
--
--   **Formalization Note** Label sets are $\mathrm{Fin}(\mathrm{width}\,t)$, as in the published controller `StreamRot.Controller`, and the table entry at time $t$ (0-based) reads the letter $w_t$, the page's $a_{t+1}$.
-- source:
--   Qi, Constant-Failure Width Bounds for Streaming Rotations, STOC 2027 submission (manuscript sha256 3ffd9cd7…), Theorem B.4, p.22 (PDF 24)

import Mathlib

namespace StreamRot

namespace Supplement

/-- The run of a deterministic table on a word: the label at cut `t ≤ N` when the initial label is `s₀` and the
label after reading the letter `a_{t+1}` at cut `t` is `next t a_{t+1} s`. Qi, Constant-Failure Width Bounds for Streaming Rotations, STOC 2027 submission (manuscript sha256 3ffd9cd7…), Theorem B.4, p.22.

**Formalization Note** Label sets are `Fin (width t)`, as in `StreamRot.Controller`, and rows are 0-based: the
table entry `next t` (`t < N`) reads the letter `w t`, the page's `a_{t+1}`. The time coordinate `t` is an
argument of the table. -/
def detRun {A : Type} {width : ℕ → ℕ} {N : ℕ} (s₀ : Fin (width 0))
    (next : (t : Fin N) → A → Fin (width t) → Fin (width (t + 1))) (w : Fin N → A) :
    (t : ℕ) → t ≤ N → Fin (width t)
  | 0, _ => s₀
  | t + 1, h => next ⟨t, h⟩ (w ⟨t, h⟩) (detRun s₀ next w t (Nat.le_of_succ_le h))

end Supplement

end StreamRot


