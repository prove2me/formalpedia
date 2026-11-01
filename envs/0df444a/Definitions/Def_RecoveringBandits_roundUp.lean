-- Prove2me | Definitions.Def_RecoveringBandits_roundUp
-- name    : RecoveringBandits_roundUp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:53:27.710646+00:00
-- url     : https://prove2.me/theorems/c2f4b2f1-2bef-4d92-baca-49017808424c
-- title:
--   The rounding sets $D_j$, $D[a]$ and the rounding (4)
-- statement:
--   For $j\ge1$ let $D_j=\{(2j-1)\cdot2^\ell:\ \ell\ge0\}$ and $D[a]=\bigcup_{j=1}^a D_j\cup\{+\infty\}$. Step 1 of the rounding-scheduling procedure rounds a frequency $x_i\in[0,1]$ to the period
--
--   $$d_i=\min\{d\ge 1/x_i,\ d\in D[a]\},\tag{4}$$
--
--   with $d_i=+\infty$ (never pulled) when $x_i=0$. Periods in one $D_j$ share their odd part, which is what makes them easy to schedule together.
--
--   **Formalization Note** $+\infty$ is the top element of `WithTop ℕ`; `Da a` is $D[a]$ without $+\infty$. For $a\ge1$ and $x>0$ the set in (4) is nonempty (powers of two lie in $D_1$). Every statement using the rounding assumes $a\ge1$ and $x\in[0,1]$.
-- source:
--   Simchi-Levi–Zheng–Zhu, Offline Planning and Online Learning under Recovering Rewards, arXiv:2106.14813v2, §4.2, Step 1, (4), p.12

import Mathlib

namespace RecoveringBandits

/-- **`D_j = {(2j − 1) × 2^ℓ}_{ℓ ≥ 0}`** (arXiv:2106.14813v2, §4.2, Step 1, p.12). Used for
`j ≥ 1`. -/
def Dj (j : ℕ) : Set ℕ :=
  {d | ∃ ℓ : ℕ, d = (2 * j - 1) * 2 ^ ℓ}

/-- **`D[a]` without `+∞`**: `⋃_{j=1}^a D_j` (arXiv:2106.14813v2, §4.2, Step 1, p.12). The paper's
`D[a]` also contains `+∞`; `roundUp` handles it separately. -/
def Da (a : ℕ) : Set ℕ :=
  {d | ∃ j, 1 ≤ j ∧ j ≤ a ∧ d ∈ Dj j}

/-- **The rounding (4)** (arXiv:2106.14813v2, §4.2, (4), p.12):
`d_i = min {d ≥ 1/x_i, d ∈ D[a]}`, with `d_i = +∞` when `x_i = 0` ("the arm is never pulled").

**Formalization Note.** `+∞` is `⊤ : WithTop ℕ`. For `a ≥ 1` and `x > 0` the set is nonempty
(every power of two lies in `D_1`), so `sInf` is its least element; every statement using
`roundUp` assumes `a ≥ 1` and `x ∈ [0, 1]`. -/
noncomputable def roundUp (a : ℕ) (x : ℝ) : WithTop ℕ :=
  if x = 0 then ⊤ else ((sInf {d : ℕ | d ∈ Da a ∧ 1 / x ≤ (d : ℝ)} : ℕ) : WithTop ℕ)

end RecoveringBandits


