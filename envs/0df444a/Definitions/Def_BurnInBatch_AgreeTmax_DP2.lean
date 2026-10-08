-- Prove2me | Definitions.Def_BurnInBatch_AgreeTmax_DP2
-- name    : BurnInBatch_AgreeTmax_DP2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T13:07:43.872591+00:00
-- url     : https://prove2.me/theorems/203efa05-7021-49fa-8bec-4a15731dd342
-- title:
--   Algorithm DP2 (§3, p. 770): $f(j)=\min_{\max\{1,j-B+1\}\le i\le j} f_i(j)$
-- statement:
--   **Algorithm DP2** of Lee, Uzsoy and Martin-Vega is a dynamic program over prefixes of the job list. Jobs are numbered $1,\dots,n$, with processing times $p_j$ and due dates $d_j$, and $B$ is the machine capacity. The values $f(j)\in\mathbb N\cup\{\infty\}$, $0\le j\le n$, are defined by
--   $$f(0)=0,\qquad f(j)=\min_{\max\{1,\,j-B+1\}\le i\le j} f_i(j)\quad (j\ge 1),$$
--   where
--   $$f_i(j)=\begin{cases} f(i-1)+p_j, & \text{if } f(i-1)+p_j\le d_i,\\ \infty, & \text{otherwise.}\end{cases}$$
--   The paper reads $f_i(j)$ as the completion time of jobs $1$ through $j$ when jobs $i,i+1,\dots,j$ form the last batch, and $f(j)$ as the minimum completion time of jobs $1,\dots,j$ if they can be scheduled feasibly, and infinity otherwise. Whether that reading is right is the content of the mission's goal theorem; this file only defines the recursion as printed.
--
--   **Formalization Note** Values lie in $\mathbb N_\infty$ (`ℕ∞`), whose top element $\top$ is the paper's $\infty$: $\top+p=\top$ and $\top\le d$ fails. The jobs are 1-based as on the page: $p_j$ and $d_i$ are read from the 0-based data at index $j-1$, $i-1$ (the helpers `pOf`, `dOf` return $0$ outside $1..n$, which the recursion never reads for $j\le n$). The paper's clause $f(j)=\infty$ for $j<0$ is never used, since $i\ge 1$. The lower limit $j-B+1$ is computed in $\mathbb N$, where it may truncate to $0$; the $\max$ with $1$ makes that harmless. The minimum is a fold over the list of indices with $\top$ as the empty value, written with an explicit comparison so that it evaluates.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 770, §3, Algorithm DP2

import Mathlib

namespace BurnInBatch.AgreeTmax

/-- Processing time `p_j` of the paper's 1-based job `j` (= `p ⟨j - 1, _⟩`); `0` outside
`1 ≤ j ≤ n`, a value the recursion below never reads for prefix lengths `j ≤ n`. -/
def pOf {n : ℕ} (p : Fin n → ℕ) (j : ℕ) : ℕ :=
  if h : 0 < j ∧ j ≤ n then p ⟨j - 1, by omega⟩ else 0

/-- Due date `d_i` of the paper's 1-based job `i`; `0` outside `1 ≤ i ≤ n` (never read). -/
def dOf {n : ℕ} (d : Fin n → ℕ) (i : ℕ) : ℕ :=
  if h : 0 < i ∧ i ≤ n then d ⟨i - 1, by omega⟩ else 0

/-- Algorithm DP2 of Lee, Uzsoy & Martin-Vega (1992), §3, p. 770, as printed:
`f(0) = 0` and, for `j ≥ 1`,
`f(j) = min_{max{1, j-B+1} ≤ i ≤ j} f_i(j)` with
`f_i(j) = f(i-1) + p_j` if `f(i-1) + p_j ≤ d_i`, and `∞` otherwise.
Values lie in `ℕ∞`, with `⊤` the paper's `∞` (`⊤ + p = ⊤` and `¬ ⊤ ≤ d`). The clause
`f(j) = ∞ for j < 0` is never reached, since `i ≥ 1`. -/
def dp2 {n : ℕ} (B : ℕ) (p d : Fin n → ℕ) (j : ℕ) : ℕ∞ :=
  if j = 0 then 0
  else
    -- the minimum, over `i = max{1, j-B+1}, …, j`, of `f_i(j)`
    -- (`if x ≤ y then x else y` is `min x y`, written so that it evaluates)
    (List.range' (max 1 (j - B + 1)) (j + 1 - max 1 (j - B + 1))).attach.foldr
      (fun i acc =>
        let fij : ℕ∞ :=
          if dp2 B p d (i.1 - 1) + (pOf p j : ℕ∞) ≤ (dOf d i.1 : ℕ∞) then
            dp2 B p d (i.1 - 1) + (pOf p j : ℕ∞)
          else ⊤
        if fij ≤ acc then fij else acc)
      ⊤
termination_by j
decreasing_by all_goals (have := List.mem_range'_1.mp i.2; omega)

end BurnInBatch.AgreeTmax


