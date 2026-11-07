-- Prove2me | Definitions.Def_SecondBestBT_greedyRun
-- name    : SecondBestBT_greedyRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:46:33.84202+00:00
-- url     : https://prove2.me/theorems/ab124bb4-28e4-4131-babb-e1c24ab98910
-- title:
--   Algorithm 1 (greedy construction), run through buyer value $b$
-- statement:
--   **Algorithm 1** (greedy construction). Input: a full-support $\alpha$-weakly regular seller prior on $\{0,\dots,K\}$ and $\alpha,\beta\ge0$. Start from $x(\cdot,0)=0$ and $t_0=0$. For $b=1,2,\dots$: copy $x(\cdot,b)\leftarrow x(\cdot,b-1)$ and $t_b\leftarrow t_{b-1}$, then run the inner loop at $b$ (the item *Algorithm 1, inner loop*).
--
--   The run through $b$ is either **fail** (some buyer value $\le b$ failed) or the allocation columns $x(\cdot,b')$ for $b'\le b$ together with the threshold $t_b$. "Algorithm 1 never returns fail" means that the run through every $b\in\mathbb N$ is not fail.
--
--   **Formalization Note** The input conditions are hypotheses of the theorems, not of the definition.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Algorithm 1, p.14

import Mathlib
import Definitions.Def_SecondBestBT_greedyFill

namespace SecondBestBT

/-- Algorithm 1, the greedy construction, run through buyer value `b` (Liu–Qin–Ren–Wang,
arXiv:2606.03849, held version sha256 17184930…, Section 4.5, Algorithm 1, p.14).

`greedyRun α β K f_S b` is `none` if the algorithm has returned `fail` at some buyer value
`≤ b`, and otherwise `some (x, t_b)`, where `x s b'` is the constructed allocation for every
buyer value `b' ≤ b` (and `0` for `b' > b`) and `t_b` the threshold after processing `b`.
Line 1: `x(·, 0) = 0`, `t_0 = 0`. Line 3: at `b + 1`, copy `x(·, b + 1) ← x(·, b)` and
`t_{b+1} ← t_b`, then run the inner loop `greedyFill`.

**Formalization Note** Each buyer value is processed once; "Algorithm 1 never returns fail" is
`∀ b, greedyRun α β K f_S b ≠ none`. The input conditions of the paper (full support,
`α`-weak regularity, `α, β ≥ 0`) are hypotheses of the theorems, not of the definition. -/
noncomputable def greedyRun (α β : ℝ) (K : ℕ) (fS : ℕ → ℝ) : ℕ → Option ((ℕ → ℕ → ℝ) × ℕ)
  | 0 => some (fun _ _ => 0, 0)
  | b + 1 =>
    (greedyRun α β K fS b).bind fun p =>
      (greedyFill α β K fS (b + 1) p.1 p.2 (fun s => p.1 s b)).map fun q =>
        (fun s b' => if b' = b + 1 then q.1 s else p.1 s b', q.2)

end SecondBestBT


