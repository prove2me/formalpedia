-- Prove2me | Definitions.Def_SecondBestBT_greedyFill
-- name    : SecondBestBT_greedyFill
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:22.858083+00:00
-- url     : https://prove2.me/theorems/d438230e-74b9-49cf-b268-3e7d43fb7f87
-- title:
--   Algorithm 1, inner loop at one buyer value
-- statement:
--   This is the inner `while` loop (lines 4–10) of **Algorithm 1** at a buyer value $b\ge1$. The state is the current column $x(\cdot,b)$, the threshold $t=t_b$, and the earlier columns $x(\cdot,b')$, $b'<b$.
--
--   1. If $H(b;x)\ge0$, processing of $b$ ends.
--   2. Otherwise, if $(1+\alpha)b\le\varphi^\alpha_S(t)$, the algorithm returns **fail**.
--   3. Otherwise $H(b;x)$ is affine in $x(t,b)$ with positive slope $f_S(t)\big((1+\alpha)b-\varphi^\alpha_S(t)\big)$; solve $H(b;x)=0$ for $z=x(t,b)$, all other entries fixed, and set $x(t,b)\leftarrow\min\{z,1\}$.
--   4. If $z\le1$, processing of $b$ ends and the threshold is retained.
--   5. Otherwise, if $t=\min\{K,b-1\}$, return **fail**; else set $t\leftarrow t+1$ and go back to step 1.
--
--   **Formalization Note** `fail` is `none`. The recursion is on the threshold and terminates because $t$ increases strictly below $\min\{K,b-1\}$; there is no fuel.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Algorithm 1, p.14

import Mathlib
import Definitions.Def_SecondBestBT_H
import Definitions.Def_SecondBestBT_alphaVirtualS

namespace SecondBestBT

/-- One buyer value of Algorithm 1, the inner `while` loop of lines 4–10 (Liu–Qin–Ren–Wang,
arXiv:2606.03849, held version sha256 17184930…, Section 4.5, Algorithm 1, p.14).

Input: the buyer value `b ≥ 1`, the earlier columns `hist s b'` (`b' < b`), the current threshold
`t` and the current column `col = x(·, b)`. Let `x` be `hist` with column `b` replaced by `col`.

* If `H(b; x) ≥ 0`, processing of `b` ends with `(col, t)` (the loop condition fails).
* Otherwise, if `(1 + α) b ≤ φ^α_S(t)`, return `fail` (`none`) (line 5).
* Otherwise solve `H(b; x) = 0` for `z = x(t, b)` with all other entries fixed. `H(b; x)` is affine
  in `x(t, b)` with slope `f_S(t)((1 + α) b − φ^α_S(t)) > 0` (p.14), so
  `z = x(t, b) − H(b; x) / (f_S(t)((1 + α) b − φ^α_S(t)))`; set `x(t, b) ← min{z, 1}` (lines 6–7).
* If `z ≤ 1`, end with the threshold retained (line 8).
* Otherwise, if `t` is the last candidate `min{K, b − 1}`, return `fail` (line 9); else advance
  `t ← t + 1` and repeat (line 10).

**Formalization Note** The recursion terminates because `t` increases strictly below
`min{K, b − 1}`; the test "`t_b = min{K, b − 1}`" of line 9 is written `min K (b − 1) ≤ t`,
which agrees with it because the threshold never exceeds the last candidate. `fail` is `none`;
there is no fuel. `b − 1` is natural subtraction and is used only for `b ≥ 1`. -/
noncomputable def greedyFill (α β : ℝ) (K : ℕ) (fS : ℕ → ℝ) (b : ℕ) (hist : ℕ → ℕ → ℝ)
    (t : ℕ) (col : ℕ → ℝ) : Option ((ℕ → ℝ) × ℕ) :=
  let x : ℕ → ℕ → ℝ := fun s b' => if b' = b then col s else hist s b'
  if 0 ≤ H α β fS x b then some (col, t)
  else if (1 + α) * b ≤ alphaVirtualS α fS t then none
  else
    let z := col t - H α β fS x b / (fS t * ((1 + α) * b - alphaVirtualS α fS t))
    let col' := Function.update col t (min z 1)
    if z ≤ 1 then some (col', t)
    else if min K (b - 1) ≤ t then none
    else greedyFill α β K fS b hist (t + 1) col'
termination_by min K (b - 1) - t

end SecondBestBT


