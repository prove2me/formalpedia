-- Prove2me | Definitions.Def_SecondBestBT_Supplement_alg2Fill
-- name    : SecondBestBT_Supplement_alg2Fill
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:36:45.740273+00:00
-- url     : https://prove2.me/theorems/03caeb87-44e9-4330-a89a-d86be061028f
-- title:
--   Algorithm 2, inner loop (lines 5–11)
-- statement:
--   One buyer value $b$ of **Algorithm 2** (State Transition), in local coordinates, with the reference pair $(\ell,b_0)$ held fixed and the current threshold $t_b$:
--
--   - (line 5) while $\hat H_{\ell,b_0}(b;x)<0$:
--     - (line 6) if $(1+\alpha)b\le\varphi^\alpha_R(t_b)$, return **fail**, where $\varphi^\alpha_R(j)=(1+\alpha)j+\alpha R_j$ for $\alpha>0$ (infinite when $R_j=\infty$) and $\varphi^0_R(j)=j$;
--     - (lines 7–8) solve $\hat H_{\ell,b_0}(b;x)=0$ for $z=x(t_b,b)$, all other entries fixed, and set $x(t_b,b)\leftarrow\min\{z,1\}$;
--     - (line 9) if $z\le1$, stop;
--     - (lines 10–11) if $t_b=b-1$, return **fail**; otherwise $t_b\leftarrow t_b+1$.
--
--   **Formalization Note** $\hat H$ is affine in $x(t_b,b)$, so its root is computed from its values at $x(t_b,b)=0$ and $1$. The test $t_b=b-1$ is written $b-1\le t_b$; the two agree because the threshold never exceeds $b-1$. Fail is `none`.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 5.1, Algorithm 2, p.18

import Mathlib
import Definitions.Def_SecondBestBT_Supplement_normResidual

open scoped ENNReal

namespace SecondBestBT.Supplement

open Classical in
/-- One buyer value of **Algorithm 2** (State Transition), the inner `while` loop of lines 5–11
(Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256 17184930…, Section 5.1, Algorithm 2, p.18), in local coordinates, with the reference pair `(ℓ, b0)`
held fixed.

Input: local ratios `r`, the reference pair `(ℓ, b0)`, the buyer value `b`, the allocation `x`
(column `b` already copied from column `b − 1`) and the current threshold `t = t_b`.

* Line 5: if `Ĥ_{ℓ,b0}(b; x) ≥ 0`, the loop ends with `(x, t)`.
* Line 6: if `(1 + α) b ≤ φ^α_R(t)`, return `fail` (`none`), where `φ^α_R(j) = (1 + α) j + α R_j`
  for `α > 0` (`= ∞` when `R_j = ∞`) and `φ^0_R(j) = j` (p.17).
* Line 7: solve `Ĥ_{ℓ,b0}(b; x) = 0` for `z = x(t, b)`, the other entries fixed; line 8:
  `x(t, b) ← min{z, 1}`; line 9: if `z ≤ 1`, break (end with `(x, t)`).
* Line 10: if `t = b − 1`, return `fail`; line 11: else `t ← t + 1` and repeat.

**Formalization Note** `Ĥ_{ℓ,b0}(b; x)` is affine in `x(t, b)` (p.17), so its root is
`z = −Ĥ₀ / (Ĥ₁ − Ĥ₀)` where `Ĥ₀`, `Ĥ₁` are its values with `x(t, b)` set to `0` and `1`. The test
`t = b − 1` of line 10 is written `b − 1 ≤ t`, which agrees with it because the threshold never
exceeds `b − 1` (the candidate thresholds end at `b − 1`, p.18); this makes the recursion
terminate. `fail` is `none`. -/
noncomputable def alg2Fill (α β : ℝ) (r : ℕ → ℝ≥0∞) (ℓ b0 b : ℕ) (x : ℕ → ℕ → ℝ) (t : ℕ) :
    Option ((ℕ → ℕ → ℝ) × ℕ) :=
  if 0 ≤ normResidual α β r ℓ b0 x b then some (x, t)
  else if (if α = 0 then (b : ℝ) ≤ t
      else r t = ⊤ ∨ (1 + α) * (b : ℝ) ≤ (1 + α) * t + α * (r t).toReal) then none
  else
    let set : ℝ → ℕ → ℕ → ℝ := fun v s b' => if s = t ∧ b' = b then v else x s b'
    let h0 := normResidual α β r ℓ b0 (set 0) b
    let h1 := normResidual α β r ℓ b0 (set 1) b
    let z := -h0 / (h1 - h0)
    if z ≤ 1 then some (set (min z 1), t)
    else if b - 1 ≤ t then none
    else alg2Fill α β r ℓ b0 b (set (min z 1)) (t + 1)
termination_by b - 1 - t
decreasing_by omega

end SecondBestBT.Supplement


