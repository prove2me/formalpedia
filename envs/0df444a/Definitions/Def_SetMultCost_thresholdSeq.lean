-- Prove2me | Definitions.Def_SetMultCost_thresholdSeq
-- name    : SetMultCost_thresholdSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:41.652266+00:00
-- url     : https://prove2.me/theorems/9daaca48-1314-4d53-a4f4-e63ef117e0a8
-- title:
--   The threshold sequence of Lemma 5.5
-- statement:
--   Given restrictions $\mathbf r$, the convergent denominators $q_j$ of $\alpha$, and a parameter $m$, the **threshold sequence** is $\tau_0=1$ and
--
--   $$\tau_i=\min\big(r_i\tau_{i-1},\ 6m\cdot\kappa\, q_hq_{h-1}\big),\qquad h=\min\{j:\tau_{i-1}<2q_j/3\}.$$
--
--   The page's formula has $\kappa=2$. Its proof and Lemma 7.3 use $\kappa=1$.
--
--   **Formalization Note** $m,\kappa\in\mathbb N$, as $\tau$ must be integer-valued. For positive digits $q_j$ is unbounded, so $h$ exists; $h\ge1$ once $\tau_{i-1}\ge1$. If some $r_i=0$, every later $\tau$ is $0$ and those coordinates are outside $S$.
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), Lemma 5.5, p.18

import Mathlib
import Definitions.Def_SetMultCost_cfDen

namespace SetMultCost

/-- The index in Lemma 5.5, p.18: "h = min {j : τi−1 < 2qj/3}".

**Formalization Note.** `Nat.sInf`, with value `0` on an empty set. The set is nonempty for digits
`aᵢ ≥ 1`, since then `qⱼ` is unbounded; it is `0` only if `t = 0`. -/
noncomputable def thresholdIndex (a : ℕ → ℤ) (t : ℕ) : ℕ :=
  sInf {j : ℕ | 3 * (t : ℤ) < 2 * cfDen a j}

/-- **The threshold sequence of Lemma 5.5.** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), p.18: "τ0 = 1, for all 1 ≤ i ≤ ∆, τi =
min (riτi−1, 6m · 2qhqh−1) where h = min {j : τi−1 < 2qj/3}".

**Formalization Note.** The factor printed as `2` is the parameter `κ`: the statement has `κ = 2`,
while its proof and Lemma 7.3 have `κ = 1`. The parameter `m` is real, as printed ("a parameter
m ≥ 0"). The paper's `τ` is integer-valued (Definitions 4.1, 4.3), so on its instances
`6m · κ · q_h q_{h−1}` is a natural number; the second argument of the minimum is its floor `⌊·⌋₊`,
which is exact there and equals the printed value for every `m ∈ ℕ`. `r` takes values in `ℕ∞`; the
minimum is finite, and `ENat.toNat` returns it. `h − 1` is exact because `h ≥ 1` once `τᵢ₋₁ ≥ 1`.
If some `r_i = 0`, every later `τ` is `0` and those coordinates are not in `S`. -/
noncomputable def thresholdSeq (r : ℕ → ℕ∞) (a : ℕ → ℤ) (m : ℝ) (κ : ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 =>
    let t := thresholdSeq r a m κ i
    let h := thresholdIndex a t
    (min (r (i + 1) * (t : ℕ∞))
      ((⌊6 * m * (κ : ℝ) * ((cfDen a h * cfDen a (h - 1) : ℤ) : ℝ)⌋₊ : ℕ) : ℕ∞)).toNat

end SetMultCost


