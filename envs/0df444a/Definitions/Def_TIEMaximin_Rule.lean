-- Prove2me | Definitions.Def_TIEMaximin_Rule
-- name    : TIEMaximin_Rule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:38:25.719936+00:00
-- url     : https://prove2.me/theorems/3bffbbb4-73ae-48b7-a659-eddfedb9a335
-- title:
--   Value order, top sets, nominations and the top-set competitive rule
-- statement:
--   Let $\pi_i(t)$ be the $t$-th largest good according to $v_i$, ties broken by index. The **top set** $T_i$ consists of the $n-1$ goods agent $i$ values most, and $f_g=|\{i:g\in T_i\}|$ is the number of agents **nominating** good $g$. The **top-set competitive rule** is
--
--   $$x_{ig}=\frac1n+\frac{\mathbf 1[g\in T_i]}{n}-\frac{\sum_{j\in N\setminus\{i\}}\mathbf 1[g\in T_j]}{n(n-1)}.$$
--
--   The rule determines the incentives and ex-ante fairness of the mechanism: everything else only implements it.
--
--   **Formalization Note** The position in $\pi_i$ is a rank function counting the goods before $g$. Divisions are real, and the rule is read under the standing assumption $n\ge2$.
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), §3.1, eq. (5), p.10; §3.2, p.12

import Mathlib

namespace TIEMaximin

open Finset

/-- **The position of good `g` in agent `i`'s value order** `π_i` (p.12), 0-based: the number of
goods before `g`, i.e. with a larger value, or with the same value and a smaller index.

arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), §3.2, p.12: "let π_i(t) be the t-th
largest item according to v_i (with ties broken by index)".

**Formalization Note.** `rankV v i (π_i(t)) = t − 1`. Ties are broken by index through this count. -/
noncomputable def rankV {n m : ℕ} (v : Fin n → Fin m → ℝ) (i : Fin n) (g : Fin m) : ℕ :=
  #{g' : Fin m | v i g < v i g' ∨ (v i g' = v i g ∧ g' < g)}

/-- **The top set** `T_i` (§3.1, p.10): the `n − 1` goods agent `i` values most, ties broken by index.

arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), §3.1, p.10.

**Formalization Note.** `n - 1` is natural subtraction, used under `2 ≤ n`. `T_i` has exactly
`n − 1` elements as soon as `m ≥ n − 1`. -/
noncomputable def topSet {n m : ℕ} (v : Fin n → Fin m → ℝ) (i : Fin n) : Finset (Fin m) :=
  {g | rankV v i g < n - 1}

/-- **The number of nominations** `f_g = |{i : g ∈ T_i}|` of good `g` (§3.1, p.10 of
arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…). -/
noncomputable def nom {n m : ℕ} (v : Fin n → Fin m → ℝ) (g : Fin m) : ℕ :=
  #{i : Fin n | g ∈ topSet v i}

/-- **The top-set competitive rule** (5), p.10:
`x_ig = 1/n + 1[g ∈ T_i]/n − (Σ_{j ≠ i} 1[g ∈ T_j]) / (n(n − 1))`.

arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), §3.1, eq. (5), p.10.

**Formalization Note.** Divisions are real. The rule is only used under `2 ≤ n`, where no denominator
vanishes (the paper's standing assumption `m ≥ n ≥ 2`, p.8). -/
noncomputable def xRule {n m : ℕ} (v : Fin n → Fin m → ℝ) (i : Fin n) (g : Fin m) : ℝ :=
  1 / (n : ℝ) + (if g ∈ topSet v i then 1 else 0) / (n : ℝ) -
    (∑ j with j ≠ i, if g ∈ topSet v j then (1 : ℝ) else 0) / ((n : ℝ) * ((n : ℝ) - 1))

end TIEMaximin


