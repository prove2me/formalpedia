-- Prove2me | Definitions.Def_AvgWorstGap_pK
-- name    : AvgWorstGap_pK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:49:04.556363+00:00
-- url     : https://prove2.me/theorems/00802a76-4c1c-4f14-8517-bb243c10bc65
-- title:
--   Probabilistic time-bounded Kolmogorov complexity $pK^{t,O}_\lambda(x\mid y)$
-- statement:
--   For strings $x,y$, a time bound $t$, a threshold $\lambda$ and an oracle $O$,
--   $$\mathrm{pK}^{t,O}_\lambda(x\mid y)=\min\Big\{s\in\mathbb N : \Pr_{r\sim\{0,1\}^t}\big[K^{t,O}(x\mid y;r)\le s\big]\ge\lambda\Big\}.$$
--   The randomness has length exactly $t$. The paper omits $O$ when it is empty and $\lambda$ when $\lambda=2/3$.
--
--   **Formalization Note** The value is $+\infty$ when no $s$ qualifies. The function is defined for every real $\lambda$. The paper's domain $\lambda\in[0,1]$ is enforced where it matters, in the instance guards of the promise problems.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Definition 2.2, p.13

import Mathlib
import Definitions.Def_AvgWorstGap_Kt
import Definitions.Def_NKtLB_prob

namespace AvgWorstGap

open NKtLB

/-- **Probabilistic time-bounded Kolmogorov complexity `pK^{t,O}_λ(x | y)`** (Def. 2.2,
arXiv:2610.19162, version of October 30, 2026, p.13): "For `x, y ∈ {0, 1}∗`, `λ ∈ [0, 1]`,
`t ∈ ℕ`, and an oracle `O`, define `pK^{t,O}_λ(x | y) ≜ min { s ∈ ℕ | Pr_{r∼{0,1}^t} [ K^{t,O}(x | y;
r) ≤ s ] ≥ λ }`. We omit `O` when it is empty and omit `λ` when `λ = 2/3`."

**Formalization Note.** The randomness `r` has length exactly `t`. The value is in `ℕ∞`, `⊤` when no
`s` qualifies. The function is defined for every real `λ`; the items restrict `λ` to the paper's
domain where it matters (the guards of the promise problems). -/
noncomputable def pK (O : Set (List Bool)) (t : ℕ) (lam : ℝ) (x y : List Bool) : ℕ∞ :=
  ⨅ (s : ℕ) (_ : lam ≤ prob t (fun r => Kt O t x y r ≤ (s : ℕ∞))), (s : ℕ∞)

end AvgWorstGap


