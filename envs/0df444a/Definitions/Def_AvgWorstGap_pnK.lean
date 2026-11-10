-- Prove2me | Definitions.Def_AvgWorstGap_pnK
-- name    : AvgWorstGap_pnK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:49:01.332224+00:00
-- url     : https://prove2.me/theorems/450e7e49-aa14-437b-bac8-df67348f4ad6
-- title:
--   Probabilistic nondeterministic Kolmogorov complexity $pnK^{t,O}_\lambda(x\mid y)$
-- statement:
--   $$\mathrm{pnK}^{t,O}_\lambda(x\mid y)=\min\Big\{s\in\mathbb N : \Pr_{r\sim\{0,1\}^t}\big[\mathrm{nK}^{t,O}(x\mid y;r)\le s\big]\ge\lambda\Big\},$$
--   with randomness of length exactly $t$ and value $+\infty$ when no $s$ qualifies. The paper omits $\lambda$ when $\lambda=2/3$. The oracle version is used in Theorem 2.13 and Lemma 2.17.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Definition 2.4, p.14

import Mathlib
import Definitions.Def_AvgWorstGap_nKt
import Definitions.Def_NKtLB_prob

namespace AvgWorstGap

open NKtLB

/-- **Probabilistic nondeterministic time-bounded Kolmogorov complexity `pnK^{t,O}_λ(x | y)`**
(Def. 2.4, arXiv:2610.19162, version of October 30, 2026, p.14): "For `x, y ∈ {0, 1}∗`,
`λ ∈ [0, 1]`, and `t ∈ ℕ`, define `pnK^t_λ(x | y) ≜ min { s ∈ ℕ | Pr_{r∼{0,1}^t} [ nK^t(x | y; r) ≤
s ] ≥ λ }`. We omit `λ` when `λ = 2/3`." The oracle version adds `O` to `nK`.

**Formalization Note.** Randomness of length exactly `t`; value in `ℕ∞`, `⊤` when no `s`
qualifies; defined for every real `λ`. -/
noncomputable def pnK (O : Set (List Bool)) (t : ℕ) (lam : ℝ) (x y : List Bool) : ℕ∞ :=
  ⨅ (s : ℕ) (_ : lam ≤ prob t (fun r => nKt O t x y r ≤ (s : ℕ∞))), (s : ℕ∞)

end AvgWorstGap


