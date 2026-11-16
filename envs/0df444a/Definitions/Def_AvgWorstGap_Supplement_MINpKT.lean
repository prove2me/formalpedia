-- Prove2me | Definitions.Def_AvgWorstGap_Supplement_MINpKT
-- name    : AvgWorstGap_Supplement_MINpKT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:06:15.394667+00:00
-- url     : https://prove2.me/theorems/2c5b7f20-c0b0-43ad-b722-224e08da10be
-- title:
--   $\mathrm{MINpKT}^O$
-- statement:
--   Let $O$ be an oracle and write $\mathrm{pK}^{t,O}_\lambda(x)$ for the probabilistic $t$-time-bounded Kolmogorov complexity of $x$ with oracle $O$ at success threshold $\lambda$ (the published $\mathrm{pK}$). $\mathrm{MINpKT}^O$ is the promise problem on instances $(x,1^s,1^t,1^a,1^b)$ with $1\le b\le a$, where
--
--   $$\mathrm{YES}=\{(x,1^s,1^t,1^a,1^b): \mathrm{pK}^{t,O}_{b/a}(x)\le s\},\qquad \mathrm{NO}=\{(x,1^s,1^t,1^a,1^b): \mathrm{pK}^{t,O}_{(b-1)/a}(x)> s\}.$$
--
--   This is the "no-gap" version of $\mathrm{Gap}_\rho\text{-}\mathrm{MINpKT}^O$: the time bound is the same on both sides and only the threshold drops from $b/a$ to $(b-1)/a$. Section 5 of the paper shows that its average-case complexity matches that of the gap version.
--
--   **Formalization Note** The guard $1\le b\le a$ keeps $b/a$ and $(b-1)/a$ in $[0,1]$, the domain of the definition of $\mathrm{pK}$; it is the guard of the published $\mathrm{Gap}_\rho\text{-}\mathrm{MINpKT}^O$. Instances use the published encoding $(x,1^s,1^t,1^a,1^b)$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Definition 2.8, p.14

import Mathlib
import Definitions.Def_AvgWorstGap_GapMINpKT

namespace AvgWorstGap.Supplement

open NKtLB

/-- **`MINpKT^O`** (Def. 2.8, Goldberg, Hu, Lu, Lyu, Oliveira, *The Gap Between Average-Case and
Worst-Case Complexity*, arXiv:2610.19162, version of October 30, 2026, p.14): "For an oracle `O`,
we define the promise language `MINpKT^O ≜ (YES, NO)` as
`YES = { (x, 1^s, 1^t, 1^a, 1^b) | pK^{t,O}_{b/a}(x) ≤ s }`,
`NO = { (x, 1^s, 1^t, 1^a, 1^b) | pK^{t,O}_{(b−1)/a}(x) > s }`."

Here `pK^{t,O}_λ(x)` is the published `pK O t λ x []` and the instance is the base `inst5`.

**Formalization Note.** An instance is in YES or NO only if `1 ≤ b ≤ a`, so that `b/a` and
`(b − 1)/a` lie in `[0, 1]`, the domain of Def. 2.2 (the guard of the base `GapMINpKT`). Values are
in `ℕ∞`, `⊤` when no `s` qualifies. -/
def MINpKT (O : Set (List Bool)) : PromiseProblem where
  yes := {z | ∃ (x : List Bool) (s t a b : ℕ), z = inst5 x s t a b ∧ 1 ≤ b ∧ b ≤ a ∧
    pK O t ((b : ℝ) / a) x [] ≤ (s : ℕ∞)}
  no := {z | ∃ (x : List Bool) (s t a b : ℕ), z = inst5 x s t a b ∧ 1 ≤ b ∧ b ≤ a ∧
    (s : ℕ∞) < pK O t (((b : ℝ) - 1) / a) x []}

end AvgWorstGap.Supplement


