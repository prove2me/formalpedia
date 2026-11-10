-- Prove2me | Definitions.Def_AvgWorstGap_MildGapMINpKT
-- name    : AvgWorstGap_MildGapMINpKT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:51:43.398809+00:00
-- url     : https://prove2.me/theorems/dcd7c713-2d9b-4c73-a55b-bb0ce616f903
-- title:
--   $\mathrm{Mild}$-$\mathrm{Gap}_\rho$-$\mathrm{MINpKT}^O$ and $\mathrm{Mild}$-$\mathrm{Gap}$-$\mathrm{MINpKT}^{\mathsf{PH}}\in\mathsf{prBPP}$
-- statement:
--   For an oracle $O$ and $\rho:\mathbb N\to\mathbb N$, $\mathrm{Mild}\text{-}\mathrm{Gap}_\rho\text{-}\mathrm{MINpKT}^O$ is the promise problem with
--   $$\mathrm{YES}=\{(x,1^s,1^t,1^a,1^b) : \mathrm{pK}^{t,O}_{b/a}(x)\le s\},$$
--   $$\mathrm{NO}=\{(x,1^s,1^t,1^a,1^b) : \mathrm{pK}^{t+\rho(|x|+a+b),O}_{(b-1)/a}(x)\ge s+\log\rho(t+a+b)\}.$$
--   The NO side allows only an additive increase $t+\mathrm{poly}(n)$ of the time bound, against $\mathrm{poly}(t)$ for the standard gap problem. $\mathrm{Mild}\text{-}\mathrm{Gap}\text{-}\mathrm{MINpKT}^O\in\mathsf{prBPP}$ and its $\mathsf{PH}$ version are defined as for the standard gap problem.
--
--   **Formalization Note** The same guard $1\le b\le a$, integer $c\ge1$, base-$2$ logarithm, extended-real comparison and tuple encoding as for $\mathrm{Gap}_\rho\text{-}\mathrm{MINpKT}^O$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Definition 2.10 and the convention after it, p.15

import Mathlib
import Definitions.Def_AvgWorstGap_GapMINpKT

namespace AvgWorstGap

open NKtLB

/-- **`Mild-Gap_ρ-MINpKT^O`** (Def. 2.10, arXiv:2610.19162, version of October 30, 2026, p.15):
"For an oracle `O` and a function `ρ: ℕ → ℕ`, we define the promise language
`Mild-Gapρ-MINpKT^O ≜ (YES, NO)` as
`YES = { (x, 1^s, 1^t, 1^a, 1^b) | pK^{t,O}_{b/a}(x) ≤ s }`,
`NO = { (x, 1^s, 1^t, 1^a, 1^b) | pK^{t+ρ(|x|+a+b),O}_{(b−1)/a}(x) ≥ s + log ρ(t + a + b) }`."

**Formalization Note.** The same guard `1 ≤ b ≤ a`, `Real.logb 2`, `EReal` comparison and
`tupleEnc` instances as `GapMINpKT`. -/
def MildGapMINpKT (O : Set (List Bool)) (ρ : ℕ → ℕ) : PromiseProblem where
  yes := {z | ∃ (x : List Bool) (s t a b : ℕ), z = inst5 x s t a b ∧ 1 ≤ b ∧ b ≤ a ∧
    pK O t ((b : ℝ) / a) x [] ≤ (s : ℕ∞)}
  no := {z | ∃ (x : List Bool) (s t a b : ℕ), z = inst5 x s t a b ∧ 1 ≤ b ∧ b ≤ a ∧
    ((((s : ℝ) + Real.logb 2 (ρ (t + a + b)) : ℝ)) : EReal) ≤
      toEReal (pK O (t + ρ (x.length + a + b)) (((b : ℝ) - 1) / a) x [])}

/-- **`Mild-Gap-MINpKT^O ∈ prBPP`** (Def. 2.10, p.15): some integer `c ≥ 1` with
`Mild-Gapρ-MINpKT^O ∈ prBPP` for `ρ(n) = n^c`. -/
def MildGapInPrBPP (O : Set (List Bool)) : Prop :=
  ∃ c : ℕ, 1 ≤ c ∧ InPrBPP (MildGapMINpKT O (fun n => n ^ c))

/-- **`Mild-Gap-MINpKT^PH ∈ prBPP`** (p.4, p.15): for every `L ∈ PH`,
`Mild-Gap-MINpKT^L ∈ prBPP` (the constant may depend on `L`). -/
def MildGapPHInPrBPP : Prop := ∀ L : Set (List Bool), InPH L → MildGapInPrBPP L

end AvgWorstGap


