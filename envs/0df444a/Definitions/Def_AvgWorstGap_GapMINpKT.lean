-- Prove2me | Definitions.Def_AvgWorstGap_GapMINpKT
-- name    : AvgWorstGap_GapMINpKT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:50:28.626584+00:00
-- url     : https://prove2.me/theorems/cdd7b327-ebc0-4b07-9c87-73319f184106
-- title:
--   $\mathrm{Gap}_\rho$-$\mathrm{MINpKT}^O$ and $\mathrm{Gap}$-$\mathrm{MINpKT}^{\mathsf{PH}}\in\mathsf{prBPP}$
-- statement:
--   For an oracle $O$ and $\rho:\mathbb N\to\mathbb N$, $\mathrm{Gap}_\rho\text{-}\mathrm{MINpKT}^O$ is the promise problem with
--   $$\mathrm{YES}=\{(x,1^s,1^t,1^a,1^b) : \mathrm{pK}^{t,O}_{b/a}(x)\le s\},$$
--   $$\mathrm{NO}=\{(x,1^s,1^t,1^a,1^b) : \mathrm{pK}^{\rho(t+a+b),O}_{(b-1)/a}(x)\ge s+\log\rho(t+a+b)\}.$$
--   $\mathrm{Gap}\text{-}\mathrm{MINpKT}^O\in\mathsf{prBPP}$ means that $\mathrm{Gap}_\rho\text{-}\mathrm{MINpKT}^O\in\mathsf{prBPP}$ for $\rho(n)=n^c$ with some constant $c$. $\mathrm{Gap}\text{-}\mathrm{MINpKT}^{\mathsf{PH}}\in\mathsf{prBPP}$ means that this holds for every oracle $L\in\mathsf{PH}$, with $c$ allowed to depend on $L$.
--
--   **Formalization Note** An instance belongs to YES or NO only if $1\le b\le a$, so that $b/a$ and $(b-1)/a$ lie in $[0,1]$, the domain of Definition 2.2. Read literally, the instance $(x,1^0,1^0,1^1,1^0)$ would lie in both YES and NO. The constant $c$ is an integer $c\ge1$; a larger $c$ only shrinks NO, so this is equivalent to real $c>0$. $\log$ is base $2$. The NO condition is compared in the extended reals. Instances use the tuple encoding.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Definition 2.9 and the convention after Definition 2.10, p.15; p.4

import Mathlib
import Definitions.Def_AvgWorstGap_pK
import Definitions.Def_AvgWorstGap_InPrBPP
import Definitions.Def_AvgWorstGap_InSigmaPO

namespace AvgWorstGap

open NKtLB

/-- The instance `(x, 1^s, 1^t, 1^a, 1^b)` as one string. -/
def inst5 (x : List Bool) (s t a b : ℕ) : List Bool :=
  tupleEnc [x, unary s, unary t, unary a, unary b]

/-- **`Gap_ρ-MINpKT^O`** (Def. 2.9, arXiv:2610.19162, version of October 30, 2026, p.15): "For an
oracle `O` and `ρ: ℕ → ℕ`, we define the promise language `Gapρ-MINpKT^O ≜ (YES, NO)` as
`YES = { (x, 1^s, 1^t, 1^a, 1^b) | pK^{t,O}_{b/a}(x) ≤ s }`,
`NO = { (x, 1^s, 1^t, 1^a, 1^b) | pK^{ρ(t+a+b),O}_{(b−1)/a}(x) ≥ s + log ρ(t + a + b) }`."

**Formalization Note.** An instance is in YES or NO only if `1 ≤ b ≤ a`, so that `b/a` and
`(b − 1)/a` lie in `[0, 1]`, the domain of Def. 2.2 (without this guard `(x, 1^0, 1^0, 1^1, 1^0)`
would lie in YES ∩ NO). `log` is `Real.logb 2`; the NO condition compares in `EReal` (`⊤ ≥` every
value). Instances are encoded by `tupleEnc`. -/
def GapMINpKT (O : Set (List Bool)) (ρ : ℕ → ℕ) : PromiseProblem where
  yes := {z | ∃ (x : List Bool) (s t a b : ℕ), z = inst5 x s t a b ∧ 1 ≤ b ∧ b ≤ a ∧
    pK O t ((b : ℝ) / a) x [] ≤ (s : ℕ∞)}
  no := {z | ∃ (x : List Bool) (s t a b : ℕ), z = inst5 x s t a b ∧ 1 ≤ b ∧ b ≤ a ∧
    ((((s : ℝ) + Real.logb 2 (ρ (t + a + b)) : ℝ)) : EReal) ≤
      toEReal (pK O (ρ (t + a + b)) (((b : ℝ) - 1) / a) x [])}

/-- **`Gap-MINpKT^O ∈ prBPP`** (Def. 2.9, p.15): "there exists a constant `c > 0` such that
`Gapρ-MINpKT^O ∈ C` with `ρ(n) = n^c`".

**Formalization Note.** `c` ranges over the integers `c ≥ 1` (`n^c` must be a natural number; a
larger `c` only shrinks NO, so this is equivalent to real `c > 0` with `⌈n^c⌉`). -/
def GapInPrBPP (O : Set (List Bool)) : Prop :=
  ∃ c : ℕ, 1 ≤ c ∧ InPrBPP (GapMINpKT O (fun n => n ^ c))

/-- **`Gap-MINpKT^PH ∈ prBPP`** (p.4: "the corresponding promise problem is in randomized polynomial
time for every oracle language `O ∈ PH`"; p.15: "for every language `L ∈ D`, there exists a constant
`c > 0` such that `Π^L ∈ C` … `ρ` may depend on the choice of `L`"). -/
def GapPHInPrBPP : Prop := ∀ L : Set (List Bool), InPH L → GapInPrBPP L

end AvgWorstGap


