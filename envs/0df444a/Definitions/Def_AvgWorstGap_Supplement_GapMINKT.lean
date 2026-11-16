-- Prove2me | Definitions.Def_AvgWorstGap_Supplement_GapMINKT
-- name    : AvgWorstGap_Supplement_GapMINKT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:05:47.84702+00:00
-- url     : https://prove2.me/theorems/d7f170a2-8edc-44a1-bfe5-495eef866f09
-- title:
--   $\mathrm{Gap}_\rho\text{-}\mathrm{MINKT}^O$ and $\mathrm{Mild}\text{-}\mathrm{Gap}_\rho\text{-}\mathrm{MINKT}^O$ (corrected: $t\ge2$), and their membership in $\mathsf P$
-- statement:
--   Let $O$ be an oracle, $\rho:\mathbb N\to\mathbb N$, and write $K^{t,O}(x)$ for the $t$-time-bounded Kolmogorov complexity of $x$ with oracle $O$ (the published $K^{t,O}$). Instances are triples $(x,1^s,1^t)$ with $t\ge2$.
--
--   1. $\mathrm{Gap}_\rho\text{-}\mathrm{MINKT}^O$ has $$\mathrm{YES}=\{(x,1^s,1^t): K^{t,O}(x)\le s\},\qquad \mathrm{NO}=\{(x,1^s,1^t): K^{\rho(t),O}(x)\ge s+\log\rho(t)\}.$$
--   2. $\mathrm{Mild}\text{-}\mathrm{Gap}_\rho\text{-}\mathrm{MINKT}^O$ has the same YES set and $$\mathrm{NO}=\{(x,1^s,1^t): K^{t+\rho(|x|),O}(x)\ge s+\log\rho(t)\}.$$
--
--   $\mathrm{Gap}\text{-}\mathrm{MINKT}^O\in\mathsf P$ means that $\mathrm{Gap}_\rho\text{-}\mathrm{MINKT}^O\in\mathsf{prP}$ for $\rho(n)=n^c$ with some constant $c$, and similarly for the mild version. $\mathrm{Gap}\text{-}\mathrm{MINKT}^{\mathsf{PH}}\in\mathsf P$ means that $\mathrm{Gap}\text{-}\mathrm{MINKT}^L\in\mathsf P$ for every $L\in\mathsf{PH}$, where $c$ may depend on $L$.
--
--   The standard gap allows the NO side polynomially more time; the mild gap allows only an additive $\rho(|x|)$. Theorems 4.1 and 4.3 relate these two regimes to the deterministic average-case and worst-case complexity of $\mathsf{PH}$.
--
--   **Formalization Note** (correction) The paper's definitions admit every $t$. At $t\le1$ and $\rho(n)=n^c$ one has $\log\rho(t)=0$, and $K^{0,O}(\epsilon)=k_0$ is finite (a program whose machine halts at step $0$). So $(\epsilon,1^{k_0},1^0)$ lies in YES $\cap$ NO for every oracle and every $c$, no algorithm decides the problem, and "$\in\mathsf P$" would be false for every oracle. The guard $t\ge2$ restores disjointness, because then $\log\rho(t)\ge1$. The constant $c$ is an integer $c\ge1$; a larger $c$ only shrinks NO, so this is equivalent to a real $c>0$. $\log$ is $\log_2$, complexities take values in $\mathbb N\cup\{\infty\}$, and the triple is encoded by the published tuple encoding.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Definition 2.6 and Definition 2.7, p.14; convention for Π^D ∈ C, p.15

import Mathlib
import Definitions.Def_AvgWorstGap_Kt
import Definitions.Def_AvgWorstGap_InSigmaPO
import Definitions.Def_AvgWorstGap_Supplement_InPrP

namespace AvgWorstGap.Supplement

open NKtLB

/-- The instance `(x, 1^s, 1^t)` as one string (the encoding of the base `MINKT`). -/
def inst3 (x : List Bool) (s t : ℕ) : List Bool := tupleEnc [x, unary s, unary t]

/-- **`Gap_ρ-MINKT^O`** (Def. 2.6, Goldberg, Hu, Lu, Lyu, Oliveira, *The Gap Between Average-Case
and Worst-Case Complexity*, arXiv:2610.19162, version of October 30, 2026, p.14): "For an oracle `O`
and `ρ: ℕ → ℕ`, we define the promise language `Gapρ-MINKT^O ≜ (YES, NO)` as
`YES = { (x, 1^s, 1^t) | K^{t,O}(x) ≤ s }`, `NO = { (x, 1^s, 1^t) | K^{ρ(t),O}(x) ≥ s + log ρ(t) }`."

Here `K^{t,O}(x)` is the published `Kt O t x [] []`.

**Formalization Note (correction).** An instance is in YES or NO only if `t ≥ 2`. Read literally,
the definition is not a promise problem at `t ≤ 1`: with `ρ(n) = n^c` one has `ρ(0) = 0`,
`ρ(1) = 1` and `log ρ(t) = 0`, and `K^{0,O}(ϵ) = k₀ < ∞` (a program whose single machine halts at
step `0`), so `(ϵ, 1^{k₀}, 1^0)` lies in YES ∩ NO for every oracle and every `c`; no algorithm
decides it, and "`Gap-MINKT^PH ∈ P`" would be false. For `t ≥ 2`, `log ρ(t) ≥ 1` and YES, NO are
disjoint. `log` is `Real.logb 2`; the NO condition compares in `EReal` (`⊤ ≥` every value);
instances are encoded by `tupleEnc`. -/
def GapMINKT (O : Set (List Bool)) (ρ : ℕ → ℕ) : PromiseProblem where
  yes := {z | ∃ (x : List Bool) (s t : ℕ), z = inst3 x s t ∧ 2 ≤ t ∧ Kt O t x [] [] ≤ (s : ℕ∞)}
  no := {z | ∃ (x : List Bool) (s t : ℕ), z = inst3 x s t ∧ 2 ≤ t ∧
    ((((s : ℝ) + Real.logb 2 (ρ t) : ℝ)) : EReal) ≤ toEReal (Kt O (ρ t) x [] [])}

/-- **`Mild-Gap_ρ-MINKT^O`** (Def. 2.7, p.14): "For an oracle `O` and a function `ρ: ℕ → ℕ`, we
define the promise language `Mild-Gapρ-MINKT^O ≜ (YES, NO)` as
`YES = { (x, 1^s, 1^t) | K^{t,O}(x) ≤ s }`,
`NO = { (x, 1^s, 1^t) | K^{t+ρ(|x|),O}(x) ≥ s + log ρ(t) }`."

**Formalization Note (correction).** The same guard `t ≥ 2` as `GapMINKT`, for the same reason
(at `x = ϵ`, `t = 0`: `K^{0+ρ(0),O}(ϵ) = K^{0,O}(ϵ)` and `log ρ(0) = 0`). The NO time is
`t + ρ(|x|)` and the NO threshold `log ρ(t)`, as printed. -/
def MildGapMINKT (O : Set (List Bool)) (ρ : ℕ → ℕ) : PromiseProblem where
  yes := {z | ∃ (x : List Bool) (s t : ℕ), z = inst3 x s t ∧ 2 ≤ t ∧ Kt O t x [] [] ≤ (s : ℕ∞)}
  no := {z | ∃ (x : List Bool) (s t : ℕ), z = inst3 x s t ∧ 2 ≤ t ∧
    ((((s : ℝ) + Real.logb 2 (ρ t) : ℝ)) : EReal) ≤ toEReal (Kt O (t + ρ x.length) x [] [])}

/-- **`Gap-MINKT^O ∈ P`** (Def. 2.6, p.14): "there exists a constant `c > 0` such that
`Gapρ-MINKT^O ∈ C` with `ρ(n) = n^c`".

**Formalization Note.** `c` ranges over the integers `c ≥ 1` (`ρ` is `ℕ`-valued; a larger `c` only
shrinks NO, so this is equivalent to a real `c > 0` with `⌈n^c⌉`). -/
def GapKTInP (O : Set (List Bool)) : Prop :=
  ∃ c : ℕ, 1 ≤ c ∧ InPrP (GapMINKT O (fun n => n ^ c))

/-- **`Gap-MINKT^PH ∈ P`** (Theorem 4.1, p.34, with the convention of p.15: "for every language
`L ∈ D`, there exists a constant `c > 0` such that `Π^L ∈ C` with gap parameter `ρ(n) = n^c`"). -/
def GapKTPHInP : Prop := ∀ L : Set (List Bool), InPH L → GapKTInP L

/-- **`Mild-Gap-MINKT^O ∈ P`** (Def. 2.7, p.14): some integer `c ≥ 1` with
`Mild-Gapρ-MINKT^O ∈ P` for `ρ(n) = n^c`. -/
def MildGapKTInP (O : Set (List Bool)) : Prop :=
  ∃ c : ℕ, 1 ≤ c ∧ InPrP (MildGapMINKT O (fun n => n ^ c))

/-- **`Mild-Gap-MINKT^PH ∈ P`** (Theorems 4.1, 4.3, p.34; convention of p.15). -/
def MildGapKTPHInP : Prop := ∀ L : Set (List Bool), InPH L → MildGapKTInP L

end AvgWorstGap.Supplement


