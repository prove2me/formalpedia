-- Prove2me | Definitions.Def_AvgWorstGap_Supplement_Relativized
-- name    : AvgWorstGap_Supplement_Relativized
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:07:49.543856+00:00
-- url     : https://prove2.me/theorems/2939f934-c3cf-4112-96e4-2f2fac78e96e
-- title:
--   Relativized $\mathrm{Gap}$/$\mathrm{Mild}\text{-}\mathrm{Gap}\text{-}\mathrm{MINpKT}^{L,O}$, $\mathsf{PH}^O$, $\mathsf{prBPP}^O$, and the two statements of Theorem 6.1
-- statement:
--   Fix an oracle $O$.
--
--   1. $\mathsf{PH}^O=\bigcup_{k\ge0}\Sigma_k^{\mathsf P,O}$.
--   2. A promise problem is in $\mathsf{prBPP}^O$ if a probabilistic polynomial-time machine with oracle access to $O$ outputs $1$ on every YES instance and $0$ on every NO instance, each with probability at least $2/3$.
--   3. For a language $L$, $\mathrm{pK}^{t,L,O}_\lambda(x)$ is probabilistic $t$-time-bounded Kolmogorov complexity in which programs have oracle access to both $L$ and $O$. $\mathrm{Gap}_\rho\text{-}\mathrm{MINpKT}^{L,O}$ asks, on $(x,1^s,1^t,1^a,1^b)$, whether $\mathrm{pK}^{t,L,O}_{b/a}(x)\le s$ (YES) or $\mathrm{pK}^{\rho(t+a+b),L,O}_{(b-1)/a}(x)\ge s+\log\rho(t+a+b)$ (NO). $\mathrm{Mild}\text{-}\mathrm{Gap}_\rho\text{-}\mathrm{MINpKT}^{L,O}$ has NO condition $\mathrm{pK}^{t+\rho(|x|+a+b),L,O}_{(b-1)/a}(x)\ge s+\log\rho(t+a+b)$.
--   4. $\mathrm{Gap}\text{-}\mathrm{MINpKT}^{\mathsf{PH}^O,O}\in\mathsf{prBPP}^O$ means: for every $L\in\mathsf{PH}^O$ there is a polynomial $\rho$ with $\mathrm{Gap}_\rho\text{-}\mathrm{MINpKT}^{L,O}\in\mathsf{prBPP}^O$.
--   5. $\mathrm{Mild}\text{-}\mathrm{Gap}\text{-}\mathrm{MINpKT}^{\mathsf{PH}^O,O}\notin\mathsf{prBPP}^O$ means: there is $L\in\mathsf{PH}^O$ such that for no constant $c\ge1$, with $\rho(n)=c\cdot n^c$, is $\mathrm{Mild}\text{-}\mathrm{Gap}_\rho\text{-}\mathrm{MINpKT}^{L,O}\in\mathsf{prBPP}^O$.
--
--   These are the relativized notions of §6, which shows that Theorem 1.1's gap reduction cannot be proved by relativizing techniques.
--
--   **Formalization Note** Access to both $L$ and $O$ is realized by the join $L\oplus O=\{0u:u\in L\}\cup\{1u:u\in O\}$: the programs inside $\mathrm{pK}$ query $L\oplus O$, at the cost of one bit per query. The problems are the published $\mathrm{Gap}_\rho\text{-}\mathrm{MINpKT}$ and $\mathrm{Mild}\text{-}\mathrm{Gap}_\rho\text{-}\mathrm{MINpKT}$ with oracle $L\oplus O$, with their guard $1\le b\le a$. The paper writes $K^{t,L,O}(x\mid r)$ inside $\mathrm{pK}^{t,L,O}$; it is read as the relativization of Def. 2.2, with $r\in\{0,1\}^t$ on the randomness tape, since §6 obtains relativization "by providing oracle access to all machines involved". The decider queries $O$ only. In the "$\in$" statement $\rho$ ranges over polynomials with natural coefficients; in the "$\notin$" statement $c$ ranges over integers $c\ge1$ (NO shrinks as $c$ grows, so this excludes every real $c\ge1$).
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), §6 "Relativization", pp.38–39 (pK^{t,L,O}_λ, Gap_ρ-MINpKT^{L,O}, Mild-Gap_ρ-MINpKT^{L,O}, "∈ prBPP^O", "∉ prBPP^O")

import Mathlib
import Definitions.Def_AvgWorstGap_InPrBPP
import Definitions.Def_AvgWorstGap_InSigmaPO
import Definitions.Def_AvgWorstGap_GapMINpKT
import Definitions.Def_AvgWorstGap_MildGapMINpKT

namespace AvgWorstGap.Supplement

open NKtLB

/-- **The join `L ⊕ O`** of two oracles: `{0u | u ∈ L} ∪ {1u | u ∈ O}`. One query to `L ⊕ O`
answers one query to `L` or to `O`. -/
def joinOracle (L O : Set (List Bool)) : Set (List Bool) :=
  {u | ∃ v, u = false :: v ∧ v ∈ L} ∪ {u | ∃ v, u = true :: v ∧ v ∈ O}

/-- **`PH^O`** (Goldberg, Hu, Lu, Lyu, Oliveira, *The Gap Between Average-Case and Worst-Case
Complexity*, arXiv:2610.19162, version of October 30, 2026, §6, p.39): `⋃_{k ≥ 0} Σ_k^{P,O}`
(the published `InSigmaPO`). -/
def InPHO (O L : Set (List Bool)) : Prop := ∃ k : ℕ, InSigmaPO O k L

/-- **A randomized oracle machine with oracle `O` decides a promise problem in time `T`**: the base
`DecidesWithin` with oracle `O` in place of `∅` (on every input `z` and random string of length
`T(|z|)` the machine halts within `T(|z|)` steps; it outputs `1` on YES and `0` on NO, each with
probability at least `2/3`). -/
def DecidesWithinO (O : Set (List Bool)) (M : Machine) (T : ℕ → ℕ) (P : PromiseProblem) : Prop :=
  ∀ z : List Bool,
    (∀ r : List Bool, r.length = T z.length → (M.run O ⟨z, [], [], r⟩ (T z.length)).state = M.halt) ∧
    (z ∈ P.yes →
      2 / 3 ≤ prob (T z.length) (fun r => M.HaltsWith O ⟨z, [], [], r⟩ (T z.length) (bitOut true))) ∧
    (z ∈ P.no →
      2 / 3 ≤ prob (T z.length) (fun r => M.HaltsWith O ⟨z, [], [], r⟩ (T z.length) (bitOut false)))

/-- **`prBPP^O`**: an oracle probabilistic polynomial-time machine with oracle `O` decides the promise
problem. -/
def InPrBPPO (O : Set (List Bool)) (P : PromiseProblem) : Prop :=
  ∃ (p : Polynomial ℕ) (M : Machine), DecidesWithinO O M (fun n => p.eval n) P

/-- **"`Gap-MINpKT^{PH^O,O} ∈ prBPP^O`"** (§6, pp.38–39): "for every language `L ∈ PH^O`, there is a
polynomial `ρ` and an oracle probabilistic polynomial-time algorithm that solves `Gapρ-MINpKT^{L,O}`
when given oracle access to `O`." Here `Gapρ-MINpKT^{L,O}` (p.38: YES `pK^{t,L,O}_{b/a}(x) ≤ s`,
NO `pK^{ρ(t+a+b),L,O}_{(b−1)/a}(x) ≥ s + log ρ(t + a + b)`) is the published `GapMINpKT` with the
programs' oracle `L ⊕ O`.

**Formalization Note.** Programs "with oracle access to both `L` and `O`" query the join
`L ⊕ O` (one extra bit per query). `pK^{t,L,O}_λ(x)` is Def. 2.2's `pK` (randomness `r ∈ {0,1}^t`
on the randomness tape) relativized to `L ⊕ O`; §6 obtains relativization "by providing oracle
access to all machines involved". `ρ` ranges over `Polynomial ℕ`. The decider queries `O` only. -/
def GapPHOInPrBPPO (O : Set (List Bool)) : Prop :=
  ∀ L : Set (List Bool), InPHO O L →
    ∃ ρ : Polynomial ℕ, InPrBPPO O (GapMINpKT (joinOracle L O) (fun n => ρ.eval n))

/-- **"`Mild-Gap-MINpKT^{PH^O,O} ∉ prBPP^O`"** (§6, p.39): "there is a language `L ∈ PH^O` such that
for no constant `c ≥ 1` and polynomial `ρ(n) = c · n^c` we have `Mild-Gapρ-MINpKT^{L,O} ∈ prBPP^O`."
Here `Mild-Gapρ-MINpKT^{L,O}` (NO: `pK^{t+ρ(|x|+a+b),L,O}_{(b−1)/a}(x) ≥ s + log ρ(t + a + b)`) is
the published `MildGapMINpKT` with the programs' oracle `L ⊕ O`.

**Formalization Note.** `c` ranges over the integers `c ≥ 1` (`ρ` is `ℕ`-valued; NO shrinks as `c`
grows, so excluding every integer `c ≥ 1` excludes every real `c ≥ 1`). -/
def MildGapPHONotInPrBPPO (O : Set (List Bool)) : Prop :=
  ∃ L : Set (List Bool), InPHO O L ∧
    ∀ c : ℕ, 1 ≤ c → ¬ InPrBPPO O (MildGapMINpKT (joinOracle L O) (fun n => c * n ^ c))

end AvgWorstGap.Supplement


