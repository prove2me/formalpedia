-- Prove2me | Definitions.Def_TargetedSamplers_InPrRTC
-- name    : TargetedSamplers_InPrRTC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:06:10.906006+00:00
-- url     : https://prove2.me/theorems/0f4c53a9-1b7d-48dd-8a84-27633ba7d988
-- title:
--   The classes $\mathrm{prRTC}_Q[T,C]$ and $\mathrm{prcoRTC}_Q[T,C]$
-- statement:
--   Let $Q:\mathbb N\to\mathbb R$ and $T,C:\mathbb N\to\mathbb N$. A promise problem $\Pi=(\Pi_Y,\Pi_N)$ is in $\mathrm{prRTC}_Q[T,C]$ if a randomized algorithm $A$ takes $x\in\{0,1\}^n$ and random bits $r\in\{0,1\}^{C(n)}$, runs in time $T(n)$ on every input and every $r$, outputs one bit, and
--
--   $$\Pr_{r}[A(x;r)=0]\le \frac{Q(C(n))}{2^{C(n)}}\ \ \text{for every }x\in\Pi_Y,\qquad \Pr_r[A(x;r)=1]=0\ \ \text{for every }x\in\Pi_N.$$
--
--   In $\mathrm{prcoRTC}_Q[T,C]$ the one-sided error sits on the no-instances: $\Pr_r[A(x;r)=0]=0$ on $\Pi_Y$ and $\Pr_r[A(x;r)=1]\le Q(C(n))/2^{C(n)}$ on $\Pi_N$. Both are also defined relative to an oracle class: the conditions must hold for every oracle in the class.
--
--   **Formalization Note** "Time $T(n)$" is $\mathrm{budget}$: constant and polylogarithmic factors on the log-cost RAM. $Q$ is real-valued (at most $Q$ bad coin strings is the same as at most $\lfloor Q\rfloor$). The requirement of Definition 4.1 that $Q,T,C$ be time-constructible is carried by the theorems that use the classes.
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Definition 4.1, p.20 (pdf p.22)

import Mathlib
import Definitions.Def_TargetedSamplers_Machine
import Definitions.Def_TargetedSamplers_coinProb
import Definitions.Def_KarpLiptonOM_PromiseProblem

namespace TargetedSamplers

/-- `A` is a randomized algorithm with time `T` and `C` coins, relative to every oracle `O` in the
class `Ocl`: on every input `x` (inside or outside the promise), every coin string `r` of length
`C(|x|)` and every such oracle, it halts within `budget K k (T |x|) |x|` and outputs one bit. -/
def IsRandDecider (A : Program) (T C : ℕ → ℕ) (K k : ℕ) (Ocl : (List Bool → ℕ) → Prop) : Prop :=
  ∀ O, Ocl O → ∀ x r : List Bool, r.length = C x.length →
    ∃ b : Bool, A.RunsIn ⟨x, r, [], O⟩ (budget K k (T x.length) x.length) (some [b])

/-- `Pr_{r ∈ {0,1}^{C(n)}}[A^O(x; r) = b]`, `n = |x|`. -/
noncomputable def outProb (A : Program) (C : ℕ → ℕ) (O : List Bool → ℕ) (x : List Bool) (b : Bool) :
    ℝ :=
  coinProb (C x.length) (fun r => A.Outputs ⟨x, r, [], O⟩ (some [b]))

/-- `A` witnesses `Π ∈ prRTC_Q[T, C]` relative to the oracle class `Ocl` (one-sided error):
for every `O ∈ Ocl`, `Pr_r[A(x; r) = 0] ≤ Q(C(n))/2^{C(n)}` on yes-instances and
`Pr_r[A(x; r) = 1] = 0` on no-instances. -/
def IsRTCAlgRel (Q : ℕ → ℝ) (T C : ℕ → ℕ) (L : KarpLiptonOM.PromiseProblem) (Ocl : (List Bool → ℕ) → Prop)
    (A : Program) : Prop :=
  ∃ K k : ℕ, IsRandDecider A T C K k Ocl ∧ ∀ O, Ocl O →
    (∀ x ∈ L.yes, outProb A C O x false ≤ Q (C x.length) / 2 ^ C x.length) ∧
    (∀ x ∈ L.no, outProb A C O x true = 0)

/-- `A` witnesses `Π ∈ prcoRTC_Q[T, C]` relative to `Ocl` (one-sided error on no-instances):
`Pr_r[A(x; r) = 0] = 0` on yes-instances and `Pr_r[A(x; r) = 1] ≤ Q(C(n))/2^{C(n)}` on
no-instances. -/
def IsCoRTCAlgRel (Q : ℕ → ℝ) (T C : ℕ → ℕ) (L : KarpLiptonOM.PromiseProblem) (Ocl : (List Bool → ℕ) → Prop)
    (A : Program) : Prop :=
  ∃ K k : ℕ, IsRandDecider A T C K k Ocl ∧ ∀ O, Ocl O →
    (∀ x ∈ L.yes, outProb A C O x false = 0) ∧
    (∀ x ∈ L.no, outProb A C O x true ≤ Q (C x.length) / 2 ^ C x.length)

/-- The class `prRTC_Q[T, C]` (Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission,
manuscript sha256 599d0a59…, Definition 4.1, p.20): a promise problem `Π = (Π_Y, Π_N)` is in it if a
randomized algorithm `A` gets `x ∈ {0,1}ⁿ` and `r ∈ {0,1}^{C(n)}`, runs in time `T(n)`, and
`Pr_r[A(x; r) = 0] ≤ Q(C(n))/2^{C(n)}` for every `x ∈ Π_Y`, `Pr_r[A(x; r) = 1] = 0` for every
`x ∈ Π_N`.

**Formalization Note** "Runs in time `T(n)`" is `budget` (constant and polylogarithmic factors),
on every input and every coin string. `Q` is real-valued: the count of bad coin strings is at most
`Q`, which is the same as at most `⌊Q⌋`. The definition's precondition that `Q, T, C` be
time-constructible is carried by the theorems that use the class. The algorithm has no oracle
(`noOracle`). -/
def InPrRTC (Q : ℕ → ℝ) (T C : ℕ → ℕ) (L : KarpLiptonOM.PromiseProblem) : Prop :=
  ∃ A : Program, IsRTCAlgRel Q T C L (fun O => O = noOracle) A

/-- The class `prcoRTC_Q[T, C]`: the one-sided error is on the no-instances (complement of
`prRTC_Q[T, C]`, Lemma 4.16, p.25). -/
def InPrCoRTC (Q : ℕ → ℝ) (T C : ℕ → ℕ) (L : KarpLiptonOM.PromiseProblem) : Prop :=
  ∃ A : Program, IsCoRTCAlgRel Q T C L (fun O => O = noOracle) A

end TargetedSamplers


