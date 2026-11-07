-- Prove2me | Definitions.Def_TargetedSamplers_InPrBPTC
-- name    : TargetedSamplers_InPrBPTC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:07:39.496937+00:00
-- url     : https://prove2.me/theorems/a8de6f3d-e09d-4303-8fce-7c586255dbb4
-- title:
--   The classes $\mathrm{prBPTC}_Q[T,C]$ and $\mathrm{prBPTIME}_Q[T]$
-- statement:
--   A promise problem $\Pi$ is in $\mathrm{prBPTC}_Q[T,C]$ if a randomized algorithm with $C(n)$ coins and time $T(n)$ errs with probability at most $Q(C(n))/2^{C(n)}$ on every yes-instance (outputs $0$) and on every no-instance (outputs $1$).
--
--   $\mathrm{prBPTIME}_Q[T]:=\mathrm{prBPTC}_Q[T,T]$: time $T(n)$, $T(n)$ coins, error at most $Q(T(n))/2^{T(n)}$.
--
--   **Formalization Note** Theorem 1.6 (p.5) says $\mathrm{prBPTIME}_Q[T]$ means error probability "$\delta=Q/T$". This is corrected to $Q/2^T$. With $Q=2^{(1-\epsilon)T}$ the printed bound is at least $1$ for large $T$ and imposes no condition, so the class would contain every promise problem, undecidable ones included. Definition 4.1 uses $Q(C)/2^C$, §4.1 speaks of error $2^{-\epsilon T}$ and the abstract of $\delta(T)=2^{-\Omega(T)}$. Time is $\mathrm{budget}$.
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Definition 4.1, p.20 (pdf p.22); Theorem 1.6, p.5 (pdf p.7)

import Mathlib
import Definitions.Def_TargetedSamplers_InPrRTC

namespace TargetedSamplers

/-- `A` witnesses `Π ∈ prBPTC_Q[T, C]` relative to `Ocl` (two-sided error): both
`Pr_r[A(x; r) = 0]` on yes-instances and `Pr_r[A(x; r) = 1]` on no-instances are at most
`Q(C(n))/2^{C(n)}`. -/
def IsBPTCAlgRel (Q : ℕ → ℝ) (T C : ℕ → ℕ) (L : KarpLiptonOM.PromiseProblem) (Ocl : (List Bool → ℕ) → Prop)
    (A : Program) : Prop :=
  ∃ K k : ℕ, IsRandDecider A T C K k Ocl ∧ ∀ O, Ocl O →
    (∀ x ∈ L.yes, outProb A C O x false ≤ Q (C x.length) / 2 ^ C x.length) ∧
    (∀ x ∈ L.no, outProb A C O x true ≤ Q (C x.length) / 2 ^ C x.length)

/-- The class `prBPTC_Q[T, C]` (Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027
submission, manuscript sha256 599d0a59…, Definition 4.1, p.20): a randomized algorithm with `C(n)`
coins and time `T(n)` errs with probability at most `Q(C(n))/2^{C(n)}` on yes-instances and on
no-instances.

**Formalization Note** As for `InPrRTC`: time is `budget`, `Q` is real-valued, no oracle. -/
def InPrBPTC (Q : ℕ → ℝ) (T C : ℕ → ℕ) (L : KarpLiptonOM.PromiseProblem) : Prop :=
  ∃ A : Program, IsBPTCAlgRel Q T C L (fun O => O = noOracle) A

/-- The class `prBPTIME_Q[T] := prBPTC_Q[T, T]`: time `T(n)`, `T(n)` coins, error at most
`Q(T(n))/2^{T(n)}` (Theorem 1.6, p.5; Theorem 4.2, p.20; Theorem 4.30, p.42).

**Formalization Note** Theorem 1.6 prints "error probability δ = Q/T". This is read `Q/2^T`: with
`Q = 2^{(1−ϵ)T}`, `Q/T ≥ 1` for large `T` and the printed bound would impose nothing, while
Definition 4.1 uses `Q(C)/2^C`, §4.1 says "from `2^{−ϵ·T}`" and the abstract says `δ(T) = 2^{−Ω(T)}`.
An algorithm reads at most as many coins as its running time, so `T` coins is the natural count. -/
def InPrBPTIME (Q : ℕ → ℝ) (T : ℕ → ℕ) (L : KarpLiptonOM.PromiseProblem) : Prop :=
  InPrBPTC Q T T L

end TargetedSamplers


