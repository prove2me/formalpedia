-- Prove2me | Definitions.Def_SchedComplexity_Tardiness_Construction
-- name    : SchedComplexity_Tardiness_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:52:50.843112+00:00
-- url     : https://prove2.me/theorems/55a9993b-ebfa-4af0-b345-3d406c4f48e8
-- title:
--   The construction of KNAPSACK ∝ $n|1||\sum w_jT_j$ (Theorem 4(d))
-- statement:
--   The instance built from a KNAPSACK instance $a_1,\dots,a_t,b$ in the proof of Theorem 4(d) (p. 20). With $A=\sum_{j\in T}a_j$ and $a_*=\max_{j\in T}a_j$ (p. 16), put
--
--   $$t'=\Big\lceil\tfrac12(t+1)(A-b)+\tfrac12\,t(t+1)a_*^2\Big\rceil ,$$
--
--   and, for a parameter $\tau$, take $n=t+t'$ jobs:
--
--   $$p_j=\tau+a_j,\quad w_j=\tau+a_j+1,\quad d_j=t\tau+b\qquad (j\in T),$$
--   $$p_j=\tau,\quad w_j=\tau+1,\quad d_j=t\tau+b\qquad (j\notin T),$$
--
--   with threshold
--
--   $$y=\tfrac12\,t'(t'+1)\tau(\tau+1)+(t'+1)\tau(A-b)+t'.$$
--
--   For a processing order $\pi$ of these jobs, $c_\pi=C_{\pi(t)}-(t\tau+b)$, and with $a_j=0$ for $j\notin T$ the double sum $\sum_{t<j\le k\le n}a_{\pi(j)}a_{\pi(k)}$ is the last term of (2).
--
--   The paper requires $\tau>2t'+A$; that condition is a hypothesis of the theorems, not part of the construction.
--
--   **Formalization Note** The printed $t'=\tfrac12(t+1)(A-b)+\tfrac12t(t+1)a_*^2$ is a half-integer when $(t+1)(A-b)$ is odd, although $t'$ counts dummy jobs; the Lean uses its ceiling $\lfloor((t+1)(A-b)+t(t+1)a_*^2+1)/2\rfloor$, and $y$ is computed from the same $t'$ (the division by $2$ in $y$ is exact because $t'(t'+1)$ is even). $A-b$ is natural-number subtraction, exact under $b<A$. Jobs are `Fin (t + t')`: indices $0,\dots,t-1$ are the KNAPSACK items, indices $\ge t$ the dummies (`aExt`). $a_*=0$ when $t=0$. $C_{\pi(t)}$ is `posCompletion` from the model definition `SchedComplexity.Tardiness.Model`: the total processing time of the jobs in the first $t$ positions of $\pi$, i.e. the completion time of $\pi(t)$ when the jobs run without idle time from time $0$.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 16 (A, a_*), p. 20, proof of Theorem 4(d)

import Mathlib
import Definitions.Def_SchedComplexity_Tardiness_Model

namespace SchedComplexity.Tardiness

/-! # The construction of the reduction KNAPSACK ∝ n|1||Σw_jT_j

Brucker, Lenstra & Rinnooy Kan 1975, proof of Theorem 4, p. 16 (`A`, `a_*`) and part (d),
p. 20. The KNAPSACK instance is `a : Fin t → ℕ` (the paper's `a_1, …, a_t`, 0-based) and `b`;
`τ` is a free parameter, constrained in the theorems by `τ > 2t' + A`. -/

/-- `A = Σ_{j ∈ T} a_j` (p. 16). -/
def bigA {t : ℕ} (a : Fin t → ℕ) : ℕ := ∑ j, a j

/-- `a_* = max_{j ∈ T} a_j` (p. 16); `0` when `t = 0`. -/
def aStar {t : ℕ} (a : Fin t → ℕ) : ℕ := Finset.univ.sup a

/-- The number of dummy jobs `t'`. The paper prints `t' = ½(t+1)(A−b) + ½t(t+1)a_*²`, which is not
an integer when `(t+1)(A−b)` is odd although `t'` counts jobs. We take its ceiling,
`⌈½(t+1)(A−b) + ½t(t+1)a_*²⌉ = ⌊((t+1)(A−b) + t(t+1)a_*² + 1)/2⌋`; `A − b` is truncated
subtraction, exact under the standing assumption `b < A`. -/
def tPrime {t : ℕ} (a : Fin t → ℕ) (b : ℕ) : ℕ :=
  ((t + 1) * (bigA a - b) + t * (t + 1) * aStar a ^ 2 + 1) / 2

/-- The paper's convention "`a_j = 0` for `j ∉ T`" (p. 20): the jobs are `Fin (t + t')`; job `j`
with `j < t` is the KNAPSACK item `j` (the job set `T`), the jobs `j ≥ t` are the `t'` dummies. -/
def aExt {t : ℕ} (a : Fin t → ℕ) (b : ℕ) : Fin (t + tPrime a b) → ℕ :=
  fun j => if h : j.val < t then a ⟨j.val, h⟩ else 0

/-- Processing times: `p_j1 = τ + a_j` for `j ∈ T`, `p_j1 = τ` for `j ∉ T`. -/
def wtP {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) : Fin (t + tPrime a b) → ℕ :=
  fun j => τ + aExt a b j

/-- Weights: `w_j = τ + a_j + 1` for `j ∈ T`, `w_j = τ + 1` for `j ∉ T`. -/
def wtW {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) : Fin (t + tPrime a b) → ℕ :=
  fun j => τ + aExt a b j + 1

/-- Due dates: `d_j = tτ + b` for every job. -/
def wtD {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) : Fin (t + tPrime a b) → ℕ :=
  fun _ => t * τ + b

/-- The threshold `y = ½t'(t'+1)τ(τ+1) + (t'+1)τ(A−b) + t'` (p. 20). Since `t'(t'+1)` is even,
the natural-number division by `2` is exact. -/
def yThr {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) : ℕ :=
  tPrime a b * (tPrime a b + 1) * τ * (τ + 1) / 2 + (tPrime a b + 1) * τ * (bigA a - b) + tPrime a b

/-- `c_π = C_π(t) − (tτ + b)` (p. 20), in `ℤ`, for a processing order `π` of the constructed jobs. -/
def cPi {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) : ℤ :=
  (posCompletion (wtP a b τ) π t : ℤ) - ((t * τ + b : ℕ) : ℤ)

/-- `Σ_{t<j≤k≤n} a_π(j) a_π(k)` (the last term of (2), p. 20), over the 0-based positions
`t ≤ i ≤ k`, with `a_j = 0` for the dummy jobs. -/
def aPairSum {t : ℕ} (a : Fin t → ℕ) (b : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin (t + tPrime a b) => t ≤ i.val),
    ∑ k ∈ Finset.univ.filter (fun k : Fin (t + tPrime a b) => i ≤ k),
      (aExt a b (π i) : ℤ) * aExt a b (π k)

end SchedComplexity.Tardiness


