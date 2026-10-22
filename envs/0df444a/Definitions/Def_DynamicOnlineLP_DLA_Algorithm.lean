-- Prove2me | Definitions.Def_DynamicOnlineLP_DLA_Algorithm
-- name    : DynamicOnlineLP_DLA_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T19:27:29.972783+00:00
-- url     : https://prove2.me/theorems/1dd75eba-8ba1-417d-8d82-7e7df6358f1c
-- title:
--   Algorithm DLA (dynamic learning algorithm): ε = 2^{-E}, L = {εn, …, 2^{E-1}εn}, h_ℓ = ε√(n/ℓ), dual prices of (13), executed decisions
-- statement:
--   Fix $\varepsilon=2^{-E}$ with $E\ge 1$ and assume $\varepsilon n$ is an integer. Let
--
--   $$L=\{\varepsilon n,\,2\varepsilon n,\,\dots,\,2^{E-1}\varepsilon n\},\qquad h_\ell=\varepsilon\sqrt{n/\ell}.$$
--
--   For $\ell\in L$ let $\hat p^{\ell}$ be an optimal dual price of the **partial linear program (13)** on the columns that arrived at times $1,\dots,\ell$:
--
--   $$\max\sum_{t=1}^{\ell}\pi_tx_t\quad\text{s.t.}\quad\sum_{t=1}^{\ell}a_{it}x_t\le(1-h_\ell)\frac{\ell}{n}b_i\ (i=1,\dots,m),\quad 0\le x_t\le 1.$$
--
--   Since optimal dual prices need not be unique, the algorithm is parametrized by a **dual-selection rule**: a map that, from $\ell$, the arrived columns and a right-hand side $d$, returns a price vector. A rule is **valid** if its output depends only on the first $\ell$ arrivals, and, whenever $\ell\le n$ and $d\ge0$, it is an optimal dual price of the partial program on the first $\ell$ arrivals with right-hand side $d$.
--
--   **Algorithm DLA.** (1) Set $t_0=\varepsilon n$ and $x_t=0$ for $t\le t_0$. (2) For $t=t_0+1,\dots,n$: (a) set $\hat x_t=x_t(\hat p^{\ell})$, the threshold rule at price $\hat p^\ell$, where $\ell=2^r\varepsilon n$ with $r$ the largest integer such that $\ell<t$; (b) if $a_{it}\hat x_t\le b_i-\sum_{j=1}^{t-1}a_{ij}x_j$ for all $i$, set $x_t=\hat x_t$, otherwise $x_t=0$.
--
--   The file defines $\varepsilon$, $\varepsilon n$, $L$, $h_\ell$, dual-selection rules and their validity, $\hat p^\ell$ in arrival order $\sigma$, the proposed decision $\hat x_t$, the executed decisions $x_t$ (computed recursively together with the resources consumed so far) and the online objective $\sum_t\pi_tx_t$.
--
--   **Formalization Note** Times are 0-based: Lean time $\tau$ is the paper's time $\tau+1$, so step (1) is $\tau<\varepsilon n$, and the learning time for $\tau\ge\varepsilon n$ is $\varepsilon n\cdot 2^{\lfloor\log_2\lfloor\tau/(\varepsilon n)\rfloor\rfloor}$, the largest $2^r\varepsilon n\le\tau$. $\varepsilon n$ is computed as the natural-number quotient $n/2^E$, exact under the theorems' hypothesis $2^E\mid n$. A dual-selection rule receives the whole arrival sequence but a valid rule may not depend on arrivals after time $\ell$; this keeps the algorithm online.
-- source:
--   Agrawal, Wang, Ye, A Dynamic Near-Optimal Algorithm for Online Linear Programming, Oper. Res. 62(4), 2014, pp. 883–884, Eq. (13), definition of h_ℓ, Algorithm DLA; p. 884, §3.1 (ε = 2^{-E}, L)

import Mathlib
import Definitions.Def_DynamicOnlineLP_DLA_PackingLP
import Definitions.Def_DynamicOnlineLP_DLA_Instance

namespace DynamicOnlineLP.DLA

/-- The accuracy parameter `ε = 2^{-E}` of §3.1. -/
noncomputable def eps (E : ℕ) : ℝ := (1 / 2 : ℝ) ^ E

/-- The length `εn = n / 2^E` of the initial learning period (an integer when `2^E ∣ n`). -/
def learnLen (n E : ℕ) : ℕ := n / 2 ^ E

/-- The set `L = {εn, 2εn, …, 2^{E−1} εn}` of learning times of §3.1. -/
def phases (n E : ℕ) : Finset ℕ :=
  (Finset.range E).image (fun r => learnLen n E * 2 ^ r)

/-- `h_ℓ = ε √(n/ℓ)`, the slack of the partial LP (13). -/
noncomputable def slack (n E ℓ : ℕ) : ℝ := eps E * Real.sqrt ((n : ℝ) / (ℓ : ℝ))

/-- A dual-selection rule: given `ℓ`, the arrival sequence (objective coefficients and constraint
columns, indexed by 0-based arrival time) and a right-hand side `d`, it returns a price vector.
It is meant to return an optimal dual price `p̂^ℓ` of the partial LP on the first `ℓ` arrivals. -/
def DualRule (m n : ℕ) : Type :=
  ℕ → (Fin n → ℝ) → (Fin n → Fin m → ℝ) → (Fin m → ℝ) → (Fin m → ℝ)

/-- A valid dual-selection rule (1) sees only the first `ℓ` arrivals: its output does not change
when arrivals at times `≥ ℓ` change; and (2) for `ℓ ≤ n` and every right-hand side `d ≥ 0` it
returns an optimal dual price of the partial LP on the first `ℓ` arrivals with right-hand side `d`
(the `p`-part of an optimal solution of the dual (8) of that LP). -/
def IsValidDualRule {m n : ℕ} (rule : DualRule m n) : Prop :=
  (∀ (ℓ : ℕ) (π π' : Fin n → ℝ) (a a' : Fin n → Fin m → ℝ) (d : Fin m → ℝ),
      (∀ t : Fin n, t.val < ℓ → π t = π' t ∧ a t = a' t) → rule ℓ π a d = rule ℓ π' a' d) ∧
  ∀ (ℓ : ℕ) (π : Fin n → ℝ) (a : Fin n → Fin m → ℝ) (d : Fin m → ℝ),
    ℓ ≤ n → (∀ i : Fin m, 0 ≤ d i) → IsOptimalDualPrice (firstTimes n ℓ) π a d (rule ℓ π a d)

/-- `p̂^ℓ`: the dual price the rule learns at time `ℓ` in arrival order `σ`, for the partial LP
(13) on the first `ℓ` arrivals with right-hand side `(1 - h_ℓ)(ℓ/n) b`. -/
noncomputable def learnedPrice {m n : ℕ} (I : Instance m n) (rule : DualRule m n) (E : ℕ)
    (σ : Equiv.Perm (Fin n)) (ℓ : ℕ) : Fin m → ℝ :=
  rule ℓ (I.arrPi σ) (I.arrA σ) (fun i => (1 - slack n E ℓ) * ((ℓ : ℝ) / (n : ℝ)) * I.b i)

/-- For a 0-based time `τ ≥ εn` (paper time `t = τ + 1 > εn`), the learning time
`ℓ = 2^r εn` with `r` the largest integer such that `ℓ < t`. -/
def phaseStart (n E τ : ℕ) : ℕ :=
  learnLen n E * 2 ^ Nat.log 2 (τ / learnLen n E)

/-- Step 2(a) of Algorithm DLA: the proposed decision `x̂_t = x_t(p̂^ℓ)` at 0-based time `t`;
it is `0` during the initial period `t < εn` (step 1). -/
noncomputable def dlaProposal {m n : ℕ} (I : Instance m n) (rule : DualRule m n) (E : ℕ)
    (σ : Equiv.Perm (Fin n)) (t : Fin n) : ℝ :=
  if t.val < learnLen n E then 0
  else threshold (I.arrPi σ) (I.arrA σ) (learnedPrice I rule E σ (phaseStart n E t.val)) t

/-- Step 2(b) of Algorithm DLA: given the resources `used` consumed by the earlier decisions,
accept the proposal if `a_{it} x̂_t ≤ b_i - ∑_{j<t} a_{ij} x_j` for all `i`, and set `x_t = 0`
otherwise. -/
noncomputable def dlaDecision {m n : ℕ} (I : Instance m n) (rule : DualRule m n) (E : ℕ)
    (σ : Equiv.Perm (Fin n)) (used : Fin m → ℝ) (t : Fin n) : ℝ :=
  by classical exact
    if ∀ i : Fin m, I.arrA σ t i * dlaProposal I rule E σ t ≤ I.b i - used i
    then dlaProposal I rule E σ t else 0

/-- Resources consumed by the DLA's executed decisions at the first `τ` times. -/
noncomputable def dlaUsed {m n : ℕ} (I : Instance m n) (rule : DualRule m n) (E : ℕ)
    (σ : Equiv.Perm (Fin n)) : ℕ → Fin m → ℝ
  | 0 => fun _ => 0
  | τ + 1 => fun i =>
      if h : τ < n then
        dlaUsed I rule E σ τ i +
          I.arrA σ ⟨τ, h⟩ i * dlaDecision I rule E σ (dlaUsed I rule E σ τ) ⟨τ, h⟩
      else dlaUsed I rule E σ τ i

/-- The executed decision `x_t` of Algorithm DLA at 0-based time `t` in arrival order `σ`. -/
noncomputable def dlaX {m n : ℕ} (I : Instance m n) (rule : DualRule m n) (E : ℕ)
    (σ : Equiv.Perm (Fin n)) (t : Fin n) : ℝ :=
  dlaDecision I rule E σ (dlaUsed I rule E σ t.val) t

/-- The DLA's objective value `∑_t π_t x_t` in arrival order `σ`. -/
noncomputable def dlaValue {m n : ℕ} (I : Instance m n) (rule : DualRule m n) (E : ℕ)
    (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ t : Fin n, I.arrPi σ t * dlaX I rule E σ t

end DynamicOnlineLP.DLA


