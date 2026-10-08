-- Prove2me | Definitions.Def_ResolvingNRM_FRUpper_Model
-- name    : ResolvingNRM_FRUpper_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:23:38.788303+00:00
-- url     : https://prove2.me/theorems/09138e28-ffd4-4723-ad47-3bb5bb7c3607
-- title:
--   Sec. 2–3 — Poisson network revenue management, the DLP, and the Frequent Re-solving (FR) policy
-- statement:
--   **Model** (Sec. 2, p. 7). There are $n$ customer classes $j \in [n]$ and $m$ resources $l \in [m]$. Class-$j$ customers arrive over the horizon $[0, T]$ according to independent Poisson processes of rates $\lambda_j > 0$. Accepting a class-$j$ customer earns $r_j \ge 0$ and consumes $a_{lj} \ge 0$ units of each resource $l$; $A = (a_{lj}) \in \mathbb{R}^{m \times n}$ is the bill-of-materials matrix and $A_j$ its $j$-th column. The initial capacity vector is $C \ge 0$. A customer can be accepted only if $A_j \le C'$ for the remaining capacity $C'$.
--
--   **The DLP** (eq. (2), p. 8). For an average capacity vector $b \ge 0$ let
--   $$v(b) = \max\Big\{ \sum_{j=1}^n r_j x_j \ :\ \sum_{j=1}^n A_j x_j \le b,\ 0 \le x_j \le \lambda_j \Big\},$$
--   the value `piValue A r b lam` of the referenced definition. The DLP value over a horizon of length $T$ is $v^{\mathrm{DLP}}(T, C) = T \, v(C/T)$.
--
--   **LP selector.** A map $\mathrm{sel}$ from right-hand sides to solutions is an *optimal-solution selector* if, for every $b \ge 0$, $\mathrm{sel}(b)$ is an optimal solution of the LP above. This models the "$\arg\max$" of Algorithm 2 with an arbitrary tie-breaking rule.
--
--   **A probabilistic allocation over a window.** During a window of length $\ell$, starting with capacity $c$, each arriving class-$j$ customer is accepted with probability $p_j$ provided $A_j$ is at most the current remaining capacity; on acceptance $r_j$ is earned and $A_j$ is subtracted. `windowExp` is the expectation of any function $F(\text{revenue}, \text{final capacity})$ of the window's outcome.
--
--   **The FR policy** (Sec. 3, p. 10; Algorithm 2, p. 11). The horizon is divided into $T$ unit periods $[t, t+1)$, $t = 0, \dots, T-1$. At the start of period $t$, with remaining capacity $C(t)$, FR sets $b(t) = C(t)/(T - t)$, solves the LP to get $x(t) = \mathrm{sel}(b(t))$, and during the period accepts each class-$j$ arrival with probability $x_j(t)/\lambda_j$, subject to the capacity check. Its expected revenue is $v^{\mathrm{FR}}(T, C)$ (`frValue`), computed by backward recursion on the number of periods to go (`frTail`). `frStateExp sel T t g C` is $\mathbb{E}[g(C(t))]$, the expectation of a function of the remaining capacity at the start of period $t$.
--
--   **Constants** (App. C.2, pp. 35–36, and Lemma 8, p. 43).
--   1. $r^l_{\max} = \max_{j \in [n]} \{ r_j \, \mathbb{I}(a_{lj} > 0) / a_{lj} \}$, the largest revenue per unit of resource $l$ (`rmaxRes`).
--   2. $K_l = \sqrt{\sum_{j=1}^n a_{lj}^2 \lambda_j}$ (`Kres`), the constant of Lemma 8 in corrected form.
--   3. $r_{\max} = \max_j r_j$ and $\lambda_{\max} = \max_j \lambda_j$.
--
--   These are the objects in which Proposition 3 and its proof are stated.
--
--   **Formalization Note.** Capacities are real vectors; the capacity check is componentwise. Within a window the acceptance probabilities are constant, so by superposition and marking of independent Poisson processes the window holds $N \sim \mathrm{Poisson}((\sum_j \lambda_j)\ell)$ arrivals, in order of arrival, with i.i.d. classes of law $\lambda_j/\sum_i \lambda_i$ and independent Bernoulli($p_j$) acceptance coins; `windowExp` is the expectation over this law, written as a series over $N$ and finite sums over classes and coins. This representation is exact for FR, whose probabilities change only at integer times. All integrands that occur are bounded by an affine function of $N$, so the series converge. The maxima $r^l_{\max}$, $r_{\max}$, $\lambda_{\max}$ are written as suprema over the finite index set, which equal the maxima for $n \ge 1$. The Lemma 8 constant uses $\lambda_j$, not the printed $\lambda_j^2$: the printed constant is false (see the Lemma 8 item). The standing assumptions $\lambda_j > 0$, $r \ge 0$, $a_{lj} \ge 0$, $C \ge 0$ are left implicit on p. 7 and appear as hypotheses of every theorem. The LP value is the published `piValue`; it is a real supremum and equals the LP maximum for $b \ge 0$.
-- source:
--   Bumpensanti, Wang, A Re-solving Heuristic with Uniformly Bounded Loss for Network Revenue Management, arXiv:1802.06192v3, Sec. 2, pp. 7–8 (model, eq. (2)); Sec. 3 and Algorithm 2, pp. 10–11 (FR); App. C.2, pp. 35–36 (r^l_max, r_max, λ_max); Lemma 8, p. 43 (K_l)

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_IRT_Model

open RLPBidPrice.Unbiased Matrix

namespace ResolvingNRM.FRUpper

/-- The expectation `E[F(revenue, final capacity)]` of a probabilistic allocation over a window
of length `ℓ` that starts with capacity `c` and accepts each class-`j` arrival with probability
`p j` (when `A_j ≤` the remaining capacity).

By superposition and marking of independent Poisson processes, the window holds
`N ~ Poisson((∑_j λ_j) ℓ)` arrivals whose classes are i.i.d. with law `λ_j / ∑_j λ_j`, in order
of arrival; each arrival carries an independent Bernoulli(`p_j`) acceptance coin. -/
noncomputable def windowExp {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (ℓ : ℝ) (p : Fin n → ℝ) (c : Fin m → ℝ) (F : ℝ → (Fin m → ℝ) → ℝ) : ℝ :=
  ∑' N : ℕ, ResolvingNRM.IRT.poissonPMF ((∑ j, lam j) * ℓ) N *
    ∑ cls : Fin N → Fin n, ∑ coin : Fin N → Bool,
      (∏ i, (lam (cls i) / ∑ j, lam j) * (if coin i then p (cls i) else 1 - p (cls i))) *
        F (ResolvingNRM.IRT.runWindow A r (List.ofFn fun i => (cls i, coin i)) c).1
          (ResolvingNRM.IRT.runWindow A r (List.ofFn fun i => (cls i, coin i)) c).2

/-- The acceptance probabilities of FR in a period: `x_j / λ_j` for the LP solution `x`
(Algorithm 2, p. 11). -/
noncomputable def frProbs {n : ℕ} (lam : Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => x j / lam j

/-- Backward recursion for the FR policy (Algorithm 2, p. 11). `frTail … sel k c` is the expected
revenue of FR over the last `k` unit periods when the remaining capacity at their start is `c`:
the period re-solves the LP with `b = c / k`, takes `x = sel b`, accepts with probabilities
`x_j / λ_j` (subject to `A_j ≤` the remaining capacity, arrival by arrival), and continues with
`k − 1` periods from the capacity left at the end of the period. -/
noncomputable def frTail {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (sel : (Fin m → ℝ) → (Fin n → ℝ)) : ℕ → (Fin m → ℝ) → ℝ
  | 0, _ => 0
  | k + 1, c =>
      windowExp A r lam 1 (frProbs lam (sel fun l => c l / ((k : ℝ) + 1))) c
        (fun rev c' => rev + frTail A r lam sel k c')

/-- `v^FR(T, C)`: the expected revenue of the FR policy over the horizon `[0, T]`, divided into
`T` unit periods, from the initial capacity `C`. -/
noncomputable def frValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (sel : (Fin m → ℝ) → (Fin n → ℝ)) (T : ℕ) (C : Fin m → ℝ) : ℝ :=
  frTail A r lam sel T C

/-- Expectations along FR. `frStateExp … sel k t g c` is `E[g(C(t))]`, the expected value of `g`
at the remaining capacity after `t` periods of FR, when FR is started with capacity `c` and `k`
periods to go. Each period re-solves with `b = c / k` (`k` = the number of periods to go at its
start). Used with `k = T` and `t ≤ T`, so the division is by `T − s ≥ 1` in every period `s < t`. -/
noncomputable def frStateExp {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (sel : (Fin m → ℝ) → (Fin n → ℝ)) : ℕ → ℕ → ((Fin m → ℝ) → ℝ) → (Fin m → ℝ) → ℝ
  | _, 0, g, c => g c
  | k, t + 1, g, c =>
      windowExp A r lam 1 (frProbs lam (sel fun l => c l / (k : ℝ))) c
        (fun _ c' => frStateExp A r lam sel (k - 1) t g c')

/-- `r^l_max = max_{j ∈ [n]} { r_j I(a_lj > 0) / a_lj }` (App. C.2, p. 35): the largest revenue per
unit of resource `l` over the classes that use it (`0` when no class uses it). Written as a
supremum over the finite index set (equal to the maximum when `n ≥ 1`, and `0` when `n = 0`). -/
noncomputable def rmaxRes {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ) (l : Fin m) :
    ℝ :=
  ⨆ j, if 0 < A l j then r j / A l j else 0

/-- `K_l = √(∑_j a_lj² λ_j)`, the constant of Lemma 8 (p. 43) **as corrected**: the printed
`√(∑_j a_lj² λ_j²)` is replaced by `√(∑_j a_lj² λ_j)`. -/
noncomputable def Kres {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (lam : Fin n → ℝ) (l : Fin m) :
    ℝ :=
  Real.sqrt (∑ j, A l j ^ 2 * lam j)

/-- `r_max = max_j r_j` (p. 36), as a supremum over the finite index set. -/
noncomputable def rMax {n : ℕ} (r : Fin n → ℝ) : ℝ := ⨆ j, r j

/-- `λ_max = max_j λ_j` (p. 36), as a supremum over the finite index set. -/
noncomputable def lamMax {n : ℕ} (lam : Fin n → ℝ) : ℝ := ⨆ j, lam j

end ResolvingNRM.FRUpper


