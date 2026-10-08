-- Prove2me | Definitions.Def_MultiSecretary_BR_Policy
-- name    : MultiSecretary_BR_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T07:56:42.739818+00:00
-- url     : https://prove2.me/theorems/857a2575-b389-408f-acc2-a5e5e4944186
-- title:
--   Sec. 4 — the Budget-Ratio policy, its remaining budget $K_t$, and the stopping times $\tau_0$ and $\tau$ of (20)
-- statement:
--   In the multi-secretary model, the **Budget-Ratio (BR) policy** of Sec. 4 decides at each time $t+1\in\{1,\dots,n\}$ by comparing the *budget ratio* $K_t/(n-t)$ (remaining budget over remaining candidates) with the thresholds $0=T_1<T_2<\dots<T_m<T_{m+1}=+\infty$. Starting from $K_0=k$, at time $t+1$ it
--
--   1. identifies the index $j=j(t)$ with $T_j\le K_t/(n-t)<T_{j+1}$;
--   2. selects $X_{t+1}$ if and only if $K_t>0$ and $X_{t+1}\ge a_j$, and sets $K_{t+1}=K_t-\sigma^{\mathrm{br}}_{t+1}$.
--
--   For a parameter $0<\delta<\epsilon$ (p. 13) the analysis uses two stopping times:
--   $$\tau_0=\inf\Big\{t\ge0:\Big|\frac{K_t}{n-t}-T_j\Big|\le\frac\delta2\text{ for some }j\in[m]\text{ or }t\ge n-2\delta^{-1}-1\Big\},$$
--   the index $j(\tau_0)$ of the threshold within $\delta/2$ of $K_{\tau_0}/(n-\tau_0)$ when $\tau_0<n-2\delta^{-1}-1$ (and $j(\tau_0)=m+1$, $T_{m+1}=+\infty$ otherwise), and
--   $$\tau=\inf\Big\{t>\tau_0:\Big|\frac{K_t}{n-t}-T_{j(\tau_0)}\Big|>\delta\text{ or }t\ge n-2\delta^{-1}-1\Big\}.\qquad(20)$$
--
--   The BR policy is the policy whose regret the mission bounds; $\tau$ is the time at which the budget ratio leaves the band around the threshold it is attracted to.
--
--   **Formalization Note** Lean index $i$ of `Fin m` is the paper's index $i+1$, so `a 0` is $a_1$, the largest ability. The rule is applied at every decision time $t+1\in\{1,\dots,n\}$; p. 11 writes $\{1,\dots,n-1\}$, a slip, since $\sigma_n$ must be defined and p. 13 describes the policy selecting all remaining values once $n-t\le K_t$. The index $j(t)$ is the largest $j$ with $T_j\le K_t/(n-t)$. The cut-off $t\ge n-2\delta^{-1}-1$ is compared in the reals, as printed. $j(\tau_0)$ is `none` exactly when $\tau_0\ge n-2\delta^{-1}-1$; otherwise it is the (unique, for $\delta<\epsilon$) threshold index within $\delta/2$. When $T_{j(\tau_0)}=+\infty$ the deviation condition in (20) holds at once. Both infima are over nonempty sets of natural numbers; $\tau$ is capped at $n$, which changes it only when $n=0$.
-- source:
--   Arlotto, Gurvich, Uniformly Bounded Regret in the Multi-Secretary Problem, arXiv:1710.07719v2, Sec. 4, pp. 11–13 (BR policy, τ₀); Sec. 4, p. 15, eq. (20)

import Mathlib
import Definitions.Def_MultiSecretary_BR_Model

namespace MultiSecretary.BR

open Finset

variable {m : ℕ}

namespace Instance

/-- The BR index of a budget ratio `r` (Sec. 4, p. 13, step (i)): the index `j` with
`T_j ≤ r < T_{j+1}`, i.e. the largest `j` with `T_j ≤ r` (`T_{m+1} = +∞`). For `r < 0`, where no
threshold lies below `r`, it is `0` by convention (never used: budget ratios are nonnegative). -/
noncomputable def brIndex (I : Instance m) (r : ℝ) : Fin m :=
  if h : (univ.filter (fun j : Fin m => I.T j ≤ r)).Nonempty then
    (univ.filter (fun j : Fin m => I.T j ≤ r)).max' h
  else I.top

/-- The remaining budget `K_t` of the Budget-Ratio policy after its first `t` decisions
(Sec. 4, pp. 11–13): `K_0 = k`, and at time `t + 1 ≤ n` the policy selects candidate `t + 1`
(Lean index `t`) iff `K_t > 0` and `X_{t+1} ≥ a_{j(t)}`, where `j(t)` is the BR index of
`K_t/(n − t)`; then `K_{t+1} = K_t − σ_{t+1}`. After time `n` the budget is frozen. -/
noncomputable def budget (I : Instance m) (n k : ℕ) (x : Fin n → Fin m) : ℕ → ℕ
  | 0 => k
  | t + 1 =>
    if h : t < n then
      if 0 < budget I n k x t ∧
          x ⟨t, h⟩ ≤ I.brIndex ((budget I n k x t : ℝ) / ((n : ℝ) - t)) then
        budget I n k x t - 1
      else budget I n k x t
    else budget I n k x t

/-- The budget ratio `K_t/(n − t)`. -/
noncomputable def ratio (I : Instance m) (n k : ℕ) (x : Fin n → Fin m) (t : ℕ) : ℝ :=
  (I.budget n k x t : ℝ) / ((n : ℝ) - t)

/-- The Budget-Ratio policy `br` (Sec. 4, p. 13): candidate `t + 1` (Lean index `t`) is selected
iff `K_t > 0` and `X_{t+1} ≥ a_{j(t)}` with `T_{j(t)} ≤ K_t/(n − t) < T_{j(t)+1}` (in Lean
indexing, `x t ≤ brIndex (K_t/(n − t))`). The rule is applied at every decision time
`t + 1 ∈ {1, …, n}`. -/
noncomputable def brPolicy (I : Instance m) (n k : ℕ) : (Fin n → Fin m) → Fin n → Bool :=
  fun x t => decide (0 < I.budget n k x t.val ∧ x t ≤ I.brIndex (I.ratio n k x t.val))

/-- The stopping time `τ₀` of p. 13, for a parameter `δ`:
`τ₀ = inf{t ≥ 0 : |K_t/(n − t) − T_j| ≤ δ/2 for some j ∈ [m] or t ≥ n − 2δ⁻¹ − 1}`.
The set is nonempty (it contains `n`), so the infimum is a minimum. -/
noncomputable def tau0 (I : Instance m) (δ : ℝ) (n k : ℕ) (x : Fin n → Fin m) : ℕ :=
  sInf {t : ℕ | (∃ j : Fin m, |I.ratio n k x t - I.T j| ≤ δ / 2) ∨ (n : ℝ) - 2 / δ - 1 ≤ t}

/-- The index `j(τ₀)` of the threshold within `δ/2` of `K_{τ₀}/(n − τ₀)` (p. 13), when
`τ₀ < n − 2δ⁻¹ − 1`; `none` encodes the paper's `j(τ₀) = m + 1`, `T_{j(τ₀)} = +∞`, set when the
cut-off fired. (For `0 < δ < ϵ` the thresholds are more than `δ` apart, so the index is unique; the
least one is taken.) -/
noncomputable def jTau0 (I : Instance m) (δ : ℝ) (n k : ℕ) (x : Fin n → Fin m) : Option (Fin m) :=
  if h : ((I.tau0 δ n k x : ℝ) < (n : ℝ) - 2 / δ - 1) ∧
      (univ.filter (fun j : Fin m => |I.ratio n k x (I.tau0 δ n k x) - I.T j| ≤ δ / 2)).Nonempty
  then some ((univ.filter
      (fun j : Fin m => |I.ratio n k x (I.tau0 δ n k x) - I.T j| ≤ δ / 2)).min' h.2)
  else none

/-- The stopping time `τ` of (20), p. 15:
`τ = inf{t > τ₀ : |K_t/(n − t) − T_{j(τ₀)}| > δ or t ≥ n − 2δ⁻¹ − 1}`, where the deviation
condition holds automatically when `T_{j(τ₀)} = +∞` (`jTau0 = none`). The set is nonempty; the
result is capped at `n` (a stopping time `τ ≤ n`, as Proposition 2 requires), which changes the
value only when `n = 0`. -/
noncomputable def tau (I : Instance m) (δ : ℝ) (n k : ℕ) (x : Fin n → Fin m) : ℕ :=
  min n (sInf {t : ℕ | I.tau0 δ n k x < t ∧
    ((∀ j, I.jTau0 δ n k x = some j → δ < |I.ratio n k x t - I.T j|) ∨
      (n : ℝ) - 2 / δ - 1 ≤ t)})

end Instance

end MultiSecretary.BR


