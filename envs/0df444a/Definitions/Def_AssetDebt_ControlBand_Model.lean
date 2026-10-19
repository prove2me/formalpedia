-- Prove2me | Definitions.Def_AssetDebt_ControlBand_Model
-- name    : AssetDebt_ControlBand_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:13:24.06111+00:00
-- url     : https://prove2.me/theorems/f7798b02-fcf4-4c1e-a19e-69916359bdf2
-- title:
--   §2, eqs. (1)–(5), (A.10), pp. 6–14 — asset selling under debt: Markov price kernels, debt-free value U, equity value V with bankruptcy, critical prices
-- statement:
--   This file sets up the finite-horizon asset-selling model of Ahn, Wang and Wu, with and without a debt obligation.
--
--   **Data.** A horizon $T \ge 1$ (periods $t = 1, \dots, T$), a discount factor $\rho \in (0,1)$, a per-period selling capacity $\ell \in (0,1]$, and price kernels $\kappa_t$: $\kappa_t(p)$ is the conditional law of the next price $P_{t+1}$ given the current price $P_t = p$. Write $E_t$ for the expectation under $\kappa_t(p_t)$, and $\kappa_{t}^{(k)}(p)$ for the law of $P_{t+k}$ given $P_t = p$ (the chained kernels). The **standing assumptions** are: each $\kappa_t$ is a probability kernel; $E[P_{t+1} \mid p_t] < \infty$ for every $t + 1 \le T$; the multi-step conditional means $E[P_{t+k+1} \mid p_t]$ are finite for $t + k + 1 \le T$; and prices are almost surely strictly positive.
--
--   **Debt-free value**, eq. (1). The seller holds an amount $x \in [0,1]$ of a divisible asset. With $U_{T+1} \equiv 0$,
--
--   $$U_t(x,p) = \max_{0 \le q \le \min(x,\ell)} \; p\,q + \rho\, E_t\, U_{t+1}(x - q, P_{t+1}), \qquad t = 1, \dots, T.$$
--
--   **Debt.** A schedule $d = (d_t)$, $d_t \ge 0$, with maturity $m$ ($1 \le m \le T$): $d_t$ is due at the end of period $t$. With working capital $w$, a quantity $q$ is **feasible** in period $t$ if $0 \le q \le \min(x,\ell)$ and $d_t \le w + p\,q$ (that is, $q \ge \underline q_t = (d_t - w)^+/p$). The **equity value** $V_t(x, w, p; d)$, $t \le m$, is $0$ if $p\min(x,\ell) + w < d_t$ (bankruptcy, limited liability), and otherwise, eqs. (2)–(3),
--
--   $$V_m(x,w,p;d) = \max_{q \text{ feasible}} \; p\,q + w - d_m + \rho\, E_m\, U_{m+1}(x-q, P_{m+1}),$$
--
--   $$V_t(x,w,p;d) = \max_{q \text{ feasible}} \; \rho\, E_t\, V_{t+1}\big(x-q,\ \rho^{-1}(w + p\,q - d_t),\ P_{t+1}; d\big), \qquad t < m.$$
--
--   For $t > m$ the equity value is set to $0$, which is the paper's convention $V_{m+1}(1,0,\cdot\,;d) := 0$ in (5). A quantity is **optimal** if it is feasible and attains the maximum.
--
--   **Single payment and critical prices.** For the schedule $d_m = D$, $d_t = 0$ ($t \ne m$), write $\delta_t = \rho^{m-t} D$. The debt-free critical price (4) is $R^o_t = \rho\, E[U_{t+1}(1, P_{t+1}) \mid P_t]$; the continuation value is $C_t = \rho\, E_t V_{t+1}(1, 0, P_{t+1}; d)$ (so $C_m = 0$); the net effect of debt (5) is $\Delta_{s} = V_{s}(1, 0, P_{s}; d) - (U_{s}(1, P_{s}) - \rho^{m-s} D)$, and $E_t\Delta_{t+1}$ is its conditional expectation. The critical prices of (A.10) are
--
--   $$R^{(1)}_t = \min\Big\{ \frac{\delta_t\, R^o_t}{R^o_t - C_t},\ C_t + \delta_t \Big\}, \qquad R^{(2)}_t = \max\{ R^o_t,\ C_t + \delta_t \}.$$
--
--   These objects are shared by every statement of the mission: the debt-free policy (Proposition 1), the closed forms (A.6), (A.8), (A.9), and the control band of Proposition 4.
--
--   **Formalization Note** All values are real numbers; the maxima are written as `sSup` of the objective's image of the feasible set, with the bankruptcy branch an explicit `if` taken first, so the supremum is only taken over a nonempty interval. $U$ and $V$ are defined by well-founded recursion on the number of remaining periods and are never given by their closed forms. Two hypotheses are added to the page: almost surely positive prices (the paper writes $P_t \ge 0$ but divides by $p_t$), and finiteness of the multi-step conditional means (the paper treats $R^o_t$ as a finite number, which the one-step assumption alone does not guarantee). The exponent $m - t - 1$ in $E_t\Delta_{t+1}$ is an integer power, equal to $\rho^{-1}$ at $t = m$.
-- source:
--   Ahn, Wang & Wu, Asset Selling Under Debt Obligations, SSRN 3472345 (version of May 7, 2019), pp. 6–9 (PDF 6–9), §2, eqs. (1)–(3), §3.1, eq. (4); pp. 13–14 (PDF 13–14), eq. (5); Online Appendix p. 8 (PDF 40), (A.10)

import Mathlib

namespace AssetDebt.ControlBand

open MeasureTheory ProbabilityTheory

/-- Primitive data of the asset-selling model of §2: the horizon `T` (periods `1, …, T`),
the discount factor `ρ`, the per-period selling capacity `ℓ`, and the price kernels:
`κ t p` is the conditional law of the price `P_{t+1}` given `P_t = p`. -/
structure Params where
  T : ℕ
  ρ : ℝ
  ℓ : ℝ
  κ : ℕ → Kernel ℝ ℝ

/-- `lawAhead P t k p` is the conditional law of the price `P_{t+k}` given `P_t = p`,
obtained by chaining the one-step kernels `κ t, κ (t+1), …, κ (t+k-1)`. -/
noncomputable def lawAhead (P : Params) (t : ℕ) : ℕ → ℝ → Measure ℝ
  | 0, p => Measure.dirac p
  | k + 1, p => (lawAhead P t k p).bind (fun p' => P.κ (t + k) p')

/-- Standing assumptions of §2 (pp. 6–7):
`T ≥ 1`, `ρ ∈ (0, 1)`, `ℓ ∈ (0, 1]`, each `κ t` is a Markov (probability) kernel, and the
conditional mean `E[P_{t+1} | p_t]` is finite for every period `t + 1 ≤ T`.
Two assumptions are ADDED to the page:
* the `k`-step conditional means `E[P_{t+k+1} | p_t]`, `t + k + 1 ≤ T`, are finite
  (the paper uses `R^o_t = ρ E_t U_{t+1}(1, P_{t+1})` as a real number, which needs this);
* prices are a.s. strictly positive (the paper writes `P_t ≥ 0` but divides by `p_t`). -/
def Params.Standing (P : Params) : Prop :=
  1 ≤ P.T ∧ 0 < P.ρ ∧ P.ρ < 1 ∧ 0 < P.ℓ ∧ P.ℓ ≤ 1 ∧
  (∀ t, IsMarkovKernel (P.κ t)) ∧
  (∀ t, t < P.T → ∀ p, Integrable (fun x : ℝ => x) (P.κ t p)) ∧
  (∀ t k, t + k < P.T → ∀ p, Integrable (fun x : ℝ => x) (lawAhead P t (k + 1) p)) ∧
  (∀ t p, ∀ᵐ p' ∂(P.κ t p), 0 < p')

/-- Objective of the debt-free problem (1) in period `t` at state `(x, p)` and quantity `q`,
given a continuation value `Unext` for period `t + 1`:
`p q + ρ E_t Unext(x - q, P_{t+1})`. -/
noncomputable def objUStep (P : Params) (t : ℕ) (x p : ℝ) (Unext : ℝ → ℝ → ℝ) (q : ℝ) : ℝ :=
  p * q + P.ρ * ∫ p', Unext (x - q) p' ∂(P.κ t p)

/-- The debt-free value `U_t(x, p)` of eq. (1):
`U_t(x, p) = max_{0 ≤ q ≤ min(x, ℓ)} p q + ρ E_t U_{t+1}(x - q, P_{t+1})` for `t ≤ T`,
and `U_t = 0` for `t > T` (in particular `U_{T+1} = 0`). -/
noncomputable def U (P : Params) (t : ℕ) (x p : ℝ) : ℝ :=
  if h : P.T < t then 0
  else sSup (objUStep P t x p (fun x' p' => U P (t + 1) x' p') '' Set.Icc 0 (min x P.ℓ))
termination_by P.T + 1 - t
decreasing_by omega

/-- The objective of (1) in period `t`, with the true continuation `U_{t+1}`. -/
noncomputable def objU (P : Params) (t : ℕ) (x p q : ℝ) : ℝ :=
  objUStep P t x p (U P (t + 1)) q

/-- `q` is an optimal selling quantity of the debt-free problem (1) in period `t` at `(x, p)`:
it is feasible and attains the maximum of the objective over `[0, min(x, ℓ)]`. -/
def IsOptimalU (P : Params) (t : ℕ) (x p q : ℝ) : Prop :=
  q ∈ Set.Icc 0 (min x P.ℓ) ∧ ∀ q' ∈ Set.Icc 0 (min x P.ℓ), objU P t x p q' ≤ objU P t x p q

/-- Feasible quantities in period `t` under the debt schedule `d` at state `(x, w, p)`:
`q̲_t ≤ q ≤ min(x, ℓ)` with `q̲_t = (d_t - w)^+ / p`, written without division as
`0 ≤ q`, `q ≤ min(x, ℓ)`, `d_t ≤ w + p q` (equivalent for `p > 0`). -/
def Feasible (P : Params) (d : ℕ → ℝ) (t : ℕ) (x w p q : ℝ) : Prop :=
  0 ≤ q ∧ q ≤ min x P.ℓ ∧ d t ≤ w + p * q

/-- Objective of the equity-value problem in period `t ≤ m`, given a continuation `Vnext`
for period `t + 1`:
* at maturity `t = m` (eq. (2)): `p q + w - d_m + ρ E_m U_{m+1}(x - q, P_{m+1})`;
* before maturity `t < m` (eq. (3)): `ρ E_t Vnext(x - q, ρ⁻¹ (w + p q - d_t), P_{t+1})`. -/
noncomputable def objVStep (P : Params) (d : ℕ → ℝ) (m t : ℕ) (x w p : ℝ)
    (Vnext : ℝ → ℝ → ℝ → ℝ) (q : ℝ) : ℝ :=
  if t = m then objU P m x p q + w - d m
  else P.ρ * ∫ p', Vnext (x - q) (P.ρ⁻¹ * (w + p * q - d t)) p' ∂(P.κ t p)

/-- The equity value `V_t(x, w, p; d)` of eqs. (2)–(3), for the debt schedule `d` with
maturity `m`. For `t ≤ m`: `0` if `p min(x, ℓ) + w < d_t` (bankruptcy, limited liability);
otherwise the maximum of the period-`t` objective over the feasible quantities.
For `t > m` it is set to `0` (the paper's convention `V_{m+1}(1, 0, ·; d) := 0` in (5)). -/
noncomputable def V (P : Params) (d : ℕ → ℝ) (m t : ℕ) (x w p : ℝ) : ℝ :=
  if h : m < t then 0
  else if p * min x P.ℓ + w < d t then 0
  else sSup (objVStep P d m t x w p (fun x' w' p' => V P d m (t + 1) x' w' p') ''
    {q | Feasible P d t x w p q})
termination_by m + 1 - t
decreasing_by omega

/-- The objective of (2)–(3) in period `t`, with the true continuation `V_{t+1}`. -/
noncomputable def objV (P : Params) (d : ℕ → ℝ) (m t : ℕ) (x w p q : ℝ) : ℝ :=
  objVStep P d m t x w p (V P d m (t + 1)) q

/-- `q` is an optimal selling quantity in period `t` at `(x, w, p)` under the debt `d`:
it is feasible and attains the maximum of the objective among feasible quantities. -/
def IsOptimal (P : Params) (d : ℕ → ℝ) (m t : ℕ) (x w p q : ℝ) : Prop :=
  Feasible P d t x w p q ∧
    ∀ q', Feasible P d t x w p q' → objV P d m t x w p q' ≤ objV P d m t x w p q

/-- The single-payment schedule: `d_m = D`, and `d_t = 0` for `t ≠ m`. -/
def singlePayment (m : ℕ) (D : ℝ) : ℕ → ℝ := fun t => if t = m then D else 0

/-- The debt-free critical price (4): `R^o_t = ρ E[U_{t+1}(1, P_{t+1}) | P_t = p]`. -/
noncomputable def Ro (P : Params) (t : ℕ) (p : ℝ) : ℝ :=
  P.ρ * ∫ p', U P (t + 1) 1 p' ∂(P.κ t p)

/-- `C_t = ρ E_t V_{t+1}(1, 0, P_{t+1}; d)` for the single payment `D` at `m`
(it is `0` at `t = m`, since `V_{m+1} := 0`). -/
noncomputable def C (P : Params) (m : ℕ) (D : ℝ) (t : ℕ) (p : ℝ) : ℝ :=
  P.ρ * ∫ p', V P (singlePayment m D) m (t + 1) 1 0 p' ∂(P.κ t p)

/-- `E_t Δ_{t+1}`, with `Δ_s = V_s(1, 0, P_s; d) - (U_s(1, P_s) - ρ^{m-s} d_m)` from (5),
`s = t + 1`, for the single payment `D` at `m` (the exponent `m - t - 1` is an integer,
equal to `-1` at `t = m`). -/
noncomputable def EDelta (P : Params) (m : ℕ) (D : ℝ) (t : ℕ) (p : ℝ) : ℝ :=
  ∫ p', (V P (singlePayment m D) m (t + 1) 1 0 p'
      - (U P (t + 1) 1 p' - P.ρ ^ ((m : ℤ) - (t : ℤ) - 1) * D)) ∂(P.κ t p)

/-- The lower critical price of (A.10):
`R^{(1)}_t = min{ρ^{m-t} d_m R^o_t / (R^o_t - ρ E_t V_{t+1}), ρ E_t V_{t+1} + ρ^{m-t} d_m}`. -/
noncomputable def R1 (P : Params) (m : ℕ) (D : ℝ) (t : ℕ) (p : ℝ) : ℝ :=
  min (P.ρ ^ (m - t) * D * Ro P t p / (Ro P t p - C P m D t p)) (C P m D t p + P.ρ ^ (m - t) * D)

/-- The upper critical price of (A.10):
`R^{(2)}_t = max{R^o_t, ρ E_t V_{t+1} + ρ^{m-t} d_m}`. -/
noncomputable def R2 (P : Params) (m : ℕ) (D : ℝ) (t : ℕ) (p : ℝ) : ℝ :=
  max (Ro P t p) (C P m D t p + P.ρ ^ (m - t) * D)

end AssetDebt.ControlBand


