-- Prove2me | Definitions.Def_DriverSurge_IC_Model
-- name    : DriverSurge_IC_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:42.047985+00:00
-- url     : https://prove2.me/theorems/7f14f6be-bac3-45da-82c9-a88a132d01e8
-- title:
--   §2.1.2–2.2, Lemmas 1, 3, App. D.3.1 — two-state surge primitives, q_{i→j}, open acceptance policies, normalized W_i, T_i, Q_i, per-state rates R_i, µ_i and the closed-form reward
-- statement:
--   The closed-form vocabulary of the dynamic model of Garg and Nazerzadeh (§2.1.2–§2.2, pp. 5–7; Lemmas 1 and 3, pp. 7 and 12; App. D.3.1, p. 56).
--
--   The world alternates between two states, the **non-surge state** $1$ and the **surge state** $2$. The **primitives** are request rates $\lambda_1,\lambda_2>0$ (a driver who is open in state $i$ receives requests at rate $\lambda_i$), switching rates $\lambda_{1\to2},\lambda_{2\to1}>0$ (the world leaves state $i$ at rate $\lambda_{i\to j}$), and trip-length laws $F_1,F_2$, probability measures carried by $(0,\infty)$. The standing assumption of App. D.3.1 is that each $F_i$ has a **bounded density** $f_i$; finite mean trip lengths $\int\tau\,dF_i(\tau)<\infty$ are a separate predicate. With $j$ the other state,
--   $$q_{i\to j}(s)=\frac{\lambda_{i\to j}}{\lambda_{i\to j}+\lambda_{j\to i}}\Big[1-e^{-(\lambda_{i\to j}+\lambda_{j\to i})s}\Big]$$
--   is the probability that the world is in state $j$ a time $s$ after being in state $i$ (Lemma 2). A **policy** $\sigma=\{\sigma_1,\sigma_2\}$ consists of open sets $\sigma_i\subseteq(0,\infty)$ of accepted trip lengths; **accept-all** is $\sigma_i=(0,\infty)$.
--
--   For a payment function $w_i$ and a set $\sigma_i$, the normalized quantities of D.3.1 are
--   $$W_i=\lambda_i\int_{\sigma_i}w_i\,dF_i,\qquad T_i=1+\lambda_i\int_{\sigma_i}\tau\,dF_i(\tau),\qquad Q_i=\lambda_{i\to j}+\lambda_i\int_{\sigma_i}q_{i\to j}\,dF_i ,$$
--   the **per-state earnings rate** is $R_i(w_i,\sigma_i)=W_i/T_i$, the **fraction of time** attributed to state $i$ is
--   $$\mu_i(\sigma)=\frac{T_iQ_j}{T_jQ_i+T_iQ_j},$$
--   and the **closed-form reward** is $R(w,\sigma)=\mu_1(\sigma)R_1(w_1,\sigma_1)+\mu_2(\sigma)R_2(w_2,\sigma_2)$.
--
--   These objects carry every closed-form statement of the mission; Lemmas 1 and 3 identify them with the driver's long-run earnings rate and occupation fractions.
--
--   **Formalization Note** Lean state `0` is the paper's state 1 and Lean `1` is state 2; `sw 0` is $\lambda_{1\to2}$ and `sw 1` is $\lambda_{2\to1}$. `Wn`, `Tn`, `Qn` are the normalized $W_i=\lambda_iF_i(\sigma_i)W_i(\sigma_i)$, $T_i=\lambda_iF_i(\sigma_i)T_i(\sigma_i)$ and $Q_i(\sigma_i)$; the printed $W_i(\sigma_i)/T_i(\sigma_i)$ equals `Wn/Tn` when $F_i(\sigma_i)>0$, and `stateRate` is $0$ on an $F_i$-null set. Integrals are Bochner integrals, which are $0$ for non-integrable integrands; every statement that uses them assumes the integrability it needs. $T_i\ge1$ and $Q_i\ge\lambda_{i\to j}>0$, so no division by zero occurs.
-- source:
--   Garg, Nazerzadeh, Driver Surge Pricing, arXiv:1905.07544v4, pp. 5–7, 12, 56, §2.1.2, §2.2, Lemmas 1–3, App. D.3.1

import Mathlib

namespace DriverSurge.IC

open MeasureTheory Set

/-! Garg–Nazerzadeh, *Driver Surge Pricing* (arXiv:1905.07544v4), §2.1.2–§2.2 (pp. 5–7),
Lemmas 1 and 3 (pp. 7, 12) and App. D.3.1 (p. 56): the closed-form vocabulary of the dynamic
two-state model.

State labels: the Lean state `0 : Fin 2` is the paper's non-surge state 1, and `1 : Fin 2` is the
paper's surge state 2. -/

/-- The other state `j ≠ i`: `other 0 = 1` and `other 1 = 0`. -/
def other (i : Fin 2) : Fin 2 := 1 - i

/-- The primitives of the dynamic model (§2.1.2, p. 5):
* `lam i` is the request rate `λ_i` while the driver is open in state `i`;
* `sw i` is the switching rate out of state `i`: `sw 0 = λ_{1→2}` and `sw 1 = λ_{2→1}`;
* `F i` is the trip-length law `F_i` in state `i`, a probability measure carried by `(0, ∞)`. -/
structure Primitives where
  lam : Fin 2 → ℝ
  sw : Fin 2 → ℝ
  F : Fin 2 → Measure ℝ
  lam_pos : ∀ i, 0 < lam i
  sw_pos : ∀ i, 0 < sw i
  prob : ∀ i, IsProbabilityMeasure (F i)
  support : ∀ i, F i (Iic 0) = 0

/-- D.3.1 (p. 56), standing assumption: each `F_i` has a bounded density `f_i` (with respect to
Lebesgue measure). -/
def HasBoundedDensity (P : Primitives) (f : Fin 2 → ℝ → ℝ) : Prop :=
  ∀ i, Measurable (f i) ∧ (∃ B : ℝ, ∀ x, 0 ≤ f i x ∧ f i x ≤ B) ∧
    P.F i = volume.withDensity (fun x => ENNReal.ofReal (f i x))

/-- Every trip-length law has a finite mean, `∫ τ dF_i(τ) < ∞`. -/
def FiniteMean (P : Primitives) : Prop :=
  ∀ i, Integrable (fun x : ℝ => x) (P.F i)

/-- Lemma 2 (p. 12), closed form: `q_{i→j}(s) = λ_{i→j}/(λ_{i→j}+λ_{j→i}) · (1 − e^{−(λ_{i→j}+λ_{j→i}) s})`,
the probability that the world is in the other state `s` time units after being in state `i`. -/
noncomputable def q (P : Primitives) (i : Fin 2) (s : ℝ) : ℝ :=
  P.sw i / (P.sw i + P.sw (other i)) * (1 - Real.exp (-(P.sw i + P.sw (other i)) * s))

/-- A driver policy (§2.2, pp. 5–6): `σ i ⊆ (0, ∞)` is the set of trip lengths accepted in state
`i`, and it is an open set. -/
def IsPolicy (σ : Fin 2 → Set ℝ) : Prop :=
  ∀ i, IsOpen (σ i) ∧ σ i ⊆ Ioi 0

/-- The policy that accepts every request, `σ = {(0, ∞), (0, ∞)}`. -/
def acceptAll : Fin 2 → Set ℝ := fun _ => Ioi 0

/-- D.3.1 (p. 56): `W_i = λ_i F_i(σ_i) W_i(σ_i) = λ_i ∫_{σ_i} w_i(τ) dF_i(τ)`. The Bochner integral is
`0` when `w` is not integrable on `s`; statements that use it assume integrability. -/
noncomputable def Wn (P : Primitives) (i : Fin 2) (w : ℝ → ℝ) (s : Set ℝ) : ℝ :=
  P.lam i * ∫ τ in s, w τ ∂(P.F i)

/-- D.3.1 (p. 56): `T_i = λ_i F_i(σ_i) T_i(σ_i) = 1 + λ_i ∫_{σ_i} τ dF_i(τ)`. Statements that use it
assume `τ` integrable on `s` (otherwise the integral takes the junk value `0`). Since `F_i` is carried
by `(0, ∞)`, `T_i ≥ 1`. -/
noncomputable def Tn (P : Primitives) (i : Fin 2) (s : Set ℝ) : ℝ :=
  1 + P.lam i * ∫ τ in s, τ ∂(P.F i)

/-- Lemma 3 (p. 12) and D.3.1 (p. 56): `Q_i(σ_i) = λ_{i→j} + λ_i ∫_{σ_i} q_{i→j}(τ) dF_i(τ)`
(`q` is bounded, so the integral is always finite; `Q_i ≥ λ_{i→j} > 0`). -/
noncomputable def Qn (P : Primitives) (i : Fin 2) (s : Set ℝ) : ℝ :=
  P.sw i + P.lam i * ∫ τ in s, q P i τ ∂(P.F i)

/-- The per-state earnings rate `R_i(w_i, σ_i) = W_i(σ_i)/T_i(σ_i)` (Lemma 1, p. 7), written with the
normalized quantities of D.3.1 as `W_i / T_i`. When `F_i(σ_i) > 0` this is the printed
`W_i(σ_i)/T_i(σ_i)`; on an `F_i`-null set it is `0`. -/
noncomputable def stateRate (P : Primitives) (i : Fin 2) (w : ℝ → ℝ) (s : Set ℝ) : ℝ :=
  Wn P i w s / Tn P i s

/-- Lemma 3 (p. 12): the long-run fraction of time spent open in state `i` or on a trip started in
state `i`,
`µ_i(σ) = λ_iF_i(σ_i)T_i(σ_i)Q_j(σ_j) / [λ_jF_j(σ_j)T_j(σ_j)Q_i(σ_i) + λ_iF_i(σ_i)T_i(σ_i)Q_j(σ_j)]`,
with `λ_iF_i(σ_i)T_i(σ_i)` the normalized `T_i`. The denominator is positive. -/
noncomputable def mu (P : Primitives) (σ : Fin 2 → Set ℝ) (i : Fin 2) : ℝ :=
  Tn P i (σ i) * Qn P (other i) (σ (other i)) /
    (Tn P (other i) (σ (other i)) * Qn P i (σ i) + Tn P i (σ i) * Qn P (other i) (σ (other i)))

/-- The closed form of the earnings rate (Lemma 1, p. 7):
`R(w, σ) = µ_1(σ) R_1(w_1, σ_1) + µ_2(σ) R_2(w_2, σ_2)`. This is a closed-form expression, not the
driver's stochastic earnings rate (see `Def_DriverSurge_IC_Process`). -/
noncomputable def rewardCF (P : Primitives) (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ) : ℝ :=
  ∑ i, mu P σ i * stateRate P i (w i) (σ i)

end DriverSurge.IC


