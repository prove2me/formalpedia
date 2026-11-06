-- Prove2me | Definitions.Def_DecodablePOMDP_Value
-- name    : DecodablePOMDP_Value
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:23:55.795787+00:00
-- url     : https://prove2.me/theorems/969c6c42-4536-405c-80ed-8e6209e48c9e
-- title:
--   Histories, policies, the value $V^\pi_h(\beta)$ and the optimal value $V^*_h(\beta)$
-- statement:
--   A **history** at time $h$ is $h_h=(a_{1:h-1},y_{2:h})$, with $h_1=\emptyset$. A **history-dependent randomised policy** assigns to every history a probability vector on $\mathcal A$; a deterministic policy assigns an action.
--
--   For a POMDP $\mathcal P$, a stage $h$, a law $\beta$ of the hidden state at stage $h$ and a policy $\pi$ acting on the histories after $h$, the **value to go**
--
--   $$V^\pi_h(\beta)=\sum_{k=h+1}^{H}\mathbb E_{\beta,\pi}\big[r_k(y_k)\big]$$
--
--   is the expected cumulative reward from time $h+1$ to $H$. The value of a policy is $V^\pi_{\mathcal P}=V^\pi_1(\mu_1)=\sum_{h=2}^H\mathbb E_{\mathcal P,\pi}[r_h(y_h)]$, and the **optimal values** are
--
--   $$V^*_h(\beta)=\sup_\pi V^\pi_h(\beta),\qquad V^*_{\mathcal P}=V^*_1(\mu_1),$$
--
--   the supremum over all history-dependent randomised policies.
--
--   The expectation is a finite sum over the joint law $p_t$ of the state and the history: $p_0=\beta$ and $p_{t+1}(s',(a,y)\cdot h)=\sum_s p_t(s,h)\,\pi(h)(a)\,T_{h+t}(s'\mid s,a)\,K_{h+t+1}(y\mid s')$.
--
--   **Formalization Note** Histories are stored newest first, pairing each action $a_k$ with the observation $y_{k+1}$ it produced. Randomised policies are behavioural. The supremum is a real supremum over the policies whose action laws are probability vectors; for valid POMDPs it is finite and attained.
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), §2, p.6 (history, value, optimal value); p.18 (value to go)

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist
import Definitions.Def_DecodablePOMDP_POMDP

namespace DecodablePOMDP

open CalibratedCE.Forecast

/-- **Histories** (p.6): a history of `t` steps is the list of action–observation pairs, stored
newest first: for a history started at stage `h`, entry `0` is `(a_{h+t-1}, y_{h+t})`, entry `t-1`
is `(a_h, y_{h+1})`. For `h = 1` this is `h_{t+1} = (a_{1:t}, y_{2:t+1})`, and `h_1 = ∅` is the
empty function on `Fin 0`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §2, p.6: "hh = (a1:h−1, y2:h). Note that
h1 = ∅."

**Formalization Note.** Pairing `a_i` with the observation `y_{i+1}` it produced is a
re-indexing of `(a_{1:h−1}, y_{2:h})`. -/
abbrev Hist (A O : Type) (t : ℕ) := Fin t → A × O

/-- **Randomized behavioural policy (raw)**: `π t hist a` is the probability of action `a` after
the `t`-step history `hist`. -/
abbrev PolicyFn (A O : Type) := (t : ℕ) → Hist A O t → A → ℝ

/-- **History-dependent randomised policy** (p.6): every `π t hist` is a probability vector on
`A`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §2, p.6: "the supremum is taken over all
history-dependent randomised policies".

**Formalization Note.** Randomization is behavioural (a law on actions per history); a mixture of
deterministic policies has a behavioural equivalent with the same value. -/
def IsRandPolicy {A O : Type} [Fintype A] (π : PolicyFn A O) : Prop :=
  ∀ t (hist : Hist A O t), IsDist (π t hist)

/-- **Deterministic history policy** (p.6): `π_h : H_h → A`. -/
abbrev DetPolicyFn (A O : Type) := (t : ℕ) → Hist A O t → A

/-- A deterministic policy viewed as a randomized one (point masses). -/
def toRand {A O : Type} [DecidableEq A] (σ : DetPolicyFn A O) : PolicyFn A O :=
  fun t hist a => if a = σ t hist then 1 else 0

/-- **Joint law of state and history from stage `h`.** `jointFrom P h β π t hist s` is the
probability that, started at stage `h` with hidden state law `β` and run with `π`, the first `t`
action–observation pairs are `hist` and the hidden state at stage `h + t` is `s`:
`p₀(s) = β(s)` and
`p_{t+1}(s', (a, y) :: hist) = Σ_s p_t(s, hist) π_t(hist)(a) T_{h+t}(s' | s, a) K_{h+t+1}(y | s')`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §2, p.6 (the law `E_{P,π}` of the value).

**Formalization Note.** Finite sums replace the expectation; `Fin.tail hist` is the history one
step earlier. -/
def jointFrom {S A O : Type} [Fintype S] (P : POMDP S A O) (h : ℕ) (β : S → ℝ)
    (π : PolicyFn A O) : (t : ℕ) → Hist A O t → S → ℝ
  | 0, _, s => β s
  | t + 1, hist, s' =>
      ∑ s, jointFrom P h β π t (Fin.tail hist) s * π t (Fin.tail hist) (hist 0).1 *
        P.T (h + t) s (hist 0).1 s' * P.K (h + t + 1) s' (hist 0).2

/-- **Value to go from stage `h`**: the expected cumulative reward from time `h + 1` to `H` when
the hidden state at stage `h` has law `β` and the policy `π` acts on the histories after `h`:
`Σ_{t=0}^{H-h-1} E[r_{h+t+1}(y_{h+t+1})]`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), p.6 and p.18 (`V^π_h(β)`, "the expected
cumulative reward from time h+1 to H"). -/
def valueFrom {S A O : Type} [Fintype S] [Fintype A] [Fintype O] (P : POMDP S A O) (h : ℕ)
    (β : S → ℝ) (π : PolicyFn A O) : ℝ :=
  ∑ t ∈ Finset.range (P.H - h), ∑ hist : Hist A O (t + 1), ∑ s,
    jointFrom P h β π (t + 1) hist s * P.r (h + t + 1) (hist 0).2

/-- **Value of a policy** (p.6): `V^π_P = Σ_{h=2}^H E_{P,π}[r_h(y_h)]`, i.e. the value to go from
stage `1` with initial law `μ₁`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §2, p.6. -/
def value {S A O : Type} [Fintype S] [Fintype A] [Fintype O] (P : POMDP S A O)
    (π : PolicyFn A O) : ℝ :=
  valueFrom P 1 P.μ₁ π

/-- **Optimal value to go from stage `h`** `V*_h(β)`: the supremum of `valueFrom P h β π` over
all history-dependent randomised policies.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), p.11 and p.18 (`V*_h`).

**Formalization Note.** A real `⨆` over the subtype of randomized policies; it is a genuine
supremum for valid POMDPs, probability vectors `β` and nonempty `A` (values lie in `[0, H]`). -/
noncomputable def optValueFrom {S A O : Type} [Fintype S] [Fintype A] [Fintype O]
    (P : POMDP S A O) (h : ℕ) (β : S → ℝ) : ℝ :=
  ⨆ π : {π : PolicyFn A O // IsRandPolicy π}, valueFrom P h β π.1

/-- **Optimal value** (p.6): `V*_P := sup_π V^π_P`, "where the supremum is taken over all
history-dependent randomised policies".

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §2, p.6. -/
noncomputable def optValue {S A O : Type} [Fintype S] [Fintype A] [Fintype O]
    (P : POMDP S A O) : ℝ :=
  optValueFrom P 1 P.μ₁

end DecodablePOMDP


