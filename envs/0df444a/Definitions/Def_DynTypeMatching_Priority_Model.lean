-- Prove2me | Definitions.Def_DynTypeMatching_Priority_Model
-- name    : DynTypeMatching_Priority_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:54:05.961016+00:00
-- url     : https://prove2.me/theorems/5a7943f7-796e-403a-aa4f-f5e62fb5693d
-- title:
--   §3, (1), pp. 8–10 — the dynamic type matching model: feasible matchings, H_t, V_t, optimal policies
-- statement:
--   **The dynamic type matching model.** There are $m$ demand types $\mathcal D=\{1,\dots,m\}$ and $n$ supply types $\mathcal S=\{1,\dots,n\}$, and a finite horizon of $T$ periods $t=1,\dots,T$. The data of a model are:
--
--   1. per-unit matching rewards $r^t_{ij}\in\mathbb R$ for matching one unit of type-$i$ demand with one unit of type-$j$ supply in period $t$ (arbitrary reals; a forbidden pair may get a zero or negative reward);
--   2. carry-over fractions $\alpha,\beta$: a fraction $\alpha$ of unmatched demand and $\beta$ of unmatched supply carries over to the next period;
--   3. for every period $t$, the joint law of the random arrival vector $(\mathbf D^t,\mathbf S^t)\in\mathbb R^m\times\mathbb R^n$.
--
--   The model is **well posed** if every arrival law is a probability measure, is supported on the nonnegative orthant $\mathbb R^m_+\times\mathbb R^n_+$, and is integrable, and if $0\le\alpha\le1$ and $0\le\beta\le1$.
--
--   In state $(\mathbf x,\mathbf y)$ (available demand and supply), a matching decision is a matrix $\mathbf Q=(q_{ij})\in\mathbb R^{m\times n}$. Its post-matching levels are
--   $$u_i=x_i-\sum_{j=1}^n q_{ij},\qquad v_j=y_j-\sum_{i=1}^m q_{ij},$$
--   and $\mathbf Q$ is **feasible** if $\mathbf Q\ge0$, $\mathbf u\ge0$ and $\mathbf v\ge0$. The matching reward is $\mathbf R^t\circ\mathbf Q=\sum_{i,j}r^t_{ij}q_{ij}$.
--
--   The value function $V_t$ and the objective $H_t$ are defined by the backward recursion (1): $V_{t}\equiv0$ for $t>T$ (in particular $V_{T+1}\equiv0$), and for $t\le T$
--   $$V_t(\mathbf x,\mathbf y)=\sup_{\mathbf Q\text{ feasible}}H_t(\mathbf Q,\mathbf x,\mathbf y),\qquad H_t(\mathbf Q,\mathbf x,\mathbf y)=\mathbf R^t\circ\mathbf Q+\mathbb E\,V_{t+1}\big(\alpha\mathbf u+\mathbf D^{t+1},\beta\mathbf v+\mathbf S^{t+1}\big),$$
--   where the expectation is over the arrivals entering period $t+1$.
--
--   A decision $\mathbf Q$ is **optimal** in period $t$ at state $(\mathbf x,\mathbf y)$ if it is feasible and $H_t(\mathbf Q',\mathbf x,\mathbf y)\le H_t(\mathbf Q,\mathbf x,\mathbf y)$ for every feasible $\mathbf Q'$. A matching policy $P=\{\mathbf Q^t(\mathbf x,\mathbf y)\}_{t=1,\dots,T}$ is **optimal** if $\mathbf Q^t(\mathbf x,\mathbf y)$ is an optimal decision for every $1\le t\le T$ and every state $\mathbf x\ge0$, $\mathbf y\ge0$. The file also defines the unit matrix $\mathbf e^{m\times n}_{ij}$.
--
--   This is the model on which every structural result of the paper (priority, compatibility, thresholds) is stated.
--
--   **Formalization Note** Periods are natural numbers with the paper's 1-based indexing; $V$ is defined by well-founded recursion on $T+1-t$, and $H_t$ uses the law of period $t+1$, as in the paper's appendix (the display (1) writes $\mathbf D^t,\mathbf S^t$ for the same arrivals). The paper permits exogenous correlation between periods; equation (1) uses one law per period and does not specify a joint arrival process. The supremum is a real `sSup` (value $0$ on an empty or unbounded set) and the expectation a Bochner integral (value $0$ for a non-integrable integrand); integrability of the arrivals is the standing assumption the paper leaves implicit and which makes the expectation in (1) meaningful. Optimality compares $H_t$ across feasible decisions rather than referring to $V_t$.
-- source:
--   Hu, Zhou, Dynamic Type Matching, arXiv:1811.07048v1, pp. 8–10, §3, display (1) and the definition of a matching policy (p. 10)

import Mathlib

namespace DynTypeMatching.Priority

open MeasureTheory

/-- The data of the dynamic type matching model (Hu–Zhou, §3, pp. 8–10).

* `m` demand types `Fin m` and `n` supply types `Fin n`;
* `T` periods, indexed `t = 1, …, T` as in the paper;
* `r t i j` is the per-unit reward `r^t_{ij}` of matching type-`i` demand with type-`j` supply in
  period `t` (only `1 ≤ t ≤ T` is ever used; rewards are arbitrary reals, footnote 2);
* `α`, `β` are the carry-over fractions of unmatched demand and supply;
* `arrival t` is the joint law of the arrival vector `(Dᵗ, Sᵗ)` entering period `t`.

Convention: `arrival t` supplies the period-`t` law used by recursion (1). The paper permits
exogenous correlation between periods; the recursion uses these per-period laws and has no joint
arrival process. -/
structure Model (m n : ℕ) where
  T : ℕ
  r : ℕ → Fin m → Fin n → ℝ
  α : ℝ
  β : ℝ
  arrival : ℕ → Measure ((Fin m → ℝ) × (Fin n → ℝ))

/-- The standing assumptions of §3: each period's arrival law is a probability measure, supported
on the nonnegative orthant and integrable (the integrability makes `E V_{t+1}` in (1) well defined),
and the carry-over fractions lie in `[0, 1]`. -/
structure Model.WellPosed {m n : ℕ} (M : Model m n) : Prop where
  isProbability : ∀ t, IsProbabilityMeasure (M.arrival t)
  arrival_nonneg : ∀ t, ∀ᵐ ω ∂ M.arrival t, 0 ≤ ω.1 ∧ 0 ≤ ω.2
  arrival_integrable : ∀ t, Integrable (fun ω : (Fin m → ℝ) × (Fin n → ℝ) => ω) (M.arrival t)
  α_nonneg : 0 ≤ M.α
  α_le_one : M.α ≤ 1
  β_nonneg : 0 ≤ M.β
  β_le_one : M.β ≤ 1

/-- Post-matching level of demand, `u_i = x_i − ∑_j q_{ij}`. -/
def postD {m n : ℕ} (x : Fin m → ℝ) (Q : Fin m → Fin n → ℝ) : Fin m → ℝ :=
  fun i => x i - ∑ j, Q i j

/-- Post-matching level of supply, `v_j = y_j − ∑_i q_{ij}`. -/
def postS {m n : ℕ} (y : Fin n → ℝ) (Q : Fin m → Fin n → ℝ) : Fin n → ℝ :=
  fun j => y j - ∑ i, Q i j

/-- A matching decision `Q` is feasible in state `(x, y)` if `Q ≥ 0`, `u ≥ 0`, `v ≥ 0`
(the constraint set of (1)). -/
def Feasible {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) (Q : Fin m → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ Q i j) ∧ (∀ i, 0 ≤ postD x Q i) ∧ (∀ j, 0 ≤ postS y Q j)

/-- The matching reward `Rᵗ ∘ Q = ∑_i ∑_j r^t_{ij} q_{ij}`. -/
def matchReward {m n : ℕ} (M : Model m n) (t : ℕ) (Q : Fin m → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, M.r t i j * Q i j

/-- The value function of (1): `V t x y = 0` for `t > T` (boundary condition `V_{T+1} ≡ 0`), and
for `t ≤ T`
`V t x y = sup_{Q feasible} (Rᵗ ∘ Q + E V_{t+1}(α u + D^{t+1}, β v + S^{t+1}))`,
the expectation being over the arrival law of period `t + 1`. -/
noncomputable def V {m n : ℕ} (M : Model m n) (t : ℕ) (x : Fin m → ℝ) (y : Fin n → ℝ) : ℝ :=
  if M.T < t then 0
  else
    sSup ((fun Q : Fin m → Fin n → ℝ =>
        matchReward M t Q +
          ∫ ω, V M (t + 1) (M.α • postD x Q + ω.1) (M.β • postS y Q + ω.2) ∂ M.arrival (t + 1)) ''
      {Q | Feasible x y Q})
termination_by M.T + 1 - t
decreasing_by omega

/-- The objective of (1):
`H t Q x y = Rᵗ ∘ Q + E V_{t+1}(α u + D^{t+1}, β v + S^{t+1})`. -/
noncomputable def H {m n : ℕ} (M : Model m n) (t : ℕ) (Q : Fin m → Fin n → ℝ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) : ℝ :=
  matchReward M t Q +
    ∫ ω, V M (t + 1) (M.α • postD x Q + ω.1) (M.β • postS y Q + ω.2) ∂ M.arrival (t + 1)

/-- The unit matrix `e^{m×n}_{ij}`. -/
def unitMat {m n : ℕ} (i : Fin m) (j : Fin n) : Fin m → Fin n → ℝ :=
  fun a b => if a = i ∧ b = j then 1 else 0

/-- `Q` is an optimal decision in period `t` at state `(x, y)`: it is feasible and maximizes
`H t · x y` over all feasible decisions. -/
def IsOptimalDecision {m n : ℕ} (M : Model m n) (t : ℕ) (x : Fin m → ℝ) (y : Fin n → ℝ)
    (Q : Fin m → Fin n → ℝ) : Prop :=
  Feasible x y Q ∧ ∀ Q', Feasible x y Q' → H M t Q' x y ≤ H M t Q x y

/-- A matching policy `P = {Qᵗ(x, y)}` is optimal if, for every period `1 ≤ t ≤ T` and every
state `x ≥ 0`, `y ≥ 0`, the decision `P t x y` is optimal. -/
def IsOptimalPolicy {m n : ℕ} (M : Model m n)
    (P : ℕ → (Fin m → ℝ) → (Fin n → ℝ) → (Fin m → Fin n → ℝ)) : Prop :=
  ∀ t, 1 ≤ t → t ≤ M.T → ∀ x y, 0 ≤ x → 0 ≤ y → IsOptimalDecision M t x y (P t x y)

end DynTypeMatching.Priority


