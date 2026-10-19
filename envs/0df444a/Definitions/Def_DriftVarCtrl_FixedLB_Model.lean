-- Prove2me | Definitions.Def_DriftVarCtrl_FixedLB_Model
-- name    : DriftVarCtrl_FixedLB_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:38.55264+00:00
-- url     : https://prove2.me/theorems/b7354212-4826-4c1c-9723-463cd5b72480
-- title:
--   §2–§3, pp. 7–11 — two controls (μᵢ, σᵢ, hᵢ), boundary U, reward −M > 0, k-interval policies (Definition 1), h*ᵢ, Δhᵢ, vᵢ, the policy value (analytic) and optimality
-- statement:
--   This file sets up the fixed-lower-boundary drift–variance control problem of Wang and Zenios.
--
--   **Controls and parameters (§2, pp. 7–8).** An entrepreneur steers a state $X(t)$ by choosing at every moment one of two controls $i \in \{1,2\}$. Control $i$ gives drift $\mu_i > 0$, volatility $\sigma_i > 0$ (infinitesimal variance $\sigma_i^2$) and costs $h_i > 0$ per unit time:
--   $$dX(t) = \mu(A(t))\,dt + \sigma(A(t))\,dB(t).$$
--   The process is absorbed at $0$ (no payment) and at the upper boundary $U > 0$, where a terminal cost $M < 0$ is paid (a reward $|M|$). The entrepreneur minimizes the expected total cost.
--
--   **Derived quantities (Definitions 2–3, p. 11).** The critical cost, the cost deviation and the effective drift of control $i$ are
--   $$h_i^* = -\frac{M\mu_i}{U},\qquad \Delta h_i = h_i - h_i^*,\qquad v_i = \frac{2\mu_i}{\sigma_i^2}.$$
--
--   **Interval policies (Definition 1, pp. 8–9).** A $k$-interval policy ($k \ge 1$) is given by breakpoints $0 = S_0 < S_1 < \dots < S_k = U$ and controls $i_1,\dots,i_k \in \{1,2\}$ with $i_j \ne i_{j+1}$; it uses control $i_j$ on $[S_{j-1}, S_j)$. It is static if $k = 1$ and dynamic if $k \ge 2$. Two special families are named: the static policy "always use control $c$", and the two-interval policy that uses a control $c$ on $[0,S)$ and the other control on $[S,U)$, for $S \in (0,U)$.
--
--   **Value of a policy.** A function $W$ is a value of the interval policy $\pi$ if $W$ is continuously differentiable on $[0,U]$, $W(0) = 0$, $W(U) = M$, and on each open piece $(S_{j-1}, S_j)$ it is twice continuously differentiable and solves
--   $$h_{i_j} + \mu_{i_j} W'(x) + \frac{\sigma_{i_j}^2}{2} W''(x) = 0 .$$
--   These are the systems (52)–(53) and (56)–(59) through which the paper computes the value of every policy it evaluates; continuity of $W'$ at the switch points is the smooth-pasting condition (57).
--
--   **Optimality.** An interval policy $\pi$ is optimal if it has a value $V$ such that $V(x) \le W(x)$ for every $x \in [0,U]$, every interval policy $\pi'$ (of any length $k$) and every value $W$ of $\pi'$.
--
--   These objects are the common ground of every statement of the mission: Theorem 1 asserts that an optimal interval policy has at most two intervals.
--
--   **Formalization Note.** Mathlib has no stochastic integral, so the SDE and the expected cost (2) are not formalized. The value of a policy is encoded analytically by its ODE boundary-value system; the identity "expected cost of $\pi$ = this $W$" is Dynkin's formula (the second half of Lemma 12) and is not part of the mission. Optimality is over interval policies, to which the paper itself restricts (p. 8). The lower boundary is $L = 0$ with terminal cost $m = 0$ (p. 8). The standing assumption $v_1 < v_2$ (p. 12) is not built in; each later theorem takes it as a hypothesis. Controls are an inductive type with two constructors; the $j$-th piece is indexed from $0$ in Lean.
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), pp. 7–11, §2 (model (1)–(2), L = m = 0), Definition 1 (k-interval policies), Definitions 2–3 ((4)–(6)); value systems (52)–(53), (56)–(59), pp. EC-4–EC-5

import Mathlib

namespace DriftVarCtrl.FixedLB

/-- The two controls `I = {1, 2}` of Wang, Zenios, *New Venture Creation: A Drift-Variance
Diffusion Control Model*, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. 7, §2. -/
inductive Ctrl
  | one
  | two
  deriving DecidableEq

/-- The control other than `c`. -/
def Ctrl.other : Ctrl → Ctrl
  | .one => .two
  | .two => .one

/-- The primitives of the fixed-lower-boundary model (Wang, Zenios, SSRN 3667132, pp. 7–8, §2):
drifts `μ₁, μ₂ > 0`, volatilities `σ₁, σ₂ > 0` (the diffusion term of (1) is `σ(A(t)) dB(t)`, so
the infinitesimal variance is `σᵢ²`), running costs `h₁, h₂ > 0`, the upper boundary `U > 0` and
the terminal cost `M < 0` paid on hitting `U` (the reward is `|M|`). The lower boundary is
`L = 0` with terminal cost `m = 0` (p. 8).

Formalization Note: the paper's standing `v₂ > v₁` (p. 12) is *not* a field; it is an explicit
hypothesis of every theorem stated after p. 12. -/
structure Params where
  μ₁ : ℝ
  μ₂ : ℝ
  σ₁ : ℝ
  σ₂ : ℝ
  h₁ : ℝ
  h₂ : ℝ
  U : ℝ
  M : ℝ
  hμ₁ : 0 < μ₁
  hμ₂ : 0 < μ₂
  hσ₁ : 0 < σ₁
  hσ₂ : 0 < σ₂
  hh₁ : 0 < h₁
  hh₂ : 0 < h₂
  hU : 0 < U
  hM : M < 0

/-- Drift `μ(c)` of control `c`. -/
def Params.mu (p : Params) : Ctrl → ℝ
  | .one => p.μ₁
  | .two => p.μ₂

/-- Volatility `σ(c)` of control `c` (the variance is `σ(c)²`). -/
def Params.sig (p : Params) : Ctrl → ℝ
  | .one => p.σ₁
  | .two => p.σ₂

/-- Running cost `h(c)` of control `c`. -/
def Params.cost (p : Params) : Ctrl → ℝ
  | .one => p.h₁
  | .two => p.h₂

/-- The effective drift `vᵢ = 2μᵢ/σᵢ²` ((6), Definition 3, SSRN 3667132 p. 11). -/
noncomputable def v (p : Params) (c : Ctrl) : ℝ := 2 * p.mu c / p.sig c ^ 2

/-- The critical cost `h*ᵢ = −M μᵢ / U` ((4), Definition 2, SSRN 3667132 p. 11). -/
noncomputable def hstar (p : Params) (c : Ctrl) : ℝ := -p.M * p.mu c / p.U

/-- The cost deviation `Δhᵢ = hᵢ − h*ᵢ` ((5), Definition 2, SSRN 3667132 p. 11). -/
noncomputable def Δh (p : Params) (c : Ctrl) : ℝ := p.cost c - hstar p c

/-- A `k`-interval policy (Definition 1, SSRN 3667132 pp. 8–9): breakpoints
`0 = S₀ < S₁ < ⋯ < S_k = U` and controls `i₁, …, i_k` with adjacent controls distinct; control
`ctrl j` is used on the interval `[S j.castSucc, S j.succ)` (0-based `j`). The policy is static if
`k = 1` and dynamic if `k ≥ 2`. -/
structure IntervalPolicy (p : Params) where
  k : ℕ
  one_le_k : 1 ≤ k
  ctrl : Fin k → Ctrl
  S : Fin (k + 1) → ℝ
  S_zero : S 0 = 0
  S_last : S (Fin.last k) = p.U
  S_strictMono : StrictMono S
  alt : ∀ (j : ℕ) (h : j + 1 < k), ctrl ⟨j, by omega⟩ ≠ ctrl ⟨j + 1, h⟩

/-- The static (1-interval) policy that always uses control `c`. -/
def static (p : Params) (c : Ctrl) : IntervalPolicy p where
  k := 1
  one_le_k := le_rfl
  ctrl := fun _ => c
  S := fun i => (i.val : ℝ) * p.U
  S_zero := by simp
  S_last := by simp
  S_strictMono := fun a b hab => mul_lt_mul_of_pos_right (by exact_mod_cast hab) p.hU
  alt := fun j h => absurd h (by omega)

/-- The two-interval policy that uses control `first` on `[0, S)` and the other control on
`[S, U)`, for a switching point `S ∈ (0, U)`. -/
def twoInt (p : Params) (first : Ctrl) (S : ℝ) (hS : S ∈ Set.Ioo 0 p.U) : IntervalPolicy p where
  k := 2
  one_le_k := by norm_num
  ctrl := fun j => if j.val = 0 then first else first.other
  S := ![0, S, p.U]
  S_zero := rfl
  S_last := rfl
  S_strictMono := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    · exact hS.1
    · exact hS.2
  alt := by
    intro j h
    have hj : j = 0 := by omega
    subst hj
    cases first <;> simp [Ctrl.other]

/-- `W` is the value of the interval policy `π` (analytic encoding of the expected cost (2),
SSRN 3667132 p. 8, through the systems (52)–(53) and (56)–(59), pp. EC-4–EC-5): `W` is `C¹` on
`[0, U]` (smooth pasting (57) at every switch point), `W(0) = 0`, `W(U) = M`, and on every open
piece `(S_{j-1}, S_j)` it is `C²` and solves `h(i_j) + μ(i_j) W′ + σ(i_j)²/2 · W″ = 0`.

Formalization Note: the identity "expected cost (2) of `π` = this `W`" (Dynkin's formula, the
second half of Lemma 12, pp. EC-14–EC-15) is not formalized; Mathlib has no stochastic
integral. -/
def IsValue (p : Params) (π : IntervalPolicy p) (W : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 1 W (Set.Icc 0 p.U) ∧ W 0 = 0 ∧ W p.U = p.M ∧
  ∀ (j : Fin π.k) (x : ℝ), x ∈ Set.Ioo (π.S j.castSucc) (π.S j.succ) →
    ContDiffAt ℝ 2 W x ∧
    p.cost (π.ctrl j) + p.mu (π.ctrl j) * deriv W x
      + p.sig (π.ctrl j) ^ 2 / 2 * deriv (deriv W) x = 0

/-- `π` is optimal: it has a value `V` lying below every value `W` of every interval policy `π'`
(of every length `k`) at every point of `[0, U]`. Minimization, since (2) is a cost and the
reward enters as `M < 0`. -/
def IsOptimal (p : Params) (π : IntervalPolicy p) : Prop :=
  ∃ V, IsValue p π V ∧ ∀ (π' : IntervalPolicy p) (W : ℝ → ℝ), IsValue p π' W →
    ∀ x ∈ Set.Icc 0 p.U, V x ≤ W x

end DriftVarCtrl.FixedLB


