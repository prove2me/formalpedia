-- Prove2me | Definitions.Def_PalmQueueing_Loynes_MultiserverQueue
-- name    : PalmQueueing_Loynes_MultiserverQueue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T22:52:39.054991+00:00
-- url     : https://prove2.me/theorems/554709e8-8fcb-45a4-9a8d-a5dd81fa2c2f
-- title:
--   The G/G/s/∞ queue: the Kiefer–Wolfowitz recurrence and the Loynes scheme
-- statement:
--   There are $s \ge 1$ servers, and an arriving customer is assigned to the server with the
--   smallest workload; once assigned it waits and is then served at unit rate until completion.
--
--   The state is the **ordered workload vector** $W_n = (W^1_n, \dots, W^s_n)$, the workloads found in
--   the servers by customer $n$ on arrival, sorted increasingly. It satisfies the **Kiefer and
--   Wolfowitz recurrence**
--   $$ W_{n+1} = \mathcal{R}\big(W_n + \sigma_n e - \tau_n \mathbf{1}\big)^+ , \tag{2.3.1} $$
--   where $e = e_1 = (1,0,\dots,0)$, $\mathbf{1} = (1,\dots,1)$, $\mathcal{R}$ arranges a vector of
--   $\mathbb{R}^s$ in increasing order, and $(\cdot)^+$ is coordinatewise. Everything happens on the
--   Palm space, driven by the two marks $\sigma$ and $\tau$ through the one-customer shift $\theta$, so
--   the equation to be solved reads
--   $$ Z \circ \theta = \mathcal{R}(Z + \sigma e - \tau \mathbf{1})^+ . \tag{2.3.2} $$
--
--   $M_n$ is the ordered workload vector found by customer $0$ if customer $-n$ finds an empty system,
--   $M_n = W^{[0]}_n \circ \theta^{-n}$ (2.3.3), so that
--   $$ M_{n+1} \circ \theta = \mathcal{R}(M_n + \sigma e - \tau\mathbf{1})^+ , \quad \forall n \ge 0 ,
--   \tag{2.3.4} $$
--   with $M_0 = 0$. The sequence increases coordinatewise to a limit $M_\infty$ satisfying (2.3.2),
--   and the book is explicit that "$M_\infty$ has possibly infinite coordinates" — which is why it is
--   carried here as an $\overline{\mathbb{R}}$-valued supremum and why Theorem 2.3.1 has content.
--   $M_\infty$ is the **minimal** solution of (2.3.2).
--
--   For the maximal solution, §2.3.3 introduces the family indexed by $x \in \mathbb{R}_+$:
--   $V^x_0 = M_\infty + x\mathbf{1}$,
--   $V^x_{n+1} \circ \theta = \mathcal{R}(V^x_n + \sigma e - \tau\mathbf{1})^+$ (2.3.13), and
--   $V^x_\infty = \lim_n V^x_n$ (2.3.12). The sequence $\{V^x_n\}$ is non-increasing in $n$ and
--   $V^x_n$ is non-decreasing in $x$, so $V^\infty_\infty = \lim_{x \uparrow \infty} V^x_\infty$
--   (2.3.14) is well defined and is a solution of (2.3.2).
--
--   A solution of (2.3.2) is an identity between random vectors and is required $P^0$-almost surely; a finite version of $M_\infty$ is a real random vector to which $M_n$ converges $P^0$-almost surely.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, §2.3.1-§2.3.3, pp. 91-94

import Mathlib

/-!
# The `G/G/s/∞` queue: the Kiefer-Wolfowitz recurrence (§2.3, pp.91-94)

The multiserver queue lives on the Palm space and is driven by the two marks `σ` (service) and `τ`
(inter-arrival) through a single map, so this module needs no point process: the shift `θ` is the
one-customer shift of the Palm space, an invertible measurable map, and everything is stated in
terms of it. That is exactly how §2.3 reads.

The state is the **ordered workload vector** `W_n = (W¹_n, …, W^s_n)`, the workloads found in the
`s` servers by customer `n` on arrival, sorted increasingly. It obeys the Kiefer-Wolfowitz
recurrence

`(2.3.1)  W_{n+1} = R(W_n + σ_n e − τ_n 1)⁺`

where `e = (1, 0, …, 0)`, `1 = (1, …, 1)`, `R` sorts a vector of `ℝ^s` increasingly and `(·)⁺` is
coordinatewise. The equation to be solved on the Palm space is

`(2.3.2)  Z ∘ θ = R(Z + σe − τ1)⁺`.
-/

namespace PalmQueueing.Loynes

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `R`, the operator arranging a vector of `ℝ^s` in increasing order (p.91). Mathlib's
`Tuple.sort` supplies the sorting permutation. -/
noncomputable def order {s : ℕ} (v : Fin s → ℝ) : Fin s → ℝ := v ∘ Tuple.sort v

/-- `e = e₁ = (1, 0, …, 0)` (p.91): the arriving customer's work goes to the least-loaded server. -/
def kwUnit (s : ℕ) : Fin s → ℝ := fun j => if (j : ℕ) = 0 then 1 else 0

/-- One step of the Kiefer-Wolfowitz recurrence: `v ↦ R(v + σe − τ1)⁺`. -/
noncomputable def kwStep {s : ℕ} (sig tau : ℝ) (v : Fin s → ℝ) : Fin s → ℝ :=
  order fun j => max (v j + sig * kwUnit s j - tau) 0

/-- `(2.3.2)`: `Z` is a solution of the stationary Kiefer-Wolfowitz equation
`Z ∘ θ = R(Z + σe − τ1)⁺`, an identity between random vectors holding `P⁰`-a.s. Being `ℝ`-valued,
such a `Z` is a **finite** solution. -/
def IsKWSolution {s : ℕ} (P0 : Measure Ω) (shift : Ω ≃ᵐ Ω) (sig tau : Ω → ℝ)
    (Z : Ω → Fin s → ℝ) : Prop :=
  ∀ᵐ ω ∂P0, Z (shift ω) = kwStep (sig ω) (tau ω) (Z ω)

/-- `M_n`, the ordered workload vector found by customer `0` if customer `−n` finds an empty system
(2.3.3), through the recurrence `(2.3.4) M_{n+1} ∘ θ = R(M_n + σe − τ1)⁺` with `M₀ = 0`. -/
noncomputable def kwM {s : ℕ} (shift : Ω ≃ᵐ Ω) (sig tau : Ω → ℝ) : ℕ → Ω → Fin s → ℝ
  | 0 => fun _ _ => 0
  | (n + 1) => fun ω =>
      kwStep (sig (shift.symm ω)) (tau (shift.symm ω)) (kwM shift sig tau n (shift.symm ω))

/-- `M_∞` is the coordinatewise limit of the non-decreasing sequence `{M_n}` (p.92). It is
`EReal`-valued because the book says in as many words that "`M_∞` has possibly infinite
coordinates"; Theorem 2.3.1 is precisely the statement that under `E⁰[σ] < s E⁰[τ]` it does not. -/
noncomputable def kwMinf {s : ℕ} (shift : Ω ≃ᵐ Ω) (sig tau : Ω → ℝ) (ω : Ω) (j : Fin s) : EReal :=
  ⨆ n : ℕ, ((kwM shift sig tau n ω j : ℝ) : EReal)

/-- `Mf` is a finite version of `M_∞`: `P⁰`-a.s. the coordinatewise limit of `{M_n}`, taken as a
real-valued random vector. §2.3.3, where the maximal solution is studied, works under stability, and
Theorem 2.3.1 then gives `M_∞ < ∞` `P⁰`-a.s. — only almost surely, which is why the convergence is
required only almost surely. -/
def IsKWLimit {s : ℕ} (P0 : Measure Ω) (shift : Ω ≃ᵐ Ω) (sig tau : Ω → ℝ)
    (Mf : Ω → Fin s → ℝ) : Prop :=
  ∀ᵐ ω ∂P0, ∀ j : Fin s,
    Tendsto (fun n : ℕ => kwM shift sig tau n ω j) atTop (𝓝 (Mf ω j))

/-- The family of finite solutions of `(2.3.2)` indexed by `x ∈ ℝ₊` (2.3.12)-(2.3.13):
`V^x₀ = M_∞ + x·1` and `V^x_{n+1} ∘ θ = R(V^x_n + σe − τ1)⁺`. The sequence `{V^x_n}` is
non-increasing in `n` and `V^x_n` is non-decreasing in `x`. -/
noncomputable def kwV {s : ℕ} (shift : Ω ≃ᵐ Ω) (sig tau : Ω → ℝ) (Mf : Ω → Fin s → ℝ) (x : ℝ) :
    ℕ → Ω → Fin s → ℝ
  | 0 => fun ω j => Mf ω j + x
  | (n + 1) => fun ω =>
      kwStep (sig (shift.symm ω)) (tau (shift.symm ω)) (kwV shift sig tau Mf x n (shift.symm ω))

end PalmQueueing.Loynes


