-- Prove2me | Definitions.Def_GallegoOzerADI_PositiveSetup_Supplement_Stationary
-- name    : GallegoOzerADI_PositiveSetup_Supplement_Stationary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:40:21.429336+00:00
-- url     : https://prove2.me/theorems/632e3ed8-9dfa-4da0-89ee-8d40719b46e7
-- title:
--   Stationary finite-horizon recursion (8)–(9), policy parameters, and the infinite-horizon inventory problem with advance demand information
-- statement:
--   This file defines the stationary version of the inventory model with advance demand information of Gallego and Özer (2001), §§2–5, indexed by the number of remaining periods, and the infinite-horizon problem.
--
--   **Data.** The lead time is $L\ge0$ and the information horizon is $N=L+M+1$ with $M\ge1$ observed demands beyond the protection period. The stationary data are the single-period cost $G:\mathbb R\to\mathbb R$, the set-up cost $K$, the discount factor $\alpha$ and the law $\mu$ of the demand vector $D=(D_{t,t},\dots,D_{t,t+N})\in\mathbb R^{N+1}$. The state is $(x,o)$: the modified inventory position $x\in\mathbb R$ and the observed-demand vector $o=(o_{t,t+L+1},\dots,o_{t,t+N-1})\in\mathbb R^M$. Ordering up to $y\ge x$ and observing $D$ leads to the state $(x',O')$ given by the published transitions (5)–(6):
--   $$
--   x'=y-D_{t,t}-\sum_{s=t+1}^{t+L+1}D_{t,s}-o_{t,t+L+1},\qquad O'_{s}=o_{s}+D_{t,s}\ (s=t+L+2,\dots,t+N),
--   $$
--   with $o_{t,t+N}=0$.
--
--   **Finite-horizon recursion.** With $\delta(z)=1$ for $z>0$ and $0$ otherwise, set $J_0\equiv0$ and, for $n\ge0$,
--   $$
--   V_n(y,o)=G(y)+\alpha\,\mathbb E\,J_n(x',O'),\qquad J_{n+1}(x,o)=\min_{y\ge x}\{K\delta(y-x)+V_n(y,o)\}.
--   $$
--   In a horizon-$T$ problem, the paper's $J_t$ is $J_{T+1-t}$ and its $V_t$ is $V_{T-t}$, so letting $T\to\infty$ with $t$ fixed is letting $n\to\infty$. The order-up-to level $S_n(o)$ is the smallest minimizer of $V_n(\cdot,o)$ (for $K=0$ the base-stock level $y_n(o)$ of Eq. (11)), and the reorder point is $s_n(o)=\max\{y:H_n(y,o)\le0\}$ with $H_n(y,o)=K+\min_{z\ge y}V_n(z,o)-V_n(y,o)$. For any function $J$ of the state, $V^J(y,o)=G(y)+\alpha\,\mathbb E\,J(x',O')$ is the cost-to-go of Theorem 3, Part 2.
--
--   **Infinite-horizon problem.** The inventory problem is the control system with state $(x,o)$, action $y$, feasibility $y\ge x$, disturbance $D$, the transitions above and one-period cost $K\delta(y-x)+G(y)$, the summand of (12). Its optimal value $J^\ast(x,o)$ is the infimum over all admissible history-dependent policies of the expected discounted cost with i.i.d. demand vectors of law $\mu$. The state-dependent $(s,S)$ policy orders up to $S(o)$ when $x\le s(o)$ and does not order otherwise; the base-stock policy with level $y$ orders up to $\max(x,y)$.
--
--   A structural lemma records that, for stationary data, the published finite-horizon model `GallegoOzerADI.PositiveSetup.Model` has exactly this recursion.
--
--   **Formalization Note.** Minima over $y\ge x$ are infima over the subtype $\{y\ge x\}$ (published `orderCost`, `reorderGap`); the smallest minimizer and the largest point with $H_n\le0$ are `sInf`/`sSup` of the corresponding sets, which are the paper's min and max whenever those exist (attainment is a theorem conclusion, never part of the definitions). Expectations are Bochner integrals against $\mu$. Nothing in this file imposes growth, moment, sign or support conditions; $K=0$ is allowed, so the zero set-up cost case uses the same definitions.
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), pp. 1347–1352, Eqs. (5), (6), (8), (9), (11), the definitions of S_t(o_t), s_t(o_t), H_t on p. 1350, stationarity on p. 1350, and Appendix A, Eq. (12), p. 1356

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_SetupCost
import Definitions.Def_GallegoOzerADI_PositiveSetup_Model
import Definitions.Def_GallegoOzerADI_PositiveSetup_Supplement_ControlSystem

open MeasureTheory

namespace GallegoOzerADI.PositiveSetup.Supplement

variable {L M : ℕ}

/-- The stationary finite-horizon recursion (8)–(9) of Gallego–Özer (2001), indexed by the
number `n` of remaining periods. The data are horizon free: the single-period cost `G`, the
set-up cost `K`, the discount factor `α` and the law `μ` of the demand vector
`D = (D_{t,t}, …, D_{t,t+N})` on `Fin (L + M + 2) → ℝ`, with `N = L + M + 1`.
`Jgo 0 ≡ 0` (the terminal `J_{T+1} ≡ 0`) and
`Jgo (n+1) x o = min_{y ≥ x} {K δ(y − x) + G y + α E Jgo n (x', O')}` with the transitions
(5)–(6) `x' = nextX y o D`, `O' = nextO o D`. In a horizon-`T` problem, `J_t = Jgo (T + 1 − t)`. -/
noncomputable def Jgo (G : ℝ → ℝ) (K α : ℝ) (μ : Measure (Fin (L + M + 2) → ℝ)) :
    ℕ → ℝ → (Fin M → ℝ) → ℝ
  | 0 => fun _ _ => 0
  | n + 1 => fun x o =>
      orderCost K (fun y => G y + α * ∫ D, Jgo G K α μ n (nextX y o D) (nextO o D) ∂μ) x

/-- The cost-to-go (9) with `n` further periods after the current one:
`Vgo n y o = G y + α E Jgo n (nextX y o D, nextO o D)`. In a horizon-`T` problem,
`V_t = Vgo (T − t)`. -/
noncomputable def Vgo (G : ℝ → ℝ) (K α : ℝ) (μ : Measure (Fin (L + M + 2) → ℝ)) (n : ℕ)
    (y : ℝ) (o : Fin M → ℝ) : ℝ :=
  G y + α * ∫ D, Jgo G K α μ n (nextX y o D) (nextO o D) ∂μ

/-- Equation (8) in the stationary recursion: `Jgo (n+1) x o = min_{y ≥ x} {K δ(y−x) + Vgo n y o}`. -/
theorem Jgo_succ (G : ℝ → ℝ) (K α : ℝ) (μ : Measure (Fin (L + M + 2) → ℝ)) (n : ℕ) (x : ℝ)
    (o : Fin M → ℝ) : Jgo G K α μ (n + 1) x o = orderCost K (fun y => Vgo G K α μ n y o) x :=
  rfl

/-- The finite-horizon order-up-to level with `n` further periods: the smallest minimizer of
`Vgo n (·, o)`, i.e. `S_t(o) = min {y : V_t(y, o) = min_x V_t(x, o)}` (p. 1350); for `K = 0` it is
the base-stock level `y_t(o)` of Eq. (11). -/
noncomputable def orderUpToLevel (G : ℝ → ℝ) (K α : ℝ) (μ : Measure (Fin (L + M + 2) → ℝ))
    (n : ℕ) (o : Fin M → ℝ) : ℝ :=
  sInf {y : ℝ | ∀ z, Vgo G K α μ n y o ≤ Vgo G K α μ n z o}

/-- The finite-horizon reorder point with `n` further periods:
`s_t(o) = max {y : H_t(y, o) ≤ 0}` (p. 1350), `H_t = K + min_{z ≥ y} V_t(z, o) − V_t(y, o)`. -/
noncomputable def reorderLevel (G : ℝ → ℝ) (K α : ℝ) (μ : Measure (Fin (L + M + 2) → ℝ))
    (n : ℕ) (o : Fin M → ℝ) : ℝ :=
  sSup {y : ℝ | reorderGap K (fun z => Vgo G K α μ n z o) y ≤ 0}

/-- The cost-to-go built from a function `J` of the next state, as in Theorem 3, Part 2:
`V(y, o) = G(y) + α E J(nextX y o D, nextO o D)`. -/
noncomputable def contValue (G : ℝ → ℝ) (α : ℝ) (μ : Measure (Fin (L + M + 2) → ℝ))
    (J : ℝ → (Fin M → ℝ) → ℝ) (y : ℝ) (o : Fin M → ℝ) : ℝ :=
  G y + α * ∫ D, J (nextX y o D) (nextO o D) ∂μ

/-- The inventory problem with advance demand information as a control system: the state is the
modified inventory position and the observed-demand vector `(x, o)`, the action is the
order-up-to level `y`, feasible iff `y ≥ x`; the disturbance is the demand vector `D`; the next
state is `(nextX y o D, nextO o D)` (Eqs. (5)–(6)), and the one-period cost is
`K δ(y − x) + G(y)`, the summand of the policy cost (12). -/
noncomputable def adiSystem (G : ℝ → ℝ) (K : ℝ) :
    ControlSystem (ℝ × (Fin M → ℝ)) ℝ (Fin (L + M + 2) → ℝ) where
  next := fun s y D => (nextX y s.2 D, nextO s.2 D)
  cost := fun s y => K * setupIndicator (y - s.1) + G y
  feasible := fun s y => s.1 ≤ y

/-- The optimal value `J(x, o)` of the infinite-horizon discounted problem: the infimum, over
all admissible history-dependent policies, of the expected discounted cost
`E ∑_{k ≥ 0} α^k {K δ(y_k − x_k) + G(y_k)}` (the infinite-horizon form of (12)), with i.i.d.
demand vectors of law `μ`. -/
noncomputable def infValue (G : ℝ → ℝ) (K α : ℝ) (μ : Measure (Fin (L + M + 2) → ℝ))
    [IsProbabilityMeasure μ] (x : ℝ) (o : Fin M → ℝ) : EReal :=
  (adiSystem (L := L) G K).optimalValue α μ (x, o)

/-- The state-dependent `(s, S)` policy: in state `(x, o)` order up to `S(o)` if `x ≤ s(o)`,
otherwise do not order. -/
noncomputable def sSPolicy (s S : (Fin M → ℝ) → ℝ) : ℝ × (Fin M → ℝ) → ℝ :=
  fun st => if st.1 ≤ s st.2 then S st.2 else st.1

/-- The base-stock policy with level `y`: order up to `max(x, y)`. -/
noncomputable def baseStockPolicy (y : ℝ) : ℝ × (Fin M → ℝ) → ℝ :=
  fun st => max st.1 y

/-- Compatibility with the published finite-horizon model: for stationary data, the base
recursion `P.Jgo` with `n` remaining periods is `Jgo n`. -/
theorem Model.Jgo_eq_stationary [NeZero M] (P : Model L M) (G : ℝ → ℝ) (K α : ℝ)
    (μ : Measure (Fin (L + M + 2) → ℝ)) (hG : ∀ t, P.G t = G) (hK : ∀ t, P.K t = K)
    (hα : ∀ t, P.α t = α) (hμ : ∀ t, P.μ t = μ) (n : ℕ) :
    P.Jgo n = Jgo G K α μ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x o
    simp only [Model.Jgo, Jgo, hG, hK, hα, hμ, ih]

end GallegoOzerADI.PositiveSetup.Supplement


