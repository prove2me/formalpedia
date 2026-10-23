-- Prove2me | Definitions.Def_MonopolyDemandUncertainty_SBSMP_Setting
-- name    : MonopolyDemandUncertainty_SBSMP_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:10:41.531005+00:00
-- url     : https://prove2.me/theorems/8b492a31-ffdf-449b-a6b5-1cab8aa6ea72
-- title:
--   §2–§3, pp. 2–5 (PDF 3–6) — two-state economy, Conditions 1–3 and 4(ii), deterministic mechanisms, EIR (2), BIC (4), profit (3), SBSMP (6), monopoly price
-- statement:
--   This file fixes the model of Peck and Rampal's monopoly problem with aggregate demand uncertainty.
--
--   1. **Economy.** A zero-cost monopolist faces a continuum of unit-demand consumers. There are two demand states: the low state (state 1, probability $\alpha_1$) and the high state (state 2, probability $\alpha_2 = 1-\alpha_1$). Valuations lie in $V = [\underline v, \bar v]$, and $D_i(v)$ is the mass of consumers with valuation above $v$ in state $i$. The demand density is $f_i(v) = -D_i'(v)$ and the density ratio is
--   $$Z(v) = \frac{-D_1'(v)}{-D_2'(v)}.$$
--   The standing assumptions are $0 \le \underline v < \bar v$, $0 < \alpha_1 < 1$ and $D_i(\bar v) = 0$.
--   2. **Conditions.** Condition 1 (regularity): each $D_i$ is $C^2$ and $D_i'(v) < 0$ on $V$. Condition 2 (information effect): $Z'(v) < 0$ on $V$. Condition 3 (concave demand): $D_i''(v) < 0$ on $V$. Condition 4(ii): $\frac{\alpha_1}{\alpha_2} Z(v) > 1$ on $V$, that is, every type finds the low state more likely.
--   3. **Mechanisms.** A deterministic direct mechanism specifies, for each state $i$ and reported valuation $v$, an allocation $x_i(v) \in \{0,1\}$ and a payment $t_i(v)$. It is anonymous: allocations and payments depend on the inferred state and on the consumer's own report only. It is *ex post individually rational* (EIR, (2)) when $0 \le t_i(v) \le v$ for all $v \in V$ and both states.
--   4. **Incentive compatibility.** Type $v$ reporting $\hat v$ obtains, up to the common positive denominator of its posterior beliefs,
--   $$U(v,\hat v) = \sum_{i=1}^{2} \big(v - t_i(\hat v)\big)\, x_i(\hat v)\, \alpha_i \big(-D_i'(v)\big),$$
--   and the mechanism is *Bayesian incentive compatible* (BIC, (4)) when $U(v,\hat v) \le U(v,v)$ for all $v, \hat v \in V$.
--   5. **Profit** (3): $\pi = \int_V \sum_i t_i(v)\, x_i(v)\, \alpha_i (-D_i'(v))\, dv$. The sets $V_i$ (types consuming only in state $i$) and $V_{12}$ (types consuming in both states) are also defined.
--   6. **SBSMP and monopoly prices.** State-by-state posted prices $(a,b)$ sell in state 1 to every $v \ge a$ at price $a$ and in state 2 to every $v \ge b$ at price $b$ (as in (6)). A monopoly price in state $i$ is a maximizer of $p\,D_i(p)$ over $p \in V$.
--   7. **Claim 4 data.** The payment $t_1(v_1^*) = v_1^* - (v_1^*-v_2^*)\frac{\alpha_2}{\alpha_1 Z(v_1^*)}$ of (A.30) and the constraint set (i)–(v) of Claim 4 on a payment scheme for $V_{12}$.
--
--   These objects are the setting of every statement in the mission.
--
--   **Formalization Note** States are indexed by `Fin 2`: index `0` is the paper's state 1 (low), index `1` its state 2 (high). Allocations are `Bool`, which encodes "deterministic". Each $D_i$ is a $C^2$ function on all of $\mathbb R$ (a $C^2$ extension of the demand on $V$); only its values on $V$ enter. The hypotheses $D_i(\bar v)=0$ (no valuation exceeds $\bar v$), $0 \le \underline v$ (needed for EIR to be satisfiable) and $0<\alpha_1<1$ are added to the page and stated explicitly. Condition 4(ii) is cross-multiplied as $\alpha_2(-D_2'(v)) < \alpha_1(-D_1'(v))$, which is equivalent to the printed ratio form under Condition 1. Condition 4(i) is deliberately not defined. Posted prices charge $0$ to non-buyers, which (6) leaves unspecified. The profit is a Lebesgue set integral, which Lean sets to $0$ for a non-integrable integrand.
-- source:
--   Peck, Rampal, Optimal Monopoly Mechanisms with Demand Uncertainty, Mathematics of Operations Research (2021), Articles in Advance, doi:10.1287/moor.2020.1120, pp. 2–5, §2–§3, (2)–(4), (6), Conditions 1–4; p. 12, (A.30); p. 13, Claim 4

import Mathlib

namespace MonopolyDemandUncertainty.SBSMP

open MeasureTheory Set

/-- §2, pp. 2–3: a monopoly economy with two demand states. Valuations lie in
`V = [vlo, vhi]`, the low state has prior probability `α₁`, and `D i v` is the mass of
consumers with valuation above `v` in state `i`. Index `0` is the paper's state 1 (low demand,
probability `α₁`); index `1` is the paper's state 2 (high demand, probability `α₂ = 1 - α₁`). -/
structure Economy where
  vlo : ℝ
  vhi : ℝ
  α₁ : ℝ
  D : Fin 2 → ℝ → ℝ

namespace Economy

/-- The valuation interval `V = [v_, v̄]`. -/
def V (E : Economy) : Set ℝ := Icc E.vlo E.vhi

/-- State probabilities: `prob 0 = α₁` (low state), `prob 1 = α₂ = 1 - α₁` (high state). -/
def prob (E : Economy) : Fin 2 → ℝ := ![E.α₁, 1 - E.α₁]

/-- The demand density `-D_i'(v)` in state `i`. -/
noncomputable def dens (E : Economy) (i : Fin 2) (v : ℝ) : ℝ := -deriv (E.D i) v

/-- The ratio `Z(v) = (-D₁'(v)) / (-D₂'(v))` (paper's states 1 and 2 = indices 0 and 1). -/
noncomputable def Z (E : Economy) (v : ℝ) : ℝ := E.dens 0 v / E.dens 1 v

/-- Standing assumptions of §2: `0 ≤ v_ < v̄`, `0 < α₁ < 1`, and `D_i(v̄) = 0` (no consumer
has a valuation above `v̄`). -/
structure Valid (E : Economy) : Prop where
  vlo_nonneg : 0 ≤ E.vlo
  vlo_lt_vhi : E.vlo < E.vhi
  α₁_pos : 0 < E.α₁
  α₁_lt_one : E.α₁ < 1
  D_vhi : ∀ i, E.D i E.vhi = 0

/-- Condition 1 (Regularity), p. 4: each `D_i` is twice continuously differentiable (on all of
`ℝ`, i.e. a `C²` extension of the demand on `V`), and `D_i'(v) < 0` for all `v ∈ V`. -/
def Condition1 (E : Economy) : Prop :=
  (∀ i, ContDiff ℝ 2 (E.D i)) ∧ ∀ i, ∀ v ∈ E.V, deriv (E.D i) v < 0

/-- Condition 2 (Information Effect), p. 4, in its printed "that is" form: `Z'(v) < 0` on `V`. -/
def Condition2 (E : Economy) : Prop := ∀ v ∈ E.V, deriv E.Z v < 0

/-- Condition 3 (Concave Demand), p. 5: `D_i''(v) < 0` for all `v ∈ V` and both states. -/
def Condition3 (E : Economy) : Prop := ∀ i, ∀ v ∈ E.V, deriv (deriv (E.D i)) v < 0

/-- Condition 4(ii), p. 5: `(α₁/α₂) Z(v) > 1` for all `v ∈ V`, stated cross-multiplied as
`α₂ (-D₂'(v)) < α₁ (-D₁'(v))` (both denominators are positive under Condition 1).
Condition 4(i) is deliberately not defined. -/
def Condition4ii (E : Economy) : Prop :=
  ∀ v ∈ E.V, E.prob 1 * E.dens 1 v < E.prob 0 * E.dens 0 v

end Economy

/-- A deterministic direct mechanism (2): in state `i`, type `v` gets the good iff `x i v`,
and pays `t i v`. Index `0` is the paper's state 1, index `1` its state 2. -/
structure Mechanism where
  x : Fin 2 → ℝ → Bool
  t : Fin 2 → ℝ → ℝ

/-- The indicator `[b] ∈ {0, 1}` of a Boolean allocation. -/
def ind (b : Bool) : ℝ := if b then 1 else 0

namespace Economy

/-- Interim payoff of type `v` reporting `vhat`, after cancelling the common positive
denominator of the beliefs (1): `Σ_i (v - t_i(vhat)) x_i(vhat) α_i (-D_i'(v))`, as in (4). -/
noncomputable def payoff (E : Economy) (M : Mechanism) (v vhat : ℝ) : ℝ :=
  ∑ i, (v - M.t i vhat) * ind (M.x i vhat) * E.prob i * E.dens i v

/-- Ex post individual rationality (2): `0 ≤ t_i(v) ≤ v` for every `v ∈ V` and both states. -/
def IsEIR (E : Economy) (M : Mechanism) : Prop :=
  ∀ i, ∀ v ∈ E.V, 0 ≤ M.t i v ∧ M.t i v ≤ v

/-- Bayesian incentive compatibility (4): no type `v ∈ V` gains by reporting any `vhat ∈ V`. -/
def IsBIC (E : Economy) (M : Mechanism) : Prop :=
  ∀ v ∈ E.V, ∀ vhat ∈ E.V, E.payoff M v vhat ≤ E.payoff M v v

/-- The firm's expected profit (3), written as one integral over `V`:
`∫_V Σ_i t_i(v) x_i(v) α_i (-D_i'(v)) dv`. -/
noncomputable def profit (E : Economy) (M : Mechanism) : ℝ :=
  ∫ v in E.V, ∑ i, M.t i v * ind (M.x i v) * E.prob i * E.dens i v

/-- `V_i`: types in `V` that consume in state `i` only. -/
def onlySet (E : Economy) (M : Mechanism) (i : Fin 2) : Set ℝ :=
  {v | v ∈ E.V ∧ M.x i v = true ∧ ∀ j, j ≠ i → M.x j v = false}

/-- `V₁₂`: types in `V` that consume in both states. -/
def bothSet (E : Economy) (M : Mechanism) : Set ℝ :=
  {v | v ∈ E.V ∧ ∀ j, M.x j v = true}

/-- A monopoly price in state `i`: a maximizer of the revenue `p · D_i(p)` over `p ∈ V`. -/
def IsMonopolyPrice (E : Economy) (i : Fin 2) (p : ℝ) : Prop :=
  p ∈ E.V ∧ ∀ q ∈ E.V, q * E.D i q ≤ p * E.D i p

/-- The state-1 payment `t₁(v₁*) = v₁* - (v₁* - v₂*) α₂ / (α₁ Z(v₁*))` of (A.30), p. 12,
with `a₁ = v₁*`, `a₂ = v₂*`. -/
noncomputable def claim4T1 (E : Economy) (a₁ a₂ : ℝ) : ℝ :=
  a₁ - (a₁ - a₂) * E.prob 1 / (E.prob 0 * E.Z a₁)

/-- The constraints (i)–(v) of Claim 4, p. 13, on a payment scheme `s` for the types of
`V₁₂ = [b, v̄]` (who consume in both states), with `a₁ = v₁*`, `a₂ = v₂*`, `b = v₁₂*`:
(i) BIC of `b` with respect to `a₁` (who consumes in state 1 only and pays `claim4T1`);
(ii) BIC of every `v ∈ (b, v̄]` with respect to `b`; (iii) EIR of `b`, `0 ≤ s_i(b) ≤ b`;
(iv) `s₂(b) ≥ v₂*`; (v) `s₁(b) ≥ t₁(v₁*)`. -/
def Claim4Feasible (E : Economy) (a₁ a₂ b : ℝ) (s : Fin 2 → ℝ → ℝ) : Prop :=
  (b - E.claim4T1 a₁ a₂) * E.prob 0 * E.dens 0 b ≤
      (b - s 0 b) * E.prob 0 * E.dens 0 b + (b - s 1 b) * E.prob 1 * E.dens 1 b ∧
    (∀ v ∈ Ioc b E.vhi,
      ∑ i, (v - s i b) * E.prob i * E.dens i v ≤ ∑ i, (v - s i v) * E.prob i * E.dens i v) ∧
    (∀ i, 0 ≤ s i b ∧ s i b ≤ b) ∧
    a₂ ≤ s 1 b ∧
    E.claim4T1 a₁ a₂ ≤ s 0 b

end Economy

/-- State-by-state posted prices (6): price `a` in state 1 (index `0`) and `b` in state 2
(index `1`); type `v` buys in a state iff its price is at most `v`, and pays `0` otherwise. -/
noncomputable def sbsmp (a b : ℝ) : Mechanism where
  x := ![fun v => decide (a ≤ v), fun v => decide (b ≤ v)]
  t := ![fun v => if a ≤ v then a else 0, fun v => if b ≤ v then b else 0]

end MonopolyDemandUncertainty.SBSMP


