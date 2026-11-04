-- Prove2me | Definitions.Def_ReverseLogisticsNEBS_Inst
-- name    : ReverseLogisticsNEBS_Inst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:50:40.614411+00:00
-- url     : https://prove2.me/theorems/927143b0-31ae-4c1a-80fd-616e8ae5410e
-- title:
--   Installation formulation: orders, feasible sets $\mathbb X$ and $\widetilde{\mathbb X}$, transition (2), objective, reductions
-- statement:
--   In the **installation formulation** the state is the vector $x$ of on-hand inventories ($x_1$ is the net inventory, possibly negative) and a decision is a triple of orders: $X^E_j$ expedited into $j$ from $j+1$, $X^R_j$ reverse-ordered from $j$ into $j+1$, and $X_j$ regular-ordered into $j$ from $j+1$, all nonnegative.
--
--   The original feasible set $\mathbb X(x)$ of (1) requires $X^E_j \le x_{j+1} + X^E_{j+1}$ ($j \le N-1$), $X^R_1 \le [x_1 + X^E_1]^+$, $X^R_j \le x_j + X^E_j - X^E_{j-1}$ ($j \ge 2$), and $X_j \le x_{j+1} - X^R_{j+1} + X^E_{j+1} - X^E_j$ ($j \le N-1$). The relaxed set $\widetilde{\mathbb X}(x)$ of p.33 adds $+X^R_j$ to the last bound.
--
--   The transition (2) is $x_{1,t+1} = x_1 - X^R_1 + X^E_1 + X_1 - D$ and $x_{j,t+1} = x_j - X^R_j + X^R_{j-1} + X^E_j - X^E_{j-1} + X_j - X_{j-1}$ for $j \ge 2$.
--
--   With continuation $G$, the installation objective of the relaxed problem is
--   $$
--   \widetilde V_t = \sum_{j=1}^N \big[(k^E_j + h_j)X^E_j + (k^R_j - h_j)X^R_j + k_j X_j + H_j x_j\big] + \gamma_t(\omega, x_1 + X^E_1 - X^R_1) + \alpha\,\mathbb E_\omega[G(\omega_{t+1}, x_{t+1})].
--   $$
--
--   A policy is **semi-unidirectional** if $X^E_j = 0$ or $X^R_j = 0$ at each $j$, and **unidirectional** if $X^E_j = X_j = 0$ or $X^R_j = 0$ at each $j$. The **semi-unidirectional reduction** is $\widehat X^E_j = [X^E_j - X^R_j]^+$, $\widehat X^R_j = [X^R_j - X^E_j]^+$, $\widehat X_j = X_j$; the **unidirectional reduction** of $\widehat X$ is $\widetilde X^E_j = \widehat X^E_j$, $\widetilde X^R_j = [\widehat X^R_j - \widehat X_j]^+$, $\widetilde X_j = [\widehat X_j - \widehat X^R_j]^+$.
--
--   **Formalization Note** The objective uses the coefficient $k_j$ of $X_j$ from the model's one-period cost (4), p.11, from which the echelon cost (5) and (8) follow. The appendix display (29) prints $(k_{jt} + h_{jt})X_{jt}$ instead, which does not match (4)–(5). Order quantities are nonnegative, including $X^E_N$ and $X_N$, for which (1) lists no interval.
-- source:
--   Angelus–Özer, When Variability Trumps Volatility: Optimal Control and Value of Reverse Logistics in Supply Chains with Multiple Flows of Product, SSRN 3508009 (Dec. 21, 2019), p.8 (decisions), (1)–(2) p.9, (4) p.11, (28)–(29) and 𝕏̃ p.33, semi-unidirectional p.33, Propositions 1–2 pp.33–35

import Mathlib
import Definitions.Def_ReverseLogisticsNEBS_Model

open MeasureTheory ProbabilityTheory

namespace ReverseLogisticsNEBS

/-- **Installation decisions** of one period (p.8): `X^E_j` units expedited into location `j`
from location `j + 1`, `X^R_j` units reverse-ordered into location `j + 1` from location `j`,
and `X_j` units regular-ordered into location `j` from location `j + 1`.

The module also defines the feasible sets `𝕏(x)` of (1), p.9, and `𝕏̃(x)` of p.33, the state
transition (2), p.9, the installation objective of the relaxed problem ((28)–(29), p.33, with the
one-period cost of (4)), optimality, and (semi-)unidirectionality (p.13, p.33).

**Formalization Note.** Locations are `Fin N` (index `j` = location `j + 1`); "`i` is directly
upstream of `j`" is `i.val = j.val + 1`. The order quantities are numbers of units, so all of
them are nonnegative, including `X^E_N` and `X_N`, for which (1) lists no interval. -/
structure Inst (N : ℕ) where
  /-- Expedited orders `X^E_j`. -/
  XE : Fin N → ℝ
  /-- Reverse orders `X^R_j`. -/
  XR : Fin N → ℝ
  /-- Regular orders `X_j`. -/
  X : Fin N → ℝ

namespace Inst

variable {N : ℕ}

/-- The value at the next location downstream, `v_{j−1}`, or `0` at location `1`. -/
def below (v : Fin N → ℝ) (j : Fin N) : ℝ :=
  if h : 0 < j.val then v ⟨j.val - 1, by omega⟩ else 0

/-- The **feasible sets** of the installation formulation at the inventory state `x`:
`relaxed = false` gives `𝕏(x)` of (1), p.9, and `relaxed = true` gives `𝕏̃(x)` of p.33:
`X^E_j ∈ [0, x_{j+1} + X^E_{j+1}]` (`j ≤ N − 1`), `X^R_1 ∈ [0, [x_1 + X^E_1]^+]`,
`X^R_j ∈ [0, x_j + X^E_j − X^E_{j−1}]` (`j ≥ 2`), and
`X_j ∈ [0, x_{j+1} − X^R_{j+1} + X^E_{j+1} − X^E_j]` (`𝕏`) or
`X_j ∈ [0, x_{j+1} − X^R_{j+1} + X^R_j + X^E_{j+1} − X^E_j]` (`𝕏̃`) for `j ≤ N − 1`; all order
quantities nonnegative. -/
def Feas (relaxed : Bool) (x : Fin N → ℝ) (a : Inst N) : Prop :=
  (∀ j, 0 ≤ a.XE j) ∧ (∀ j, 0 ≤ a.XR j) ∧ (∀ j, 0 ≤ a.X j) ∧
  (∀ i j : Fin N, i.val = j.val + 1 → a.XE j ≤ x i + a.XE i) ∧
  (∀ j : Fin N, j.val = 0 → a.XR j ≤ max (x j + a.XE j) 0) ∧
  (∀ i j : Fin N, i.val = j.val + 1 → a.XR i ≤ x i + a.XE i - a.XE j) ∧
  (∀ i j : Fin N, i.val = j.val + 1 →
    a.X j ≤ x i - a.XR i + (if relaxed then a.XR j else 0) + a.XE i - a.XE j)

/-- The **state transition (2)** (p.9): with demand `d`,
`x_{1,t+1} = x_1 − X^R_1 + X^E_1 + X_1 − d` and
`x_{j,t+1} = x_j − X^R_j + X^R_{j−1} + X^E_j − X^E_{j−1} + X_j − X_{j−1}` for `j ≥ 2`. -/
def next (x : Fin N → ℝ) (a : Inst N) (d : ℝ) : Fin N → ℝ := fun j =>
  x j - a.XR j + below a.XR j + a.XE j - below a.XE j + a.X j - below a.X j -
    (if j.val = 0 then d else 0)

/-- **Semi-unidirectional** (p.33): at each location, `X^E_j = 0` or `X^R_j = 0`. -/
def SemiUnidir (a : Inst N) : Prop := ∀ j, a.XE j = 0 ∨ a.XR j = 0

/-- **Unidirectional** (p.13): at each location, `X^E_j = X_j = 0` or `X^R_j = 0`. -/
def Unidir (a : Inst N) : Prop := ∀ j, (a.XE j = 0 ∧ a.X j = 0) ∨ a.XR j = 0

/-- The **semi-unidirectional reduction** of Proposition 1 (p.33):
`X̂^E_j = [X^E_j − X^R_j]^+`, `X̂^R_j = [X^R_j − X^E_j]^+`, `X̂_j = X_j`. -/
def semiReduce (a : Inst N) : Inst N where
  XE := fun j => max (a.XE j - a.XR j) 0
  XR := fun j => max (a.XR j - a.XE j) 0
  X := a.X

/-- The **unidirectional reduction** of Proposition 2 (p.35), applied to a semi-unidirectional
reduction `â`: `X̃^E_j = X̂^E_j`, `X̃^R_j = [X̂^R_j − X̂_j]^+`, `X̃_j = [X̂_j − X̂^R_j]^+`. -/
def uniReduce (a : Inst N) : Inst N where
  XE := a.XE
  XR := fun j => max (a.XR j - a.X j) 0
  X := fun j => max (a.X j - a.XR j) 0

end Inst

namespace Model

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : Model N Ω)

/-- The continuation `G(ω_{t+1}, x_{t+1})` of the installation objective is integrable under
the period-`t` law `κ t ω`. -/
def InstContIntegrable (t : ℕ) (G : Ω → (Fin N → ℝ) → ℝ) (ω : Ω) (x : Fin N → ℝ)
    (a : Inst N) : Prop :=
  Integrable (fun z : ℝ × Ω => G z.2 (Inst.next x a z.1)) (M.κ t ω)

/-- The **installation objective** `Ṽ_t(ω, x, X^E, X^R, X)` of the relaxed problem, (29), p.33,
with continuation `G = F̃_{t+1}`:
`Σ_j [(k^E_j + h_j) X^E_j + (k^R_j − h_j) X^R_j + k_j X_j + H_j x_j]
 + γ_t(ω, x_1 + X^E_1 − X^R_1) + α E_ω[G(ω_{t+1}, x_{t+1})]`.

**Formalization Note.** The coefficient of `X_j` is `k_j`, as in the one-period cost (4) on p.11
(and the cost on p.10), which (5) and (8) rewrite in echelon variables. The appendix display (29)
prints `(k_jt + h_jt) X_jt`, which does not match (4)–(5); see the items of Propositions 1–2. -/
noncomputable def instObj (t : ℕ) (G : Ω → (Fin N → ℝ) → ℝ) (ω : Ω) (x : Fin N → ℝ)
    (a : Inst N) : ℝ :=
  ∑ j, ((M.kE j + M.h j) * a.XE j + (M.kR j - M.h j) * a.XR j + M.k j * a.X j + M.H j * x j) +
    M.gamma t ω (firstLoc x + firstLoc a.XE - firstLoc a.XR) +
    M.α * ∫ z, G z.2 (Inst.next x a z.1) ∂(M.κ t ω)

/-- `a` is an **optimal policy** of the relaxed problem (28) in period `t` at `(ω, x)`: feasible
in `𝕏̃(x)`, with a finite expected continuation, and no feasible policy with a finite expected
continuation has a smaller objective. -/
def IsOptimalInst (t : ℕ) (G : Ω → (Fin N → ℝ) → ℝ) (ω : Ω) (x : Fin N → ℝ) (a : Inst N) :
    Prop :=
  Inst.Feas true x a ∧ M.InstContIntegrable t G ω x a ∧
    ∀ a', Inst.Feas true x a' → M.InstContIntegrable t G ω x a' →
      M.instObj t G ω x a ≤ M.instObj t G ω x a'

end Model

end ReverseLogisticsNEBS


