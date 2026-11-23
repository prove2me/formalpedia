-- Prove2me | Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_Separated
-- name    : ArapostathisAC_VanishingDiscount_Supplement_Separated
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:04:02.103855+00:00
-- url     : https://prove2.me/theorems/446e49af-b0f1-49c8-94f9-d27b3baf1405
-- title:
--   The countable partially observable model under Assumption 7.1, the belief simplex $\Delta$, (7.10)–(7.14), nonrandomized separated policies and the (DC′) cost and value
-- statement:
--   A partially observable model with finite or countably infinite hidden state space $X$ and observation space $Y$, action space $A$ with $U(y)=A$, and, under Assumption 7.1, transition law $P(x,y\mid x',a)$ and cost $c(x,a)\ge0$ that do not depend on the current observation and are continuous in $a$.
--
--   1. The belief simplex $\Delta=\{\psi\in[0,1]^X:\sum_x\psi(x)=1\}$ (7.9).
--   2. (7.10) $q(x,y\mid\psi,a)=\sum_{x'}P(x,y\mid x',a)\psi(x')$; (7.11) $V(y,\psi,a)=\sum_xq(x,y\mid\psi,a)$; (7.12) $T(y,\psi,a)=q(\cdot,y\mid\psi,a)/V(y,\psi,a)$ if $V(y,\psi,a)\ne0$; (7.14) $\tilde c(\psi,a)=\sum_xc(x,a)\psi(x)$.
--   3. A **nonrandomized separated policy** chooses $A_t$ as a function of the belief history $(\Psi_0,A_0,\dots,\Psi_{t-1},A_{t-1})$ and of $\Psi_t$, where $\Psi_0=\psi$ and $\Psi_{s}=T(Y_s,\Psi_{s-1},A_{s-1})$. Its (DC′) cost is
--   $$J_\beta(\psi,\pi)=E^\pi_\psi\Big[\sum_{t\ge0}\beta^t\tilde c(\Psi_t,A_t)\Big]=\sum_{t\ge0}\beta^t\sum_{y_1,\dots,y_t}\Big(\prod_{s=1}^tV(y_s,\Psi_{s-1},A_{s-1})\Big)\tilde c(\Psi_t,A_t),$$
--   and $J^*_\beta(\psi)$ is its infimum over nonrandomized separated policies.
--
--   **Formalization Note** Values are in $[0,\infty]$. Where $V(y,\psi,a)=0$ the paper sets $T=0$, which is not a belief; here $T=\psi$, and the choice is irrelevant because $T$ enters only with the weight $V=0$. Separated policies are arbitrary functions of the belief history: from a fixed prior only countably many belief histories occur, so every such policy agrees on them with a Borel one. The infimum over nonrandomized policies is taken as the (DC′) value; for a discounted problem with nonnegative cost, randomization does not lower it.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), pp. 324–328, §7.1–§7.2.2, Assumption 7.1, (7.9)–(7.14), (DC′)

import Mathlib

open Filter Topology
open scoped ENNReal

namespace ArapostathisAC.VanishingDiscount.Supplement

/-- The partially observable model of §7.2.2 (pp. 325–327) under Assumption 7.1: hidden states
`X` and observations `Y` are finite or countably infinite, `A` is the action space and
`U(y) = A`. The transition law `P(x, y | x', a)` and the cost `c(x, a)` do not depend on the
current observation (Assumption 7.1) and are continuous in `a`; costs are nonnegative
(Assumption 2.1). -/
structure POModel (X Y A : Type*) [TopologicalSpace A] where
  /-- `P(x, y | x', a)`: probability of the next pair `(x, y)` given hidden state `x'` and action
  `a` -/
  P : X → A → X × Y → ℝ≥0∞
  P_sum : ∀ x' a, ∑' p, P x' a p = 1
  P_cont : ∀ x' p, Continuous fun a => P x' a p
  /-- the one-stage cost `c(x, a)` -/
  c : X → A → ℝ
  c_nonneg : ∀ x a, 0 ≤ c x a
  c_cont : ∀ x, Continuous (c x)

/-- The belief simplex `Δ = {ψ ∈ [0, 1]^X : ∑_x ψ(x) = 1}` of (7.9) (p. 327), with values in
`[0, ∞]` (they lie in `[0, 1]` because they sum to `1`). -/
def Belief (X : Type*) : Type _ := {ψ : X → ℝ≥0∞ // ∑' x, ψ x = 1}

variable {X Y A : Type*} [TopologicalSpace A]

/-- (7.10): `q(x, y | ψ, a) = ∑_{x'} P(x, y | x', a) ψ(x')`. -/
noncomputable def qJoint (M : POModel X Y A) (ψ : Belief X) (a : A) (p : X × Y) : ℝ≥0∞ :=
  ∑' x', M.P x' a p * ψ.1 x'

/-- (7.11): `V(y, ψ, a) = ∑_x q(x, y | ψ, a)`, the probability of observing `y`. -/
noncomputable def obsProb (M : POModel X Y A) (y : Y) (ψ : Belief X) (a : A) : ℝ≥0∞ :=
  ∑' x, qJoint M ψ a (x, y)

/-- (7.12): the filter `T(y, ψ, a) = q(·, y | ψ, a) / V(y, ψ, a)` when `V(y, ψ, a) ≠ 0`. When
`V(y, ψ, a) = 0` the paper sets `T = 0`; here `T = ψ` (a belief), which changes nothing since
`T` only enters with the weight `V(y, ψ, a) = 0`. (`V ≤ 1` always, so the case `V = ∞` does not
occur.) -/
noncomputable def filterT (M : POModel X Y A) (y : Y) (ψ : Belief X) (a : A) : Belief X :=
  if h : obsProb M y ψ a ≠ 0 ∧ obsProb M y ψ a ≠ ⊤ then
    ⟨fun x => qJoint M ψ a (x, y) / obsProb M y ψ a, by
      simp only [div_eq_mul_inv]
      rw [ENNReal.tsum_mul_right]
      exact ENNReal.mul_inv_cancel h.1 h.2⟩
  else ψ

/-- (7.14): the separated one-stage cost `c̃(ψ, a) = ∑_x c(x, a) ψ(x)`, in `[0, ∞]`. -/
noncomputable def costTilde (M : POModel X Y A) (ψ : Belief X) (a : A) : ℝ≥0∞ :=
  ∑' x, ψ.1 x * ENNReal.ofReal (M.c x a)

/-- A nonrandomized separated admissible policy (p. 328): the action at epoch `t` is a function of
the belief history `(Ψ₀, A₀, …, Ψ_{t-1}, A_{t-1})` (most recent pair first) and of the current
belief `Ψ_t`. -/
def SepPolicy (X A : Type*) : Type _ := List (Belief X × A) → Belief X → A

/-- The separated process along an observation record `y_t, …, y_1` (most recent first) under the
policy `π` from the prior `ψ₀`: the belief history, the current belief `Ψ_t`
(`Ψ_s = T(y_s, Ψ_{s-1}, A_{s-1})`), and the probability `∏_{s ≤ t} V(y_s, Ψ_{s-1}, A_{s-1})` of the
record. -/
noncomputable def runSep (M : POModel X Y A) (π : SepPolicy X A) (ψ₀ : Belief X) :
    List Y → List (Belief X × A) × Belief X × ℝ≥0∞
  | [] => ([], ψ₀, 1)
  | y :: ys =>
    let r := runSep M π ψ₀ ys
    let a := π r.1 r.2.1
    ((r.2.1, a) :: r.1, filterT M y r.2.1 a, r.2.2 * obsProb M y r.2.1 a)

/-- The (DC′) cost `J_β(ψ, π) = E^π_ψ [∑_t β^t c̃(Ψ_t, A_t)]` (p. 328) of a nonrandomized
separated policy, in `[0, ∞]`: the expectation is the sum over observation records of length `t`
weighted by their probabilities. -/
noncomputable def sepDiscCost (M : POModel X Y A) (π : SepPolicy X A) (β : ℝ) (ψ : Belief X) :
    ℝ≥0∞ :=
  ∑' t : ℕ, ∑' ys : {l : List Y // l.length = t},
    ENNReal.ofReal (β ^ t) * ((runSep M π ψ ys.1).2.2 *
      costTilde M (runSep M π ψ ys.1).2.1 (π (runSep M π ψ ys.1).1 (runSep M π ψ ys.1).2.1))

/-- The (DC′) value `J*_β(ψ) = inf_π J_β(ψ, π)` over nonrandomized separated policies. -/
noncomputable def sepDiscValue (M : POModel X Y A) (β : ℝ) (ψ : Belief X) : ℝ≥0∞ :=
  ⨅ π : SepPolicy X A, sepDiscCost M π β ψ

/-- The term minimized in (7.15): `c̃(ψ, a) + β ∑_y V(y, ψ, a) J*_β(T(y, ψ, a))`. -/
noncomputable def dcoeTerm (M : POModel X Y A) (β : ℝ) (ψ : Belief X) (a : A) : ℝ≥0∞ :=
  costTilde M ψ a +
    ENNReal.ofReal β * ∑' y, obsProb M y ψ a * sepDiscValue M β (filterT M y ψ a)

end ArapostathisAC.VanishingDiscount.Supplement


