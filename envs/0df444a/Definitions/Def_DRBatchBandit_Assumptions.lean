-- Prove2me | Definitions.Def_DRBatchBandit_Assumptions
-- name    : DRBatchBandit_Assumptions
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:24:09.918463+00:00
-- url     : https://prove2.me/theorems/5d3b89db-997f-41fc-a893-c38b46072c14
-- title:
--   Assumptions 1.2, 1.3, 2.1, 2.2 and the measurability convention for $\Pi$
-- statement:
--   The standing assumptions of Theorem 2 (§2.1, p.9), for a model with context law $P_X$, conditional reward law $\mathbf P_0(Y\in\cdot\mid X=x)$ and logging policy $\pi_0(a\mid x)$.
--
--   1. **Overlap** (Assumption 1.2): there is $\eta>0$ with $\pi_0(a\mid x)\ge\eta$ for all $(x,a)$.
--   2. **Bounded reward support** (Assumption 1.3): $0\le Y(a^i)\le M$ for $i=1,\dots,d$, $\mathbf P_0$-almost surely.
--   3. **Continuous case** (Assumption 2.1): for every $i$ and every $x\in\mathcal X$, $Y(a^i)\mid X=x$ has a conditional density $f_i(y_i\mid x)\ge\underline b>0$ on $[0,M]$.
--   4. **Discrete case** (Assumption 2.2): every $Y(a^i)$ is supported on a finite set $\mathbb D$ with $|\mathbb D|>1$, and $\mathbf P_0(Y(a^i)=v\mid X)\ge\underline b>0$ almost surely, for every $v\in\mathbb D$.
--   5. **Measurability convention** (not printed): every policy in $\Pi$ is measurable, and for every $m$ and every action pattern $s\in\{a^1,\dots,a^d\}^m$ the set of $m$-point sequences on which some policy of $\Pi$ realizes $s$ is measurable.
--
--   Assumption 1.1 (unconfoundedness) is built into the joint law of the published model. Item 5 is the convention under which "with probability at least $1-\varepsilon$" in Theorem 2, and the cited concentration inequality, refer to events.
--
--   **Formalization Note** $\pi_0(a\mid x)$ is `M.e x a`, the paper's $M$ is `Mrew`. Assumption 2.1 is encoded, equivalently by the Radon–Nikodym theorem, as: the law of the $i$-th coordinate under `M.κY x` is absolutely continuous with respect to Lebesgue measure and gives every measurable $s\subseteq[0,M]$ mass at least $\underline b\,\lambda(s)$. In Assumption 2.2 the support condition is $\mathbf P_0$-almost sure and the point-mass bound holds for $P_X$-almost every $x$, as printed.
-- source:
--   Si, Zhang, Zhou & Blanchet, Distributionally Robust Batch Contextual Bandits, arXiv:2006.05630v7, §2.1 p.9 (Assumption 1.2, 1.3, Assumption 2.1, 2.2). PDF sha256 ac485985feb75d33b603f06f5a5d93c52077877db7be11de3d71107c7c374b02

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Setting
import Definitions.Def_DRBatchBandit_RobustValue

open MeasureTheory ProbabilityTheory

namespace DRBatchBandit

open OfflinePolicyLearning.Regret

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

/-- Assumption 1.2, overlap (arXiv:2006.05630v7, p.9): there is `η > 0` with
`π₀(a | x) ≥ η` for all `(x, a) ∈ 𝒳 × 𝒜`.

**Formalization Note.** `π₀(a | x)` is `M.e x a = (M.κA x {a}).toReal`. Assumption 1.1
(unconfoundedness) is built into `Model.law`. -/
def Overlap (M : Model X d) (η : ℝ) : Prop :=
  0 < η ∧ ∀ x a, η ≤ M.e x a

/-- Assumption 1.3, bounded reward support (arXiv:2006.05630v7, p.9):
`0 ≤ Y(aⁱ) ≤ M` for `i = 1, …, d`, almost surely under `P₀`.

**Formalization Note.** The paper's bound `M` is called `Mrew` here. -/
def BoundedReward (M : Model X d) (Mrew : ℝ) : Prop :=
  ∀ᵐ z ∂(P0 M), ∀ a, 0 ≤ z.2 a ∧ z.2 a ≤ Mrew

/-- Assumption 2.1, continuous case (arXiv:2006.05630v7, p.9): for every action `i` and every
context `x`, `Y(aⁱ) | X = x` has a conditional density `fᵢ(yᵢ | x) ≥ b > 0` on `[0, M]`.

**Formalization Note.** The conditional law of `Y(aⁱ)` given `X = x` is the image of `M.κY x`
under the `i`-th coordinate. "Has a density that is `≥ b` on `[0, M]`" is encoded, equivalently
by the Radon–Nikodym theorem, as absolute continuity with respect to Lebesgue measure together
with `b · λ(s) ≤ P(Y(aⁱ) ∈ s | X = x)` for every measurable `s ⊆ [0, M]`. -/
def DensityLB (M : Model X d) (Mrew b : ℝ) : Prop :=
  0 < b ∧ ∀ (x : X) (i : Fin d),
    (M.κY x).map (fun y => y i) ≪ volume ∧
    ∀ s ⊆ Set.Icc 0 Mrew, MeasurableSet s →
      ENNReal.ofReal b * volume s ≤ (M.κY x).map (fun y => y i) s

/-- Assumption 2.2, discrete case (arXiv:2006.05630v7, p.9): every `Y(aⁱ)` is supported on a
finite set `𝔻` with more than one element, and `P₀(Y(aⁱ) = v | X) ≥ b > 0` almost surely for
every `v ∈ 𝔻`.

**Formalization Note.** Support is `P₀(Y(aⁱ) ∈ 𝔻) = 1`; the conditional probability is
`M.κY x {y | y i = v}`, and the lower bound holds for `P_X`-almost every `x`, as printed. -/
def PointMassLB (M : Model X d) (D : Finset ℝ) (b : ℝ) : Prop :=
  0 < b ∧ 1 < D.card ∧ (∀ᵐ z ∂(P0 M), ∀ i, z.2 i ∈ D) ∧
    ∀ᵐ x ∂M.PX, ∀ i, ∀ v ∈ D, ENNReal.ofReal b ≤ M.κY x {y | y i = v}

/-- Measurability convention for the policy class `Π` (not stated in arXiv:2006.05630v7; it is
the standing convention under which "with probability at least `1 − ε`" in Theorem 2 and the
cited Theorem A7 refer to events): every policy is measurable, and for every `m` and every
action pattern `s`, the set of `m`-point sequences on which some policy of `Π` realizes `s` is
measurable. -/
def MeasurablePolicyClass (Pol : Set (X → Fin d)) : Prop :=
  (∀ π ∈ Pol, Measurable π) ∧
    ∀ (m : ℕ) (s : Fin m → Fin d), MeasurableSet {x : Fin m → X | ∃ π ∈ Pol, ∀ i, π (x i) = s i}

end DRBatchBandit


