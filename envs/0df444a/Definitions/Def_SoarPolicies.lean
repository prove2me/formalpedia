-- Prove2me | Definitions.Def_SoarPolicies
-- name    : SoarPolicies
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-22T18:57:21.996622+00:00
-- url     : https://prove2.me/theorems/f3936501-f76c-473c-a84e-98fc9e7e9025
-- title:
--   Dynamic matching policies, their regret, and the Greedy policy
-- statement:
--   This module formalizes the class $\Pi$ of dynamic matching policies of Section 2, against which the lower bounds of Section 4 are stated, and the Greedy policy of Section 3.1.
--
--   **Dynamic matching policies.** The platform observes the initial endowment $Y_1, \dots, Y_n$ of supply units and the demand units $X_1, X_2, \dots$ as they arrive, and upon the arrival of $X_t$ must immediately and irrevocably assign it an available supply unit, possibly at random. The paper writes a policy as a collection $\pi = (\pi_t)_{1 \le t \le n}$ with $\pi_t(X_t, H_t)$ a distribution over the indices of the remaining supply units, $H_t$ being the history up to epoch $t$. Over the whole horizon the realized assignment is a permutation $\tau \in S_n$ (demand $t$ receives supply $\tau(t)$), and it is a function of the supply features $y \in \mathcal Y^n$, the demand sequence $x \in \mathcal X^n$ and an auxiliary random seed $\omega$ carrying all the randomization. A **dynamic matching policy** is such a rule $\tau(y, x, \omega)$ that is measurable and **non-anticipative**: for every $t$, the coordinate $\tau(y, x, \omega)(t)$ depends on the demand sequence only through $x_1, \dots, x_t$,
--   $$x_s = x'_s \ \text{for all } s \le t \quad\Longrightarrow\quad \tau(y, x, \omega)(t) = \tau(y, x', \omega)(t).$$
--
--   **Value and regret.** With supply i.i.d. $Q$, demand i.i.d. $P$ and the seed drawn from a law $\mu$, independently, the **average expected match value** of the policy (equation (1)) is
--   $$U_n(\pi) = \frac{1}{n}\,\mathbb E\Bigl[\sum_{t=1}^{n} \varphi\bigl(X_t, Y_{\tau(Y, X, \omega)(t)}\bigr)\Bigr],$$
--   and its **regret** (equation (3)) is $\mathrm{Reg}_n(\pi) = U_\infty - U_n(\pi)$.
--
--   **Greedy.** A policy is **Greedy** for $\varphi$ (Section 3.1) if each arriving demand unit is matched to a myopically optimal supply unit: for every $t$, the unit $\tau(t)$ maximizes $\varphi(x_t, y_i)$ over the indices $i$ not assigned to an earlier demand unit $s < t$. Ties may be broken in any way.
--
--   **Role.** The lower bounds of Theorem 2, Proposition 2 and Corollary 3 are statements about $\inf_{\pi \in \Pi} \mathrm{Reg}_n(\pi)$, so they need the policy class; Proposition 1 is a statement about every Greedy policy.
--
--   **Formalization Note** A policy is represented by its realized assignment as a permutation-valued measurable function of $(y, x, \omega)$ with non-anticipative coordinates; every sequence of choices of an available unit yields such a permutation and conversely, and any randomized history-dependent policy is realized by such a rule on a suitable seed space, so the class coincides with the paper's $\Pi$. The seed space $\Omega$ and its law $\mu$ are free parameters; theorems quantify over all of them. Greedy is a predicate on policies, so a statement about Greedy is a statement about every tie-breaking rule. The expectation is a Bochner integral over $Q^{\otimes n} \otimes P^{\otimes n} \otimes \mu$; the standing measurability and boundedness hypotheses make it finite. With $n = 0$ the value is the junk value $0$.
-- source:
--   Y. Chen, Y. Kanoria, A. Kumar, W. Zhang, Feature-Based Dynamic Matching, SSRN working paper 4451799 (version of 27 May 2025; extended abstract in Proc. 24th ACM Conference on Economics and Computation, EC'23), https://ssrn.com/abstract=4451799, Section 2 (dynamic matching policies, equations (1) and (3)) and Section 3.1 (the Greedy policy)

import Mathlib
import Definitions.Def_SoarModel

/-!
# Dynamic matching policies and the Greedy policy

Chen, Kanoria, Kumar, Zhang, *Feature-Based Dynamic Matching*, Section 2 (dynamic matching
policies and eq. (1)) and Section 3.1 (the Greedy policy).

A dynamic matching policy observes the initial endowment of supply units and the demand units as
they arrive, may randomize through an auxiliary seed, and assigns to each arriving demand unit a
still-available supply unit; its decision at time `t` may depend on the demand units only through
the first `t` of them (non-anticipativity).  The realized assignment over the whole horizon is a
permutation, so a policy is recorded as a permutation-valued rule whose `t`-th coordinate is
non-anticipative.
-/

open MeasureTheory
open scoped BigOperators

/-- A (possibly randomized) dynamic matching policy for `n` supply units: `assign y x ω` is the
realized assignment (demand `t` is matched to supply `assign y x ω t`) given the supply features
`y`, the demand sequence `x` and an auxiliary random seed `ω`; the assignment of demand `t` may
depend on the demand sequence only through `x 0, …, x t` (non-anticipativity), and the rule is
measurable. -/
structure SoarDynamicPolicy (X Y Ω : Type*) [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Ω] (n : ℕ) where
  /-- The realized assignment. -/
  assign : (Fin n → Y) → (Fin n → X) → Ω → Equiv.Perm (Fin n)
  /-- The decision at time `t` does not look at demand units arriving after `t`. -/
  nonanticipative : ∀ (y : Fin n → Y) (x x' : Fin n → X) (ω : Ω) (t : Fin n),
    (∀ s : Fin n, s ≤ t → x s = x' s) → assign y x ω t = assign y x' ω t
  /-- The rule is a measurable function of its inputs. -/
  measurable : Measurable fun q : ((Fin n → Y) × (Fin n → X)) × Ω => assign q.1.1 q.1.2 q.2

/-- The average expected match value `U_n(π; P, Q, φ)` (eq. (1)) of a dynamic matching policy:
the supply units are i.i.d. `Q`, the demand units i.i.d. `P`, the seed has law `μ`, all
independent. -/
noncomputable def SoarPolicyValue {X Y Ω : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Ω] (P : Measure X) (Q : Measure Y) (μ : Measure Ω) [SigmaFinite P]
    [SigmaFinite Q] [SigmaFinite μ] (φ : X → Y → ℝ) {n : ℕ} (π : SoarDynamicPolicy X Y Ω n) :
    ℝ :=
  (∫ q, ∑ t, φ (q.1.2 t) (q.1.1 (π.assign q.1.1 q.1.2 q.2 t))
      ∂((Measure.pi fun _ : Fin n => Q).prod (Measure.pi fun _ : Fin n => P)).prod μ) / n

/-- The regret `Reg_n(π; P, Q, φ) = U_∞ - U_n(π)` (eq. (3)) of a dynamic matching policy. -/
noncomputable def SoarPolicyRegret {X Y Ω : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Ω] (P : Measure X) (Q : Measure Y) (μ : Measure Ω) [SigmaFinite P]
    [SigmaFinite Q] [SigmaFinite μ] (φ : X → Y → ℝ) {n : ℕ} (π : SoarDynamicPolicy X Y Ω n) :
    ℝ :=
  SoarLimit P Q φ - SoarPolicyValue P Q μ φ π

/-- The policy is Greedy for `φ` (Section 3.1): each arriving demand unit is matched to a
myopically optimal supply unit, one maximizing `φ (x t) (y i)` among the supply units `i` not
matched to an earlier demand unit; ties may be broken arbitrarily. -/
def SoarIsGreedy {X Y Ω : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω]
    (φ : X → Y → ℝ) {n : ℕ} (π : SoarDynamicPolicy X Y Ω n) : Prop :=
  ∀ (y : Fin n → Y) (x : Fin n → X) (ω : Ω) (t i : Fin n),
    (∀ s : Fin n, s < t → π.assign y x ω s ≠ i) →
      φ (x t) (y i) ≤ φ (x t) (y (π.assign y x ω t))


