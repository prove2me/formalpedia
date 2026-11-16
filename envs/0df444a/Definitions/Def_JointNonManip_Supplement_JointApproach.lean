-- Prove2me | Definitions.Def_JointNonManip_Supplement_JointApproach
-- name    : JointNonManip_Supplement_JointApproach
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:28:17.829102+00:00
-- url     : https://prove2.me/theorems/23604d85-c027-4427-80c1-f9fc1990976a
-- title:
--   Joint approachability (Definition 5.2) and joint halfspace satisfiability (Definition 5.5) of a target set $S\subseteq\mathbb R^d$
-- statement:
--   The vector-payoff setting of §5 of Collina, Fullerton, Liu & Weinberg. A finite game has an optimizer with action set $A_0$ and independent learners $i\in L$ with action sets $A_i$; a joint action is $a=(c,a_L)\in A=A_0\times A_L$. A **vector statistic** is a map $g:A\to\mathbb R^d$. It is extended multilinearly: for $y\in\Delta(A_0)$ and a product distribution $q=\bigotimes_{i\in L}x_i$ with $x_i\in\Delta(A_i)$,
--
--   $$g(y,q)=\sum_{c\in A_0}\sum_{a_L\in A_L} y(c)\,q(a_L)\,g(c,a_L).$$
--
--   For a set $S\subseteq\mathbb R^d$ write $h_S(U)=\max_{s\in S}\langle U,s\rangle$.
--
--   1. $S$ is **jointly halfspace satisfiable** if for every direction $U\in\mathbb R^d$ there are lotteries $x_i\in\Delta(A_i)$ such that, with $q=\bigotimes_i x_i$,
--   $$\langle U,g(y,q)\rangle\le h_S(U)\qquad\text{for every }y\in\Delta(A_0).$$
--   2. A **profile of independent learning algorithms** gives each learner $i$, in every round $t$, a lottery $x_i^{(t)}\in\Delta(A_i)$ that is a function of the realized past play $a^{(1)},\dots,a^{(t-1)}$; the learners sample independently, so their joint mixed action is $\bigotimes_i x_i^{(t)}$. An **optimizer policy** chooses $y^{(t)}\in\Delta(A_0)$ as a function of the realized past. In round $t$, $c^{(t)}\sim y^{(t)}$ and then $a_L^{(t)}\sim\bigotimes_i x_i^{(t)}$.
--   3. $S$ is **jointly approachable** if some profile of independent learning algorithms ensures, against every optimizer policy $\pi$,
--   $$\lim_{T\to\infty}\mathbb E\big[\operatorname{dist}(\bar g_T,S)\big]=0,\qquad \bar g_T=\frac1T\sum_{t=1}^T g(a^{(t)}),$$
--   where $\operatorname{dist}$ is the Euclidean distance and $\bar g_T$ averages the realized statistic.
--
--   These are the two sides of Theorem 5.7, the multi-learner analogue of Blackwell's characterization of approachable convex sets without shared randomness.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` and $\operatorname{dist}$ is `Metric.infDist`. $h_S(U)$ is the real supremum of $\{\langle U,s\rangle:s\in S\}$, which is the maximum for nonempty compact $S$ (the published `OnlineConvexOpt.Blackwell.SupportFunction` is not reused: as a double supremum `⨆ x ∈ S` in $\mathbb R$ it equals $\max(\sup_S,0)$). Profiles and policies are anytime (one object for all horizons, as in Definition 5.2); expectations are finite sums over trajectories of length $T$. `IsPublicHistory` marks the profiles whose lotteries depend only on the optimizer's past actions, the class of the paper's Algorithm 2.
-- source:
--   Collina, Fullerton, Liu & Weinberg, Non-manipulability and Approachability Beyond Two-Player Games (manuscript, STOC 2027 submission), Definitions 5.2 and 5.5, pp.12–13; Q and g(c, q), Appendix A.9, p.30

import Mathlib
import Definitions.Def_JointNonManip_RepeatedPlay

namespace JointNonManip.Supplement

/-!
# Joint approachability and joint halfspace satisfiability

Collina, Fullerton, Liu & Weinberg, *Non-manipulability and Approachability Beyond Two-Player
Games* (manuscript, STOC 2027 submission), §5, pp.12–13 (Definitions 5.2 and 5.5), and
Appendix A.9, p.30 (the set `Q` of product distributions and the conditional payoff `g(c, q)`).

A **vector statistic** `g : A → ℝ^d` assigns a vector to every joint action
`a = (c, a_L) ∈ A₀ × A_L`. It is extended multilinearly to mixed actions: for `y ∈ ∆(A₀)` and a
product distribution `q = ⊗ᵢ xᵢ` on `A_L`, `g(y, q) = ∑_{c, a_L} y(c) q(a_L) g(c, a_L)`.

**Formalization Note**
* `ℝ^d` is `EuclideanSpace ℝ (Fin d)`; `dist(·, S)` is the Euclidean `Metric.infDist`.
* `h_S(U) = max_{s ∈ S} ⟨U, s⟩` (p.30) is the real `sSup` of the image of `S` under
  `s ↦ ⟨U, s⟩`; it is the maximum when `S` is nonempty and compact, which every statement using
  it assumes. (The published `OnlineConvexOpt.Blackwell.SupportFunction` is not reused: it is the
  double supremum `⨆ x ∈ S`, which in `ℝ` equals `max(sup_S, 0)` for `S ≠ univ`.)
* Definition 5.2 takes one learner profile and lets `T → ∞`, so profiles and optimizer policies
  here are **anytime** (not indexed by the horizon). A learner profile (`IndepProfile`) gives each
  learner a lottery in round `t` as a function of the whole realized past (all optimizer and
  learner actions of rounds `< t`); the learners sample independently, so the joint mixed action
  is the product `⊗ᵢ xᵢ(t)` (no shared randomness). This is the largest class of independent
  learners; the paper's Algorithm 2 uses only the public optimizer history and lies in it.
* An optimizer policy (`AnytimePolicy`) chooses a lottery on `A₀` in round `t` as a function of
  the whole realized past. The learners' current product distribution is a function of that past
  and of the (fixed) profile, so the optimizer "observes" it (p.30).
* `E[dist(ḡ_T, S)]` is the finite sum over trajectories `ω : Fin T → A`, weighted by the law in
  which, in each round, `c(t) ∼ y(t)` and then the learners draw `a_L(t) ∼ ⊗ᵢ xᵢ(t)`
  independently. `ḡ_T = (1/T) ∑ₜ g(a(t))` is the average of the **realized** statistic.
-/

open Finset
open scoped InnerProductSpace

variable {A0 : Type} [Fintype A0] [DecidableEq A0]
variable {L : Type} [Fintype L] [DecidableEq L]
variable {Act : L → Type} [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]

/-- The multilinear extension `g(y, q) = ∑_{c ∈ A₀} ∑_{a_L ∈ A_L} y(c) q(a_L) g(c, a_L)` of a
vector statistic (p.13; `g(c, q) = g(e_c, q)`, p.30). -/
noncomputable def gMix {d : ℕ} (g : A0 × ((i : L) → Act i) → EuclideanSpace ℝ (Fin d))
    (y : A0 → ℝ) (q : ((i : L) → Act i) → ℝ) : EuclideanSpace ℝ (Fin d) :=
  ∑ c, ∑ a, (y c * q a) • g (c, a)

/-- The support value `h_S(U) = max_{s ∈ S} ⟨U, s⟩` (p.30), as the real supremum of
`{⟨U, s⟩ : s ∈ S}` (the maximum for nonempty compact `S`). -/
noncomputable def supportVal {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (U : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sSup ((fun s => ⟪U, s⟫_ℝ) '' S)

/-- **Joint halfspace satisfiability** (Definition 5.5, p.13): for every direction `U ∈ ℝ^d`
there is a product distribution `q = ⊗ᵢ xᵢ`, `xᵢ ∈ ∆(Aᵢ)`, such that for every `y ∈ ∆(A₀)`,
`⟨U, g(y, q)⟩ ≤ max_{s ∈ S} ⟨U, s⟩`. -/
def IsJointlyHalfspaceSatisfiable {d : ℕ}
    (g : A0 × ((i : L) → Act i) → EuclideanSpace ℝ (Fin d))
    (S : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ U : EuclideanSpace ℝ (Fin d), ∃ x : (i : L) → Act i → ℝ, (∀ i, AGT.IsLottery (x i)) ∧
    ∀ y : A0 → ℝ, AGT.IsLottery y → ⟪U, gMix g y (AGT.profileProb x)⟫_ℝ ≤ supportVal S U

/-- An (anytime) **profile of independent learning algorithms** (Definition 5.2, p.12): in round
`t`, after the realized past `h = (a(0), …, a(t−1))`, learner `i` plays the lottery `x t h i`;
the learners sample independently. -/
structure IndepProfile (A0 : Type) {L : Type} (Act : L → Type) [∀ i, Fintype (Act i)] where
  /-- Learner `i`'s mixed action in round `t` after the realized past `h`. -/
  x : (t : ℕ) → (Fin t → A0 × ((i : L) → Act i)) → (i : L) → Act i → ℝ
  /-- Every mixed action is a lottery. -/
  isLottery : ∀ t h i, AGT.IsLottery (x t h i)

/-- An (anytime) **optimizer policy** (Definition 5.2, p.12): in round `t`, after the realized
past `h`, the optimizer plays the lottery `y t h` on `A₀`. -/
structure AnytimePolicy (A0 : Type) {L : Type} (Act : L → Type) [Fintype A0] where
  /-- The optimizer's mixed action in round `t` after the realized past `h`. -/
  y : (t : ℕ) → (Fin t → A0 × ((i : L) → Act i)) → A0 → ℝ
  /-- Every mixed action is a lottery. -/
  isLottery : ∀ t h, AGT.IsLottery (y t h)

/-- The probability of the length-`T` trajectory `ω` when the optimizer follows `π` and the
learners follow `P`: in round `t`, `c(t) ∼ y(t)` and then `a_L(t) ∼ ⊗ᵢ xᵢ(t)` independently. -/
def approachTrajWeight (P : IndepProfile A0 Act) (π : AnytimePolicy A0 Act) {T : ℕ}
    (ω : Fin T → A0 × ((i : L) → Act i)) : ℝ :=
  ∏ t : Fin T, π.y t (histPrefix ω t) (ω t).1 *
    AGT.profileProb (P.x t (histPrefix ω t)) (ω t).2

/-- The average realized statistic `ḡ_T = (1/T) ∑_{t=1}^T g(a(t))` of a trajectory (p.12). -/
noncomputable def avgStat {d : ℕ} (g : A0 × ((i : L) → Act i) → EuclideanSpace ℝ (Fin d))
    {T : ℕ} (ω : Fin T → A0 × ((i : L) → Act i)) : EuclideanSpace ℝ (Fin d) :=
  (T : ℝ)⁻¹ • ∑ t, g (ω t)

/-- The expected distance `E[dist(ḡ_T, S)]` at horizon `T` (Definition 5.2, p.12). -/
noncomputable def expDistToSet {d : ℕ} (g : A0 × ((i : L) → Act i) → EuclideanSpace ℝ (Fin d))
    (S : Set (EuclideanSpace ℝ (Fin d))) (P : IndepProfile A0 Act) (π : AnytimePolicy A0 Act)
    (T : ℕ) : ℝ :=
  ∑ ω : Fin T → A0 × ((i : L) → Act i),
    approachTrajWeight P π ω * Metric.infDist (avgStat g ω) S

/-- The profile `P` approaches `S`: against every optimizer policy `π`,
`lim_{T→∞} E[dist(ḡ_T, S)] = 0` (Definition 5.2, p.12). -/
def Approaches {d : ℕ} (g : A0 × ((i : L) → Act i) → EuclideanSpace ℝ (Fin d))
    (S : Set (EuclideanSpace ℝ (Fin d))) (P : IndepProfile A0 Act) : Prop :=
  ∀ π : AnytimePolicy A0 Act,
    Filter.Tendsto (fun T => expDistToSet g S P π T) Filter.atTop (nhds 0)

/-- **Joint approachability** (Definition 5.2, p.12): there is a profile of independent learning
algorithms such that, against every optimizer policy `π`, `lim_{T→∞} E[dist(ḡ_T, S)] = 0`. -/
def IsJointlyApproachable {d : ℕ} (g : A0 × ((i : L) → Act i) → EuclideanSpace ℝ (Fin d))
    (S : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ P : IndepProfile A0 Act, Approaches g S P

/-- The profile's lotteries depend only on the optimizer's past actions `c(1), …, c(t−1)` (the
public history used by Algorithm 2, p.32). -/
def IsPublicHistory (P : IndepProfile A0 Act) : Prop :=
  ∀ (t : ℕ) (h h' : Fin t → A0 × ((i : L) → Act i)), (∀ r, (h r).1 = (h' r).1) →
    P.x t h = P.x t h'

end JointNonManip.Supplement


