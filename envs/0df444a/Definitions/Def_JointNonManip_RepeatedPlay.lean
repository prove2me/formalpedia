-- Prove2me | Definitions.Def_JointNonManip_RepeatedPlay
-- name    : JointNonManip_RepeatedPlay
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:29.255206+00:00
-- url     : https://prove2.me/theorems/73eda0c7-4023-4d11-af27-dc7119c8ebc2
-- title:
--   Repeated play of an optimizer against independent learners: CSPs, $S_{\mathrm{NE}}(G_{\mathcal L})$, swap gains, profiles, policies, menus, swap regret, non-manipulability
-- statement:
--   The model of §2 of Collina, Fullerton, Liu & Weinberg.
--
--   **The game.** A finite normal-form game $G=(A_0,A_1,\dots,A_{n-1},u_0,u_1,\dots,u_{n-1})$ has an optimizer (player $0$) and learners $\mathcal L=\{1,\dots,n-1\}$, with finite nonempty action sets. Write $A_{\mathcal L}=\prod_{i\in\mathcal L}A_i$ and $A=A_0\times A_{\mathcal L}$; utilities are $u_i:A\to[-1,1]$. The learners know $G_{\mathcal L}=(A_0,\dots,A_{n-1},u_1,\dots,u_{n-1})$ but not $u_0$. A **correlated strategy profile** (CSP) is a vector $\mu\in\Delta(A)\subset\mathbb R^A$; $e_a$ is a point mass, $y\otimes q$ the product of $y\in\Delta(A_0)$ and $q\in\Delta(A_{\mathcal L})$, and $\langle v,\mu\rangle=\sum_a v(a)\mu(a)$.
--
--   **The Nash response target.** For $y\in\Delta(A_0)$ the induced learner game $G_{\mathcal L}(y)$ has utilities $u_i^y(a_{\mathcal L})=\mathbb E_{c\sim y}[u_i(c,a_{\mathcal L})]$. With $\mathrm{NE}(G_{\mathcal L}(y))$ its set of product mixed Nash equilibria,
--   $$
--   E_{\mathrm{NE}}=\{y\otimes q:\ y\in\Delta(A_0),\ q\in\mathrm{NE}(G_{\mathcal L}(y))\},\qquad S_{\mathrm{NE}}(G_{\mathcal L})=\mathrm{conv}\,E_{\mathrm{NE}}.
--   $$
--   The **swap gain** of learner $i$ and swap $\phi:A_i\to A_i$ is $G_{i,\phi}(\mu)=\sum_{a\in A}\mu(a)\,[u_i(a_0,\phi(a_i),a_{-i})-u_i(a)]$.
--
--   **Repeated play.** In round $t$ of $T$, each learner $i$ plays a lottery $x_i^{(t)}$ that depends only on the horizon and the optimizer's past actions $c^{(1)},\dots,c^{(t-1)}$; the learners randomize independently, so their joint mixed action is $q^{(t)}=\bigotimes_i x_i^{(t)}$. The optimizer chooses $y^{(t)}\in\Delta(A_0)$ as a function of the whole past, draws $c^{(t)}\sim y^{(t)}$, and the learners draw $a^{(t)}\sim q^{(t)}$. Then:
--
--   1. $k^{(t)}=e_{c^{(t)}}\otimes q^{(t)}$, and the **horizon-$T$ menu** is $\mathcal M_T=\mathrm{conv}\{\frac1T\sum_{t=1}^T e_{c^{(t)}}\otimes q^{(t)} : (c^{(1)},\dots,c^{(T)})\in A_0^T\}$;
--   2. $\varphi_T(\pi)=\mathbb E[\frac1T\sum_t e_{c^{(t)}}\otimes q^{(t)}]$ is the expected CSP of the policy $\pi$, and $y^{\otimes T}$ is the static policy playing $y$ every round;
--   3. the realized **swap regret** is $R_i^{\mathrm{sw}}(T)=\max_{\phi}\sum_t[u_i(c^{(t)},\phi(a_i^{(t)}),a_{-i}^{(t)})-u_i(c^{(t)},a^{(t)})]$;
--   4. a profile has **no swap regret** if $\sup_\pi\mathbb E[R_i^{\mathrm{sw}}(T)]=o(T)$ for every learner, and is **jointly non-manipulable** if for every $u_0:A\to[-1,1]$, $\sup_{\pi}\langle u_0,\varphi_T(\pi)\rangle\le\sup_{y}\langle u_0,\varphi_T(y^{\otimes T})\rangle+o(1)$;
--   5. the menus **converge** to a set $\mathcal M$ when their Hausdorff distance to $\mathcal M$ tends to $0$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Lotteries, products of independent lotteries and mixed Nash equilibria are the published `AGT.IsLottery`, `AGT.profileProb`, `AGT.IsMixedNash`. Profiles are horizon-aware (indexed by $T$) and see only the optimizer's past actions; policies see all past actions. Expectations are finite sums over trajectories. $o(\cdot)$ is written $\forall\varepsilon>0\,\exists T_0\,\forall T\ge T_0$, uniformly over policies; Hausdorff distance is `Metric.hausdorffEDist` for the sup metric (all norms give the same convergence). The real infimum `l1InfDist` is only applied to the nonempty $S_{\mathrm{NE}}$.
-- source:
--   Collina, Fullerton, Liu & Weinberg, Non-manipulability and Approachability Beyond Two-Player Games (manuscript, STOC 2027 submission), §2, pp.4–7 (Definitions 2.2–2.6, swap-regret inequalities p.6); App. A.6, p.26 (E_NE)

import Mathlib
import Definitions.Def_agt_games

namespace JointNonManip

/-!
# Repeated play between one optimizer and independent learners

Collina, Fullerton, Liu & Weinberg, *Non-manipulability and Approachability Beyond Two-Player
Games* (manuscript, STOC 2027 submission), §2, pp.4–7, and Appendix A.6, p.26.

The game `G = (A₀, A₁, …, A_{n−1}, u₀, u₁, …, u_{n−1})` (p.4) is given by
* a finite nonempty optimizer action type `A0`;
* a finite type `L` of learners and, for every learner `i`, a finite nonempty action type `Act i`;
* the joint action type `A = A₀ × A_L`, written `A0 × ((i : L) → Act i)`;
* learner utilities `u : L → A0 × ((i : L) → Act i) → ℝ` (`u i` is `uᵢ : A → [−1, 1]`), and an
  optimizer utility `u0 : A0 × ((i : L) → Act i) → ℝ`, which is never part of the learners' data.

Lotteries, products of independent lotteries and mixed Nash equilibria are the published
`AGT.IsLottery`, `AGT.profileProb` and `AGT.IsMixedNash`.

**Formalization Note**
* A correlated strategy profile (CSP, Definition 2.3, p.5) is a real function on the finite type
  `A`; ℓ₁ and ℓ₂ distances are the explicit sums `l1dist`, `l2dist`. Hausdorff distances between
  sets of CSPs are `Metric.hausdorffEDist` for the sup metric of the function type; on a finite
  dimensional space all norms give the same Hausdorff convergence, and the extended distance is
  `⊤` (not `0`) between an empty and a nonempty set.
* A profile of learner algorithms (`Profile`) is **horizon-aware** (indexed by the horizon `T`,
  Lemma A.4, p.26 and p.38) and **public-history**: learner `i`'s lottery in round `t` is a
  function of the optimizer's realized actions `c(1), …, c(t−1)` only (p.4, "learner algorithms
  whose mixed strategies are determined by the optimizer's previously observed actions").
  Rounds are `Fin T` (round `t` of the paper is index `t − 1`).
* An optimizer policy at horizon `T` (`Policy`) chooses, in every round, a lottery on `A0` as a
  function of the whole past (all realized optimizer and learner actions). The learners' current
  product distribution `q(t)` is a function of that past and the fixed profile, so it is not a
  separate argument.
* The expected CSP `φ_T(π, A_L)` and the expected swap regret are finite sums over trajectories
  `ω : Fin T → A`, weighted by the probability `trajWeight` of `ω` under the policy and the
  profile, where in round `t` the optimizer draws `c(t) ∼ y(t)` and the learners then draw their
  actions independently from `q(t)`.
* `o(·)` statements are written `∀ ε > 0, ∃ T₀, ∀ T ≥ T₀`, uniformly over the optimizer
  policies at horizon `T`.
-/

open Finset

variable {A0 : Type} [Fintype A0] [DecidableEq A0]
variable {L : Type} [Fintype L] [DecidableEq L]
variable {Act : L → Type} [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]

/-- The point mass `e_a` on `a` (p.4). -/
def pointMass {α : Type} [DecidableEq α] (a : α) : α → ℝ :=
  fun b => if b = a then 1 else 0

/-- The product `y ⊗ q ∈ ℝ^A` of a weight function `y` on `A₀` and a weight function `q` on
`A_L` (p.4). -/
def otimes (y : A0 → ℝ) (q : ((i : L) → Act i) → ℝ) : A0 × ((i : L) → Act i) → ℝ :=
  fun a => y a.1 * q a.2

/-- The pairing `⟨v, μ⟩ = ∑ₐ v(a) μ(a)` (multilinear extension of utilities, p.4). -/
def pairing {α : Type} [Fintype α] (v μ : α → ℝ) : ℝ :=
  ∑ a, v a * μ a

/-- The ℓ₁ distance `‖μ − ν‖₁` of two vectors on a finite type. -/
def l1dist {α : Type} [Fintype α] (μ ν : α → ℝ) : ℝ :=
  ∑ a, |μ a - ν a|

/-- The Euclidean (ℓ₂) distance `‖μ − ν‖₂` of two vectors on a finite type. -/
noncomputable def l2dist {α : Type} [Fintype α] (μ ν : α → ℝ) : ℝ :=
  Real.sqrt (∑ a, (μ a - ν a) ^ 2)

/-- The ℓ₁ distance `dist₁(μ, S) = inf_{s ∈ S} ‖μ − s‖₁` from a vector to a set (Lemma A.4,
p.26). The infimum is a real `⨅` of values bounded below by `0`; on the empty set it would be
`0`, but it is only applied to `S_NE`, which is nonempty for every game with nonempty action
sets (Nash's theorem). -/
noncomputable def l1InfDist {α : Type} [Fintype α] (μ : α → ℝ) (S : Set (α → ℝ)) : ℝ :=
  ⨅ s : S, l1dist μ s

/-- The induced game `G_L(y)` among the learners (Definition 2.5, p.6): learner `i`'s utility
is `u_i^y(a₁, …, a_{n−1}) = E_{c∼y}[u_i(c, a₁, …, a_{n−1})]`. -/
def inducedUtility (u : L → A0 × ((i : L) → Act i) → ℝ) (y : A0 → ℝ) :
    L → ((i : L) → Act i) → ℝ :=
  fun i a => ∑ c, y c * u i (c, a)

/-- The generating set `E_NE = {y ⊗ q : y ∈ ∆(A₀), q ∈ NE(G_L(y))}` (Definition 2.5, p.6;
p.26), where `q = ⊗ᵢ xᵢ` is the product of a mixed Nash equilibrium `x` of `G_L(y)`. -/
def ENE (u : L → A0 × ((i : L) → Act i) → ℝ) : Set (A0 × ((i : L) → Act i) → ℝ) :=
  {μ | ∃ (y : A0 → ℝ) (x : (i : L) → Act i → ℝ),
    AGT.IsLottery y ∧ AGT.IsMixedNash (inducedUtility u y) x ∧ μ = otimes y (AGT.profileProb x)}

/-- The Nash response target `S_NE(G_L) = conv E_NE` (Definition 2.5, p.6). -/
def SNE (u : L → A0 × ((i : L) → Act i) → ℝ) : Set (A0 × ((i : L) → Act i) → ℝ) :=
  convexHull ℝ (ENE u)

/-- The swap-gain functional `G_{i,ϕ}(μ) = ∑_{a ∈ A} μ(a) [u_i(a₀, ϕ(a_i), a_{−i}) − u_i(a)]`
(p.6; Lemma 3.1, p.7). -/
def swapGain (u : L → A0 × ((i : L) → Act i) → ℝ) (i : L) (ϕ : Act i → Act i)
    (μ : A0 × ((i : L) → Act i) → ℝ) : ℝ :=
  ∑ a, μ a * (u i (a.1, Function.update a.2 i (ϕ (a.2 i))) - u i a)

/-- A **horizon-aware, public-history profile of learner algorithms** (p.4; Definition 2.4,
p.6; Lemma A.4, p.26): for horizon `T`, round `t < T` and the optimizer's past actions
`h = (c(1), …, c(t))` (as `Fin t → A0`), learner `i` plays the lottery `x T t h i` on `Act i`.
The learners randomize independently, so their joint mixed action is the product
`q(t) = ⊗ᵢ x T t h i`. -/
structure Profile (A0 : Type) {L : Type} (Act : L → Type) [∀ i, Fintype (Act i)] where
  /-- Learner `i`'s mixed action in round `t` of horizon `T` after the optimizer history `h`. -/
  x : (T : ℕ) → (t : Fin T) → (Fin t → A0) → (i : L) → Act i → ℝ
  /-- Every prescribed mixed action is a lottery. -/
  isLottery : ∀ T t h i, AGT.IsLottery (x T t h i)

/-- An **optimizer policy at horizon `T`** (p.4): in round `t` the optimizer chooses
`y(t) ∈ ∆(A₀)` as a function of the whole past (realized optimizer and learner actions of
rounds before `t`). -/
structure Policy (A0 : Type) {L : Type} (Act : L → Type) [Fintype A0] (T : ℕ) where
  /-- The optimizer's mixed action in round `t` after the history `h`. -/
  y : (t : Fin T) → (Fin t → A0 × ((i : L) → Act i)) → A0 → ℝ
  /-- Every chosen mixed action is a lottery. -/
  isLottery : ∀ t h, AGT.IsLottery (y t h)

/-- The static policy `y^{⊗T}`: the optimizer plays the fixed lottery `y` in every round
(Definition 2.6, p.7). -/
def Policy.static (y : A0 → ℝ) (hy : AGT.IsLottery y) (T : ℕ) : Policy A0 Act T :=
  ⟨fun _ _ => y, fun _ _ => hy⟩

/-- The prefix `(h(0), …, h(t−1))` of a length-`T` sequence, before round `t`. -/
def histPrefix {α : Type} {T : ℕ} (h : Fin T → α) (t : Fin T) : Fin t → α :=
  fun s => h (Fin.castLE t.isLt.le s)

/-- The learners' product distribution `q(t) = ⊗ᵢ xᵢ(t)` in round `t` along the optimizer
action path `c` (p.4). -/
def qAt (P : Profile A0 Act) (T : ℕ) (c : Fin T → A0) (t : Fin T) :
    ((i : L) → Act i) → ℝ :=
  AGT.profileProb (P.x T t (histPrefix c t))

/-- The mixed-action CSP of round `t`, `k(t) = e_{c(t)} ⊗ q(t)` (p.8). -/
def kAt (P : Profile A0 Act) (T : ℕ) (c : Fin T → A0) (t : Fin T) :
    A0 × ((i : L) → Act i) → ℝ :=
  otimes (pointMass (c t)) (qAt P T c t)

/-- The average CSP `(1/T) ∑ₜ e_{c(t)} ⊗ q(t)` of the optimizer action path `c`
(Definition 2.4, p.6; `k̄_T`, p.26). -/
noncomputable def pathCSP (P : Profile A0 Act) (T : ℕ) (c : Fin T → A0) :
    A0 × ((i : L) → Act i) → ℝ :=
  (T : ℝ)⁻¹ • ∑ t, kAt P T c t

/-- The **horizon-`T` menu** `M_T(A_L) = conv{(1/T) ∑ₜ e_{c(t)} ⊗ q(t) : c ∈ A₀^T}`
(Definition 2.4, p.6). -/
def menu (P : Profile A0 Act) (T : ℕ) : Set (A0 × ((i : L) → Act i) → ℝ) :=
  convexHull ℝ (Set.range (pathCSP P T))

/-- The probability of the trajectory `ω = ((c(t), a(t)))ₜ` when the optimizer follows `π` and
the learners follow `P`: in round `t` the optimizer draws `c(t) ∼ y(t)` and then the learners
independently draw `a(t) ∼ q(t)` (p.4). -/
def trajWeight (P : Profile A0 Act) {T : ℕ} (π : Policy A0 Act T)
    (ω : Fin T → A0 × ((i : L) → Act i)) : ℝ :=
  ∏ t, π.y t (histPrefix ω t) (ω t).1 *
    AGT.profileProb (P.x T t (histPrefix (fun s => (ω s).1) t)) (ω t).2

/-- The expected CSP `φ_T(π, A_L) = E[(1/T) ∑ₜ e_{c(t)} ⊗ q(t)]` (Definition 2.3, p.5). -/
noncomputable def expCSP (P : Profile A0 Act) {T : ℕ} (π : Policy A0 Act T) :
    A0 × ((i : L) → Act i) → ℝ :=
  ∑ ω : Fin T → A0 × ((i : L) → Act i), trajWeight P π ω • pathCSP P T (fun s => (ω s).1)

/-- The realized **swap regret** `R_i^sw(T) = max_ϕ ∑ₜ [u_i(c(t), ϕ(a_i(t)), a_{−i}(t)) −
u_i(c(t), a_i(t), a_{−i}(t))]` of learner `i` on the trajectory `ω` (Definition 2.2, p.5). -/
def swapRegret (u : L → A0 × ((i : L) → Act i) → ℝ) (i : L) {T : ℕ}
    (ω : Fin T → A0 × ((i : L) → Act i)) : ℝ :=
  Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ fun ϕ : Act i → Act i =>
    ∑ t, (u i ((ω t).1, Function.update (ω t).2 i (ϕ ((ω t).2 i))) - u i (ω t))

/-- The expected swap regret `E[R_i^sw(T)]` of learner `i` under the policy `π` and the profile
`P` (Definition 2.2, p.5). -/
def expSwapRegret (u : L → A0 × ((i : L) → Act i) → ℝ) (P : Profile A0 Act) {T : ℕ}
    (π : Policy A0 Act T) (i : L) : ℝ :=
  ∑ ω : Fin T → A0 × ((i : L) → Act i), trajWeight P π ω * swapRegret u i ω

/-- **No swap regret** (Definition 2.2, p.5): every learner's expected swap regret is `o(T)`
uniformly over all (adaptive) optimizer policies. -/
def NoSwapRegret (u : L → A0 × ((i : L) → Act i) → ℝ) (P : Profile A0 Act) : Prop :=
  ∀ i : L, ∀ ε > 0, ∃ T0 : ℕ, ∀ T ≥ T0, ∀ π : Policy A0 Act T,
    expSwapRegret u P π i ≤ ε * T

/-- **Joint non-manipulability** (Definition 2.6, p.7): for every optimizer utility
`u₀ : A → [−1, 1]`,
`sup_{π_T} ⟨u₀, φ_T(π_T, A_L)⟩ ≤ sup_{y ∈ ∆(A₀)} ⟨u₀, φ_T(y^{⊗T}, A_L)⟩ + o(1)`,
written: for every `ε > 0` there is `T₀` such that for every `T ≥ T₀` every policy is matched
up to `ε` by some static policy. -/
def JointlyNonManipulable (P : Profile A0 Act) : Prop :=
  ∀ u0 : A0 × ((i : L) → Act i) → ℝ, (∀ a, |u0 a| ≤ 1) →
    ∀ ε > 0, ∃ T0 : ℕ, ∀ T ≥ T0, ∀ π : Policy A0 Act T,
      ∃ (y : A0 → ℝ) (hy : AGT.IsLottery y),
        pairing u0 (expCSP P π) ≤ pairing u0 (expCSP P (Policy.static y hy T)) + ε

/-- The horizon-`T` menus converge to `M` in Hausdorff distance (Definition 2.4, p.6:
"`M(A_L)` for the limit of `M_T(A_L)` in Hausdorff distance"). -/
def MenuConvergesTo (P : Profile A0 Act) (M : Set (A0 × ((i : L) → Act i) → ℝ)) : Prop :=
  Filter.Tendsto (fun T => Metric.hausdorffEDist (menu P T) M) Filter.atTop (nhds 0)

end JointNonManip


