-- Prove2me | Definitions.Def_StrictCompatLB_MeanField_Policy
-- name    : StrictCompatLB_MeanField_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:49:54.76221+00:00
-- url     : https://prove2.me/theorems/eb68dcf5-6b0f-4634-8612-e8b34a024e56
-- title:
--   JSQ(d) on a compatibility graph, assignment probability functions, Lipschitz policies (Def. 4.1), the JSQ(d) function (E.1) and the system (4.2)
-- statement:
--   Task assignment policies on a compatibility graph $G_N$.
--
--   1. **JSQ(d)** (§2, pp. 8–9). When a task arrives at dispatcher $w$, the dispatcher samples a uniformly random subset $U\subseteq\mathcal N_w$ of $k_w=\min(d,|\mathcal N_w|)$ servers (without replacement) and assigns the task to a server of $U$ with the shortest queue, ties broken uniformly at random. In state $z$, server $v$ receives the task with probability
--   $$\binom{|\mathcal N_w|}{k_w}^{-1}\sum_{\substack{U\subseteq\mathcal N_w\\|U|=k_w}}\frac{\mathbb 1\{v\in\arg\min_U z\}}{|\arg\min_U z|}.$$
--   2. **Assignment probability functions** (§4.1, p. 15). A policy $\Pi$ is given by $p^\Pi=(p^\Pi_0,p^\Pi_1,\dots):\mathcal X\to[0,1]^{\mathbb N}$: at an arrival at $w$ with LEQD $x^w$, (a) a level $I$ is drawn with $P(I=i)=p^\Pi_i(x^w)$, and (b) the task joins a server of $\mathcal N_w$ with queue length $I$, chosen uniformly at random. We require that $p^\Pi(x)$ is a probability vector for $x\in\mathcal X$ and that $p^\Pi_i(x)=0$ whenever $x_i=0$.
--   3. **Lipschitz continuity** (Definition 4.1). $\Pi$ is Lipschitz continuous if there is a finite constant $K>0$ with
--   $$\sum_{i=0}^\infty|p^\Pi_i(x)-p^\Pi_i(y)|\le K\sum_{i=0}^\infty|x_i-y_i|\qquad\text{for all }x,y\in\mathcal X.$$
--   4. **The JSQ(d) assignment function** (E.1): with $q_i=\sum_{j\ge i}x_j$, $p^\Pi_{i-1}(x)=q_{i-1}^d-q_i^d$ for $i\ge1$.
--   5. **The mean-field system** (4.2) of a policy: $q^*$ solves (4.2) on $[0,\infty)$ if $q^*(t)$ is an occupancy state for every $t\ge0$ and for $i\ge1$
--   $$\frac{dq^*_i(t)}{dt}=\lambda\,p^\Pi_{i-1}\big((q^*_j(t)-q^*_{j+1}(t))_{j\ge0}\big)-\big(q^*_i(t)-q^*_{i+1}(t)\big).$$
--   6. The index of Theorem 4.11: $i_0=\min\{i\ge1:\lambda(2q^*_i(\infty)+1)<(1+\lambda)/2\}$, with $q^*_i(\infty)=\lambda^{(d^i-1)/(d-1)}$.
--
--   These definitions describe the dynamics whose large-system limit the mission studies.
--
--   **Formalization Note** The JSQ(d) routing law is the explicit finite probability vector above; sampling is without replacement, as in §2, Definition 3.3 and (H.5) (with replacement, Theorem 4.8 fails under Definition 3.3). The two conditions in item 2 are not written in the paper; without them steps (a)–(b) can ask for a uniform choice from an empty set. Lipschitz continuity uses `l1dist` in $[0,\infty]$. In item 5 the derivative at $t=0$ is one-sided and $q^*_0\equiv1$. In item 6 the fixed point is the corrected value $\lambda^{(d^i-1)/(d-1)}$ of `PowerTwoChoices.Limit.fixedPoint` (the printed (3.4) has the exponent $(d^i-d)/(d-1)$, which gives $q^*_1(\infty)=1$); the minimum is an `sInf`, of a set that is nonempty for $0<\lambda<1$, $d\ge1$.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, pp. 8–9, §2 (JSQ(d)); p. 15, §4.1 (policies Π), Definition 4.1, (4.1); p. 16, (4.2); p. 22, Theorem 4.11 (i_0); p. 41, (E.1)

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Occupancy

open Finset
open scoped ENNReal

namespace StrictCompatLB.MeanField

/-! Task assignment policies of Rutten & Mukherjee, arXiv:2008.07562v2: JSQ(d) on the
compatibility graph (§2, pp. 8–9), generic policies `Π` given by an assignment probability
function (§4.1, p. 15; Def. 4.1), the JSQ(d) assignment function (E.1) (p. 41), the
mean-field system (4.2) of a policy (p. 16) and the index `i₀` of Theorem 4.11 (p. 22). -/

/-- The servers of `U` with the shortest queue in state `z`. -/
def argminSet {N : ℕ} (U : Finset (Fin N)) (z : Fin N → ℕ) : Finset (Fin N) :=
  U.filter (fun u => ∀ u' ∈ U, z u ≤ z u')

/-- **JSQ(d) on the compatibility graph** (pp. 8–9; Def. 3.3 and the remark after it, p. 11):
the probability that a task arriving at dispatcher `w` in state `z` joins server `v`. The
dispatcher samples a uniformly random subset `U ⊆ 𝒩_w` of `k_w = min(d, |𝒩_w|)` servers
(without replacement) and sends the task to a shortest queue of `U`, ties broken uniformly at
random:
`∑_{U ⊆ 𝒩_w, |U| = k_w} C(|𝒩_w|, k_w)⁻¹ · 𝟙{v ∈ argmin_U z} / |argmin_U z|`.
When `𝒩_w ≠ ∅` these numbers form a probability vector supported on `𝒩_w`. -/
noncomputable def jsqdRoute (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N d : ℕ)
    (w : Fin (M N)) (z : Fin N → ℕ) (v : Fin N) : ℝ :=
  ((Nat.choose (nbrW M G N w).card (min d (nbrW M G N w).card) : ℕ) : ℝ)⁻¹ *
    ∑ U ∈ (nbrW M G N w).powersetCard (min d (nbrW M G N w).card),
      (if v ∈ argminSet U z then ((argminSet U z).card : ℝ)⁻¹ else 0)

/-- An **assignment probability function** `p^Π : 𝒳 → [0, 1]^ℕ` (p. 15), with the two
conditions under which steps (a)–(b) on p. 15 define a routing law: on `𝒳`, `p^Π(x)` is a
probability vector, and `p^Π_i(x) = 0` whenever `x_i = 0` (so that the level `I` drawn in
step (a) is always occupied). -/
def IsAssignmentFn (p : (ℕ → ℝ) → ℕ → ℝ) : Prop :=
  ∀ x, InX x → (∀ i, 0 ≤ p x i) ∧ HasSum (p x) 1 ∧ ∀ i, x i = 0 → p x i = 0

/-- (4.1) with constant `K`: `∑_{i ≥ 0} |p^Π_i(x) − p^Π_i(y)| ≤ K ∑_{i ≥ 0} |x_i − y_i|` for all
`x, y ∈ 𝒳` (both sides in `[0, ∞]`). -/
def IsLipschitzPolicyWith (p : (ℕ → ℝ) → ℕ → ℝ) (K : ℝ) : Prop :=
  ∀ x y, InX x → InX y →
    PowerOfDUniversality.Fluid.l1dist (p x) (p y) ≤
      ENNReal.ofReal K * PowerOfDUniversality.Fluid.l1dist x y

/-- Definition 4.1 (p. 15): the policy is **Lipschitz continuous** if (4.1) holds for some finite
positive constant `K`. -/
def IsLipschitzPolicy (p : (ℕ → ℝ) → ℕ → ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ IsLipschitzPolicyWith p K

/-- The routing law of a policy `Π` with assignment function `p` on `G_N` (p. 15): at an
arrival at `w` with LEQD `x^w(z)`, (a) a level `I` is drawn with `P(I = i) = p_i(x^w(z))`, and
(b) the task joins a server of `𝒩_w` with queue length `I`, uniformly at random. So server
`v ∈ 𝒩_w` is chosen with probability `p_{z_v}(x^w(z)) / |{u ∈ 𝒩_w : z_u = z_v}|`. -/
noncomputable def piRoute (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (p : (ℕ → ℝ) → ℕ → ℝ) (w : Fin (M N)) (z : Fin N → ℕ) (v : Fin N) : ℝ :=
  if v ∈ nbrW M G N w then
    p (leqd M G N z w) (z v) / (((nbrW M G N w).filter (fun u => z u = z v)).card : ℝ)
  else 0

/-- The tail `q_i = ∑_{j ≥ i} x_j` of `x ∈ 𝒳`. -/
noncomputable def tailOf (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑' j, if i ≤ j then x j else 0

/-- The JSQ(d) assignment probability function (E.1) (p. 41):
`p_{i−1}(x) = q_{i−1}^d − q_i^d` for `i ≥ 1`, i.e. `p_i(x) = q_i^d − q_{i+1}^d`, `q_i = ∑_{j ≥ i} x_j`. -/
noncomputable def jsqdAssign (d : ℕ) (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  tailOf x i ^ d - tailOf x (i + 1) ^ d

/-- A **solution of (4.2)** (p. 16) on `[0, ∞)`: `s t` is a state (`s t 0 = 1`, nonnegative,
nonincreasing) for every `t ≥ 0`, and for every `i ≥ 1` the coordinate `t ↦ s t i` has, at every
`t ≥ 0` (one-sided at `t = 0`), derivative
`λ p_{i−1}((s_j(t) − s_{j+1}(t))_{j ≥ 0}) − (s_i(t) − s_{i+1}(t))`. -/
def IsPiTrajectory (lam : ℝ) (p : (ℕ → ℝ) → ℕ → ℝ) (s : ℝ → ℕ → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → PowerTwoChoices.Limit.IsState (s t)) ∧
  ∀ i : ℕ, 1 ≤ i → ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt (fun u => s u i)
      (lam * p (fun j => s t j - s t (j + 1)) (i - 1) - (s t i - s t (i + 1))) (Set.Ici 0) t

/-- The index `i₀ = min{i ≥ 1 : λ(2 q*_i(∞) + 1) < (1 + λ)/2}` of Theorem 4.11 (p. 22), with
`q*_i(∞) = λ^{(d^i − 1)/(d − 1)}` the fixed point `PowerTwoChoices.Limit.fixedPoint`. For
`0 < λ < 1` and `d ≥ 1` the set is nonempty (`q*_i(∞) → 0`), so `sInf` is its minimum. -/
noncomputable def i0Index (lam : ℝ) (d : ℕ) : ℕ :=
  sInf {i : ℕ | 1 ≤ i ∧ lam * (2 * PowerTwoChoices.Limit.fixedPoint lam d i + 1) < (1 + lam) / 2}

end StrictCompatLB.MeanField


