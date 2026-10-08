-- Prove2me | Definitions.Def_PrimalDualSubgrad_DA_ProxSetting
-- name    : PrimalDualSubgrad_DA_ProxSetting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:26.622667+00:00
-- url     : https://prove2.me/theorems/f2c92400-f4da-426b-a683-57af8c7f6a2e
-- title:
--   Prox-function setting: closed convex set Q, σ-strongly convex prox-function d, prox-center x₀; support-type functions ξ_D, V_β; argmin map π_β
-- statement:
--   Let $E$ be a finite-dimensional real vector space with an arbitrary norm $\|\cdot\|$, and let $E^*$ be its dual, with the value of $s \in E^*$ at $x \in E$ written $\langle s, x\rangle$ and the dual norm $\|s\|_* = \max\{\langle s, x\rangle : \|x\| \le 1\}$.
--
--   A **prox setting** consists of
--
--   1. a closed convex set $Q \subseteq E$;
--   2. a **prox-function** $d$ of $Q$: a function continuous on $Q$ and strongly convex on $Q$ with **convexity parameter** $\sigma > 0$, that is, for all $x, y \in Q$ and $\alpha \in [0,1]$,
--   $$d(\alpha x + (1-\alpha) y) \le \alpha d(x) + (1-\alpha) d(y) - \tfrac12 \sigma \alpha (1-\alpha) \|x - y\|^2; \qquad (1.8)$$
--   3. a **prox-center** $x_0 \in Q$, a minimizer of $d$ on $Q$, normalized so that $d(x_0) = 0$ (1.9).
--
--   On top of a prox setting we define, for $D \ge 0$, $\beta > 0$ and $s \in E^*$, the level set $F_D = \{x \in Q : d(x) \le D\}$ and the two support-type functions (2.1)
--   $$\xi_D(s) = \max_{x \in Q}\{\langle s, x - x_0\rangle : d(x) \le D\}, \qquad V_\beta(s) = \max_{x \in Q}\{\langle s, x - x_0\rangle - \beta d(x)\}.$$
--   Finally, a map $(\beta, s) \mapsto \pi_\beta(s)$ is an **argmin map** if for every $\beta > 0$ and $s \in E^*$ the point $\pi_\beta(s)$ lies in $Q$ and minimizes $-\langle s, x\rangle + \beta d(x)$ over $Q$ (2.4).
--
--   These are the objects of Nesterov's Dual Averaging analysis: $\xi_D$ is the support function of $F_D$, and $V_\beta$ is a smoothed approximation of the support function of $Q$, whose gradient is $\pi_\beta(s) - x_0$.
--
--   **Formalization Note** $E^*$ is `StrongDual ℝ E` (continuous linear functionals) with its operator norm, which equals $\|\cdot\|_*$; $\langle s, x\rangle$ is `s x`. Strong convexity (1.8) is Mathlib's `StrongConvexOn Q σ d`. The prox-function is a real-valued function on all of $E$ of which only the values on $Q$ are used (the paper's "domain belonging to $Q$"). The page allows $\sigma \ge 0$; $\sigma > 0$ is taken from Definition 1 (p. 36) and is needed for every bound with $1/\sigma$. The maxima are real suprema (`sSup`); they are finite exactly in the paper's ranges $D \ge 0$, $\beta > 0$, and every statement assumes these ranges (outside them Lean's `sSup` returns the junk value $0$). The argmin map is a predicate on a given map, not a construction: its existence and uniqueness is Lemma 6.
-- source:
--   Nesterov, Primal-dual subgradient methods for convex problems, Math. Program. 120 (2009), pp. 5–7, (1.8), (1.9), (2.1), (2.4); p. 36, Definition 1

import Mathlib

namespace PrimalDualSubgrad.DA

/-- The setting of Nesterov (2009), *Notations and generalities*, p. 5, (1.8)–(1.9):
a closed convex set `Q` in a real normed space `E` with an arbitrary norm, a prox-function `d`
of `Q` (continuous on `Q` and strongly convex on `Q` with convexity parameter `σ > 0`, in the
sense (1.8) = Mathlib's `StrongConvexOn Q σ d`), and the prox-center `x0` of `Q` (a minimizer
of `d` on `Q`), normalized by `d x0 = 0`. Only the values of `d` on `Q` matter: this is the
paper's "d has domain belonging to Q". The page allows `σ ≥ 0`; `σ > 0` is required by
Definition 1 (p. 36) and by every bound with `1/σ`. -/
structure ProxSetting (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The feasible set `Q`. -/
  Q : Set E
  /-- The prox-function `d`. -/
  d : E → ℝ
  /-- The convexity parameter `σ` of `d`. -/
  σ : ℝ
  /-- The prox-center `x0` of `Q`. -/
  x0 : E
  isClosed_Q : IsClosed Q
  convex_Q : Convex ℝ Q
  continuousOn_d : ContinuousOn d Q
  σ_pos : 0 < σ
  strongConvexOn_d : StrongConvexOn Q σ d
  x0_mem : x0 ∈ Q
  x0_isMin : ∀ x ∈ Q, d x0 ≤ d x
  d_x0 : d x0 = 0

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The level set `F_D = {x ∈ Q : d(x) ≤ D}` (p. 6). -/
def FD (P : ProxSetting E) (D : ℝ) : Set E := {x ∈ P.Q | P.d x ≤ D}

/-- The support function `ξ_D(s) = max_{x ∈ Q} {⟨s, x − x0⟩ : d(x) ≤ D}` of `F_D`, (2.1), p. 6.
Written as a real `sSup`. The set is nonempty for `D ≥ 0` (it contains the value at `x0`) and
bounded above because `σ > 0` makes `F_D` bounded; for `D < 0` the set is empty and Lean's
`sSup ∅ = 0` is a junk value, so every statement using `xi` assumes `D ≥ 0`. -/
noncomputable def xi (P : ProxSetting E) (D : ℝ) (s : StrongDual ℝ E) : ℝ :=
  sSup ((fun x => s (x - P.x0)) '' FD P D)

/-- The proximal-type support function `V_β(s) = max_{x ∈ Q} {⟨s, x − x0⟩ − β d(x)}`, (2.1),
p. 6. Written as a real `sSup`; the set is nonempty (`x0 ∈ Q`) and bounded above when
`β > 0` and `σ > 0`. For `β ≤ 0` and unbounded `Q` the set is unbounded and Lean's `sSup`
returns the junk value `0`, so every statement using `V` assumes `β > 0` (the page's range). -/
noncomputable def V (P : ProxSetting E) (β : ℝ) (s : StrongDual ℝ E) : ℝ :=
  sSup ((fun x => s (x - P.x0) - β * P.d x) '' P.Q)

/-- `π` is the argmin map of (2.4), p. 7: for every `β > 0` and `s ∈ E*`, the point `π β s`
lies in `Q` and minimizes `−⟨s, x⟩ + β d(x)` over `Q`. (Existence and uniqueness of this
minimizer is Lemma 6, p. 36, a theorem; it is not assumed here.) -/
def IsProxMap (P : ProxSetting E) (π : ℝ → StrongDual ℝ E → E) : Prop :=
  ∀ β : ℝ, 0 < β → ∀ s : StrongDual ℝ E,
    π β s ∈ P.Q ∧ ∀ x ∈ P.Q, -(s (π β s)) + β * P.d (π β s) ≤ -(s x) + β * P.d x

end PrimalDualSubgrad.DA


