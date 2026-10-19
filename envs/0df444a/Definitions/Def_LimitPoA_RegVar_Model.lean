-- Prove2me | Definitions.Def_LimitPoA_RegVar_Model
-- name    : LimitPoA_RegVar_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:20.938759+00:00
-- url     : https://prove2.me/theorems/0846f899-f4c2-4f49-a1f0-39c598347b35
-- title:
--   §1.2, §2.1–2.2, pp. 6–8 — non-atomic congestion games, (2.1), NE, SO, PoA(d), regular variation, unbounded sequences, Definition 2.1
-- statement:
--   This file sets up the model of Wu, Möhring, Chen and Xu, *Selfishness need not be bad* (§1.2 and §2.1–2.2).
--
--   **Games.** A non-atomic congestion game $\Gamma$ has a finite non-empty set $\mathcal K$ of groups, a finite set $A$ of resources and, for each group $k$, a finite non-empty set $\mathcal S_k$ of strategies available only to group $k$. Each strategy $s$ is a non-empty subset of $A$, and every resource lies in some strategy:
--   $$\{s \in \mathcal S : a \in s\} \neq \emptyset \ \ \forall a \in A \quad\text{and}\quad s \neq \emptyset \ \ \forall s \in \mathcal S. \qquad (2.1)$$
--   Each resource has a cost function $\tau_a$ that is non-negative, non-decreasing and continuous on $[0,\infty)$.
--
--   **Profiles and costs.** For a demand vector $d = (d_k)_{k\in\mathcal K}$ with $d_k \ge 0$, a profile is a vector $f = (f_s)_{s\in\mathcal S}$ with $f_s \ge 0$ and $d_k = \sum_{s\in\mathcal S_k} f_s$. The joint consumption of resource $a$ is $f_a = \sum_{s \ni a} f_s$, the cost of strategy $s$ is $\tau_s(f) = \sum_{a\in s}\tau_a(f_a)$, and the social cost is
--   $$C(f) = \sum_{a\in A} f_a\,\tau_a(f_a).$$
--   An NE profile (Wardrop equilibrium) $\tilde f$ uses only strategies $s \in \mathcal S_k$ with $\tau_s(\tilde f) \le \tau_{s'}(\tilde f)$ for all $s' \in \mathcal S_k$; an SO profile $f^*$ minimizes $C$. The price of anarchy for $d$ is the worst cost of an NE profile over the optimum cost,
--   $$\mathrm{PoA}(d) = \frac{C(\tilde f)}{C(f^*)}.$$
--
--   **Unbounded sequences and Definition 2.1.** The total demand is $T(d) = \sum_k d_k$. A demand sequence $(d^{(n)})_{n\in\mathbb N}$ is unbounded if $T(d^{(n)}) \to \infty$. The game $\Gamma$ is *asymptotically well designed* if $\mathrm{PoA}(d^{(n)}) \to 1$ for every unbounded demand sequence.
--
--   **Regular variation (§1.2, p. 6).** A function $g$ is regularly varying if for every $x > 0$ the limit
--   $$\lim_{t\to\infty}\frac{g(t\cdot x)}{g(t)} = q(x)$$
--   exists and lies in $(0,\infty)$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The flows, loads and the Wardrop condition are those of the published definition `KellyStochasticNetworks_Wardrop` (incidence `inc a s ∈ {0,1}`, group map `grp`, so the sets $\mathcal S_k$ are disjoint; two groups may own strategies with the same resource set, which are then distinct strategies). The standing assumptions (non-empty $\mathcal K$, 0/1 incidence, (2.1), $\mathcal S_k \ne \emptyset$) are bundled as `Game.Standing`. Cost functions are maps $\mathbb R \to \mathbb R$ constrained only on $[0,\infty)$; only arguments in $[0,\infty)$ ever enter. Demand vectors may have zero entries: the paper's own sequences use them (Example 2.3, p. 23, Appendix A.6), and a zero-demand group carries no flow. $C(f^*)$ is the `sInf` and the worst NE cost the `sSup` of real sets; under `Game.Standing` and the cost-function class both sets are non-empty and bounded (the profile set is a non-empty compact polytope, and Wardrop equilibria exist for continuous non-decreasing costs), so neither is a junk value. When $C(f^*) = 0$ (possible only for small total demand) Lean's $x/0 = 0$ applies; this concerns finitely many terms of an unbounded sequence and does not affect any limit. Regular variation forces $g(t) > 0$ for all large $t$, since $g(t\,x)/g(t)$ is $0$ in Lean when $g(t) = 0$; no index is fixed.
-- source:
--   Wu, Möhring, Chen & Xu, Selfishness need not be bad, arXiv:1712.07464v2, pp. 6–8, §1.2 (definition of regular variation, p. 6), §2.1, (2.1), Definition 2.1

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop

namespace LimitPoA.RegVar

open Filter Topology KellyStochasticNetworks

/-- §2.1, p. 7: a non-atomic congestion game. `J` resources, `R` strategies, `Sd` groups;
resource `a` lies in strategy `s` iff `inc a s = 1`; strategy `s` is available only to the group
`grp s`, so `S_k = {s | grp s = k}` and the sets `S_k` are disjoint. -/
structure Game where
  J : ℕ
  R : ℕ
  Sd : ℕ
  inc : Fin J → Fin R → ℝ
  grp : Fin R → Fin Sd

/-- Standing assumptions of §2.1, pp. 7–8: the set of groups is non-empty, the incidence is 0/1,
every strategy is a non-empty set of resources and every resource lies in some strategy ((2.1)),
and every group has at least one strategy. -/
def Game.Standing (Γ : Game) : Prop :=
  0 < Γ.Sd ∧ (∀ a s, Γ.inc a s = 0 ∨ Γ.inc a s = 1) ∧ (∀ s, ∃ a, Γ.inc a s = 1) ∧
    (∀ a, ∃ s, Γ.inc a s = 1) ∧ (∀ k, ∃ s, Γ.grp s = k)

/-- §2.1, p. 7: a (unit) cost function is non-negative, non-decreasing and continuous on `[0, ∞)`. -/
def IsCostFn (h : ℝ → ℝ) : Prop :=
  ContinuousOn h (Set.Ici 0) ∧ MonotoneOn h (Set.Ici 0) ∧ ∀ x, 0 ≤ x → 0 ≤ h x

/-- §1.2, p. 6: `g` is regularly varying iff `lim_{t→∞} g(t·x)/g(t) = q(x) ∈ (0, ∞)` for all `x > 0`. -/
def IsRegularlyVarying (g : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → ∃ q : ℝ, 0 < q ∧ Tendsto (fun t => g (t * x) / g t) atTop (𝓝 q)

variable (Γ : Game)

/-- p. 8: the total demand `T(d) = Σ_k d_k`. -/
def totalDemand (d : Fin Γ.Sd → ℝ) : ℝ := ∑ k, d k

/-- p. 7: a strategy profile for the demand vector `d`: `f_s ≥ 0` and `d_k = Σ_{s ∈ S_k} f_s`. -/
def IsProfile (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) : Prop := f ∈ wardropFeasible Γ.grp d

/-- p. 7: the joint consumption `f_a = Σ_{s ∋ a} f_s`. -/
def load (f : Fin Γ.R → ℝ) (a : Fin Γ.J) : ℝ := linkFlow Γ.inc f a

/-- p. 7: the cost of strategy `s`, `τ_s(f) = Σ_{a ∈ s} τ_a(f_a)`. -/
def stratCost (τ : Fin Γ.J → ℝ → ℝ) (f : Fin Γ.R → ℝ) (s : Fin Γ.R) : ℝ :=
  ∑ a, τ a (load Γ f a) * Γ.inc a s

/-- p. 7: the social cost `C(f) = Σ_a f_a · τ_a(f_a)`. -/
def cost (τ : Fin Γ.J → ℝ → ℝ) (f : Fin Γ.R → ℝ) : ℝ :=
  ∑ a, load Γ f a * τ a (load Γ f a)

/-- p. 8: an NE profile (Wardrop equilibrium) for `d`. -/
def IsNE (τ : Fin Γ.J → ℝ → ℝ) (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) : Prop :=
  IsWardropEquilibrium Γ.inc Γ.grp τ d f

/-- p. 7: an SO profile for `d`: a profile of minimum social cost. -/
def IsSO (τ : Fin Γ.J → ℝ → ℝ) (d : Fin Γ.Sd → ℝ) (f : Fin Γ.R → ℝ) : Prop :=
  IsProfile Γ d f ∧ ∀ g, IsProfile Γ d g → cost Γ τ f ≤ cost Γ τ g

/-- The optimum cost `C(f*)` for `d`. -/
noncomputable def SOCost (τ : Fin Γ.J → ℝ → ℝ) (d : Fin Γ.Sd → ℝ) : ℝ :=
  sInf (cost Γ τ '' {f | IsProfile Γ d f})

/-- The worst cost of an NE profile for `d`. -/
noncomputable def NECost (τ : Fin Γ.J → ℝ → ℝ) (d : Fin Γ.Sd → ℝ) : ℝ :=
  sSup (cost Γ τ '' {f | IsNE Γ τ d f})

/-- p. 8: the price of anarchy `PoA(d)`, the worst NE cost over the optimum cost. -/
noncomputable def PoA (τ : Fin Γ.J → ℝ → ℝ) (d : Fin Γ.Sd → ℝ) : ℝ :=
  NECost Γ τ d / SOCost Γ τ d

/-- p. 8: an unbounded demand sequence: non-negative demands with `T(d^(n)) → ∞`. -/
def IsUnbounded (d : ℕ → Fin Γ.Sd → ℝ) : Prop :=
  (∀ n k, 0 ≤ d n k) ∧ Tendsto (fun n => totalDemand Γ (d n)) atTop atTop

/-- Definition 2.1, p. 8: `Γ` is asymptotically well designed if `PoA(d^(n)) → 1` for all
unbounded demand sequences. -/
def IsAsymptoticallyWellDesigned (τ : Fin Γ.J → ℝ → ℝ) : Prop :=
  ∀ d : ℕ → Fin Γ.Sd → ℝ, IsUnbounded Γ d → Tendsto (fun n => PoA Γ τ (d n)) atTop (𝓝 1)

end LimitPoA.RegVar


