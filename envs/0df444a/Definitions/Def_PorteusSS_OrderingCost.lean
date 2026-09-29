-- Prove2me | Definitions.Def_PorteusSS_OrderingCost
-- name    : PorteusSS_OrderingCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:52:13.870823+00:00
-- url     : https://prove2.me/theorems/c78ec8bb-80e2-44fd-adb6-575f6f5e2e98
-- title:
--   The concave increasing ordering cost and its supporting lines $C_1(z)$, $C_2(z)$, $C$, $K_c$ (§II)
-- statement:
--   Let $c$ denote the ordering cost function: ordering $z \ge 0$ units costs $c(z)$. For $z > 0$ define the set of supporting lines of $c$ touching it at $z$,
--   $$ C_1(z) = \{(\kappa, K) \in \mathbb R^2 : \kappa z + K = c(z) \text{ and } \kappa y + K \ge c(y) \text{ for all } y \ge 0\}, $$
--   and the subset with the smallest intercept,
--   $$ C_2(z) = \{(\kappa, K) \in C_1(z) : K \le K' \text{ for all } (\kappa', K') \in C_1(z)\}. $$
--   The set of slopes is
--   $$ C = \{\kappa \in \mathbb R : (\kappa, K) \in C_2(z) \text{ for some } K \ge 0 \text{ and } z > 0\}, $$
--   and for $\kappa \in C$, $K_\kappa$ is the real number with $(\kappa, K_\kappa) \in C_2(x)$ for some $x > 0$.
--
--   The **standing assumptions of §II** on $c$ are: $c$ is concave and increasing on $[0, \infty)$, $c(0) = 0$, and the limits
--   $$ \lim_{z \downarrow 0} C_2(z) = (c_0, K_0), \qquad \lim_{z \to \infty} C_2(z) = (c_\infty, K_\infty) $$
--   exist as finite pairs. The paper writes $c$ both for the cost function and for the slopes in $C$; here the slopes are called $\kappa$. The linear function $x \mapsto \kappa x$ is written $\kappa\cdot$.
--
--   For concave increasing $c$ every $C_2(z)$, $z > 0$, is a single pair (the line through $(z, c(z))$ with slope the left derivative), and $c(z) = \min_{\kappa \in C}\{K_\kappa + \kappa z\}$ for $z > 0$; the numbers $K_\kappa$ act as setup costs and the slopes $\kappa$ as marginal costs of the linear pieces that bound $c$ from above.
--
--   **Formalization Note.** $c$ is a function $\mathbb R \to \mathbb R$; only its values on $[0,\infty)$ enter. "Increasing" is read as nondecreasing (`MonotoneOn`), which allows the setup-plus-linear cost with zero marginal cost. $K_\kappa$ is the infimum of the set of intercepts $K$ with $(\kappa, K) \in C_2(z)$ for some $z > 0$; for $\kappa \in C$ this set is a singleton, so the infimum is that number (it is only used for $\kappa \in C$). The limit of $C_2(z)$ is stated as: for every neighbourhood $U$ of the limit pair, $C_2(z) \subseteq U$ eventually (as $z \downarrow 0$, resp. $z \to \infty$).
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), p. 412, §II (C_1(z), C_2(z), limits (c_0, K_0), (c_∞, K_∞), C, K_c)

import Mathlib

open Filter Topology Set

namespace PorteusSS

/-! The concave increasing ordering cost of §II. Throughout, `c : ℝ → ℝ` is the ordering cost
function (only its values on `[0, ∞)` matter) and `κ` denotes a slope in the set `C` of the
paper, which the paper also writes `c`. -/

/-- `C₁(z) = {(κ, K) ∈ ℝ² ; κ z + K = c(z) and κ y + K ≥ c(y) for all y ≥ 0}`: the lines
supporting `c` on `[0, ∞)` and touching it at `z`. -/
def C1 (c : ℝ → ℝ) (z : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 * z + p.2 = c z ∧ ∀ y : ℝ, 0 ≤ y → c y ≤ p.1 * y + p.2}

/-- `C₂(z) = {(κ, K) ∈ C₁(z) ; K ≤ K' for all (κ', K') ∈ C₁(z)}`. -/
def C2 (c : ℝ → ℝ) (z : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ C1 c z ∧ ∀ q ∈ C1 c z, p.2 ≤ q.2}

/-- `C = {κ ∈ ℝ ; (κ, K) ∈ C₂(z) for some K ≥ 0 and z > 0}`. -/
def slopeSet (c : ℝ → ℝ) : Set ℝ :=
  {κ | ∃ K : ℝ, 0 ≤ K ∧ ∃ z : ℝ, 0 < z ∧ (κ, K) ∈ C2 c z}

/-- `K_κ` for `κ ∈ C`: the real number with `(κ, K_κ) ∈ C₂(x)` for some `x > 0`. The set below is
a singleton for `κ ∈ C` (two supporting lines of the same slope that touch `c` coincide), so the
infimum is that number. Only used for `κ ∈ slopeSet c`. -/
noncomputable def Kc (c : ℝ → ℝ) (κ : ℝ) : ℝ :=
  sInf {K : ℝ | ∃ z : ℝ, 0 < z ∧ (κ, K) ∈ C2 c z}

/-- The standing assumptions of §II on the ordering cost: `c` is concave and increasing
(nondecreasing) on `[0, ∞)`, `c 0 = 0`, and `lim_{z ↓ 0} C₂(z) = (c₀, K₀)`,
`lim_{z → ∞} C₂(z) = (c_∞, K_∞)` exist (every element of `C₂(z)` is eventually in any
neighbourhood of the limit pair). -/
structure IsOrderingCost (c : ℝ → ℝ) (c0 K0 cInf KInf : ℝ) : Prop where
  concave : ConcaveOn ℝ (Ici 0) c
  mono : MonotoneOn c (Ici 0)
  zero : c 0 = 0
  lim_zero : ∀ U ∈ 𝓝 ((c0, K0) : ℝ × ℝ), ∀ᶠ z in 𝓝[>] (0 : ℝ), C2 c z ⊆ U
  lim_top : ∀ U ∈ 𝓝 ((cInf, KInf) : ℝ × ℝ), ∀ᶠ z in atTop, C2 c z ⊆ U

end PorteusSS


