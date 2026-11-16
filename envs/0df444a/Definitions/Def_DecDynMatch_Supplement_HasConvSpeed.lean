-- Prove2me | Definitions.Def_DecDynMatch_Supplement_HasConvSpeed
-- name    : DecDynMatch_Supplement_HasConvSpeed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:24:57.805489+00:00
-- url     : https://prove2.me/theorems/02826a90-9d44-4510-8007-3ddd26dd81e0
-- title:
--   Convergence speed $g$ of a protocol (Definition 1) and the post-event cost $L_\Pi(h;I)$
-- statement:
--   For a protocol $\Pi$ and an instance $I$ with last population-event time $t^*$, the **post-event cost** is
--   $$
--   L_\Pi(h;I)=\mathbb E\bigl[D_\Pi(t^*+h;I)-D_\Pi(t^*;I)\bigr],\qquad h\ge 1,
--   $$
--   the expected number of mismatched rounds among $t^*+1,\dots,t^*+h$ (eq. (8)).
--
--   **Definition 1.** $\Pi$ has **convergence speed** $g$ if for every $\varepsilon\in(0,1)$ there is a constant $c_\varepsilon>0$ such that for every instance $I$
--   $$
--   \frac{L_\Pi(h;I)}{h}\le\varepsilon\qquad\text{for all } h\ge c_\varepsilon\, g(t^*).
--   $$
--
--   **Formalization Note** $c_\varepsilon$ is chosen before the instance. "Every instance" ranges over instances on the protocol's $K$ arms with utilities in $[0,1]$ and any finite player type in `Type` (every finite player set is in bijection with one, and protocols do not see identities). The paper's standing monotonicity of $g$ is stated in Theorem 3, where $g$ is quantified.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), eq. (8) and Definition 1, p.10

import Mathlib
import Definitions.Def_DecDynMatch_Supplement_expD
import Definitions.Def_DecDynMatch_Supplement_UnitUtilities

namespace DecDynMatch.Supplement

open DecDynMatch

/-- **Post-event cost** `L_Π(h; I)`, eq. (8), p.10: "L_Π(h; I) = E[D_Π(t* + h; I) − D_Π(t*; I)]",
the expected number of mismatched rounds among `t* + 1, …, t* + h`. -/
noncomputable def postCost {K : ℕ} {ι : Type*} [Fintype ι] (P : Protocol K) (I : Instance K ι)
    (h : ℕ) : ℝ :=
  expD P I (tstar I + h) - expD P I (tstar I)

/-- **Convergence speed (Definition 1).** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*, arXiv:2610.41912
(held version, sha256 6a27277e…), Definition 1, p.10: "Let g : ℕ≥1 → ℕ≥1 be a
non-decreasing function. A decentralized matching protocol Π has convergence speed g if, for every
ε ∈ (0, 1), there is a constant c_ε > 0 such that, for every instance I, we have
L_Π(h; I)/h ≤ ε, ∀ h ≥ c_ε g(t*)."

**Formalization Note.**
* `c_ε` is chosen before the instance; "every instance" is every instance on the protocol's `K`
  arms with utilities in `[0, 1]` (§2.1), over every finite player type `ι : Type` (every finite
  set of players is in bijection with such a type, and the protocol does not see player identities).
* `h` ranges over integers `h ≥ 1` with `h ≥ c_ε g(t*)` (eq. (8) defines `L_Π(h; I)` for `h ≥ 1`).
* Monotonicity of `g` is the paper's standing assumption on `g`; it is stated where `g` is
  quantified (Theorem 3), not here. -/
def HasConvSpeed {K : ℕ} (P : Protocol K) (g : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ c : ℝ, 0 < c ∧
    ∀ (ι : Type) [Fintype ι] (I : Instance K ι), UnitUtilities I →
      ∀ h : ℕ, 1 ≤ h → c * (g (tstar I) : ℝ) ≤ (h : ℝ) → postCost P I h / (h : ℝ) ≤ ε

end DecDynMatch.Supplement


