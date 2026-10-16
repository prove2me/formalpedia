-- Prove2me | Definitions.Def_ContextualAuctions_Structure_Structural
-- name    : ContextualAuctions_Structure_Structural
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T19:28:44.105853+00:00
-- url     : https://prove2.me/theorems/a006bfb9-a123-4b72-b6b1-bdf9d7b45279
-- title:
--   §6, p. 14 — the support δ(G), the Euclidean norm, and the standing assumptions of §6 (zero reserves, convex compact δ(G), unique best response µ)
-- statement:
--   This file states the standing assumptions of §6 ("Structural Properties") of Balseiro, Kroer and Kumar, on top of the model of the `Setting` file.
--
--   Write $\delta(G)$ for the support of the type law $G$: the set of types $(w,B)$ every neighbourhood of which has positive $G$-probability. Write $\|w\| = \big(\sum_i w_i^2\big)^{1/2}$ for the Euclidean norm.
--
--   A pair $(M, \mu)$ of a model and a pacing function satisfies the **§6 standing assumptions** when:
--
--   1. the reserve price is zero, $r(\alpha) = 0$ for every $\alpha$;
--   2. $\delta(G)$ is convex and compact, and $\delta(G) \subseteq \Theta$;
--   3. $\mu$ is a pacing function with values in $[0, \omega/B_{\min}]$ on $\Theta$;
--   4. for every $(w, B) \in \delta(G)$, $\mu(w,B)$ is the **unique** minimizer of the dual function over $[0,\omega/B_{\min}]$:
--   $$\mu(w,B) = \operatorname*{arg\,min}_{t \in [0,\omega/B_{\min}]} q^\mu(w,B,t),$$
--   that is, $\mu(w,B) \in [0,\omega/B_{\min}]$, $q^\mu(w,B,\mu(w,B)) \le q^\mu(w,B,t)$ for every $t \in [0,\omega/B_{\min}]$, and every other minimizer over $[0,\omega/B_{\min}]$ equals $\mu(w,B)$.
--
--   Note that $\mu$ appears both inside $q^\mu$ (through the competitors' strategy $\beta^\mu$) and as its minimizer: condition 4 says that, against competitors paced by $\mu$, the unique optimal multiplier of every type in the support is the one $\mu$ assigns to it. As the paper remarks, this assumes that the best response is unique, not that the equilibrium is unique.
--
--   **Formalization Note.** The paper assumes that $\delta(G)$ is a convex compact subset of $\mathbb{R}^{d+1}_+$. Since $\mu$ is defined on $\Theta$ and the uniqueness condition evaluates it on $\delta(G)$, the formalization assumes $\delta(G) \subseteq \Theta$ (which implies the paper's $\delta(G) \subseteq \mathbb{R}^{d+1}_+$); this is a disclosed addition. The norm is written as an explicit square root of a sum because Lean's default norm on `Fin d → ℝ` is the sup norm.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science, Articles in Advance (2023), doi:10.1287/mnsc.2023.4719, p. 14, §6, first paragraph; §2.1, p. 4 (Euclidean norm)

import Mathlib
import Definitions.Def_ContextualAuctions_Structure_Setting

namespace ContextualAuctions.Structure

open MeasureTheory

/-- `δ(G)`, the support of the type law `G` (§6, p. 14). -/
noncomputable def supp (M : Model) : Set ((Fin M.d → ℝ) × ℝ) := M.G.support

/-- The Euclidean norm `‖w‖ = (∑ i w_i²)^{1/2}` of a weight vector (§2.1). -/
noncomputable def wnorm {d : ℕ} (w : Fin d → ℝ) : ℝ := Real.sqrt (∑ i, w i ^ 2)

/-- `a` is the unique minimizer of `f` over `s`: it lies in `s`, minimizes `f` there, and every
minimizer of `f` over `s` equals `a`. -/
def IsUniqueMinOn (f : ℝ → ℝ) (s : Set ℝ) (a : ℝ) : Prop :=
  a ∈ s ∧ IsMinOn f s a ∧ ∀ b ∈ s, IsMinOn f s b → b = a

/-- The standing assumptions of §6 (p. 14) on the model and the pacing function `µ`: zero reserve
prices, a convex compact support `δ(G)` contained in `Θ`, `µ : Θ → [0, ω/B_min]`, and `µ(w, B)` the
unique minimizer of `t ↦ q^µ(w, B, t)` over `[0, ω/B_min]` for every `(w, B) ∈ δ(G)`. -/
structure SixStanding (M : Model) (mu : (Fin M.d → ℝ) × ℝ → ℝ) : Prop where
  zero_reserve : ∀ α, M.r α = 0
  supp_convex : Convex ℝ (supp M)
  supp_compact : IsCompact (supp M)
  supp_subset : supp M ⊆ Theta M
  pacing : IsPacing M mu
  range : ∀ θ ∈ Theta M, mu θ ∈ Set.Icc 0 (omega M / M.Bmin)
  unique_best_response :
    ∀ θ ∈ supp M, IsUniqueMinOn (qDual M mu θ) (Set.Icc 0 (omega M / M.Bmin)) (mu θ)

end ContextualAuctions.Structure


