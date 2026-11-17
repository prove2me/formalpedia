-- Prove2me | Definitions.Def_LocalBreadth_Supplement_IsAchievable
-- name    : LocalBreadth_Supplement_IsAchievable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:19:41.786885+00:00
-- url     : https://prove2.me/theorems/20e9232b-1d28-4826-a566-f477f879895c
-- title:
--   Achievable density profiles
-- statement:
--   A **density profile** on a family $\mathcal X$ is a function $\alpha:\mathcal X\to[0,1]$. It is **achievable at threshold $h$** if one fresh, universally eventually valid generator guarantees
--   $$\delta_h(O,K)\ge\alpha(K)$$
--   for every $K\in\mathcal X$ and every full enumeration of $K$.
--
--   The set of achievable profiles is the generation frontier that §7 characterizes exactly.
--
--   **Formalization Note** A profile is a function on all languages; only its values on $\mathcal X$ matter, and their range $[0,1]$ is stated in the theorems.
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc309339291b1a61b8504342f4050ece6e4e903dd18b2bf541446f1064), §1.4.2, p.8; Theorem 7.2, p.52

import Mathlib
import Definitions.Def_LocalBreadth_Supplement_GeneratorP
import Definitions.Def_LocalBreadth_Supplement_deltaH

namespace LocalBreadth.Supplement

variable {P : Type} [Preorder P]

/-- An **achievable profile** at threshold `h` (§1.4.2, p.8; Theorem 7.2, p.52): one globally fresh,
universally eventually valid generator guarantees `δ_h(O, K) ≥ α(K)` for every `K ∈ X` and every full
enumeration of `K`. Kleinberg, Wei, STOC 2027 submission (manuscript sha256 f924cbfc…).

**Formalization Note.** A profile is a function `α : Set P → ℝ`; its values off `X` are unused and its
range `[0, 1]` on `X` is a hypothesis of the theorems. -/
def IsAchievable (h : ℕ → ℝ) (X : Set (Set P)) (α : Set P → ℝ) : Prop :=
  ∃ G : GeneratorP P, IsFreshP X G ∧ IsEventuallyValidP X G ∧
    ∀ K ∈ X, ∀ x, IsFullEnumerationP K x → α K ≤ deltaH h (outputSetP G x) K

end LocalBreadth.Supplement


