-- Prove2me | Definitions.Def_NSWBetter_WellBehavedAgent
-- name    : NSWBetter_WellBehavedAgent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:56:56.231772+00:00
-- url     : https://prove2.me/theorems/e1619f9e-bfc2-409b-870f-9f485e26e959
-- title:
--   Well-behaved agent (Definition 4.14)
-- statement:
--   $x$ is **well-behaved for agent $i$** if $i$ has the small good fraction property in $x$ and the artificial instance $I_{i,x}(\Delta)$ is well-behaved for every feasible $\Delta$.
--
--   **Formalization Note** "Every feasible $\Delta$" is taken as every $\Delta\ge1$ with all $\Delta x_{ig}$ integral (the $\Delta$ for which $I_{i,x}(\Delta)$ exists). By Lemma 4.12 this is the same predicate for rational $x$, and it does not depend on the rounding scheme.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Definition 4.14, p.25

import Mathlib
import Definitions.Def_NSWBetter_WellBehaved
import Definitions.Def_NSWBetter_artificial
import Definitions.Def_NSWBetter_SmallGoodFrac

namespace NSWBetter

/-- **Well-behaved agents (Definition 4.14).**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Definition 4.14, p.25: "We say that x is well-behaved for an agent i if i satisfies the small good fraction property in x and the artificial instance for agent i, Ii,x(∆), is well-behaved for all feasible ∆ with respect to x."

**Formalization Note.** The artificial instance is required to be well-behaved for every `Δ ≥ 1` for which it is defined, i.e. every `Δ x_ig` is an integer. Every feasible `Δ` (Definition 4.1) is such a `Δ`, and by Lemma 4.12 (whose argument uses only the instance) well-behavedness is the same for all of them; for rational `x` feasible `Δ` exist, so the predicate is the paper's. This form does not depend on the rounding scheme or on the order of tied goods. -/
def WellBehavedAgent {n m : ℕ} (v : Fin n → Fin m → ℝ) (x : Fin n → Fin m → ℝ) (i : Fin n) : Prop :=
  SmallGoodFrac v x i ∧
  ∀ Δ : ℕ, 1 ≤ Δ → (∀ g, ∃ k : ℕ, (Δ : ℝ) * x i g = k) → WellBehaved Δ (artificial v x i Δ)

end NSWBetter


