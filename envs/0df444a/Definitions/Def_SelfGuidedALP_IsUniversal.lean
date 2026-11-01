-- Prove2me | Definitions.Def_SelfGuidedALP_IsUniversal
-- name    : SelfGuidedALP_IsUniversal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:26:35.793999+00:00
-- url     : https://prove2.me/theorems/c0c25a8c-0ac8-4abf-a51a-062f501aee3d
-- title:
--   Universal random basis functions (Definition 1)
-- statement:
--   A class of random basis functions is **universal** when for every continuous $V:\mathcal S\to\mathbb R$ and every $\varepsilon>0$ there is $\boldsymbol\beta_\varepsilon=(\beta_{0,\varepsilon},B_\varepsilon)$ with $V(\boldsymbol\beta_\varepsilon)\in\mathcal R$ and
--   $$
--   \|V-V(\boldsymbol\beta_\varepsilon)\|_\infty<\varepsilon .
--   $$
--
--   This is the approximation power that makes $V^*\in\mathcal R$ a mild assumption.
--
--   **Formalization Note** The requirement is stated pointwise on $\mathcal S$ rather than through a supremum. The pointwise requirement for every $\varepsilon>0$ and the requirement on the maximum for every $\varepsilon>0$ are the same condition.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Definition 1, p.9

import Mathlib
import Definitions.Def_SelfGuidedALP_MDP
import Definitions.Def_SelfGuidedALP_intVFA

namespace SelfGuidedALP

/-- The class of random basis functions is universal on `𝒮`: every continuous `V : 𝒮 → ℝ` is
approximated by some `V(·;𝛃_ε) ∈ ℛ` within `ε` in the `∞`-norm
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Definition 1, p.9).

**Formalization Note.** `‖V‖_∞ := max_{s∈𝒮} |V(s)|`, and the requirement is stated pointwise on `𝒮`
to avoid a real `sSup`. Pointwise `< ε` for every `ε > 0` and `max < ε` for every `ε > 0` are the same
condition. -/
def IsUniversal {d m : ℕ} (M : MDP d m) (R : RBClass d) : Prop :=
  ∀ V : EuclideanSpace ℝ (Fin d) → ℝ, ContinuousOn V M.S → ∀ ε > 0,
    ∃ (β₀ : ℝ) (B : Bspace R), ∀ s ∈ M.S, |V s - intVFA R β₀ B s| < ε

end SelfGuidedALP


