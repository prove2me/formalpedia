-- Prove2me | Definitions.Def_PersuadeFly_persSet
-- name    : PersuadeFly_persSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:29:51.638043+00:00
-- url     : https://prove2.me/theorems/c1748678-8b1f-4a53-a8ae-3d0f8040fdba
-- title:
--   Robustly persuasive mechanisms $\mathsf{Pers}(\mathcal B)$
-- statement:
--   For a set $\mathcal B$ of distributions,
--   $$
--   \mathsf{Pers}(\mathcal B)=\bigcap_{\mu\in\mathcal B}\mathsf{Pers}(\mu),
--   $$
--   the mechanisms that are persuasive under every distribution in $\mathcal B$.
--
--   **Formalization Note** The intersection is taken inside the set $\mathcal S$ of mechanisms, so $\mathsf{Pers}(\emptyset)=\mathcal S$.
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, §3, p.21; Definition 2, p.17

import Mathlib
import Definitions.Def_PersuadeFly_pers

namespace PersuadeFly

/-- **Robustly persuasive mechanisms `Pers(B)`.** Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, §3, p.21 (and Definition 2, p.17):
`Pers(B) = ∩_{μ ∈ B} Pers(μ)`, the mechanisms persuasive under every distribution in `B`.

**Formalization Note** The intersection is taken inside the set `S` of mechanisms, so `Pers(∅) = S`. -/
def persSet {Ω A : Type} [Fintype Ω] [Fintype A] (I : Instance Ω A) (B : Set (Ω → ℝ)) :
    Set (Ω → A → ℝ) :=
  {σ | IsMechanism σ ∧ ∀ μ ∈ B, σ ∈ pers I μ}

end PersuadeFly


