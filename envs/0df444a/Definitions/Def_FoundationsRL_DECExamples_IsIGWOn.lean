-- Prove2me | Definitions.Def_FoundationsRL_DECExamples_IsIGWOn
-- name    : FoundationsRL_DECExamples_IsIGWOn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:20:04.856328+00:00
-- url     : https://prove2.me/theorems/64dadc9e-4e9b-4cb7-b587-b726836cd581
-- title:
--   Inverse gap weighting (3.36) restricted to a finite set of decisions $\Pi'$
-- statement:
--   Let $\Pi'\subseteq\Pi$ be finite with $|\Pi'|=A$, let $\widehat f:\Pi\to\mathbb R$ and $\gamma\ge0$. A distribution $p$ on $\Pi$ is **inverse gap weighting applied to $\widehat f$, restricted to $\Pi'$** if $p$ vanishes outside $\Pi'$ and on $\Pi'$
--
--   $$
--   p(\pi)=\frac{1}{\lambda+2\gamma\big(\widehat f(\widehat\pi)-\widehat f(\pi)\big)},\qquad\pi\in\Pi',
--   $$
--
--   where $\widehat\pi$ maximizes $\widehat f$ over $\Pi'$ and $\lambda\in[1,A]$ makes $p$ sum to one. This is the distribution of step 2 of Proposition 18.
--
--   **Formalization Note** The definition enumerates $\Pi'$ by $\{0,\dots,A-1\}$ and requires the published `FoundationsRL.Contextual.IsIGW` (Definition 4) of the vector $(\widehat f(\pi))_{\pi\in\Pi'}$; the enumeration does not matter. Distributions are `PMF`, and the values compared with (3.36) are their real parts.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Definition 4, (3.36), p. 50; Proposition 18, step 2, p. 74

import Mathlib
import Definitions.Def_FoundationsRL_Contextual_IsIGW

namespace FoundationsRL.DECExamples

/-- `p` is the result of applying the inverse gap weighting strategy (3.36) with parameter `γ` to
`f̂`, restricted to the finite decision space `D'`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Proposition 18, step 2, p. 74, with (3.36), p. 50.

**Formalization Note.** `p` has support in `D'`, and along an enumeration `e` of `D'` it is the
published `FoundationsRL.Contextual.IsIGW` distribution of the vector `f̂ ∘ e`. The enumeration does
not matter: the normalizer `λ`, and so `p`, is determined by `f̂` on `D'`. -/
def IsIGWOn {D : Type*} (D' : Finset D) (fhat : D → ℝ) (γ : ℝ) (p : PMF D) : Prop :=
  (∀ π, π ∉ D' → p π = 0) ∧
    ∃ (e : Fin D'.card ≃ D') (bstar : Fin D'.card),
      FoundationsRL.Contextual.IsIGW D'.card (fun i => fhat (e i)) γ bstar
        (fun i => (p (e i)).toReal)

end FoundationsRL.DECExamples


