-- Prove2me | Definitions.Def_OfflineToOnline_IsBlackwellReducible
-- name    : OfflineToOnline_IsBlackwellReducible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:34:19.455993+00:00
-- url     : https://prove2.me/theorems/8e209516-bfab-425f-8b89-980c021ff66a
-- title:
--   Blackwell reducibility of Offline-IG
-- statement:
--   An instance of Algorithm 1 is **Blackwell reducible** via a Blackwell game $(\mathcal X,\mathcal Y,\boldsymbol p)$ and a **synthetic Blackwell adversary** $\mathrm{AdvB}:\mathcal D\times\mathcal F\to\mathcal Y$ if
--
--   1. the player 1 action space is the parameter space, $\mathcal X=\Theta$, and $\Theta$ and $\mathcal Y$ are compact and convex, $\Theta$ nonempty, and $\boldsymbol p$ is biaffine on $\Theta\times\mathcal Y$;
--   2. $\mathrm{AdvB}(z,f)\in\mathcal Y$ and $\textsc{Payoff}(\theta,z,f)=\boldsymbol p\big(\theta,\mathrm{AdvB}(z,f)\big)$ for all $\theta\in\Theta$, $z\in\mathcal D$, $f\in\mathcal F$;
--   3. the nonnegative orthant $S=\{u\in\mathbb R^{d_{\mathrm{payoff}}}:[u]_j\ge0\}$ is response-satisfiable.
--
--   Reducibility turns the local optimization step of each subproblem into a Blackwell game whose target is the orthant.
--
--   **Formalization Note** $\mathcal Y$, $\boldsymbol p$ and $\mathrm{AdvB}$ are arguments of the predicate rather than existentially quantified, because Theorem 2's bound involves $D(\boldsymbol p)$. The action space $\Theta$ is required nonempty.
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, Definition 7, p.18

import Mathlib
import Definitions.Def_OfflineToOnline_IGInstance
import Definitions.Def_OfflineToOnline_IsBiaffineOn
import Definitions.Def_OfflineToOnline_IsResponseSatisfiable
import Definitions.Def_OfflineToOnline_orthant

namespace OfflineToOnline

/-- Blackwell reducibility, Definition 7, p.18: there is a Blackwell game `(X, Y, p)` with `X = Θ`,
`X`, `Y` compact and convex, `p` biaffine, and a synthetic Blackwell adversary
`AdvB : D × F → Y` such that `Payoff(θ, z, f) = p(θ, AdvB(z, f))` for `θ ∈ Θ`, `z ∈ D`, `f ∈ F`,
and the nonnegative orthant is response-satisfiable.

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, Definition 7, p.18 (with the Blackwell game of Definition 3's paragraph, p.11).

Formalization Note: `Y`, `p` and `AdvB` are arguments, not existentially quantified, because
Theorem 2's bound involves `D(p)`. The action space `X = Θ` is required nonempty. -/
def IsBlackwellReducible {D Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω] {m k d : ℕ}
    (I : IGInstance D Ω m d) (Y : Set (Fin k → ℝ)) (p : (Fin m → ℝ) → (Fin k → ℝ) → (Fin d → ℝ))
    (AdvB : D → (D → ℝ) → (Fin k → ℝ)) : Prop :=
  IsCompact I.Θ ∧ Convex ℝ I.Θ ∧ I.Θ.Nonempty ∧ IsCompact Y ∧ Convex ℝ Y ∧ IsBiaffineOn I.Θ Y p ∧
    (∀ z, ∀ f ∈ I.F, AdvB z f ∈ Y) ∧
    (∀ θ ∈ I.Θ, ∀ z, ∀ f ∈ I.F, I.payoff θ z f = p θ (AdvB z f)) ∧
    IsResponseSatisfiable I.Θ Y p (orthant d)

end OfflineToOnline


