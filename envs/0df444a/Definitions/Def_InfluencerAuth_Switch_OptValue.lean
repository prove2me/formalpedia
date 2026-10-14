-- Prove2me | Definitions.Def_InfluencerAuth_Switch_OptValue
-- name    : InfluencerAuth_Switch_OptValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:27.806981+00:00
-- url     : https://prove2.me/theorems/9afa2979-4d3b-4062-a713-24f5b8dd71db
-- title:
--   §3.3, p. 5 — the value function V(A) as the supremum of discounted profit over admissible policies
-- statement:
--   The **value function** $V(A_0)$ of §3.3 is the value "if the influencer starts with awareness level $A_0$ and always follows the optimal policy". In the setting of the module `Model`, it is defined as the supremum of the discounted profit over all admissible policy–path pairs from $A_0$:
--   $$
--   V(A_0)=\sup\big\{J(S,A)\;:\;(S,A)\ \text{admissible from } A_0\big\}.
--   $$
--   It is the object of Lemma 1, which bounds how fast $V$ can increase in awareness once more than half of the potential followers know the influencer.
--
--   **Formalization Note** The supremum is Lean's real `sSup`, which returns $0$ on an empty or unbounded set. For $A_0\in[0,1]$ the set is nonempty (a constant policy has an admissible path) and bounded above by $\gamma\varphi/r$, because every admissible path takes values in $[0,1]$; the mission only evaluates $V$ at $A_0\in(0,1)$.
-- source:
--   Nistor, Selove, Villas-Boas, Management Science (Articles in Advance 2024), §3.3, p. 5

import Mathlib
import Definitions.Def_InfluencerAuth_Switch_Model

namespace InfluencerAuth.Switch

/-- The value function `V(A₀)` of §3.3 (p. 5): the supremum of the discounted profit over all
admissible policy–path pairs started at awareness `A₀`. For `A₀ ∈ [0, 1]` the set is nonempty
(a constant policy has a path) and bounded above by `γ φ / r` (paths take values in `[0, 1]`),
so the real supremum is the genuine one there; statements use it only for `A₀ ∈ (0, 1)`. -/
noncomputable def optValue (β γ φ r A₀ : ℝ) : ℝ :=
  sSup {J : ℝ | ∃ (S : Set ℝ) (A : ℝ → ℝ), IsPath β γ A₀ S A ∧ J = discountedProfit γ φ r S A}

end InfluencerAuth.Switch


