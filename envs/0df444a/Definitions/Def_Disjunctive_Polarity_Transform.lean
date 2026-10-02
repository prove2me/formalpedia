-- Prove2me | Definitions.Def_Disjunctive_Polarity_Transform
-- name    : Disjunctive_Polarity_Transform
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T16:14:58.413549+00:00
-- url     : https://prove2.me/theorems/ed059d9d-3624-48b9-91d7-5d5041038b36
-- title:
--   Dropping the auxiliary coordinate of a transformed projection cone
-- statement:
--   This definition names the one projection operation Proposition 2.11 needs beyond
--   `ProjOntoX`: dropping an auxiliary coordinate `w` from a cone living in `(v,w,v0)`-space.
--
--   Given a subset $S \subseteq \mathbb{R}^q \times \mathbb{R}^w \times \mathbb{R}$, its
--   projection onto the $(v,v_0)$-coordinates is
--   $\mathrm{Proj}_{(v,v_0)}(S) := \{(v,v_0) : \exists\, w,\ (v,w,v_0) \in S\}$.
--
--   This is used to state Proposition 2.11's characterization of the facets of $\mathrm{Proj}_x(Q)$
--   via the extreme rays of $\mathrm{Proj}_{(v,v_0)}(\tilde W)$, where $\tilde W$ is the projection
--   cone of a transformed polyhedron $\tilde Q$ cited from [14].
--
--   **Formalization Note.** This is the same "drop a coordinate via an existential" idea as
--   `ProjOntoX`, specialized to the three-coordinate space `(Fin q → ℝ) × (Fin w → ℝ) × ℝ`.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 32, Section 2.3

import Mathlib

namespace Disjunctive.Polarity

/-- The projection of a subset of `(Fin q → ℝ) × (Fin w → ℝ) × ℝ` onto its `(v, v0)`-components,
dropping the auxiliary `w`-coordinate (Balas §2.3, p. 32: `Proj_{(v,v0)}(W̃)`). -/
def ProjVW {q w : ℕ} (S : Set ((Fin q → ℝ) × (Fin w → ℝ) × ℝ)) : Set ((Fin q → ℝ) × ℝ) :=
  {p | ∃ ww : Fin w → ℝ, (p.1, ww, p.2) ∈ S}

end Disjunctive.Polarity


