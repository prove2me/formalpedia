-- Prove2me | Definitions.Def_CEPolytopeHard_MLGame_Valid
-- name    : CEPolytopeHard_MLGame_Valid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:18.852038+00:00
-- url     : https://prove2.me/theorems/4bee800d-ea47-41a2-9ca9-a4f6e15d3594
-- title:
--   Valid multilinear polytope game
-- statement:
--   A multilinear polytope game is **valid** when
--
--   1. its representation is well formed;
--   2. every strategy set $X_i$ is a nonempty bounded (hence compact) polytope;
--   3. every utility maps the profile set $X = X_1 \times \cdots \times X_n$ into $[0, 1]$: $u_i(x) \in [0, 1]$ for all $x \in X$.
--
--   These are the requirements of Section 2.3: "each $X_i$ is a compact polytope" and "a function $u_i : X \to [0, 1]$ defines the utility of player $i$". They are promises on the instance: Theorem 4 is about games satisfying them.
--
--   **Formalization Note** A polytope given by finitely many non-strict inequalities is closed, so compactness is boundedness; nonemptiness is part of being a strategy set.
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Section 2.3, p.11

import Mathlib
import Definitions.Def_CEPolytopeHard_MLGame

set_option autoImplicit false

namespace CEPolytopeHard

/-- A **valid** multilinear polytope game (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang,
*The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version
of November 2, 2026, sha256 6aec500a…7820, Section 2.3, p.11): the representation is well formed,
each strategy set `X_i` is a compact polytope (nonempty and bounded), and each utility maps the
profile set `X = X_1 × ⋯ × X_n` into `[0, 1]` ("a function `u_i : X → [0, 1]` defines the utility
of player i").

**Formalization Note** A polytope given by finitely many non-strict inequalities is closed, so
"compact" is "bounded"; nonemptiness is part of being a strategy set. The range `[0, 1]` is a
promise on the instance, as in Section 2.1 ("our negative results will only contain instances in
which the promise holds"). -/
def MLGame.Valid (G : MLGame) : Prop :=
  G.WellFormed ∧
  (∀ i, (G.strategySet i).Nonempty ∧ Bornology.IsBounded (G.strategySet i)) ∧
  ∀ x : G.Profile, (∀ i, x i ∈ G.strategySet i) → ∀ i, G.utility i x ∈ Set.Icc (0 : ℝ) 1

end CEPolytopeHard


