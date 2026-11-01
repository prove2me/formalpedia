-- Prove2me | Definitions.Def_MVBlossoms_IsBasalAt
-- name    : MVBlossoms_IsBasalAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:43:07.539363+00:00
-- url     : https://prove2.me/theorems/c98dac7e-9a5c-4ce6-a532-baf67a1bed15
-- title:
--   Basal vertex at stage $t$
-- statement:
--   A vertex $b$ is **basal at stage $t$** if it is the base of some vertex $v$ whose tenacity $s$ is eligible and satisfies $s\le t$.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definitions 21 and 29, pp.2030, 2037

import Mathlib
import Definitions.Def_MVBlossoms_tenacity
import Definitions.Def_MVBlossoms_IsEligible
import Definitions.Def_MVBlossoms_IsBase

namespace MVBlossoms

/-- **Basal vertex at stage t.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definitions 21 (p.2030) and 29 (p.2037): the base
of a vertex of eligible tenacity "will be called a basal vertex". At stage `t` of the induction the
bases defined are those of vertices of eligible tenacity at most `t`.

`IsBasalAt M b t`: `b` is the base of some vertex whose tenacity is an eligible `s ≤ t`. -/
def IsBasalAt {V : Type} [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph) (b : V) (t : ℕ) : Prop :=
  ∃ (v : V) (s : ℕ), IsEligible M s ∧ s ≤ t ∧ tenacity M v = (s : ℕ∞) ∧ IsBase M v b

end MVBlossoms


