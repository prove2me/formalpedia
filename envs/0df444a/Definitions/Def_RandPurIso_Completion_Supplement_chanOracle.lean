-- Prove2me | Definitions.Def_RandPurIso_Completion_Supplement_chanOracle
-- name    : RandPurIso_Completion_Supplement_chanOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:49:27.704519+00:00
-- url     : https://prove2.me/theorems/9f7d7493-7470-4cc0-a465-0c24acaed5ea
-- title:
--   Forward query access to a channel (stateless oracle)
-- statement:
--   For a channel $\Phi$ on a finite-dimensional space $X$, the **forward channel oracle** is the stateless oracle of Definition 3.2 (private register trivial) whose map applies $\Phi$ to the query register:
--
--   $$
--   \rho\ \longmapsto\ (\Phi\otimes\mathrm{id}_{\mathsf{St}})(\rho),\qquad \mathsf{St}\ \text{one-dimensional}.
--   $$
--
--   An oracle algorithm run against it makes "forward channel queries" in the sense of §7 (Theorems 7.1, 7.9 and 7.10).
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, §7, pp. 48–58 (forward channel queries); Definition 3.2, p. 17

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_RandPurIso_Completion_Oracle
open Matrix

namespace RandPurIso.Completion.Supplement

open RandPurIso.Completion

/-- **Forward query access to a channel** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, §7, pp. 48–58: "forward channel queries").

The stateless oracle (Definition 3.2 with a trivial private register `St = Unit` in the state
`1`) whose map is `Φ ⊗ id_St`, i.e. one application of the channel `Φ` to the query register. -/
noncomputable def chanOracle {X : Type} (Φ : Matrix X X ℂ → Matrix X X ℂ) : Oracle X X Unit where
  map := PeresTerno.ampliate Φ
  init := fun _ => 1

end RandPurIso.Completion.Supplement


