-- Prove2me | Definitions.Def_AvoidPlast_haltTime
-- name    : AvoidPlast_haltTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:44:11.186783+00:00
-- url     : https://prove2.me/theorems/466b6734-4858-4e2f-a090-8f0536bec1a2
-- title:
--   Running time
-- statement:
--   The running time: the first step count at which the run is in a halting state.
--
--   **Formalization Note** On a non-halting run the value is the junk $0$. Every class of the mission requires halting or bounds the time before it reads the running time, the output, the work space or the queries.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Section 3, machine model, p.13

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_HaltsWithin

namespace AvoidPlast

/-- The running time: the first step count at which the run is in a halting state (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), §3, p.13,
the machine model).

**Formalization Note** On a non-halting run `sInf ∅ = 0`. Every class in this development requires
halting (or bounds the time) before it reads `haltTime`, `output`, `workSpace` or `queries`. -/
noncomputable def haltTime {r : ℕ} (M : Machine r) (xs : Fin r → List Bool) : ℕ :=
  sInf {t | HaltsWithin M xs t}

end AvoidPlast


