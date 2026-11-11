-- Prove2me | Definitions.Def_RandPurIso_Completion_Oracle
-- name    : RandPurIso_Completion_Oracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:26:07.455847+00:00
-- url     : https://prove2.me/theorems/c79f5b23-1c7b-4db2-9a1b-0f42a771c811
-- title:
--   Stateful oracle (Definition 3.2)
-- statement:
--   An **oracle** mapping a register $\mathsf{In}$ to a register $\mathsf{Out}$ is a map
--   $$O:\mathbf L(\mathsf{In}\otimes\mathsf{St})\to\mathbf L(\mathsf{Out}\otimes\mathsf{St})$$
--   together with an initial state $|\varphi_0\rangle$ of a private register $\mathsf{St}$. The private register persists between queries and is never seen by the algorithm.
--
--   **Formalization Note** The structure carries the data only. Every oracle used by the mission's theorems is built by an explicit construction (a contraction channel or a realized circuit); no theorem quantifies over arbitrary oracles, and unit norm of a free initial state is a hypothesis where it occurs.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Definition 3.2, p. 17

import Mathlib
open Matrix

namespace RandPurIso.Completion

/-- **Stateful oracle** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Definition 3.2, p. 17): a map
`O : L(In ⊗ St) → L(Out ⊗ St)` together with an initial state `|φ₀⟩` of the private register `St`.

**Formalization Note.** The structure holds the data only (`map`, `init`). Definition 3.2 also asks
that `map` be CPTP and `init` a unit vector; every oracle that the mission's theorems use is
built by an explicit construction (`contractionOracle`, `StatefulCirc.realize`) and the unit-norm
condition on initial states is a hypothesis where an initial state is a free variable. No theorem
quantifies over arbitrary `Oracle`s. -/
structure Oracle (In Out St : Type) where
  /-- the map `L(In ⊗ St) → L(Out ⊗ St)` -/
  map : Matrix (In × St) (In × St) ℂ → Matrix (Out × St) (Out × St) ℂ
  /-- the initial state `|φ₀⟩` of the private register -/
  init : St → ℂ

end RandPurIso.Completion


