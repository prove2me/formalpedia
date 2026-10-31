-- Prove2me | Definitions.Def_FirstChoiceDesign_Problem
-- name    : FirstChoiceDesign_Problem
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:54.578443+00:00
-- url     : https://prove2.me/theorems/7055041d-f606-41ae-ba90-f8c6a1c1062a
-- title:
--   Assignment problem $X$
-- statement:
--   An **assignment problem** is $X=(I,S,\succ_I,(c_s)_{s\in S},(\rho_s)_{s\in S})$: students, schools, preferences and capacities, together with a coarse priority $\rho_{is}\in\{1,\dots,K\}$ of each student at each school, where $\rho_{is}<\rho_{js}$ means that $s$ prioritizes $i$ over $j$. Every student is acceptable to every school. Priorities may be coarse: $\rho_{is}=\rho_{js}$ is possible for $i\ne j$.
--
--   **Formalization Note** `Problem K n m` extends `Setting n m`. The bound `K` is a parameter; statements use `φ.K n`.
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), §2, p.6

import Definitions.Def_FirstChoiceDesign_GDA

namespace FirstChoiceDesign

/-- An assignment problem `X = (I, S, ≻_I, (c_s)_{s ∈ S}, (ρ_s)_{s ∈ S})`, §2, p.6, with priorities
`ρ_is ∈ {1, …, K}`, where a smaller value is a better status. `K` is the number of priority
statuses, for the student count at hand. -/
structure Problem (K n m : ℕ) extends Setting n m where
  ρ : Fin n → Fin m → ℕ
  ρ_mem : ∀ i s, 1 ≤ ρ i s ∧ ρ i s ≤ K

end FirstChoiceDesign


