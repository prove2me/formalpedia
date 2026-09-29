-- Prove2me | Definitions.Def_RamadgeWonham_Synthesis_Problems
-- name    : RamadgeWonham_Synthesis_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:37:54.513603+00:00
-- url     : https://prove2.me/theorems/f695b9c8-1d26-45ab-beba-5eb9c4713252
-- title:
--   Supervisory Marking Problem (SMP) and Supervisory Control Problem (SCP) (§7, p. 217)
-- statement:
--   Let $\mathcal G$ be a generator with controllable events $\Sigma_c$, and let $L_a, L_g \subseteq \Sigma^*$ be the **minimal acceptable** and **legal** languages (in the paper, $\emptyset \neq L_a \subseteq L_g \subseteq L_m(\mathcal G)$). A supervisor $\mathcal S = (S, \phi)$ with accessible automaton $S$
--
--   1. **solves the Supervisory Marking Problem (SMP)** if $\mathcal S$ is proper and
--   $$L_a \subseteq L_m(\mathcal S/\mathcal G) \subseteq L_g;$$
--   2. **solves the Supervisory Control Problem (SCP)** if $\mathcal S$ is proper and
--   $$L_a \subseteq L_c(\mathcal S/\mathcal G) \subseteq L_g.$$
--
--   SMP (respectively SCP) is **solvable** when some supervisor solves it.
--
--   **Formalization Note.** The accessibility of $S$ is the paper's standing assumption on supervisors (p. 210), included as a conjunct. The conditions on $L_a, L_g$ are hypotheses of the theorems that use these predicates, not part of the predicates.
-- source:
--   Ramadge and Wonham, Supervisory Control of a Class of Discrete Event Processes, SIAM J. Control Optim. 25(1), 1987, p. 217, §7, definitions of SMP and SCP

import Mathlib
import Definitions.Def_RamadgeWonham_Shared_Supervisor

namespace RamadgeWonham.Synthesis

variable {α : Type} {Ec : Set α}

/-- `𝒮` solves the Supervisory Marking Problem (SMP) for `𝒢`, `L_a`, `L_g` (§7, p. 217): `𝒮` is a
proper supervisor (with accessible automaton `S`, the standing assumption of p. 210) and
`L_a ⊆ L_m(𝒮/𝒢) ⊆ L_g`. -/
def SolvesSMP (G : Shared.Generator α) (La Lg : Set (List α)) (𝒮 : Shared.Supervisor α Ec) : Prop :=
  𝒮.S.Accessible ∧ Shared.Proper G 𝒮 ∧ La ⊆ Shared.Lmsup G 𝒮 ∧ Shared.Lmsup G 𝒮 ⊆ Lg

/-- `𝒮` solves the Supervisory Control Problem (SCP) for `𝒢`, `L_a`, `L_g` (§7, p. 217): `𝒮` is a
proper supervisor (with accessible automaton `S`) and `L_a ⊆ L_c(𝒮/𝒢) ⊆ L_g`. -/
def SolvesSCP (G : Shared.Generator α) (La Lg : Set (List α)) (𝒮 : Shared.Supervisor α Ec) : Prop :=
  𝒮.S.Accessible ∧ Shared.Proper G 𝒮 ∧ La ⊆ Shared.Lcsup G 𝒮 ∧ Shared.Lcsup G 𝒮 ⊆ Lg

end RamadgeWonham.Synthesis


