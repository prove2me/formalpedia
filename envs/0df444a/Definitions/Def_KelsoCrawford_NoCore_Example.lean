-- Prove2me | Definitions.Def_KelsoCrawford_NoCore_Example
-- name    : KelsoCrawford_NoCore_Example
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:18:55.662639+00:00
-- url     : https://prove2.me/theorems/c9cb9cc9-b292-4bbf-88c9-3b500175e20f
-- title:
--   Section 6 example — two firms j, k and three workers with the printed technologies, σ = 0, u^i(j; s) = s
-- statement:
--   The market of the example of Section 6 has three workers $1, 2, 3$ and two firms $j, k$. Firm $j$'s technology (p. 1502) and firm $k$'s (p. 1503) are
--
--   | $C$ | $\emptyset$ | $\{1\}$ | $\{2\}$ | $\{3\}$ | $\{1,2\}$ | $\{1,3\}$ | $\{2,3\}$ | $\{1,2,3\}$ |
--   |---|---|---|---|---|---|---|---|---|
--   | $y^j(C)$ | $0$ | $4$ | $4$ | $4\tfrac14$ | $7\tfrac12$ | $7$ | $7$ | $9$ |
--   | $y^k(C)$ | $0$ | $4\tfrac14$ | $4$ | $4$ | $7$ | $7$ | $7\tfrac12$ | $9$ |
--
--   so firm $k$'s technology is firm $j$'s with workers $1$ and $3$ interchanged. Every reservation salary is zero, $\sigma_{ij} = \sigma_{ik} = 0$, and utilities are the salaries themselves, as in (23):
--   $$u^i(j; s_{ij}) = s_{ij}, \qquad u^i(k; s_{ik}) = s_{ik}, \qquad i = 1, 2, 3.$$
--
--   This is the paper's example of a market without (GS) whose core is empty.
--
--   **Formalization Note** Workers $1, 2, 3$ are `0, 1, 2 : Fin 3` and firms $j, k$ are `0, 1 : Fin 2`. The technologies are written as a case split on the eight subsets; $4\tfrac14 = 17/4$ and $7\tfrac12 = 15/2$.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1502 (firm j's technology, σ_ij = 0) and p. 1503 (firm k's technology, σ_ik = 0, eq. (23)), Section 6

import Mathlib
import Definitions.Def_KelsoCrawford_NoCore_Model

namespace KelsoCrawford.NoCore

/-- Firm `j`'s technology (p. 1502). Workers 1, 2, 3 of the paper are `0, 1, 2 : Fin 3`. -/
noncomputable def techJ (C : Finset (Fin 3)) : ℝ :=
  if C = ∅ then 0
  else if C = {0} then 4
  else if C = {1} then 4
  else if C = {2} then 17 / 4
  else if C = {0, 1} then 15 / 2
  else if C = {0, 2} then 7
  else if C = {1, 2} then 7
  else 9

/-- Firm `k`'s technology (p. 1503): firm `j`'s with workers 1 and 3 interchanged. -/
noncomputable def techK (C : Finset (Fin 3)) : ℝ :=
  if C = ∅ then 0
  else if C = {0} then 17 / 4
  else if C = {1} then 4
  else if C = {2} then 4
  else if C = {0, 1} then 7
  else if C = {0, 2} then 7
  else if C = {1, 2} then 15 / 2
  else 9

/-- The two-firm, three-worker market of Section 6 (p. 1503). Firm `j` is `0 : Fin 2` and
firm `k` is `1 : Fin 2`; utilities are `u^i(j; s) = s` (eq. (23)) and every reservation salary
is `0`. -/
noncomputable def noCoreMarket : Market (Fin 3) (Fin 2) where
  u := fun _ _ s => s
  y := fun j => if j = 0 then techJ else techK
  σ := fun _ _ => 0

end KelsoCrawford.NoCore


