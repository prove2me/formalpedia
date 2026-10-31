-- Prove2me | Definitions.Def_FirstChoiceDesign_First
-- name    : FirstChoiceDesign_First
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:24:23.097344+00:00
-- url     : https://prove2.me/theorems/d6159f0d-af9c-4c3e-b440-c56c83c8697a
-- title:
--   Assignment indicator $D_{is}(r)$ and the set $\mathit{First}_s(r)$
-- statement:
--   $D_{is}(r)=1$ if student $i$ is assigned school $s$ under lottery number profile $r$ in problem $X$. The **first-choice set** is
--
--   $$
--   \mathit{First}_s(r)=\{i\in I\mid \mathrm{rank}_{is}=1\text{ and }\exists i'\text{ such that }\mathrm{rank}_{i's}=1,\ \rho_{is}=\rho_{i's},\text{ and }D_{is}(r)\ne D_{i's}(r)\},
--   $$
--
--   the students who rank $s$ first and are in a priority group at $s$ where some are assigned $s$ and others are not. It may be empty.
--
--   **Formalization Note** `D` is a proposition and `First` a set. $D_{is}(r)\neq D_{i's}(r)$ is `¬ (D .. ↔ D ..)`.
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), §3, pp.9–10

import Definitions.Def_FirstChoiceDesign_Problem
import Definitions.Def_FirstChoiceDesign_outcome

namespace FirstChoiceDesign

/-- `D_is(r) = 1`: student `i` is assigned school `s` at lottery numbers `r` in problem `X`, p.9. -/
def D {n m : ℕ} (φ : GDA) (X : Problem (φ.K n) n m) (i : Fin n) (s : Fin m) (r : Lottery n m) :
    Prop :=
  outcome φ X.toSetting X.ρ r i = some s

/-- `First_s(r) = {i ∈ I | rank_is = 1 and ∃ i' such that rank_i's = 1, ρ_is = ρ_i's, and
D_is(r) ≠ D_i's(r)}`, p.10. It may be empty (footnote 12). -/
def First {n m : ℕ} (φ : GDA) (X : Problem (φ.K n) n m) (s : Fin m) (r : Lottery n m) :
    Set (Fin n) :=
  {i | X.rank i s = 1 ∧ ∃ i', X.rank i' s = 1 ∧ X.ρ i s = X.ρ i' s ∧ ¬(D φ X i s r ↔ D φ X i' s r)}

end FirstChoiceDesign


