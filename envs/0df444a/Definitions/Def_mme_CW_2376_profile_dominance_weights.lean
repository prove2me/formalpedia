-- Prove2me | Definitions.Def_mme_CW_2376_profile_dominance_weights
-- name    : mme_CW_2376_profile_dominance_weights
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-24T20:29:53.601382+00:00
-- url     : https://prove2.me/theorems/24deb836-2f8d-42a5-8a73-bc8bf520cfaf
-- title:
--   Integral product weights for the optimized CW profile
-- statement:
--   This module records integral product weights for the optimized squared Coppersmith--Winograd joint profile. With orbit weights $s=699$, $r=37518$, $c=307638$, and $u=616627$, the grade weights are
--
--   $$
--   (q_0,q_1,q_2,q_3,q_4)=(u^2,u^2,cu,rc,sc),
--   $$
--
--   and the common scale is $D=cu^4$. The target joint-type set is the union of the scalar, rectangular, central, and coupled orbits from equation (13).
--
--   For every target type $(i,j,k)$ with base multiplicity $w_{ijk}$, these choices satisfy $q_i q_j q_k=Dw_{ijk}$. This exact product form is the key to proving that the target completion term dominates every feasible joint table with the same three marginals.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), optimized profile equation (13) on journal p. 268; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_profile_address

namespace MME

def cw2376DominanceGradeWeight : Fin 5 → ℕ
  | ⟨0, _⟩ => 616627 ^ 2
  | ⟨1, _⟩ => 616627 ^ 2
  | ⟨2, _⟩ => 307638 * 616627
  | ⟨3, _⟩ => 37518 * 307638
  | ⟨4, _⟩ => 699 * 307638

def cw2376DominanceScale : ℕ := 307638 * 616627 ^ 4

def cw2376TargetJointTypes : Finset (Fin 3 → Fin 5) :=
  cw2376ScalarTypes ∪ cw2376RectTypes ∪
    cw2376CentralTypes ∪ cw2376CoupledTypes

end MME


