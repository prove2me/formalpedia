-- Prove2me | Definitions.Def_NKtLB_Supplement_coAM
-- name    : NKtLB_Supplement_coAM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:28:45.060748+00:00
-- url     : https://prove2.me/theorems/b6f7fb60-4e72-4368-815b-e7e78fc468c4
-- title:
--   $\mathsf{coAM}$
-- statement:
--   $\mathsf{coAM}=\{L : \overline L\in\mathsf{AM}\}$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 9 item 3, p.13

import Mathlib
import Definitions.Def_NKtLB_Supplement_AM

namespace NKtLB.Supplement

/-- **`coAM`** (used in Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorem 9 item 3, p.13): the complements of the languages in `AM`. -/
def coAM : Set (Set (List Bool)) := {L | Lᶜ ∈ AM}

end NKtLB.Supplement


