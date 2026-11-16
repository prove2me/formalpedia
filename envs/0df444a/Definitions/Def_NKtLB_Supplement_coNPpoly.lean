-- Prove2me | Definitions.Def_NKtLB_Supplement_coNPpoly
-- name    : NKtLB_Supplement_coNPpoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:32:18.765684+00:00
-- url     : https://prove2.me/theorems/f31c9311-9120-41f0-8326-b58cf3cb64e1
-- title:
--   $\mathsf{coNP}/\mathsf{poly}$
-- statement:
--   $\mathsf{coNP}/\mathsf{poly}=\{L : \overline L\in\mathsf{NP}/\mathsf{poly}\}$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorems 4, 5, 80, 82

import Mathlib
import Definitions.Def_NKtLB_Supplement_NPpoly

namespace NKtLB.Supplement

/-- **`coNP/poly`**: the complements of the languages in `NP/poly` (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorems 4, 5, 80, 82). -/
def coNPpoly : Set (Set (List Bool)) := {L | Lᶜ ∈ NPpoly}

end NKtLB.Supplement


