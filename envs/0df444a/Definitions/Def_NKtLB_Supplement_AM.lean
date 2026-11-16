-- Prove2me | Definitions.Def_NKtLB_Supplement_AM
-- name    : NKtLB_Supplement_AM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:28:05.515074+00:00
-- url     : https://prove2.me/theorems/309382dc-99e1-4246-b51a-89b1cabc1089
-- title:
--   $\mathsf{AM}$
-- statement:
--   $\mathsf{AM}=\bigcup_{k\in\mathbb N}\mathsf{AMTIME}[n^k]$, the languages with polynomial-time public-coin Arthur–Merlin protocols.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 9 item 3, p.13

import Mathlib
import Definitions.Def_NKtLB_Supplement_AMTIME

namespace NKtLB.Supplement

/-- **`AM`** (used in Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorem 9 item 3, p.13): `⋃_k AMTIME[n^k]`. -/
def AM : Set (Set (List Bool)) := {L | ∃ k : ℕ, L ∈ AMTIME (fun n => n ^ k)}

end NKtLB.Supplement


