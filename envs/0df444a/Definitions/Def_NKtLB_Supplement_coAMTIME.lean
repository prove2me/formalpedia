-- Prove2me | Definitions.Def_NKtLB_Supplement_coAMTIME
-- name    : NKtLB_Supplement_coAMTIME
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:27:33.697044+00:00
-- url     : https://prove2.me/theorems/c053e401-7014-4bdb-b2f2-6398007f1af7
-- title:
--   $\mathsf{coAMTIME}[T]$
-- statement:
--   $\mathsf{coAMTIME}[T(n)]=\{L : \overline L\in\mathsf{AMTIME}[T(n)]\}$, the complements of Arthur–Merlin languages.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 9, pp.12–13

import Mathlib
import Definitions.Def_NKtLB_Supplement_AMTIME

namespace NKtLB.Supplement

/-- **`coAMTIME[T(n)]`**: the complements of the languages in `AMTIME[T(n)]` (used in Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026),
Theorem 9, pp.12–13). -/
def coAMTIME (T : ℕ → ℕ) : Set (Set (List Bool)) := {L | Lᶜ ∈ AMTIME T}

end NKtLB.Supplement


