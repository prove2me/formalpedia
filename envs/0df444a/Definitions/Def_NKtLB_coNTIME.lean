-- Prove2me | Definitions.Def_NKtLB_coNTIME
-- name    : NKtLB_coNTIME
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:08:18.827777+00:00
-- url     : https://prove2.me/theorems/84099f67-f9e0-4cb6-8f34-72915c12e29c
-- title:
--   $\mathsf{coNTIME}[T(n)]$
-- statement:
--   $\mathsf{coNTIME}[T(n)]=\{L : \{0,1\}^*\setminus L\in\mathsf{NTIME}[T(n)]\}$, the class of complements of languages in $\mathsf{NTIME}[T(n)]$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 8, p.12 (standard class)

import Mathlib
import Definitions.Def_NKtLB_NTIME

namespace NKtLB

/-- **`coNTIME[T(n)]`**: the complements of the languages in `NTIME[T(n)]` (used in Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026),
Theorem 8, p.12). -/
def coNTIME (T : ℕ → ℕ) : Set (Set (List Bool)) := {L | Lᶜ ∈ NTIME T}

end NKtLB


