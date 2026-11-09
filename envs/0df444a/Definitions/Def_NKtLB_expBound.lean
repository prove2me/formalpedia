-- Prove2me | Definitions.Def_NKtLB_expBound
-- name    : NKtLB_expBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:56:09.232219+00:00
-- url     : https://prove2.me/theorems/8d30f458-b2c2-4770-af2c-fb70882e00b0
-- title:
--   The time bound $2^{\varepsilon n}$
-- statement:
--   For a real $\varepsilon$, the time bound $T(n)=\lceil 2^{\varepsilon n}\rceil$, used in $\mathsf{NTIME}[2^{\varepsilon n}]\cap\mathsf{coNTIME}[2^{\varepsilon n}]$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 8, p.12

import Mathlib

namespace NKtLB

/-- **The time bound `2^{εn}`** of Theorem 8 (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), p.12), rounded up to a natural number:
`n ↦ ⌈2^{ε n}⌉`. -/
noncomputable def expBound (ε : ℝ) (n : ℕ) : ℕ := ⌈(2 : ℝ) ^ (ε * n)⌉₊

end NKtLB


