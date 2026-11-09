-- Prove2me | Definitions.Def_SqrtQueries_smearA
-- name    : SqrtQueries_smearA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:29:35.021762+00:00
-- url     : https://prove2.me/theorems/2ab8a777-af1a-40ed-8738-3210fbb90761
-- title:
--   The Hermitian matrix $A=(S+S^\dagger)/2$
-- statement:
--   For an integer $N\ge1$ let $S$ be the shift operator on $\mathbb C^N$ and $S^\dagger$ its conjugate transpose. Define
--   $$
--   A=\frac{S+S^\dagger}{2}.
--   $$
--   $A$ is real symmetric; for $N\ge3$ its entries are $\tfrac12$ at the cyclically adjacent positions $(j\pm1,j)$ and $0$ elsewhere.
--
--   Conjugating the clock operator by $e^{iA/4}$ "smears" it: this produces the NOTDIAG oracle $U_1$ of Definition 3.2.
-- source:
--   Ma–Tang, Square-root queries can help, STOC 2027 submission (manuscript sha256 783868e7…c5f15a), Definition 3.2, p.16

import Mathlib
import Definitions.Def_SqrtQueries_shiftOp

namespace SqrtQueries

open Matrix

/-- The Hermitian matrix `A = (S + S†)/2` of Definition 3.2 (Ma–Tang, *Square-root queries can
help*, STOC 2027 submission manuscript, sha256 783868e7…c5f15a, Definition 3.2, p.16), where `S`
is the shift operator of Section 2.1 and `S† = Sᴴ` its conjugate transpose. -/
noncomputable def smearA (N : ℕ) [NeZero N] : Matrix (Fin N) (Fin N) ℂ :=
  (1 / 2 : ℂ) • (shiftOp N + (shiftOp N)ᴴ)

end SqrtQueries


