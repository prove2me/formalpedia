-- Prove2me | Definitions.Def_LawLocalComp_Resource_params
-- name    : LawLocalComp_Resource_params
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:10:57.151979+00:00
-- url     : https://prove2.me/theorems/37f45426-1027-417c-940a-713e828e8af4
-- title:
--   Resource as a list of numbers
-- statement:
--   For machine input a resource is written as a tag ($0$ horizon, $1$ rank, $2$ both) followed by the supplied numbers $N$, $q$.
--
--   **Formalization Note** These numbers are later written in binary, so running times may depend on $\log N$ and $\log q$ but not on $N$, $q$.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Theorem 1.1, p.2

import Mathlib
import Definitions.Def_LawLocalComp_Resource

namespace LawLocalComp

/-- **The resource as machine input.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Theorem 1.1, p.2 ("polynomial in input bits, 1/ε and logarithmic supplied resources").

A tag (`0` horizon, `1` rank, `2` both) followed by the supplied numbers, written later in binary.

**Formalization Note.** The numbers are encoded in binary by `RobustToDynamics.encListRat`, so the
machine's running time may depend on `log N` and `log q`, never on `N` or `q`. -/
def Resource.params : Resource → List ℚ
  | .horizon N => [0, (N : ℚ)]
  | .rank q => [1, (q : ℚ)]
  | .both N q => [2, (N : ℚ), (q : ℚ)]

end LawLocalComp


