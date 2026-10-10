-- Prove2me | Definitions.Def_LandauFunction_landau
-- name    : LandauFunction_landau
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:26:47.892421+00:00
-- url     : https://prove2.me/theorems/5420dfaa-3c5a-4433-979e-a745482dca7d
-- title:
--   Landau's function $g(n)$
-- statement:
--   For a natural number $n$, **Landau's function** $g(n)$ is the largest order of an element of the symmetric group $S_n$:
--
--   $$g(n)=\max_{\sigma\in S_n}\operatorname{ord}(\sigma).$$
--
--   All results of this mission are stated in terms of $g$.
--
--   **Formalization Note** $S_n$ is `Equiv.Perm (Fin n)` and the maximum is the supremum `Finset.sup` of `orderOf` over the (nonempty) finite group, so $g(0)=1$.
-- source:
--   Wikipedia, "Landau's function", revision oldid=1303222269 (https://en.wikipedia.org/w/index.php?title=Landau%27s_function&oldid=1303222269), first paragraph (definition).

import Mathlib

namespace LandauFunction

/-- Landau's function `g(n)`: the largest order of an element of the symmetric group `Sₙ`,
realised as the permutation group of `Fin n`. -/
noncomputable def landau (n : ℕ) : ℕ :=
  (Finset.univ : Finset (Equiv.Perm (Fin n))).sup fun σ => orderOf σ

end LandauFunction


