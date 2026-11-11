-- Prove2me | Definitions.Def_PermInvCC_BS
-- name    : PermInvCC_BS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:24:11.611992+00:00
-- url     : https://prove2.me/theorems/4b36d1df-6c05-4b4a-a9cb-d401b824eafb
-- title:
--   Conditional averaging operator $B_S$
-- statement:
--   Fix margins $\rho,\sigma$ and a type $S$ with these margins; let $(x,y)$ be uniform on all input pairs of type $S$. Then
--   $$B_S:L^2(X_\rho)\to L^2(X_\sigma),\qquad (B_Sf)(y):=\mathbb E[f(x)\mid y], \tag{B.1}$$
--   the average of $f(x)$ over the strings $x$ with joint type $S$ together with $y$.
--
--   **Formalization Note** For $y\in X_\sigma$ the set of such $x$ is nonempty and the conditional law is uniform on it; for other $y$ the value is $0$ and is not used.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), App. B.1, eq. (B.1), p.40

import Mathlib
import Definitions.Def_PermInvCC_jointType

namespace PermInvCC

/-- The **conditional averaging operator** `B_S : L²(X) → L²(Y)`, `(B_S u)(y) = E[u(x) | y]` for
`(x, y)` uniform on the input pairs of joint type `S` (Y. Huang and Z. Ye, arXiv:2609.40116, held
version sha256 fe1797dd…, App. B.1, eq. (B.1), p.40): the average of `u(x)` over the strings `x`
with `jointType x y = S`.

**Formalization Note.** For `y` in the column multislice of `S` this set of `x` is nonempty and
the conditional law given `y` is uniform on it; for other `y` the value is `0` and is never
read. -/
noncomputable def BS {N q : ℕ} (S : Fin q → Fin q → ℕ) (u : (Fin N → Fin q) → ℝ)
    (y : Fin N → Fin q) : ℝ :=
  (∑ x ∈ (Finset.univ.filter fun x => jointType x y = S), u x) /
    ((Finset.univ.filter fun x : Fin N → Fin q => jointType x y = S).card : ℝ)

end PermInvCC


