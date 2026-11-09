-- Prove2me | Definitions.Def_PrivPCP_gridQ
-- name    : PrivPCP_gridQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:42:47.547217+00:00
-- url     : https://prove2.me/theorems/481dd463-02af-43e7-bea1-4ee1d7045dbc
-- title:
--   Grid vanishing polynomials and the certificate spaces $Q_i(a)$
-- statement:
--   For finite sets $H_1,\dots,H_k\subseteq\mathbb F_q$ with $h_i=|H_i|$ and a degree profile $a$ with $a_i\ge h_i$:
--   $$Z_i(X_i)=\prod_{c\in H_i}(X_i-c),\qquad Q_i(a)=\{Q\in\mathbb F_q[X_1,\dots,X_k]:\ \deg_{X_i}Q\le a_i-h_i,\ \deg_{X_j}Q\le a_j\ (j\ne i)\}.$$
--   $Z_i$ vanishes exactly on $H_i$, and $\sum_i Z_iQ_i$ with $Q_i\in Q_i(a)$ has individual degree at most $a$ and vanishes on $D=\prod_i H_i$; Fact 3.3 says these are all such polynomials.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Fact 3.3, p.12 (PDF p.14)

import Mathlib

namespace PrivPCP

open MvPolynomial

/-- The vanishing polynomial `Z_i(X_i) = ∏_{c∈H_i} (X_i − c)` of the `i`-th side of the grid
`D = ∏_i H_i` (Bafna, Vyas, *Private PCPs from Product Expansion*, STOC 2027 submission manuscript (sha256
c2cac1e0…), Fact 3.3, p.12). -/
noncomputable def gridZ {F : Type} [Field F] {k : ℕ} (H : Fin k → Finset F) (i : Fin k) :
    MvPolynomial (Fin k) F :=
  ∏ c ∈ H i, (X i - C c)

/-- The certificate space `Q_i(a) = {Q : deg_{X_i} Q ⩽ a_i − h_i, deg_{X_j} Q ⩽ a_j for j ≠ i}` of Fact 3.3
(p.12), `h_i = |H_i|`, for a degree profile with `a_i ⩾ h_i`. -/
def gridQ {F : Type} [Field F] {k : ℕ} (H : Fin k → Finset F) (a : Fin k → ℕ) (i : Fin k) :
    Set (MvPolynomial (Fin k) F) :=
  {Q | Q.degreeOf i ≤ a i - (H i).card ∧ ∀ j, j ≠ i → Q.degreeOf j ≤ a j}

end PrivPCP


