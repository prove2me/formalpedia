-- Prove2me | Definitions.Def_PCNonBool_oddHolesOn
-- name    : PCNonBool_oddHolesOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:30:01.510903+00:00
-- url     : https://prove2.me/theorems/38387e17-7f1f-4aa4-9701-1e05134c8b8d
-- title:
--   Holes of a pigeon occurring to an odd power
-- statement:
--   For a monomial $m$, a pigeon $i$ and a hole set $V_a$, let
--   $$H_i(m)=\{\,j\in N(i)\cap V_a : x_{i,j}\text{ occurs in } m \text{ with odd exponent}\,\}.$$
--   Modulo the range axioms $x_{i,j}^2=1$, the factor of $m$ in the variables of pigeon $i$ (within $V_a$) equals $\prod_{j\in H_i(m)}x_{i,j}$. Modulo the parity axiom $\prod_{j}x_{i,j}=-1$ it also equals $-\prod_{j\notin H_i(m)}x_{i,j}$, so pigeon $i$ disappears from the reduced monomial exactly when $H_i(m)$ is empty or all of $N(i)\cap V_a$.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Definition 5.5 (reduction modulo parity and range axioms), p.27 (PDF p.30)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_nbrOn
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_edgeExp

namespace PCNonBool

/-- The holes `j ∈ N(i) ∩ Va` for which `x_{i,j}` occurs in `m` with odd exponent. Modulo the
range axioms `x² = 1`, the part of `m` belonging to pigeon `i` (inside `Va`) is
`∏_{j ∈ oddHolesOn G Va m i} x_{i,j}` (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Definition 5.5, p.27 (PDF p.30)). -/
def oddHolesOn {U V : Type*} (G : BipGraph U V) (Va : Finset V) (m : Var G →₀ ℕ) (i : U) :
    Finset V :=
  (nbrOn G Va i).filter (fun j => Odd (edgeExp G m i j))

end PCNonBool


