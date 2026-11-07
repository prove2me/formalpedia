-- Prove2me | Definitions.Def_PCNonBool_xv
-- name    : PCNonBool_xv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:28:38.826599+00:00
-- url     : https://prove2.me/theorems/48c794dc-1b89-4b0d-9f17-7e04cd577551
-- title:
--   The variable $x_{i,j}$ as a polynomial
-- statement:
--   For a pigeon $i$ and a hole $j\in N(i)$, $x_{i,j}$ denotes the polynomial variable of the edge $(i,j)$ in the polynomial ring $\mathbb F[x_e : e\in E]$. Under the $\pm1$ encoding, $x_{i,j}=-1$ means that pigeon $i$ flies to hole $j$.
--
--   **Formalization Note** The Lean function is total: for a non-edge it returns $0$. It is only ever applied with $j\in N(i)$.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), (33a)–(33d), p.25 (PDF p.28)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var

namespace PCNonBool

/-- The polynomial `x_{i,j}` for a pigeon `i` and a hole `j` (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), (33a)–(33d), p.25
(PDF p.28)). It is the variable of the edge `(i, j)` when `(i, j) ∈ E`, and the polynomial `0`
otherwise.

**Formalization Note** Every use of `xv G i j` in this mission has `j ∈ N(i)`, so the junk value
`0` never enters a statement. -/
noncomputable def xv {F : Type*} [CommRing F] {U V : Type*} (G : BipGraph U V) (i : U) (j : V) :
    MvPolynomial (Var G) F :=
  if h : G.Adj i j then MvPolynomial.X ⟨(i, j), h⟩ else 0

end PCNonBool


