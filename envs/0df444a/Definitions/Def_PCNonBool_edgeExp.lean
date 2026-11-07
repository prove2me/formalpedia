-- Prove2me | Definitions.Def_PCNonBool_edgeExp
-- name    : PCNonBool_edgeExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:28:47.177341+00:00
-- url     : https://prove2.me/theorems/0273ef48-cb2c-4498-a9cf-585143ccc58d
-- title:
--   Exponent of $x_{i,j}$ in a monomial
-- statement:
--   For a monomial $m$ in the variables $x_e$, $e\in E$, and a pigeon–hole pair $(i,j)$, this is the exponent of $x_{i,j}$ in $m$, and $0$ when $(i,j)$ is not an edge. A monomial is a finitely supported exponent vector $E\to\mathbb N$.
--
--   It is the bookkeeping device behind pairwise pigeon degree (Definition 5.5) and the notion of a monomial pair being "touched" by $(x_{i,j},x_{i,j'})$.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Definition 5.5 and the definition of "touched", pp.27–28 (PDF pp.30–31)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var

namespace PCNonBool

/-- The exponent of the variable `x_{i,j}` in the monomial `m` (`0` if `(i, j)` is not an edge).
Used to read off which hole variables of a pigeon a monomial contains
(Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Definition 5.5 and "touched", pp.27–28 (PDF pp.30–31)). -/
def edgeExp {U V : Type*} (G : BipGraph U V) (m : Var G →₀ ℕ) (i : U) (j : V) : ℕ :=
  if h : G.Adj i j then m ⟨(i, j), h⟩ else 0

end PCNonBool


