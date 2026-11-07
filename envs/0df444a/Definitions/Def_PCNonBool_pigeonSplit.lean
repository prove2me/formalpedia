-- Prove2me | Definitions.Def_PCNonBool_pigeonSplit
-- name    : PCNonBool_pigeonSplit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:20.078245+00:00
-- url     : https://prove2.me/theorems/4ca8d937-c936-4957-aa47-7eebec9b2a87
-- title:
--   Pigeon split $\mathrm{PigeonSplit}_{i,j,j'}(p)$
-- statement:
--   Let $i\in U$ and $j\ne j'\in N(i)$. Define the restrictions $\rho_1$: $x_{i,j}\mapsto-1$, $x_{i,j'}\mapsto1$, and $\rho_2$: $x_{i,j}\mapsto1$, $x_{i,j'}\mapsto-1$, both leaving all other variables untouched. For a polynomial $p$,
--   $$\mathrm{PigeonSplit}_{i,j,j'}(p)=\frac12\begin{pmatrix}1&1\\1&-1\end{pmatrix}\begin{pmatrix}p\restriction\rho_1\\ p\restriction\rho_2\end{pmatrix}.$$
--   In particular $p=x_{i,j}x_{i,j'}p_1+x_{i,j}p_2+x_{i,j'}p_3+p_4$ is sent to the pair $(p_4-p_1,\ p_3-p_2)$. The two restrictions send pigeon $i$ to hole $j$ and to hole $j'$ respectively.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Definition 5.8 (Pigeon Split), (36)–(37), p.28 (PDF p.31)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_restrict

namespace PCNonBool

/-- `PigeonSplit_{i,j,j'}(p)` (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Definition 5.8, (36)–(37), p.28 (PDF p.31)): with the
restrictions `ρ₁ : x_{i,j} ↦ -1, x_{i,j'} ↦ 1` and `ρ₂ : x_{i,j} ↦ 1, x_{i,j'} ↦ -1` (all
other variables untouched),
`PigeonSplit(p) = ½ [[1, 1], [1, -1]] (p↾ρ₁, p↾ρ₂) = (½(p↾ρ₁ + p↾ρ₂), ½(p↾ρ₁ - p↾ρ₂))`.
For `p = x_{i,j} x_{i,j'} p₁ + x_{i,j} p₂ + x_{i,j'} p₃ + p₄` this is `(p₄ - p₁, p₃ - p₂)`.

**Formalization Note** `½` is `(2 : F)⁻¹`; the paper works over fields of characteristic ≠ 2. -/
noncomputable def pigeonSplit {F : Type*} [Field F] {U V : Type*} [DecidableEq U] [DecidableEq V]
    (G : BipGraph U V) (i : U) (j j' : V) (p : MvPolynomial (Var G) F) :
    MvPolynomial (Var G) F × MvPolynomial (Var G) F :=
  let ρ₁ : Var G → Option F := fun e =>
    if e.1 = (i, j) then some (-1) else if e.1 = (i, j') then some 1 else none
  let ρ₂ : Var G → Option F := fun e =>
    if e.1 = (i, j) then some 1 else if e.1 = (i, j') then some (-1) else none
  ((2 : F)⁻¹ • (restrict ρ₁ p + restrict ρ₂ p), (2 : F)⁻¹ • (restrict ρ₁ p - restrict ρ₂ p))

end PCNonBool


