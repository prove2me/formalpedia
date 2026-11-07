-- Prove2me | Definitions.Def_KServerConj_minorVal
-- name    : KServerConj_minorVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:05.91634+00:00
-- url     : https://prove2.me/theorems/6ad075e0-74de-4fef-992f-39ebffc46421
-- title:
--   Minimum valuation $\mu(G)$ of a maximal minor, equation (16)
-- statement:
--   Let $G$ be a matrix with $d$ rows and columns $g_1,\dots,g_m$ over a valued field. Its **minimum maximal-minor valuation** is
--
--   $$\mu(G)=\min_{1\le i_1<\dots<i_d\le m}\nu\big(\det(g_{i_1},\dots,g_{i_d})\big),$$
--
--   where a dependent choice contributes $+\infty$. The potential of the proof and the three quantities attached to a request are all of this form.
--
--   **Formalization Note** Defined for every matrix with finite row set $R$ and finite column set $\iota$ over a Hahn-series field $F((z^{\mathbb R}))$ (any coefficient field $F$), as the minimum over injections $R\hookrightarrow\iota$ of $\nu$ of the chosen square minor; column order only changes signs, which have valuation $0$. The paper defines $\mu$ for spanning families; here the value is $\top$ when every maximal minor vanishes or there are fewer columns than rows.
-- source:
--   Coester, Koutsoupias, Zbysiński, The k-server conjecture is true, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), §3.2, equation (16), p.9 (pdf p.10)

import Mathlib

namespace KServerConj

/-- **The minimum valuation of a maximal minor**, equation (16) of Coester, Koutsoupias, Zbysiński,
*The k-server conjecture is true*, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…),
§3.2, printed p.9 (PDF p.10):

"Let G = [g₁ ⋯ g_m] be a matrix whose columns span K^d. Define
µ(G) = min_{1≤i₁<⋯<i_d≤m} ν(det(g_{i₁}, …, g_{i_d})). A dependent choice contributes +∞. […]
Column order affects only the determinant's sign, which has valuation zero."

For a matrix `G` with finite row set `R` and finite column set `ι`, over a field of Hahn series
`HahnSeries ℝ F` with its valuation `ν = HahnSeries.addVal`, `minorVal G` is the minimum, over all
injections `e : R ↪ ι` (choices of `|R|` columns, in some order), of `ν` of the determinant of the
square matrix formed by the chosen columns.

**Formalization Note.** Values are in `WithTop ℝ`. Ordered choices give the same minimum as the
paper's increasing ones, since reordering columns changes only the sign. The paper defines `µ` for
spanning families only; here it is defined for every matrix, with value `⊤` when every maximal
minor vanishes (a non-spanning family) or when there are fewer columns than rows. The coefficient
field `F` is arbitrary; the mission uses `F = KServerConj.F k M`. -/
noncomputable def minorVal {F : Type*} [Field F] {R ι : Type*} [Fintype R] [Fintype ι]
    (G : Matrix R ι (HahnSeries ℝ F)) : WithTop ℝ := by
  classical
  exact Finset.univ.inf fun e : R ↪ ι => HahnSeries.addVal ℝ F (G.submatrix id e).det

end KServerConj


