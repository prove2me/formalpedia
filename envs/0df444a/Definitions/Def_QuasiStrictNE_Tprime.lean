-- Prove2me | Definitions.Def_QuasiStrictNE_Tprime
-- name    : QuasiStrictNE_Tprime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:11:21.465275+00:00
-- url     : https://prove2.me/theorems/01e1a18b-a899-44f2-86fc-6ad71e0903d8
-- title:
--   The piecewise-linear self-map $T'$
-- statement:
--   For a bimatrix game $(A,B)$ and selections $p,q$ of relative-interior points of the faces of $\mathcal C_m$, $\mathcal C_n$, set (equation (9))
--   $$
--   h_1(x,y)=x+R_1(y)-S_1(x),\qquad h_2(x,y)=y+R_2(x)-S_2(y),
--   $$
--   and
--   $$
--   T'(x,y)=\bigl(\Pi_m(h_1(x,y)),\ \Pi_n(h_2(x,y))\bigr).
--   $$
--   $T'$ is a continuous self-map of $\Delta_m\times\Delta_n$ whose fixed points give quasi-strict equilibria.
--
--   **Formalization Note** The selections are arguments; the paper chooses them by Lemma 3 in §4.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), §4, (9), p.13

import Mathlib
import Definitions.Def_QuasiStrictNE_S1
import Definitions.Def_QuasiStrictNE_R2
import Definitions.Def_QuasiStrictNE_S2
import Definitions.Def_QuasiStrictNE_R1
import Definitions.Def_QuasiStrictNE_Proj

namespace QuasiStrictNE

/-- **The piecewise-linear self-map `T′`** (Hansen & Nie, *On Existence and Computational Complexity
of Quasi-strict Equilibria*, arXiv:2611.06350, §4, (9), p.13: "h1(x, y) = x + R1(y) − S1(x),
h2(x, y) = y + R2(x) − S2(y). Define T′(x, y) = (x′, y′) by x′i = max{(h1(x, y))i − tm(h1(x, y)), 0},
i ∈ M, y′j = max{(h2(x, y))j − tn(h2(x, y)), 0}, j ∈ N").

For a bimatrix game `(A, B)` and selections `p`, `q` of relative-interior points of the faces of
`Cm`, `Cn`, `Tprime A B p q (x, y) = (Πm(h1(x, y)), Πn(h2(x, y)))` with
`h1(x, y) = x + R1(y) − S1(x)` and `h2(x, y) = y + R2(x) − S2(y)`.

**Formalization Note** The selections are arguments (the paper fixes them in (1), p.10, and chooses
them by Lemma 3 in §4); the theorems state which selections they assume. -/
noncomputable def Tprime {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ)
    (p : Set (Fin m → ℝ) → (Fin m → ℝ)) (q : Set (Fin n → ℝ) → (Fin n → ℝ)) :
    (Fin m → ℝ) × (Fin n → ℝ) → (Fin m → ℝ) × (Fin n → ℝ) :=
  fun xy => (Proj m (xy.1 + R1 A q xy.2 - S1 B p xy.1), Proj n (xy.2 + R2 B p xy.1 - S2 A q xy.2))

end QuasiStrictNE


