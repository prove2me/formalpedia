-- Prove2me | Definitions.Def_GoodQLTC_cobdMat
-- name    : GoodQLTC_cobdMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:46:25.397264+00:00
-- url     : https://prove2.me/theorems/3324d484-84e1-404f-83aa-54abcbe898b8
-- title:
--   Cochains, coboundary $\delta^j$, block weight, $M_j$ and $h_j$
-- statement:
--   For a cosheaf $\mathcal F$ on $X$, $C^j=\bigoplus_{f\in X(j)}\mathcal F(f)$ and
--   $$
--   (\delta^jx)(g)=\sum_{f\in X_{\le g}(j)}R_{gf}\,x(f)\qquad(g\in X(j+1)).
--   $$
--   The block weight of $x$ is $|x|_b=|\{f:x(f)\ne0\}|$; $M_j=\dim C^j$ and $h_j=\dim H^j$, $H^j=\ker\delta^j/\mathrm{im}\,\delta^{j-1}$.
--
--   **Formalization Note** `cobdMat φ Fs i j` is the matrix from degree $i$ to degree $j$ (used with $j=i+1$); cochains are functions on pairs (face, stalk coordinate). $\delta^{-1}=0$ in `cohomDim`.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §4.4, pp.17–18 (PDF pp.20–21)

import Mathlib
import Definitions.Def_GoodQLTC_Face
import Definitions.Def_GoodQLTC_Cosheaf

namespace GoodQLTC

/-- The cochain space `C^j(X; F) := ⨁_{f∈X(j)} F(f)` in coordinates, Gay–Jeronimo,
arXiv:2609.20780 (held version), §4.4, p.17: a cochain is a function on the pairs `(f, a)` with
`f ∈ X(j)` and `a` a coordinate of the stalk `F(f) = F^{d(f)}`. -/
abbrev Cochain {X : Type} [PartialOrder X] {t : ℕ} (φ : X → Fin t → Option Bool) {F : Type}
    [Field F] (Fs : Cosheaf X F) (j : ℕ) (M : Type*) : Type _ :=
  (Σ f : Face φ j, Fin (Fs.d f.1)) → M

open Classical in
/-- The **coboundary** `δ` as a matrix, Gay–Jeronimo, arXiv:2609.20780 (held version), §4.4,
p.17: `(δ^j x)(g) := ∑_{f ∈ X_{≤g}(j)} R_{gf} x(f)` for `g ∈ X(j+1)`.

**Formalization Note.** `cobdMat φ Fs i j` has rows indexed by `X(j)` (with stalk coordinates) and
columns by `X(i)`; its `(g, f)` block is `R_{gf}` if `f ≤ g` and `0` otherwise. It is the paper's
`δ^i` when `j = i + 1`; the two degrees are separate arguments so that `δ^{k−1} : C^{k−1} → C^k`
and `δ^k : C^k → C^{k+1}` share the index type of `C^k`. -/
noncomputable def cobdMat {X : Type} [PartialOrder X] [Fintype X] {t : ℕ}
    (φ : X → Fin t → Option Bool) {F : Type} [Field F] (Fs : Cosheaf X F) (i j : ℕ) :
    Matrix (Σ g : Face φ j, Fin (Fs.d g.1)) (Σ f : Face φ i, Fin (Fs.d f.1)) F :=
  Matrix.of fun g f => if f.1.1 ≤ g.1.1 then Fs.R f.1.1 g.1.1 g.2 f.2 else 0

open Classical in
/-- The **block weight** `|x|_b := |{f : x(f) ≠ 0}|` of a vector `x` in a direct sum
`⨁_b M^{d(b)}` written in coordinates (arXiv:2609.20780, §4.4, p.17; §9.1, p.27). -/
noncomputable def blockWeight {B : Type} [Fintype B] {d : B → ℕ} {M : Type*} [Zero M]
    (x : (Σ b : B, Fin (d b)) → M) : ℕ :=
  (Finset.univ.filter fun b => ∃ a, x ⟨b, a⟩ ≠ 0).card

/-- `M_j := dim_F C^j` (arXiv:2609.20780, §4.4, p.18). -/
noncomputable def cochainDim {X : Type} [PartialOrder X] [Fintype X] {t : ℕ}
    (φ : X → Fin t → Option Bool) {F : Type} [Field F] (Fs : Cosheaf X F) (j : ℕ) : ℕ :=
  Fintype.card (Σ f : Face φ j, Fin (Fs.d f.1))

/-- `h_j := dim_F H^j(X; F)`, `H^j := ker δ^j / im δ^{j−1}` (arXiv:2609.20780, §4.4, p.18).
**Formalization Note.** The quotient of `ker δ^j` by `im δ^{j−1} ∩ ker δ^j` (which is
`im δ^{j−1}` since `δ^j δ^{j−1} = 0`, Lemma 4.9); `δ^{−1} := 0`. -/
noncomputable def cohomDim {X : Type} [PartialOrder X] [Fintype X] {t : ℕ}
    (φ : X → Fin t → Option Bool) {F : Type} [Field F] (Fs : Cosheaf X F) (j : ℕ) : ℕ :=
  Module.finrank F
    (↥(LinearMap.ker (cobdMat φ Fs j (j + 1)).mulVecLin) ⧸
      (LinearMap.range (if j = 0 then 0 else (cobdMat φ Fs (j - 1) j).mulVecLin)).comap
        (LinearMap.ker (cobdMat φ Fs j (j + 1)).mulVecLin).subtype)

end GoodQLTC


