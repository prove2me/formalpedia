-- Prove2me | Definitions.Def_RamseyDisambig_Spherical_Supplement_PartialVC
-- name    : RamseyDisambig_Spherical_Supplement_PartialVC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:22:59.726924+00:00
-- url     : https://prove2.me/theorems/5f3662ec-e42d-4097-a4c9-404050f83bde
-- title:
--   Partial-matrix VC-dimension, pure constant 2×2 submatrices, casting ⋆ entries
-- statement:
--   Let $M$ be a partial matrix with rows $R$, columns $C$ and entries in $\{0,1,\star\}$. A set of columns $c_1,\dots,c_h$ is **shattered** by $M$ if for every pattern $\delta\in\{0,1\}^h$ some row $r$ satisfies $M[r,c_i]=\delta_i$ for every $i$; only specified entries count, so a $\star$ never realizes a pattern. The **VC-dimension** of $M$ is
--   $$\operatorname{VC}(M)=\sup\{h:\ \text{some } h \text{ columns are shattered by } M\}\in\mathbb N\cup\{\infty\}.$$
--   On a total matrix this is the usual VC-dimension with rows as concepts and columns as points.
--
--   A submatrix is **pure** if all its entries are specified. *Every pure $2\times2$ submatrix of $M$ is constant* means: for distinct rows $r_1\ne r_2$ and distinct columns $c_1\ne c_2$ whose four entries $M[r_i,c_j]$ are all specified, the four values coincide. *No row or column of $U$ contains both a 0 entry and a 1 entry* is the condition of Lemma 18. Finally $U^{(b)}$, for $b\in\{0,1\}$, is the total matrix obtained from $U$ by replacing every $\star$ by $b$ and keeping all specified entries.
--
--   These notions are the vocabulary of Theorem 3 and Lemma 18.
--
--   **Formalization Note** A partial matrix is the published `PartialMatrix Row Col = Row → Col → Option Bool`, with `none` for $\star$. The VC-dimension is valued in `ℕ∞` and has the same shape as the published `NatureSLT.GrowthFunction.vcDim`; the verification module proves that the two agree on total matrices. Shattered column tuples need not be given as injective maps: a repeated column cannot be shattered once $h\ge2$.
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), Preliminaries, p. 8; p. 2 footnote 1; p. 4; Lemma 18, p. 17 (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Definitions.Def_RamseyDisambig_Spherical_Matrices
import Definitions.Def_NatureSLT_GrowthFunction_vcDim

set_option autoImplicit false

noncomputable section

namespace RamseyDisambig.Spherical.Supplement

open RamseyDisambig.Spherical

/-- Shattering of a partial matrix through specified entries only (Preliminaries, p. 8): the
columns `z 0, …, z (h-1)` are shattered when every pattern `δ` is realized by some row whose
entries in these columns are *specified* and equal to `δ`. A `⋆` (`none`) never helps. -/
def PartialShatters {Row Col : Type*} (M : PartialMatrix Row Col) {h : ℕ} (z : Fin h → Col) :
    Prop :=
  ∀ δ : Fin h → Bool, ∃ r : Row, ∀ i : Fin h, M r (z i) = some (δ i)

/-- The VC-dimension of a partial matrix (p. 8): the supremum, in `ℕ∞`, of the sizes of finite
shattered column sets. Same shape as `NatureSLT.GrowthFunction.vcDim`; on a total matrix
`fun r c => some (b r c)` it coincides with `vcDim b`. Rows are concepts, columns are points. -/
def partialVCDim {Row Col : Type*} (M : PartialMatrix Row Col) : ℕ∞ :=
  ⨆ (h : ℕ) (_ : ∃ z : Fin h → Col, PartialShatters M z), (h : ℕ∞)

/-- "Every pure 2 × 2 submatrix of `M` is constant" (pp. 2, 4): for two distinct rows and two
distinct columns whose four entries are all specified, the four specified values agree. -/
def PureTwoByTwoConstant {Row Col : Type*} (M : PartialMatrix Row Col) : Prop :=
  ∀ (r₁ r₂ : Row) (c₁ c₂ : Col), r₁ ≠ r₂ → c₁ ≠ c₂ →
    ∀ a b c d : Bool, M r₁ c₁ = some a → M r₁ c₂ = some b → M r₂ c₁ = some c →
      M r₂ c₂ = some d → a = b ∧ a = c ∧ a = d

/-- "No row or column of `U` contains both a 0 entry and a 1 entry" (Lemma 18, p. 17). -/
def NoRowOrColumnMixed {Row Col : Type*} (U : PartialMatrix Row Col) : Prop :=
  (∀ (r : Row) (c c' : Col), U r c = some false → U r c' ≠ some true) ∧
  (∀ (c : Col) (r r' : Row), U r c = some false → U r' c ≠ some true)

/-- `U^(b)`: the total matrix obtained by casting every `⋆` entry of `U` into `b` (p. 17);
specified entries are kept. -/
def castStars {Row Col : Type*} (U : PartialMatrix Row Col) (b : Bool) : Row → Col → Bool :=
  fun r c => (U r c).getD b

end RamseyDisambig.Spherical.Supplement


