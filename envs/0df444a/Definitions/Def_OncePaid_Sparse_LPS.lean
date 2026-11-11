-- Prove2me | Definitions.Def_OncePaid_Sparse_LPS
-- name    : OncePaid_Sparse_LPS
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T13:47:48.697336+00:00
-- url     : https://prove2.me/theorems/2d141ab9-e65b-4c1c-b7a8-91d0096051a6
-- title:
--   The LPS graph $X_{101,\ell}$ on $\mathrm{PGL}(2,\mathbb F_\ell)$, its square/non-square determinant classes and the host $H_\ell$
-- statement:
--   Fix a prime $\ell$ and $i\in\mathbb F_\ell$ (intended: $i^2=-1$). Let $\Sigma_{101}$ be the set of integer quadruples $(a_0,a_1,a_2,a_3)$ with
--
--   $$
--   a_0^2+a_1^2+a_2^2+a_3^2=101,\qquad a_0>0\text{ odd},\quad a_1,a_2,a_3\text{ even}
--   $$
--
--   (it has $101+1=102$ elements). Each quadruple gives the matrix $\begin{pmatrix}a_0+ia_1 & a_2+ia_3\\ -a_2+ia_3 & a_0-ia_1\end{pmatrix}$ over $\mathbb F_\ell$, of determinant $a_0^2+a_1^2+a_2^2+a_3^2$. The **generators** are the images in $\mathrm{PGL}(2,\mathbb F_\ell)$ of the invertible such matrices, and the **LPS graph** $X_{101,\ell}$ is the Cayley graph on $\mathrm{PGL}(2,\mathbb F_\ell)$ with an edge $\{g,gs\}$ for every vertex $g$ and generator $s$.
--
--   An element of $\mathrm{PGL}(2,\mathbb F_\ell)$ lies in the **square class** (the image of $\mathrm{PSL}(2,\mathbb F_\ell)$) if a representative matrix has square determinant; this does not depend on the representative, since a scalar $\mu$ changes the determinant by $\mu^2$. The host $H_\ell$ has the square class as its rows $V_L$, the non-square class as its columns $V_R$, and the edges of $X_{101,\ell}$ between them. Finally $n=\ell(\ell^2-1)/2$.
--
--   This is the explicit sparse family of the main separation: for primes $\ell\equiv305\pmod{404}$ it is a $102$-regular bipartite Ramanujan graph (milestone *§A.3, LPS family*).
--
--   **Formalization Note** The quadruples are a decidable filter of $\{-10,\dots,10\}^4$; generators are defined as the projective images of invertible matrices equal to the quaternion matrix, so no determinant certificate is built into the definition. The graph is `SimpleGraph.mulCayley` on `Matrix.ProjGenLinGroup (Fin 2) (ZMod ℓ)` (quotient of $\mathrm{GL}_2$ by its center), following the platform's $p=13$ definition `opg37364_lps13`, which is not imported. The root $i$ is a parameter; no property of the graph (regularity, bipartiteness, connectivity, spectrum) is assumed.
-- source:
--   Chao, Li, Gao, Wang, Once-Paid Subsequences and the Cost of Min-Plus Approximation, STOC 2027 submission (manuscript sha256 9dc21472…), p. 20, §4 and p. 37, App. A.3 (PDF pp. 22, 39), citing Lubotzky, Phillips, Sarnak, Ramanujan graphs, Combinatorica 8 (1988), https://doi.org/10.1007/BF02126799, and Davidoff, Sarnak, Valette (2003), Prop. 2.5.2 and §4.2

import Mathlib
import Definitions.Def_OncePaid_Sparse_BipHost

namespace OncePaid.Sparse

/-!
# The LPS graph `H_ℓ = X_{101,ℓ}` and its two sides

Chao, Li, Gao, Wang, *Once-Paid Subsequences and the Cost of Min-Plus Approximation*,
STOC 2027 submission (manuscript sha256 9dc21472…), p. 20 §4 and p. 37 App. A.3, which cite the
construction from Lubotzky, Phillips, Sarnak, *Ramanujan graphs*, Combinatorica 8 (1988), and
Davidoff, Sarnak, Valette, *Elementary Number Theory, Group Theory, and Ramanujan Graphs* (2003),
Prop. 2.5.2 and §4.2 (construction pattern of the platform definition `opg37364_lps13`, here for
`p = 101`).

* `lpsCoords`: the integer solutions of `a₀² + a₁² + a₂² + a₃² = 101` with `a₀ > 0` odd and
  `a₁, a₂, a₃` even (a decidable filter of `[-10, 10]⁴`; there are `p + 1 = 102` of them).
* For `i ∈ 𝔽_ℓ` (intended: `i² = −1`) the quaternion matrix
  `[[a₀ + i a₁, a₂ + i a₃], [−a₂ + i a₃, a₀ − i a₁]]` (determinant `a₀² + a₁² + a₂² + a₃²`).
* `lpsGenerators ℓ i`: the images in `PGL(2, 𝔽_ℓ)` of the invertible such matrices.
* `lpsGraph ℓ i`: the Cayley graph `SimpleGraph.mulCayley` on `PGL(2, 𝔽_ℓ)`, edges `{g, g s}`.
* `IsSquareClass g`: `g` has a representative with square determinant (the image of `PSL(2, 𝔽_ℓ)`;
  well defined because scalars change the determinant by a square).
* The bipartite host `lpsAdj ℓ i : lpsLeft ℓ → lpsRight ℓ → Prop` has rows the square class,
  columns its complement (non-square determinant), and the edges of `lpsGraph ℓ i` between them.
* `lpsN ℓ = ℓ(ℓ² − 1)/2`, the intended number of vertices per side.
-/

/-- The integers `-10, …, 10`. -/
def lpsRange : Finset ℤ := (Finset.range 21).image (fun k : ℕ => (k : ℤ) - 10)

/-- The 102 integer quadruples `(a₀, a₁, a₂, a₃)` with `Σ a_k² = 101`, `a₀ > 0` odd, `a₁, a₂, a₃`
even. -/
def lpsCoords : Finset (ℤ × ℤ × ℤ × ℤ) :=
  (lpsRange ×ˢ lpsRange ×ˢ lpsRange ×ˢ lpsRange).filter
    (fun a => a.1 ^ 2 + a.2.1 ^ 2 + a.2.2.1 ^ 2 + a.2.2.2 ^ 2 = 101 ∧ 0 < a.1 ∧ a.1 % 2 = 1 ∧
      a.2.1 % 2 = 0 ∧ a.2.2.1 % 2 = 0 ∧ a.2.2.2 % 2 = 0)

/-- The matrix `[[a₀ + i a₁, a₂ + i a₃], [−a₂ + i a₃, a₀ − i a₁]]` over `ZMod ℓ`. -/
def lpsMatrix (ℓ : ℕ) (i : ZMod ℓ) (a : ℤ × ℤ × ℤ × ℤ) : Matrix (Fin 2) (Fin 2) (ZMod ℓ) :=
  !![(a.1 : ZMod ℓ) + i * a.2.1, (a.2.2.1 : ZMod ℓ) + i * a.2.2.2;
     -(a.2.2.1 : ZMod ℓ) + i * a.2.2.2, (a.1 : ZMod ℓ) - i * a.2.1]

/-- The projective vertex group is finite. -/
instance lpsPGL_finite (ℓ : ℕ) [Fact ℓ.Prime] :
    Finite (Matrix.ProjGenLinGroup (Fin 2) (ZMod ℓ)) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

/-- The generator set: projective images of the invertible matrices `lpsMatrix ℓ i a`,
`a ∈ lpsCoords`. -/
def lpsGenerators (ℓ : ℕ) (i : ZMod ℓ) : Set (Matrix.ProjGenLinGroup (Fin 2) (ZMod ℓ)) :=
  {g | ∃ a ∈ lpsCoords, ∃ A : Matrix.GeneralLinearGroup (Fin 2) (ZMod ℓ),
    (A : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) = lpsMatrix ℓ i a ∧ Matrix.ProjGenLinGroup.mk A = g}

/-- The LPS Cayley graph `X_{101,ℓ}` on `PGL(2, 𝔽_ℓ)`, with edges `{g, g s}`. -/
def lpsGraph (ℓ : ℕ) (i : ZMod ℓ) : SimpleGraph (Matrix.ProjGenLinGroup (Fin 2) (ZMod ℓ)) :=
  SimpleGraph.mulCayley (lpsGenerators ℓ i)

/-- `g ∈ PGL(2, 𝔽_ℓ)` lies in the image of `PSL(2, 𝔽_ℓ)`: some representative has square
determinant. -/
def IsSquareClass (ℓ : ℕ) (g : Matrix.ProjGenLinGroup (Fin 2) (ZMod ℓ)) : Prop :=
  ∃ A : Matrix.GeneralLinearGroup (Fin 2) (ZMod ℓ),
    Matrix.ProjGenLinGroup.mk A = g ∧ IsSquare (A : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).det

/-- The left side `V_L`: the square-determinant class. -/
def lpsLeft (ℓ : ℕ) : Type := {g : Matrix.ProjGenLinGroup (Fin 2) (ZMod ℓ) // IsSquareClass ℓ g}

/-- The right side `V_R`: the non-square-determinant class. -/
def lpsRight (ℓ : ℕ) : Type :=
  {g : Matrix.ProjGenLinGroup (Fin 2) (ZMod ℓ) // ¬ IsSquareClass ℓ g}

noncomputable instance lpsLeft.fintype (ℓ : ℕ) [Fact ℓ.Prime] : Fintype (lpsLeft ℓ) := by
  unfold lpsLeft; exact Fintype.ofFinite _

noncomputable instance lpsRight.fintype (ℓ : ℕ) [Fact ℓ.Prime] : Fintype (lpsRight ℓ) := by
  unfold lpsRight; exact Fintype.ofFinite _

/-- The bipartite host `H_ℓ`: row `a` (square class) and column `b` (non-square class) are
adjacent when they are adjacent in `X_{101,ℓ}`. -/
def lpsAdj (ℓ : ℕ) (i : ZMod ℓ) (a : lpsLeft ℓ) (b : lpsRight ℓ) : Prop :=
  (lpsGraph ℓ i).Adj a.1 b.1

/-- `n = ℓ(ℓ² − 1)/2`. -/
def lpsN (ℓ : ℕ) : ℕ := ℓ * (ℓ ^ 2 - 1) / 2

end OncePaid.Sparse


