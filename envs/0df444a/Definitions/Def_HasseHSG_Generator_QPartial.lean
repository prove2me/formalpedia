-- Prove2me | Definitions.Def_HasseHSG_Generator_QPartial
-- name    : HasseHSG_Generator_QPartial
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:35:48.548654+00:00
-- url     : https://prove2.me/theorems/c85d0965-3023-40f3-a1de-40558015dfe9
-- title:
--   $q$-partial derivatives and $q$-partial closed subspaces (Eqs. (12)–(13), Definition 7.1)
-- statement:
--   Let $F$ be a field, $a_1,\dots,a_n\in F$, $q$ transcendental over $F$, $c_i(t)=(q-1)t\,a_i/(1-a_it)$, and $B=F(q)(t)[x_1,\dots,x_n]$.
--
--   1. For $0\le i\le n$ let $x^{(i)}=(x_1+c_1(t),\dots,x_i+c_i(t),x_{i+1},\dots,x_n)$ (Eq. (12)).
--   2. The **$q$-partial derivative** of $f\in B$ is
--   $$\frac{d_q}{dx_i}f=\frac{f(qt,x^{(i)})-f(qt,x^{(i-1)})}{c_i(t)}\qquad(1\le i\le n),$$
--   as in Eq. (13).
--   3. An $F(q)$-subspace $V\subseteq F(q)[x_1,\dots,x_n]$ is **$q$-partial closed** (Definition 7.1) if
--   $$\frac{d_q}{dx_i}V\subseteq F(q)(t)\otimes_{F(q)}V\qquad\text{for all }1\le i\le n.$$
--   Here $F(q)(t)\otimes_{F(q)}V$ is the $F(q)(t)$-linear span of $V$ inside $B$.
--
--   This is the $q$-analogue of a space closed under partial derivatives. It is the hypothesis of the $x$-freeness of the Wronskian (Lemma 7.5).
--
--   **Formalization Note.** Variables are indexed by `Fin n`: the paper's $x_i$ is `X (i-1)`. `shiftUpTo a k f` is $f(qt,x^{(k)})$. `qPartial a i` is $d_q/dx_{i+1}$ for `i : Fin n`. The base change $F(q)(t)\otimes V$ is the `Submodule.span` over $F(q)(t)$ of the image of $V$; the paper notes on p. 31 that the base-change map is injective, so this span is the tensor product.
--
--   The standing assumptions are that the $a_i$ are distinct and nonzero. The Lean formula is total; the source interpretation and every theorem using it retain these assumptions, so $c_i(t)\ne0$.
-- source:
--   Bal, Ghosh, Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary Characteristic Fields, STOC 2027 submission (held manuscript, sha256 1b7cccc3…), p. 22, Eqs. (12)–(13); p. 30, Definition 7.1

import Mathlib
import Definitions.Def_HasseHSG_Generator_QDifference

open MvPolynomial

namespace HasseHSG.Generator

/-!
Bal, Ghosh, *Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary
Characteristic Fields*: the partial shifts `x^{(i)}` (Eq. (12), p. 22), the `q`-partial
derivatives `d_q/dxᵢ` (Eq. (13), p. 22) and `q`-partial closed subspaces (Definition 7.1, p. 30).
Variables are indexed by `Fin n`: the paper's `xᵢ` (`1 ≤ i ≤ n`) is `X (i − 1)`.
-/

/-- `f ↦ f(qt, x^{(k)})` on `B`, where `x^{(k)} = (x₁ + c₁(t), …, x_k + c_k(t), x_{k+1}, …, xₙ)`
(Eq. (12)): the coefficients are mapped by `t ↦ qt`, and the variable `X j` is shifted by
`c_{j+1}(t)` exactly when `j < k`. -/
noncomputable def shiftUpTo {F : Type*} [Field F] {n : ℕ} (a : Fin n → F) (k : ℕ)
    (f : BRing F n) : BRing F n :=
  ∑ m ∈ f.support, C (sigmaT (f.coeff m)) *
    ∏ j : Fin n, (X j + (if (j : ℕ) < k then C (cShift a j) else 0)) ^ (m j)

/-- The `q`-partial derivative `(d_q/dx_{i+1}) f = (f(qt, x^{(i+1)}) − f(qt, x^{(i)})) / c_{i+1}(t)`
(Eq. (13)), for `i : Fin n`. -/
noncomputable def qPartial {F : Type*} [Field F] {n : ℕ} (a : Fin n → F) (i : Fin n)
    (f : BRing F n) : BRing F n :=
  C (cShift a i)⁻¹ * (shiftUpTo a ((i : ℕ) + 1) f - shiftUpTo a (i : ℕ) f)

/-- `V ⊆ F(q)[x₁, …, xₙ]` (an `F(q)`-subspace) is `q`-partial closed (Definition 7.1) if
`(d_q/dxᵢ) V ⊆ F(q)(t) ⊗_{F(q)} V` for every `i`, where `F(q)(t) ⊗_{F(q)} V` is realized as the
`F(q)(t)`-span of `V` inside `B = F(q)(t)[x]`. -/
def IsQPartialClosed {F : Type*} [Field F] {n : ℕ} (a : Fin n → F)
    (V : Submodule (Fq F) (MvPolynomial (Fin n) (Fq F))) : Prop :=
  ∀ i : Fin n, ∀ g ∈ V,
    qPartial a i (embFqxB g) ∈ Submodule.span (Fqt F) (embFqxB '' (V : Set _))

end HasseHSG.Generator


