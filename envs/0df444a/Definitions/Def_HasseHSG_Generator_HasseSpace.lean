-- Prove2me | Definitions.Def_HasseHSG_Generator_HasseSpace
-- name    : HasseHSG_Generator_HasseSpace
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:35:00.930002+00:00
-- url     : https://prove2.me/theorems/c2b5ffef-51b1-4ac5-9996-8b0dc537a914
-- title:
--   Hasse derivative space, the class $\mathcal P_{n,d,r}(F)$ and hitting set generators (Definitions 1.1, 4.3)
-- statement:
--   Let $R$ be a commutative ring and $f\in R[x_1,\dots,x_n]$. For $\gamma\in\mathbb N^n$ the **Hasse derivative** $\hat\partial^{(\gamma)}f$ is the coefficient of $y^\gamma$ in $f(x+y)\in R[x][y]$; equivalently, the coefficient of $x^\beta$ in $\hat\partial^{(\gamma)}f$ is $\binom{\beta+\gamma}{\gamma}f_{\beta+\gamma}$ with $\binom{\beta+\gamma}{\gamma}=\prod_j\binom{\beta_j+\gamma_j}{\gamma_j}$. No division by factorials occurs, so the notion is meaningful in every characteristic. The **Hasse derivative space** of $f$ is
--
--   $$\hat\partial^{*}f=\operatorname{span}_R\{\hat\partial^{(\gamma)}f:\gamma\in\mathbb N^n\}.$$
--
--   Since $\hat\partial^{(0)}f=f$, it always contains $f$.
--
--   For a field $F$ and $n,d,r\in\mathbb N$, the class $\mathcal P_{n,d,r}(F)$ consists of the $f\in F[x_1,\dots,x_n]$ of total degree at most $d$ with $\dim_F\hat\partial^{*}f\le r$.
--
--   A polynomial map $G=(G_1,\dots,G_n)$ with $G_i\in F[y_1,\dots,y_m]$ is a **hitting set generator** for a set $\mathcal P$ of $n$-variate polynomials if for every $f\in\mathcal P$,
--   $$f\neq0\iff f(G_1,\dots,G_n)\neq0,$$
--   where $f(G)$ is the polynomial obtained by substitution, not a function on points.
--
--   These are the objects of the goal theorem: the class of polynomials with a small Hasse derivative space, and the generator that must preserve nonzeroness for all of them at once.
--
--   **Formalization Note.** The Hasse derivative is the published `KakeyaHasse.hasse` (definition `KakeyaPolynomialMethods`), which defines it by the coefficient formula above. The dimension is `Module.rank` (a cardinal), so an infinite-dimensional span is never counted as small.
-- source:
--   Bal, Ghosh, Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary Characteristic Fields, STOC 2027 submission (held manuscript, sha256 1b7cccc3…), p. 4, Definition 1.1; p. 16, Definition 4.3

import Mathlib
import Definitions.Def_KakeyaPolynomialMethods

open MvPolynomial

namespace HasseHSG.Generator

/-!
Bal, Ghosh, *Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary
Characteristic Fields*, p. 4, Definition 1.1, and p. 16, Definition 4.3.

The Hasse derivative `KakeyaHasse.hasse γ f` (published definition `KakeyaPolynomialMethods`) is
the coefficient of `y^γ` in `f(x + y)`: its coefficient at `x^β` is `binom(β + γ, γ) · f_{β+γ}`.
-/

/-- The Hasse derivative space `∂̂* f`: the `R`-linear span of all Hasse derivatives `∂̂^{(γ)} f`,
`γ ∈ ℕ^σ` (including `γ = 0`, which gives `f` itself). -/
noncomputable def hasseSpace {σ R : Type*} [Fintype σ] [CommRing R] (f : MvPolynomial σ R) :
    Submodule R (MvPolynomial σ R) :=
  Submodule.span R (Set.range fun γ : σ →₀ ℕ => KakeyaHasse.hasse γ f)

/-- The class `P_{n,d,r}(F)`: polynomials in `F[x₁, …, xₙ]` of total degree at most `d` whose Hasse
derivative space has `F`-dimension at most `r` (dimension as a cardinal, `Module.rank`). -/
def hasseClass (F : Type*) [Field F] (n d r : ℕ) : Set (MvPolynomial (Fin n) F) :=
  {f | f.totalDegree ≤ d ∧ Module.rank F (hasseSpace f) ≤ (r : Cardinal)}

/-- A polynomial map `G = (G₁, …, Gₙ)` with `Gᵢ ∈ F[y₁, …, y_m]` is a hitting set generator for a
set `P` of `n`-variate polynomials (Definition 4.3) if for every `f ∈ P`, `f ≠ 0` if and only if
the polynomial `f(G₁, …, Gₙ)` is nonzero. -/
def IsHittingSetGenerator {F : Type*} [Field F] {n m : ℕ} (G : Fin n → MvPolynomial (Fin m) F)
    (P : Set (MvPolynomial (Fin n) F)) : Prop :=
  ∀ f ∈ P, f ≠ 0 ↔ MvPolynomial.aeval G f ≠ 0

end HasseHSG.Generator


