-- Prove2me | Definitions.Def_NCQuadLB_CoeffX
-- name    : NCQuadLB_CoeffX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:27:38.625206+00:00
-- url     : https://prove2.me/theorems/983b5320-5769-4009-9f36-14d956de7a61
-- title:
--   Parts $\hat g_X,\hat g_Y,\hat g_{XY}$, the projection $\pi_d$, $\mathrm{coeff}_m$ and $\mathrm{Coeff}_X(f)$
-- statement:
--   Work in $\mathbb F\langle X,Y\rangle$. A monomial is **$X,Y$-separated** if every $X$-variable in it appears before every $Y$-variable, i.e. it is $u\,m$ with $u$ a word in $X$ and $m$ a word in $Y$. For a polynomial $f$:
--
--   1. $f_X$ is the sum of the monomials of $f$ involving only variables from $X$, $f_Y$ the sum of those involving only variables from $Y$ (both include the constant term), and $f_{XY}$ the sum of the $X,Y$-separated monomials of $f$;
--   2. $\pi_d(f)$ is the homogeneous degree-$d$ component of $f$;
--   3. for a word $m$ in $Y$, $\mathrm{coeff}_m(f)=c_m=\sum_{u}[u\,m]f\cdot u\in\mathbb F\langle X\rangle$, the sum over words $u$ in $X$, so that a separated $f$ is $\sum_m c_m\,m$;
--   4. $$\mathrm{Coeff}_X(f)=\{\mathrm{coeff}_m(f)\mid m\in Y^*,\ c_m\neq0\}\subseteq\mathbb F\langle X\rangle,$$ where $Y^*$ is the set of non-constant monomials in the $Y$-variables.
--
--   The dimension of $\mathrm{span}\,\mathrm{Coeff}_X(f)$ is the complexity measure of the lower bound.
--
--   **Formalization Note** $\mathbb F\langle X\rangle$ is the subalgebra of $\mathbb F\langle X,Y\rangle$ of polynomials in the $X$-variables. The formula for $\mathrm{coeff}_m$ is applied to every $f$; on separated $f$ it is the source's $c_m$. $Y^*$ excludes the empty word.
-- source:
--   Shastri, Willumsgaard, A Quadratic Lower Bound for Noncommutative Circuits, arXiv:2604.20575 (version of November 2, 2026, sha256 34159453…), §2, p.4 (separated polynomials, coeff_m, Coeff_X); pp.4–5 (π_d); §3, p.5 (ĝ_X, ĝ_Y, ĝ_XY)

import Mathlib
import Definitions.Def_NCFactorClosure607_Circuits_Polynomials

namespace NCQuadLB

open NCFactorClosure607.Circuits

variable {F : Type*} [Field F] {σ τ : Type*}

/-- The polynomial with a given finitely supported coefficient family on words. -/
noncomputable def ofCoeffs {V : Type*} (c : FreeMonoid V →₀ F) : FreeAlgebra F V :=
  FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.ofCoeff c)

/-- The sum of the monomials of `f` whose word satisfies `P` (keep the coefficient of every word
satisfying `P`, set the others to `0`). -/
noncomputable def restrictWords {V : Type*} (P : FreeMonoid V → Prop) (f : FreeAlgebra F V) :
    FreeAlgebra F V :=
  open scoped Classical in ofCoeffs ((coeffs f).filter P)

/-- A word in the `X`-variables only (`X = Sum.inl`); the empty word counts. -/
def IsXWord (w : FreeMonoid (σ ⊕ τ)) : Prop := ∀ a ∈ w.toList, a.isLeft = true

/-- A word in the `Y`-variables only (`Y = Sum.inr`); the empty word counts. -/
def IsYWord (w : FreeMonoid (σ ⊕ τ)) : Prop := ∀ a ∈ w.toList, a.isRight = true

/-- An `X, Y`-separated word: every `X`-variable appears before every `Y`-variable, i.e. the word is
`u · m` with `u` an `X`-word and `m` a `Y`-word. -/
def IsSeparated (w : FreeMonoid (σ ⊕ τ)) : Prop :=
  ∃ u m : FreeMonoid (σ ⊕ τ), IsXWord u ∧ IsYWord m ∧ w = u * m

/-- `ĝ_X` (arXiv:2604.20575, version of November 2, 2026, sha256 34159453…, §3, p.5): the sum of all
monomials of `f` involving only variables from `X` (the constant term included). -/
noncomputable def xPart (f : FreeAlgebra F (σ ⊕ τ)) : FreeAlgebra F (σ ⊕ τ) :=
  restrictWords IsXWord f

/-- `ĝ_Y` (§3, p.5): the sum of all monomials of `f` involving only variables from `Y` (the constant
term included). -/
noncomputable def yPart (f : FreeAlgebra F (σ ⊕ τ)) : FreeAlgebra F (σ ⊕ τ) :=
  restrictWords IsYWord f

/-- `ĝ_{XY}` (§3, p.5): the sum of all `X, Y`-separated monomials of `f` (§2, p.4: in each such
monomial every `X`-variable appears before every `Y`-variable). -/
noncomputable def xyPart (f : FreeAlgebra F (σ ⊕ τ)) : FreeAlgebra F (σ ⊕ τ) :=
  restrictWords IsSeparated f

/-- `π_d` (pp.4–5): the linear projection onto the homogeneous degree `d` component (keep the
monomials of degree exactly `d`). -/
noncomputable def proj {V : Type*} (d : ℕ) (f : FreeAlgebra F V) : FreeAlgebra F V :=
  restrictWords (fun w => w.length = d) f

/-- `coeff_m(f)` (§2, p.4): for a `Y`-word `m`, the polynomial `c_m = ∑_{u ∈ X-words} [u·m]f · u ∈ F⟨X⟩`,
so that an `X, Y`-separated `f` is `∑_m c_m m`.

**Formalization Note** The formula is applied to every `f`, separated or not; on a separated `f` it is
the source's `c_m`. `F⟨X⟩` is the subalgebra of `F⟨X, Y⟩` of polynomials in the `X`-variables. The
coefficient of `u` is `[u·m]f`, read through right multiplication by `m`, which is injective on words. -/
noncomputable def coeffY (m : FreeMonoid (σ ⊕ τ)) (f : FreeAlgebra F (σ ⊕ τ)) :
    FreeAlgebra F (σ ⊕ τ) :=
  open scoped Classical in
  ofCoeffs (((coeffs f).comapDomain (· * m)
    (fun _ _ _ _ h => mul_right_cancel h)).filter IsXWord)

/-- `Coeff_X(f)` (arXiv:2604.20575, version of November 2, 2026, sha256 34159453…, §2, p.4): the set
`{coeff_m(f) | m ∈ Y*, c_m ≢ 0} ⊆ F⟨X⟩` of the nonzero coefficients of `f` at the non-constant
monomials `m` in the `Y`-variables.

**Formalization Note** `Y*` is the set of nonempty `Y`-words (`m ≠ 1`), as the source says
("non-constant monomials"); `≢ 0` is `≠ 0`. -/
def CoeffX (f : FreeAlgebra F (σ ⊕ τ)) : Set (FreeAlgebra F (σ ⊕ τ)) :=
  {c | ∃ m : FreeMonoid (σ ⊕ τ), IsYWord m ∧ m ≠ 1 ∧ coeffY m f = c ∧ c ≠ 0}

end NCQuadLB


