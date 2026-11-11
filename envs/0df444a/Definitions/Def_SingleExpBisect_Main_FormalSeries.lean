-- Prove2me | Definitions.Def_SingleExpBisect_Main_FormalSeries
-- name    : SingleExpBisect_Main_FormalSeries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:38:51.279258+00:00
-- url     : https://prove2.me/theorems/3d11ef38-5e46-442e-9d5d-58252cc3103e
-- title:
--   Formal logarithm and exponential, truncations and variable renaming of multivariate power series over ℚ
-- statement:
--   Series are multivariate formal power series with rational coefficients, $\mathbb Q[[X]]$ (Lean `MvPowerSeries σ ℚ`).
--
--   - **Logarithm** (2): for $F$ with constant term one, $\log F=\sum_{j\ge1}\frac{(-1)^{j+1}}{j}(F-1)^j$. **Exponential** (3): for $F$ with constant term zero, $\exp F=\sum_{j\ge0}\frac1{j!}F^j$. Both are defined coefficientwise: the coefficient of a monomial $m$ of total degree $d$ is the finite sum over $j\le d$, which is exact under the stated constant-term condition because the omitted powers have no monomial of degree $\le d$.
--   - **Truncation**: `discard U F` deletes the monomials of a set $U$. $\langle F\rangle_{\deg\le D}$ discards the monomials of total degree $>D$. A set $U$ is **upward closed** if $m\in U$ implies $m\,m'\in U$ for every monomial $m'$.
--   - **Renaming variables**: For a finite source variable type (`[Finite σ]`), `renamePS f F` substitutes the variable $f(z)$ for each variable $z$; the coefficient of $m$ is the sum of the coefficients of the monomials mapped to $m$.
-- source:
--   Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, arXiv:2611.05982 (October 2026 version; PDF SHA256 6530ce94…6b76541), §2, p. 14, (2), (3) and the truncation ⟨F⟩_{deg ≤ D}; §3.3, pp. 19–22 (substitutions)

import Mathlib

open scoped Classical

namespace SingleExpBisect.Main

/-- **Formal logarithm.** Kumabe, *Single-Exponential FPT Algorithms for Minimum Bisection and
Matching Cut via a New Unbreakable Decomposition*, arXiv:2611.05982 (October 2026), §2, p. 14, (2):
"For a series F whose constant term is one, define log F := Σ_{j ≥ 1} (−1)^{j+1}/j · (F − 1)^j."

**Formalization Note.** Series are Mathlib's `MvPowerSeries σ ℚ` (`Q[[X]]`). The sum is taken
coefficientwise: the coefficient of the monomial `m` is the finite sum over `1 ≤ j ≤ deg m` (total
degree). When the constant term of `F` is one, `(F − 1)^j` has no monomial of total degree `< j`, so
the omitted terms `j > deg m` contribute zero and this is exactly (2). For other `F` the value is not
used. -/
noncomputable def logPS {σ : Type} (F : MvPowerSeries σ ℚ) : MvPowerSeries σ ℚ :=
  fun m => ∑ j ∈ Finset.Icc 1 (Finsupp.degree m),
    ((-1 : ℚ) ^ (j + 1) / (j : ℚ)) * MvPowerSeries.coeff m ((F - 1) ^ j)

/-- **Formal exponential.** ibid., §2, p. 14, (3): "For a series F whose constant term is zero,
define exp F := Σ_{j ≥ 0} (1/j!) F^j."

**Formalization Note.** Coefficientwise, the coefficient of `m` is the finite sum over
`0 ≤ j ≤ deg m`; when the constant term of `F` is zero, `F^j` has no monomial of total degree `< j`,
so this is exactly (3). -/
noncomputable def expPS {σ : Type} (F : MvPowerSeries σ ℚ) : MvPowerSeries σ ℚ :=
  fun m => ∑ j ∈ Finset.range (Finsupp.degree m + 1),
    (1 / (Nat.factorial j : ℚ)) * MvPowerSeries.coeff m (F ^ j)

/-- **Discarding a set of monomials.** `discard U F` is `F` with the monomials of `U` deleted
(their coefficients set to zero). The truncations `⟨F⟩_{deg ≤ D}` (§2, p. 14), `⟨F⟩_{deg_w ≤ k}`
(§3, pp. 17, 25) and `⟨F⟩_{≤(k,n,2k)}` (§3.3, p. 20) are `discard U` for the set `U` of monomials
violating the stated degree bound(s). -/
noncomputable def discard {σ : Type} (U : Set (σ →₀ ℕ)) (F : MvPowerSeries σ ℚ) :
    MvPowerSeries σ ℚ :=
  fun m => if m ∈ U then 0 else MvPowerSeries.coeff m F

/-- **`⟨F⟩_{deg ≤ D}`.** ibid., §2, p. 14: "For a series F and a nonnegative degree bound D, let
⟨F⟩_{deg≤D} denote the series obtained by discarding the monomials of degree greater than D."
Degree is total degree. -/
noncomputable def truncDeg {σ : Type} (D : ℕ) (F : MvPowerSeries σ ℚ) : MvPowerSeries σ ℚ :=
  discard {m | D < Finsupp.degree m} F

/-- A set of monomials closed under multiplication by any monomial (`m ∈ U → m·m′ ∈ U`); the set
of monomials of degree `> D`, and the set violating any family of upper bounds on partial degrees
(such as `≤(k, n, 2k)`), are of this kind. -/
def IsUpClosed {σ : Type} (U : Set (σ →₀ ℕ)) : Prop :=
  ∀ m ∈ U, ∀ m' : σ →₀ ℕ, m + m' ∈ U

/-- **Substituting variables for variables in a power series.** `renamePS f F` replaces every
variable `z` of `F` by the variable `f z`: the coefficient of `m` in the result is the sum of the
coefficients of all monomials `e` of `F` that `f` maps to `m`. This is the substitution used in
§3.3 (ω_t^{B_t}, σ_t, `x′ ↦ x`, pp. 19–22) applied to a series.

**Formalization Note.** For a finite variable type every fibre is finite (`f` preserves total
degree), so the `finsum` is an honest finite sum. -/
noncomputable def renamePS {σ τ : Type} [Finite σ] (f : σ → τ) (F : MvPowerSeries σ ℚ) :
    MvPowerSeries τ ℚ :=
  fun m => ∑ᶠ (e : σ →₀ ℕ) (_ : Finsupp.mapDomain f e = m), MvPowerSeries.coeff e F

end SingleExpBisect.Main


