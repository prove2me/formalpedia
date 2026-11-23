-- Prove2me | Definitions.Def_ESAxioms_Characterization_Supplement_Setting
-- name    : ESAxioms_Characterization_Supplement_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:28:21.259163+00:00
-- url     : https://prove2.me/theorems/55e9e595-3eea-41c6-9b72-a21d1697500e
-- title:
--   Definition 3, p. 12, and the copula convention of Theorem 3 (v) — comonotonic random vectors; C is a copula of (X₁, …, Xₙ)
-- statement:
--   Fix a probability space $(\Omega,\mathcal F,\mathbb P)$. Random variables are measurable functions $X:\Omega\to\mathbb R$, and $F_X(x)=\mathbb P(X\le x)$ is the cdf of $X$. "Increasing" means non-decreasing, as on p. 5 of the paper.
--
--   1. **Comonotonicity (Definition 3).** A random vector $(X_1,\dots,X_n)$ is *comonotonic* if there exist a random variable $Z$ and increasing functions $f_1,\dots,f_n:\mathbb R\to\mathbb R$ such that
--   $$X_i=f_i(Z)\quad\text{almost surely, for every } i=1,\dots,n.$$
--   2. **Copula of a random vector.** An $n$-dimensional copula is the distribution function $C(u)=\mu([0,u_1]\times\dots\times[0,u_n])$, $u\in[0,1]^n$, of a probability measure $\mu$ on $[0,1]^n$ whose $n$ one-dimensional marginals are all uniform on $[0,1]$. A copula $C$ is a *copula of* $(X_1,\dots,X_n)$ if
--   $$\mathbb P(X_1\le x_1,\dots,X_n\le x_n)=C\big(F_{X_1}(x_1),\dots,F_{X_n}(x_n)\big)\qquad\text{for every }x\in\mathbb R^n .$$
--   A random vector always has a copula (Sklar's theorem); it is unique only when the marginal cdfs are continuous.
--
--   Together with the published definitions of tail events and $p$-concentration, these objects state Theorems 3 and 4 of the paper: $p$-concentration is characterized by a copula with diagonal value $p$, and concentration at every level is comonotonicity.
--
--   **Formalization Note** The copula is the published `ProbabilityTheory.Copula n` (a probability measure on $[0,1]^n$ with uniform marginals) and its distribution function `Copula.cdf`. The cdf values $F_{X_i}(x_i)$ lie in $[0,1]$ for a probability measure; `Set.projIcc 0 1` only gives them the type $[0,1]$ and does not change them. In Definition 3, $Z$ is required to be measurable (a random variable) and the equalities $X_i=f_i(Z)$ hold almost surely.
-- source:
--   Wang & Zitikis, An Axiomatic Foundation for the Expected Shortfall, SSRN 3423042 (version of 12 March 2020), p. 12 (Definition 3; copula convention of Theorem 3 (v) with reference to Nelsen 2006), p. 5 (increasing means non-strict), p. 13 (Remark 4), p. 31 (proof of Theorem 3, (i)⇔(v))

import Mathlib
import Definitions.Def_ESAxioms_Characterization_Setting
import Definitions.Def_LeanPool_Copula_CDF

open MeasureTheory ProbabilityTheory

namespace ESAxioms.Characterization.Supplement

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Definition 3, p. 12: `(X₁, …, Xₙ)` is comonotonic if there exist a random variable `Z` and
increasing (non-strict, §1.2 p. 5) functions `f₁, …, fₙ : ℝ → ℝ` with `Xᵢ = fᵢ(Z)` a.s. for every
`i`. -/
def IsComonotonic (P : Measure Ω) {n : ℕ} (Xs : Fin n → Ω → ℝ) : Prop :=
  ∃ Z : Ω → ℝ, Measurable Z ∧ ∃ f : Fin n → ℝ → ℝ, (∀ i, Monotone (f i)) ∧
    ∀ i, Xs i =ᵐ[P] fun ω => f i (Z ω)

/-- Theorem 3 (v), p. 12 (copula convention, Nelsen 2006): the `n`-dimensional copula `C` (a
probability measure on `[0, 1]ⁿ` with uniform marginals, published `ProbabilityTheory.Copula`) is a
copula of `(X₁, …, Xₙ)`: `ℙ(X₁ ≤ x₁, …, Xₙ ≤ xₙ) = C(F_{X₁}(x₁), …, F_{Xₙ}(xₙ))` for every
`x ∈ ℝⁿ`. The cdf values lie in `[0, 1]`, so `Set.projIcc` only changes their type to `[0, 1]`. -/
def IsCopulaOf (P : Measure Ω) {n : ℕ} (Xs : Fin n → Ω → ℝ) (C : ProbabilityTheory.Copula n) :
    Prop :=
  ∀ x : Fin n → ℝ, P.real {ω | ∀ i, Xs i ω ≤ x i} =
    C.cdf (fun i => Set.projIcc (0 : ℝ) 1 zero_le_one
      (TailRiskSharing.VaRConv.distFn P (Xs i) (x i)))

end ESAxioms.Characterization.Supplement


