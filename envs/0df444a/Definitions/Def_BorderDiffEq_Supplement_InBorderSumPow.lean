-- Prove2me | Definitions.Def_BorderDiffEq_Supplement_InBorderSumPow
-- name    : BorderDiffEq_Supplement_InBorderSumPow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:50:44.39205+00:00
-- url     : https://prove2.me/theorems/3c76a721-fcaa-4dd9-8e29-6bb9162a994d
-- title:
--   The border of sums of $k$ powers, $\overline{\Sigma^{[k]}\wedge\mathcal D}$
-- statement:
--   For a class $\mathcal D$ of polynomials, $\Sigma^{[k]}\wedge\mathcal D=\{\sum_{i=1}^k P_i^{e_i} : P_i\in\mathcal D,\ e_i\ge1\}$. A polynomial $f\in F[x_1,\dots,x_n]$ lies in the **border** $\overline{\Sigma^{[k]}\wedge\mathcal D}$ if there are at most $k$ polynomials $P_1,\dots,P_t\in F((\epsilon))[x]$ satisfying the constraints of $\mathcal D$ (read over $F((\epsilon))$) and exponents $e_i\ge1$ with
--   $$
--   \sum_{i=1}^{t}P_i^{e_i}=f+\epsilon\,S,\qquad S\in F[[\epsilon]][x].
--   $$
--
--   This is the hypothesis of Theorems 2.5 and 2.6 for the classes of bases of low degree, small partial derivative space, and common-order or any-order roABPs.
--
--   **Formalization Note** $\mathcal D$ is a predicate on polynomials over $F((\epsilon))$ (Mathlib `LaurentSeries F`). The border relation is the published `BorderDiffEq.IsEpsApprox`. "$k$ summands" is read as "at most $k$"; every class used here contains $0$, so this is the same class.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), §2.2, pp.7–8 (definition of Σ[k] ∧ D and "In the border setting, the bases Pi are polynomials over F(ϵ) that satisfy the same constraints"); §4, p.23

import Mathlib
import Definitions.Def_BorderDiffEq_IsEpsApprox

namespace BorderDiffEq.Supplement

open BorderDiffEq

/-- **The border of sums of `k` powers of polynomials from a class `D`, `f ∈ cl(Σ^{[k]} ∧ D)`**
(Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of Structured Algebraic Circuits via
Differential Equations*, manuscript (STOC 2027 submission), §2.2, pp.7–8:
`Σ^{[k]} ∧ D := {∑_{i=1}^k Pᵢ(x)^{eᵢ} : Pᵢ ∈ D, eᵢ ≥ 1}`; "In the border setting, the bases `Pᵢ`
are polynomials over `F(ε)` that satisfy the same constraints"; borders as in §4, p.23): a
polynomial `f ∈ F[x₁, …, xₙ]` is in the border if there are at most `k` bases
`P₁, …, P_t ∈ F((ε))[x]` in the class `D` and exponents `eᵢ ≥ 1` with
`∑ᵢ Pᵢ^{eᵢ} = f + ε·S` for a polynomial `S` with coefficients in `F[[ε]]`.

**Formalization Note.** The class `D` is a predicate on polynomials over `F((ε))` (Mathlib
`LaurentSeries F`), so the constraints on the bases (degree, partial derivative dimension, roABP
size) are read over `F((ε))`, as the paper prescribes. `IsEpsApprox` is the published border
relation of the base mission (constants in `F((ε))` cover the paper's `F(ε)`). "`k` summands" is
read as "at most `k`"; for every class used here `0 ∈ D` and `0^1 = 0`, so this is the same class. -/
def InBorderSumPow (F : Type) [Field F] (n k : ℕ)
    (D : MvPolynomial (Fin n) (LaurentSeries F) → Prop) (f : MvPolynomial (Fin n) F) : Prop :=
  ∃ (t : ℕ) (P : Fin t → MvPolynomial (Fin n) (LaurentSeries F)) (e : Fin t → ℕ),
    t ≤ k ∧ (∀ i, 1 ≤ e i) ∧ (∀ i, D (P i)) ∧ IsEpsApprox (∑ i, P i ^ e i) f

end BorderDiffEq.Supplement


