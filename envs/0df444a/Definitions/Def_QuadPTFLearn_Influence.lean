-- Prove2me | Definitions.Def_QuadPTFLearn_Influence
-- name    : QuadPTFLearn_Influence
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:22:48.919908+00:00
-- url     : https://prove2.me/theorems/9d271e5c-f590-4fea-ac53-dc04400bd566
-- title:
--   The low-degree projection $F_\ell=\mathrm{proj}_{\le\ell}(y)$, the influence matrix $G_\ell$ and $B_i(v)$
-- statement:
--   The objects of Lemma 6.3.
--
--   Let $D$ be a law on $\mathbb R^d\times\{0,1\}$ whose marginal on $\mathbb R^d$ is $N(0,I_d)$, and $\ell\ge1$.
--
--   1. $c_\alpha=\mathbb E_{(x,y)\sim D}[y\,H_\alpha(x)]$ and $F_\ell=\sum_{|\alpha|\le\ell}c_\alpha H_\alpha$, the projection of $y$ (that is, of $x\mapsto\mathbb E[y\mid x]$) onto polynomials of degree at most $\ell$ in $L^2(N(0,I_d))$.
--   2. $G_\ell=\mathbb E_{x\sim N(0,I)}[\nabla F_\ell(x)\nabla F_\ell(x)^\top]$.
--   3. For a unit vector $v$ and $i\le\ell$,
--   $$B_i(v)=\sup\big\{\mathbb E_{(x,y)\sim D}[y\,h_i(v\cdot x)\,p(w)]:\ p\text{ a polynomial on }v^\perp,\ \deg p\le\ell-i,\ \|p\|_2\le1\big\}.$$
--
--   $G_\ell$ is the matrix whose quadratic form detects the directions along which the label has low-degree dependence.
--
--   **Formalization Note** The set in the supremum is nonempty ($p=0$) and bounded above by $\|F_\ell\|_2$, so the real supremum is the supremum of the page. The label lies in $\{0,1\}$ almost surely; the law is a probability measure on $\mathbb R^d\times\mathbb R$.
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Lemma 6.3 and its proof, p.63 (PDF p.65); pp.63–64 (PDF pp.65–66); Hermite basis §2, p.14

import Mathlib
import Definitions.Def_QuadPTFLearn_Gaussian

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace QuadPTFLearn

/-!
# The low-degree projection of the label and the influence matrix `G_ℓ`

I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Lemma 6.3, p.63 (PDF p.65), and its proof, pp.63–64; the Hermite basis of §2, p.14.

**Formalization Note.**
* `D` is a law on `ℝᵈ × ℝ` (point, label). With marginal `N(0, I_d)`, the projection
  `F_ℓ = proj_{≤ℓ}(y)` of `x ↦ E[y | x]` onto polynomials of degree at most `ℓ` in `L²(N(0, I))`
  is `Σ_{|α| ≤ ℓ} c_α H_α` with `c_α = E_D[y H_α(x)]`, because the `H_α` are an orthonormal basis.
* `G_ℓ = E_{x∼N(0,I)}[∇F_ℓ(x) ∇F_ℓ(x)ᵀ]`, with the gradient of the polynomial `F_ℓ`.
* `Bcoef D ℓ v i = B_i(v) = sup { E_D[y h_i(v · x) p(w)] : p on v⊥, deg p ≤ ℓ − i, ‖p‖₂ ≤ 1 }`.
  The set is nonempty (`p = 0`) and bounded above by `‖F_ℓ‖₂` (Cauchy–Schwarz), so the real
  supremum is the supremum of the page.
-/

/-- The multi-indices `α ∈ ℕᵈ` with `|α| ≤ ℓ`. -/
def multiIdx (d ℓ : ℕ) : Finset (Fin d → ℕ) :=
  ((Finset.univ : Finset (Fin d → Fin (ℓ + 1))).image (fun a i => (a i : ℕ))).filter
    (fun α => ∑ i, α i ≤ ℓ)

/-- The Hermite coefficient `c_α = E_{(x,y)∼D}[y H_α(x)]`. -/
noncomputable def hermCoef {d : ℕ} (D : Measure (Pt d × ℝ)) (α : Fin d → ℕ) : ℝ :=
  ∫ z, z.2 * peval (hermMono α) z.1 ∂D

/-- `F_ℓ = proj_{≤ℓ}(y) = Σ_{|α| ≤ ℓ} c_α H_α`. -/
noncomputable def Fell {d : ℕ} (D : Measure (Pt d × ℝ)) (ℓ : ℕ) : Poly d :=
  ∑ α ∈ multiIdx d ℓ, MvPolynomial.C (hermCoef D α) * hermMono α

/-- `G_ℓ = E_{x∼N(0,I)}[∇F_ℓ(x) ∇F_ℓ(x)ᵀ]`. -/
noncomputable def Gell {d : ℕ} (D : Measure (Pt d × ℝ)) (ℓ : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ∫ x, peval (MvPolynomial.pderiv i (Fell D ℓ)) x *
    peval (MvPolynomial.pderiv j (Fell D ℓ)) x ∂gauss d

/-- `B_i(v) = sup_{p(w) ∈ P_{≤ℓ−i}, ‖p‖ ≤ 1} E_{(x,y)∼D}[y h_i(v · x) p(w)]`. -/
noncomputable def Bcoef {d : ℕ} (D : Measure (Pt d × ℝ)) (ℓ : ℕ) (v : Pt d) (i : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ p : Poly d, IsOnPerp v p ∧ p.totalDegree ≤ ℓ - i ∧ l2norm (peval p) ≤ 1 ∧
    r = ∫ z, z.2 * hnorm i ⟪v, z.1⟫ * peval p z.1 ∂D}

/-- The law `D` on `ℝᵈ × ℝ` has marginal `N(0, I_d)` and its label lies in `{0, 1}` almost
surely (Definition 1.2 and Lemma 6.3: "a distribution over `ℝᵈ × {0, 1}` such that
`D_x = N(0, I)`"). -/
def IsBoolGaussLaw {d : ℕ} (D : Measure (Pt d × ℝ)) : Prop :=
  D.map Prod.fst = gauss d ∧ ∀ᵐ z ∂D, z.2 = 0 ∨ z.2 = 1

end QuadPTFLearn


