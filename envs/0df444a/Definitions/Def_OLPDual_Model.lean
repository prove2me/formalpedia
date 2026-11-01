-- Prove2me | Definitions.Def_OLPDual_Model
-- name    : OLPDual_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:20:37.426746+00:00
-- url     : https://prove2.me/theorems/43df8d22-eb3f-4f3f-9ab0-1d2fab9b1213
-- title:
--   The dual online LP model: parameters of $\Xi$, $f_n$ (6), $f$ (7), $\phi$, $\nabla f$ (8), $\Omega_p$, Assumptions 1 and 2
-- statement:
--   This module fixes the objects of the dual convergence analysis of online linear programming.
--
--   **Setting** (§2, §3.1, pp. 7–11). Vectors live in $\mathbb R^m$ with the Euclidean norm. A column is $u=(a,r)\in\mathbb R^m\times\mathbb R$, and a sample is $n$ columns $u_j=(a_j,r_j)$ drawn i.i.d. from a law $\mathcal P$. Writing $d_i=b_i/n$ for the capacity per period, the sample average approximation and the stochastic program are
--
--   $$
--   f_n(p)=d^\top p+\frac1n\sum_{j=1}^n\bigl(r_j-a_j^\top p\bigr)^+,\qquad
--   f(p)=d^\top p+\mathbb E\bigl[(r-a^\top p)^+\bigr],
--   $$
--
--   both minimized over $p\ge 0$. The sub-gradient of the integrand and its mean are
--
--   $$
--   \phi(p,u)=d-a\,I(r>a^\top p),\qquad \nabla f(p):=\mathbb E[\phi(p,u)],
--   $$
--
--   where the indicator is strict and $\nabla f$ is a definition, since $f$ need not be differentiable. An optimal solution of either problem is a feasible point at which no feasible point has a smaller value (`IsOptimal`). The region $\Omega_p=\{p\ge 0: e^\top p\le\bar r/\underline d\}$ contains every optimal solution. The second-order term of the identities (9) and (11) is built from $\int_{a^\top p}^{a^\top q}\bigl(I(r>v)-I(r>a^\top q)\bigr)\,dv$, an oriented integral.
--
--   **Assumption 1.** $|r|\le\bar r$ and $\|a\|\le\bar a$ almost surely, and $d_i\in(\underline d,\bar d)$ for every $i$.
--
--   **Assumption 2,** at an optimal solution $p^*$ of (7): (a) $v^\top\mathbb E[aa^\top]v\ge\lambda_{\min}\|v\|^2$ for all $v$; (b) for every $p\in\Omega_p$ and almost every $a$,
--
--   $$
--   \lambda|a^\top p-a^\top p^*|\le\bigl|\mathbb P(r>a^\top p\mid a)-\mathbb P(r>a^\top p^*\mid a)\bigr|\le\mu|a^\top p-a^\top p^*|;
--   $$
--
--   (c) $p_i^*=0$ if and only if $d_i-\mathbb E[a_iI(r>a^\top p^*)]>0$.
--
--   The family $\Xi$ of the paper is the set of laws satisfying these assumptions for one fixed value of the parameters $\bar r,\bar a,\underline d,\bar d,\lambda,\mu,\lambda_{\min}$, which `Model` bundles. All later statements are written over these objects.
--
--   **Formalization Note** The law of $(a,r)$ is written `Pa ⊗ₘ κ`, with `Pa` the law of $a$ and `κ` a Markov kernel giving the conditional law of $r$ given $a$; every law on $\mathbb R^m\times\mathbb R$ has this form. `lamMin` is a lower bound on the smallest eigenvalue, and the smallest eigenvalue is one admissible value. The factor `gFactor m` is $m\log m$ for $m\ge 2$ and $1$ for $m=1$. Assumption 1 (d), $n>m$, is carried by the theorems that state it.
-- source:
--   Li–Ye, Online Linear Programming: Dual Convergence, New Algorithms, and Regret Bounds, arXiv:1909.05499v5 (19 Apr 2021), §3, (6) and (7) p.8, Assumption 1 and Ω_p p.9, Assumption 2 p.10, φ and (8) p.11, Ξ p.12, parameters p.13

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OLPDual

/-- The dual space `ℝ^m` of the online linear program, with its Euclidean norm: `‖·‖` is the
`‖·‖₂` of Li–Ye, arXiv:1909.05499v5, Assumption 1, p.9 (PDF 9). -/
abbrev E (m : ℕ) : Type := EuclideanSpace ℝ (Fin m)

/-- A sample of `n` columns. The `j`-th coordinate is `u_j = (a_j, r_j)`; the paper writes
`u_j = (r_j, a_j)`, Li–Ye, arXiv:1909.05499v5, §3.2, p.12 (PDF 12).
**Formalization Note** The order `(a, r)` fits `Measure.compProd`. -/
abbrev Sample (m n : ℕ) : Type := Fin n → E m × ℝ

/-- **The parameters of the family `Ξ`**, Li–Ye, arXiv:1909.05499v5, Assumptions 1–2, pp.9–10
(PDF 9–10), and p.13 ("All of these parameters are not dependent on the specific distribution
`𝒫`"): the bounds `r̄`, `ā`, the capacity box `(d̲, d̄)`, the constants `λ`, `μ` of Assumption 2 (b)
and `λ_min` of Assumption 2 (a).
**Formalization Note** The paper's family `Ξ` (p.12) is the set of laws satisfying Assumptions 1–2
for one fixed value of these parameters; a statement uniform over `Ξ` quantifies over `Model`
first. `lamMin` is a lower bound on the smallest eigenvalue of `E[aaᵀ]` (Assumption 2 (a) below);
the smallest eigenvalue itself is one admissible value. -/
structure Model where
  /-- `r̄`, the bound on `|r|`. -/
  rbar : ℝ
  /-- `ā`, the bound on `‖a‖`. -/
  abar : ℝ
  /-- `d̲`, the lower end of the capacity box. -/
  dlow : ℝ
  /-- `d̄`, the upper end of the capacity box. -/
  dhigh : ℝ
  /-- `λ` of Assumption 2 (b). -/
  lam : ℝ
  /-- `μ` of Assumption 2 (b). -/
  mu : ℝ
  /-- `λ_min` of Assumption 2 (a). -/
  lamMin : ℝ
  rbar_pos : 0 < rbar
  abar_pos : 0 < abar
  dlow_pos : 0 < dlow
  dlow_lt_dhigh : dlow < dhigh
  lam_pos : 0 < lam
  mu_pos : 0 < mu
  lamMin_pos : 0 < lamMin

/-- The feasible set `p ≥ 0` of (5), (6) and (7), Li–Ye, arXiv:1909.05499v5, p.8 (PDF 8). -/
def orthant (m : ℕ) : Set (E m) := {p | ∀ i, 0 ≤ p i}

/-- `p` is an optimal solution of `min g(p)` s.t. `p ≥ 0`, the form of (5), (6) and (7),
Li–Ye, arXiv:1909.05499v5, p.8 (PDF 8): `p` is feasible and no feasible point has a smaller value.
**Formalization Note** Mathlib's `IsMinOn g s p` does not say `p ∈ s`, so feasibility is explicit. -/
def IsOptimal {m : ℕ} (g : E m → ℝ) (p : E m) : Prop :=
  p ∈ orthant m ∧ ∀ q ∈ orthant m, g p ≤ g q

/-- The region `Ω_p = {p ∈ ℝ^m : p ≥ 0, eᵀp ≤ r̄ / d̲}`, Li–Ye, arXiv:1909.05499v5, p.9 (PDF 9). -/
def OmegaP (Θ : Model) (m : ℕ) : Set (E m) :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i ≤ Θ.rbar / Θ.dlow}

/-- The sample average approximation `f_n(p) = dᵀp + (1/n) Σ_j (r_j − a_jᵀp)⁺`, display (6),
Li–Ye, arXiv:1909.05499v5, p.8 (PDF 8). Here `d_i = b_i / n`. -/
noncomputable def fn {m n : ℕ} (d : E m) (ω : Sample m n) (p : E m) : ℝ :=
  ⟪d, p⟫ + (1 / (n : ℝ)) * ∑ j, max ((ω j).2 - ⟪(ω j).1, p⟫) 0

/-- The stochastic program's objective `f(p) = dᵀp + E[(r − aᵀp)⁺]`, display (7),
Li–Ye, arXiv:1909.05499v5, p.8 (PDF 8), where `law` is the law of `(a, r)`.
**Formalization Note** The integrand is bounded almost surely under `Assumption1`, so the Bochner
integral is not a junk value. -/
noncomputable def f {m : ℕ} (d : E m) (law : Measure (E m × ℝ)) (p : E m) : ℝ :=
  ⟪d, p⟫ + ∫ u, max (u.2 - ⟪u.1, p⟫) 0 ∂law

/-- The sub-gradient `φ(p, u) = d − a · I(r > aᵀp)` of `h(p, u) = dᵀp + (r − aᵀp)⁺`,
Li–Ye, arXiv:1909.05499v5, p.11 (PDF 11). The indicator is strict, as printed: `φ(p, u) = d` when
`r = aᵀp`. -/
noncomputable def phi {m : ℕ} (d p : E m) (u : E m × ℝ) : E m :=
  d - (if u.2 > ⟪u.1, p⟫ then u.1 else 0)

/-- `∇f(p) := E[φ(p, u)]`, display (8), Li–Ye, arXiv:1909.05499v5, p.11 (PDF 11). It is a
definition: `f` need not be differentiable.
**Formalization Note** `φ` is measurable and bounded almost surely under `Assumption1`, so the
Bochner integral is not a junk value. -/
noncomputable def gradf {m : ℕ} (d : E m) (law : Measure (E m × ℝ)) (p : E m) : E m :=
  ∫ u, phi d p u ∂law

/-- The integrand of the second-order term of (9), (11) and (12),
`∫_{aᵀp}^{aᵀq} (I(r > v) − I(r > aᵀq)) dv`, Li–Ye, arXiv:1909.05499v5, pp.11–13 (PDF 11–13).
**Formalization Note** An oriented interval integral, as printed: `aᵀp` may exceed `aᵀq`. Both
indicators are strict. -/
noncomputable def knightTerm {m : ℕ} (a : E m) (r : ℝ) (p q : E m) : ℝ :=
  ∫ v in ⟪a, p⟫..⟪a, q⟫, ((if r > v then (1 : ℝ) else 0) - (if r > ⟪a, q⟫ then (1 : ℝ) else 0))

/-- The law of an i.i.d. sample of `n` columns from `law`: Assumption 1 (a),
Li–Ye, arXiv:1909.05499v5, p.9 (PDF 9). -/
noncomputable def sampleLaw {m : ℕ} (law : Measure (E m × ℝ)) (n : ℕ) : Measure (Sample m n) :=
  Measure.pi fun _ : Fin n => law

/-- **Assumption 1 (b), (c)**, Li–Ye, arXiv:1909.05499v5, p.9 (PDF 9): `|r| ≤ r̄` and `‖a‖ ≤ ā`
almost surely, and `d_i ∈ (d̲, d̄)` for every `i`.
**Formalization Note** Assumption 1 (a) is `sampleLaw`. Assumption 1 (d), `n > m`, is written as a
hypothesis of a theorem exactly when the theorem's own statement has it. -/
structure Assumption1 (Θ : Model) {m : ℕ} (d : E m) (law : Measure (E m × ℝ)) : Prop where
  /-- Assumption 1 (b). -/
  bounded : ∀ᵐ u ∂law, |u.2| ≤ Θ.rbar ∧ ‖u.1‖ ≤ Θ.abar
  /-- Assumption 1 (c). -/
  growth : ∀ i, Θ.dlow < d i ∧ d i < Θ.dhigh

/-- **Assumption 2**, Li–Ye, arXiv:1909.05499v5, p.10 (PDF 10), at an optimal solution `pstar` of
(7), for the law `Pa ⊗ₘ κ` of `(a, r)`: `Pa` is the law of `a` and `κ a` the conditional law of
`r` given `a`.
**Formalization Note** Every law on `E m × ℝ` has this form (disintegration), so the kernel encodes
`ℙ(· | a)`; (b) is read "for every `p ∈ Ω_p`, for `Pa`-almost every `a`". `lamMin` in (a) is a lower
bound on the smallest eigenvalue of `M = E[aaᵀ]`: the inequality says `vᵀMv ≥ λ_min ‖v‖²`. -/
structure Assumption2 (Θ : Model) {m : ℕ} (d : E m) (Pa : Measure (E m))
    (κ : Kernel (E m) ℝ) (pstar : E m) : Prop where
  /-- Assumption 2 (a): `E[aaᵀ]` is positive definite with smallest eigenvalue at least `λ_min`. -/
  secondMoment : ∀ v : E m, Θ.lamMin * ‖v‖ ^ 2 ≤ ∫ a, ⟪a, v⟫ ^ 2 ∂Pa
  /-- Assumption 2 (b): the two-sided Lipschitz condition on the conditional law of `r`. -/
  conditional : ∀ p ∈ OmegaP Θ m, ∀ᵐ a ∂Pa,
    Θ.lam * |⟪a, p⟫ - ⟪a, pstar⟫| ≤
        |(κ a).real (Set.Ioi ⟪a, p⟫) - (κ a).real (Set.Ioi ⟪a, pstar⟫)| ∧
      |(κ a).real (Set.Ioi ⟪a, p⟫) - (κ a).real (Set.Ioi ⟪a, pstar⟫)| ≤
        Θ.mu * |⟪a, p⟫ - ⟪a, pstar⟫|
  /-- Assumption 2 (c): strict complementarity. -/
  strictComplementarity : ∀ i, pstar i = 0 ↔
    0 < d i - ∫ u, (if u.2 > ⟪u.1, pstar⟫ then u.1 i else 0) ∂(Pa ⊗ₘ κ)

/-- The dimension factor of Theorem 1, Li–Ye, arXiv:1909.05499v5, pp.13–14 (PDF 13–14): `m log m`
for `m ≥ 2`, and `1` for `m = 1` ("without the `log m` term", p.14). -/
noncomputable def gFactor (m : ℕ) : ℝ := if m = 1 then 1 else m * Real.log m

end OLPDual


