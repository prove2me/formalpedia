-- Prove2me | Definitions.Def_LCAntiConc_IsCertAntiConc
-- name    : LCAntiConc_IsCertAntiConc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:49:22.24987+00:00
-- url     : https://prove2.me/theorems/9c5a4174-1157-4ef6-aee4-0a9ee2f5c632
-- title:
--   Definition 1.1 — $\delta$-certifiable anti-concentration at degree $D$
-- statement:
--   Let $\delta>0$, let $D$ be a positive integer and $A$ a constant. A random vector $X\in\mathbb R^d$ is **$\delta$-certifiably anti-concentrated at degree $D$** (with constant $A$) if there is a univariate polynomial $q$ of degree at most $D$ with
--
--   $$q(t)\ge0\quad(t\in\mathbb R),\qquad q(t)\ge1\quad(|t|\le\delta),\tag{1.2}$$
--
--   such that
--
--   $$\{\|v\|_2^2=1\}\vdash_D\ \mathbb E\,q(\langle X,v\rangle)\le A\,\delta.\tag{1.3}$$
--
--   Since $q$ majorizes the indicator of $[-\delta,\delta]$, evaluating the certificate at unit vectors gives $\mathbb P[|\langle X,u\rangle|\le\delta]\le A\delta$ for every unit $u$, and a semidefinite program can find such a certificate in time $d^{O(D)}$.
--
--   **Formalization Note** The page's $O(\delta)$ is the explicit constant $A$, quantified by every statement that uses the definition. The coefficients of $q(\langle x,v\rangle)$ are required to be integrable, so that $\mathbb E\,q(\langle X,v\rangle)$ exists, as (1.3) presupposes.
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), Definition 1.1, (1.2)–(1.3), p.2 (PDF p.4)

import Mathlib
import Definitions.Def_LCAntiConc_SphereSoSLe
import Definitions.Def_LCAntiConc_PolyIntegrable
import Definitions.Def_LCAntiConc_linForm
import Definitions.Def_LCAntiConc_expectQ

namespace LCAntiConc

open MeasureTheory

/-- **Definition 1.1** (certifiable anti-concentration), with the `O(δ)` of (1.3) as the explicit
constant `A`: a random vector `X ∈ ℝ^d` (law `μ`) is `δ`-certifiably anti-concentrated at degree
`D` (a positive integer) if there is a polynomial `q : ℝ → ℝ` of degree at most `D` with
`q(t) ≥ 0` for all `t`, `q(t) ≥ 1` for `|t| ≤ δ` (1.2), and
`{‖v‖₂² = 1} ⊢_D 𝔼 q(⟨X, v⟩) ≤ A δ` (1.3).

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), Definition 1.1, p.2 (PDF p.4).

**Formalization Note** `O(δ)` is the constant `A`, quantified by every statement that uses the
definition. The coefficients of `q(⟨x, v⟩)` are required to be integrable, so that the polynomial
`𝔼 q(⟨X, v⟩)` exists (this is presupposed by (1.3)). -/
def IsCertAntiConc {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) (δ : ℝ) (D : ℕ) (A : ℝ) :
    Prop :=
  0 < D ∧ ∃ q : Polynomial ℝ, q.natDegree ≤ D ∧ (∀ t, 0 ≤ q.eval t) ∧
    (∀ t, |t| ≤ δ → 1 ≤ q.eval t) ∧
    PolyIntegrable μ (fun x => Polynomial.aeval (linForm x) q) ∧
    SphereSoSLe D (expectQ μ q) (A * δ)

end LCAntiConc


