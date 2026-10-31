-- Prove2me | Definitions.Def_BewleyGE_excessDemand
-- name    : BewleyGE_excessDemand
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:31:49.724987+00:00
-- url     : https://prove2.me/theorems/5de801c7-ccca-4e95-b824-5c0713767a86
-- title:
--   Excess demand $\zeta:P\to\mathbb R^{n+1}$
-- statement:
--   For a family $(x,g,\mu)$ and $(p,r)\in P$, the **excess demand** $\zeta(p,r)\in\mathbb R^{n+1}$ has the goods coordinates
--   $$
--   \zeta_i(p,r)=\int_{A(p,r)}x^*_i\big(a-g(a,p,r),p\big)\,\mu(da;p,r)-\sum_{y\in\mathcal Y}e(y)\,y_i,\qquad i=1,\dots,n,
--   $$
--   and the savings coordinate
--   $$
--   \zeta_{n+1}(p,r)=-\int_{A(p,r)}g(a,p,r)\,\mu(da;p,r).
--   $$
--   $(p,r)$ is an equilibrium price exactly when $\zeta(p,r)=0$.
--
--   **Formalization Note** The marginal sum $\sum_{y_i\in\mathcal Y_i}e_i(y_i)y_i$ of the paper is written $\sum_{y\in\mathcal Y}e(y)y_i$ (p.24).
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, §3.1, p.10 (restated p.20)

import Mathlib
import Definitions.Def_BewleyGE_wealthSet

open MeasureTheory

namespace BewleyGE

/-- **Excess demand** `ζ : P → ℝⁿ⁺¹`. Light, arXiv:1906.06810v2, §3.1, p.10 (restated p.20):
`ζᵢ(p, r) = ∫_{A(p,r)} x*ᵢ(a − g(a, p, r), p) μ(da; p, r) − ∑_{yᵢ ∈ 𝒴ᵢ} eᵢ(yᵢ) yᵢ` for goods
`i = 1, …, n`, and `ζ_{n+1}(p, r) = −∫_{A(p,r)} g(a, p, r) μ(da; p, r)` for savings.

Given a family `(x, g, μ)` indexed by `π = (p, r)`, the excess demand at `π` has the goods
coordinates `i.castSucc` and the savings coordinate `Fin.last n`.

**Formalization Note.** The marginal sum `∑_{yᵢ} eᵢ(yᵢ) yᵢ` is written `∑_{y ∈ 𝒴} e(y) yᵢ`, the
identity of p.24. The paper's `ζ` is this function for the family of Lemmas 1–2 (see
`IsEqFamily`); only its values on `P` are meaningful. -/
noncomputable def excessDemand {n : ℕ} (E : Economy n)
    (x : (Fin (n + 1) → ℝ) → ℝ → Fin n → ℝ) (g : (Fin (n + 1) → ℝ) → ℝ → ℝ)
    (μ : (Fin (n + 1) → ℝ) → Measure ℝ) (π : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc (α := fun _ => ℝ)
    (fun i : Fin n =>
      (∫ a in wealthSet E (fun j => π j.castSucc) (π (Fin.last n)), x π (a - g π a) i ∂(μ π))
        - ∑ y ∈ E.Y, E.e y * y i)
    (-∫ a in wealthSet E (fun j => π j.castSucc) (π (Fin.last n)), g π a ∂(μ π))

end BewleyGE


