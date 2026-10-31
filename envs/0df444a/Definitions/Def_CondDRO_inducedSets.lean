-- Prove2me | Definitions.Def_CondDRO_inducedSets
-- name    : CondDRO_inducedSets
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:24:55.155017+00:00
-- url     : https://prove2.me/theorems/cf1667c1-3be4-4352-9e4c-38a75b8c2712
-- title:
--   Atom-wise sets $\mathfrak A_i=\{Q_{|\varpi_i}: Q\in\mathfrak M,\ Q(\varpi_i)\neq0\}$ induced by $\mathfrak M$, display (2.8)
-- statement:
--   Let $\{\varpi_i\}_{i\in\mathcal I}$ be a finite partition of a measurable space $(\Omega,\mathcal F)$ and $\mathfrak M$ a set of probability measures. For a probability measure $Q$ with $Q(\varpi_i)\neq0$, the conditional probability given $\varpi_i$ is (display (2.4))
--
--   $$
--   Q_{|\varpi_i}(A)=\frac{Q(A\cap\varpi_i)}{Q(\varpi_i)},\qquad A\in\mathcal F,
--   $$
--
--   a probability measure supported on $\varpi_i$. The **sets induced by $\mathfrak M$** are
--
--   $$
--   \mathfrak A_i:=\bigl\{Q_{|\varpi_i}\ :\ Q\in\mathfrak M\text{ and }Q(\varpi_i)\neq0\bigr\},\qquad i\in\mathcal I .
--   $$
--
--   They turn an ambiguity set on $\Omega$ into one ambiguity set per atom, so that the conditional risk measure (2.7) of these sets can be compared with the conditional distributionally robust functional (2.6) of $\mathfrak M$.
--
--   **Formalization Note** $Q_{|\varpi_i}$ is Mathlib's conditional measure `ProbabilityTheory.cond`, defined as $Q(\varpi_i)^{-1}$ times the restriction of $Q$ to $\varpi_i$; for a measurable $\varpi_i$ with $0<Q(\varpi_i)<\infty$ it is exactly (2.4).
-- source:
--   Shapiro & Pichler, Conditional Distributionally Robust Functionals, preprint (October 9, 2022), display (2.8), p.5, with the conditional probability (2.4), p.4

import Mathlib
import Definitions.Def_CondDRO_FinitePartition

open MeasureTheory ProbabilityTheory

namespace CondDRO

/-- **The sets 𝔄ᵢ induced by an ambiguity set 𝔐** (Shapiro & Pichler, *Conditional
Distributionally Robust Functionals*, preprint (October 9, 2022), display (2.8), p.5):
`𝔄ᵢ := { Q|ϖᵢ | Q ∈ 𝔐 and Q(ϖᵢ) ≠ 0 }`, `i ∈ ℐ`, where `Q|ϖᵢ(A) = Q(A ∩ ϖᵢ)/Q(ϖᵢ)` is the
conditional probability (2.4), p.4.

**Formalization Note.** `Q|ϖᵢ` is Mathlib's `ProbabilityTheory.cond Q (ϖ.cell i)` (notation
`Q[|ϖ.cell i]`), defined as `(Q ϖᵢ)⁻¹ • Q.restrict ϖᵢ`; for a measurable cell with
`0 < Q(ϖᵢ) < ∞` it assigns `Q(A ∩ ϖᵢ)/Q(ϖᵢ)` to every measurable `A` (`cond_apply`), which is (2.4). -/
noncomputable def inducedSets {Ω : Type*} [MeasurableSpace Ω] {I : Type*}
    (M : Set (Measure Ω)) (ϖ : FinitePartition Ω I) : I → Set (Measure Ω) :=
  fun i => (fun Q : Measure Ω => Q[|ϖ.cell i]) '' {Q : Measure Ω | Q ∈ M ∧ Q (ϖ.cell i) ≠ 0}

end CondDRO


