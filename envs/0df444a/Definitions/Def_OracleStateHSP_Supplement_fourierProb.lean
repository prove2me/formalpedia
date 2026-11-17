-- Prove2me | Definitions.Def_OracleStateHSP_Supplement_fourierProb
-- name    : OracleStateHSP_Supplement_fourierProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:10:05.472242+00:00
-- url     : https://prove2.me/theorems/9bfe4af1-b49d-42dc-9e14-9aa31e78b925
-- title:
--   Weak Fourier sampling distribution $P(\lambda) = \|\frac{1}{|G|}\sum_g \chi_\lambda(g)R(g)|\varphi\rangle\|^2$ (eq. (24))
-- statement:
--   Let $G$ be a finite abelian group with a unitary representation $R$ and let $|\varphi\rangle$ be a state vector. The Fourier sampling circuit applied to one copy of $|\varphi\rangle$ prepares
--   $$
--   |\varphi_F\rangle = \frac{1}{|G|}\sum_{g \in G}\sum_{\lambda \in \hat G} \chi_\lambda(g)\, |\lambda\rangle \otimes R(g)|\varphi\rangle ,
--   $$
--   and measuring its first register returns $\lambda \in \hat G$ with the Born probability
--   $$
--   P(\lambda) = \Big\| \frac{1}{|G|} \sum_{g \in G} \chi_\lambda(g)\, R(g)|\varphi\rangle \Big\|^2 .
--   $$
--   Each call consumes one copy, so successive calls are independent draws from $P$.
--
--   **Formalization Note** $P$ is defined by the Born rule; the closed form (25) of Fact 3.5 and the support property of Fact 3.6 are consequences, not part of the definition.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, eqs. (22)–(24), p.22

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_OracleStateHSP_Supplement_chi

namespace OracleStateHSP

namespace Supplement

open QAlgorithms

/-- The weak Fourier sampling distribution of Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, eqs. (22)–(24), p.22: the probability of
outcome `λ ∈ Ĝ` when the first register of
`|φ_F⟩ = (1/|G|) ∑_(g∈G) ∑_λ χ_λ(g) |λ⟩ ⊗ R(g)|φ⟩` is measured, i.e. the Born probability
`P(λ) = ‖(1/|G|) ∑_(g∈G) χ_λ(g) R(g)|φ⟩‖²`.

**Formalization Note.** Defined by the Born rule, not by the closed form (25) of Fact 3.5 (which is
a consequence). One call to the Fourier sampling routine consumes one copy of `|φ⟩` and returns a
draw from `P`. -/
noncomputable def fourierProb {n : ℕ} {M : Fin n → ℕ} [∀ l, NeZero (M l)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : CycProd n M → Matrix ι ι ℂ) (φ : EuclideanSpace ℂ ι) (lam : CycProd n M) : ℝ :=
  ‖((Fintype.card (CycProd n M) : ℂ)⁻¹) • ∑ g, chi lam g • act (R g) φ‖ ^ 2

end Supplement

end OracleStateHSP


