-- Prove2me | Definitions.Def_PrettyGoodCriterion_OutputSymmetric
-- name    : PrettyGoodCriterion_OutputSymmetric
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:29:11.756194+00:00
-- url     : https://prove2.me/theorems/79573e05-b04d-4d16-acfb-aa77fb69e10a
-- title:
--   Output-symmetric binary-input classical–quantum channels
-- statement:
--   A **binary-input classical–quantum (cq) channel** is a map $\Phi_\sigma:\{0,1\}\to\mathrm D(\mathbb C^d)$, $\Phi_\sigma(b)=\sigma_b$. It is **output-symmetric** if some $d\times d$ unitary $U$ exchanges the outputs:
--   $$U\sigma_0U^\dagger=\sigma_1,\qquad U\sigma_1U^\dagger=\sigma_0 .$$
--   The **memoryless extension** sends a word $c=(c_1,\dots,c_n)\in\{0,1\}^n$ to the product state
--   $$\sigma_c:=\Phi_\sigma^{\otimes n}(c)=\sigma_{c_1}\otimes\cdots\otimes\sigma_{c_n}.$$
--
--   The binary symmetric and binary erasure channels are output-symmetric cq channels with commuting outputs; the paper's new channels have non-commuting outputs.
--
--   **Formalization Note** The channel is its pair of outputs `σ : Fin 2 → Matrix ι ι ℂ`; $U^\dagger$ is `star U` and $U$ ranges over `Matrix.unitaryGroup ι ℂ`. The product state $\sigma_c$ is the published `HolevoCQ.wordState σ n c`: the tensor power $(\mathbb C^d)^{\otimes n}$ is indexed by `Fin n → ι` (coordinate $i$ is the $i$-th factor), and $\sigma_c$ has entries $\prod_i\sigma_{c_i}(a_i,b_i)$.
-- source:
--   Alrabiah, Guruswami, Binary code rate bounds via classical–quantum channels, arXiv:2608.09347 (held version, sha256 e6d5ac13…), Definition 2.4, p.15 (PDF 17)

import Mathlib

namespace PrettyGoodCriterion

/-- A binary-input cq channel `Φ_σ : b ↦ σ_b` is **output-symmetric** if some unitary `U`
exchanges its outputs: `Uσ₀U† = σ₁` and `Uσ₁U† = σ₀`, Alrabiah–Guruswami, arXiv:2608.09347
(held version), Definition 2.4, p.15 (PDF 17).

**Formalization Note.** The channel is its pair of output matrices `σ : Fin 2 → Matrix ι ι ℂ`
(bits are `Fin 2`); `U†` is `star U`. Its memoryless extension
`σ_c = σ_{c₁} ⊗ ⋯ ⊗ σ_{cₙ}` (Definition 2.4) is the published `HolevoCQ.wordState σ n c`, indexed
by `Fin n → ι` with entries `∏ᵢ σ_{cᵢ}(aᵢ, bᵢ)`. -/
def OutputSymmetric {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Fin 2 → Matrix ι ι ℂ) : Prop :=
  ∃ U ∈ Matrix.unitaryGroup ι ℂ, U * σ 0 * star U = σ 1 ∧ U * σ 1 * star U = σ 0

end PrettyGoodCriterion


