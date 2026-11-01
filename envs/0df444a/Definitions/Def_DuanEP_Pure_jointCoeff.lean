-- Prove2me | Definitions.Def_DuanEP_Pure_jointCoeff
-- name    : DuanEP_Pure_jointCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:21:27.904471+00:00
-- url     : https://prove2.me/theorems/60007fd0-d660-4cd9-a404-c67e637aa3fb
-- title:
--   Joint state $|\Psi\rangle_{(A_iB_i)}$ of $m$ squeezed pairs
-- statement:
--   Let $m\in\mathbb N$ and $r\in\mathbb R$. The **joint state** of $m$ pairs $A_1B_1,\dots,A_mB_m$, each in the two-mode squeezed state $|\Psi\rangle_{A_iB_i}$ of Eq. (1), is the tensor product of the $m$ pair states. Its Fock labels are pairs $(a,b)$ of occupation vectors $a,b\in\mathbb N^m$, where $a_i$ is the occupation of mode $A_i$ and $b_i$ that of mode $B_i$, and its coefficient is
--
--   $$
--   \Psi^{(m)}_r(a,b)=\prod_{i=1}^m c_r(a_i,b_i).
--   $$
--
--   The split of a label into $a$ (the modes $A_1,\dots,A_m$ held by side A) and $b$ (the modes $B_1,\dots,B_m$ held by side B) is the bipartite cut A|B with respect to which entanglement is measured.
-- source:
--   Duan, Giedke, Cirac, Zoller, Entanglement purification of Gaussian continuous variable quantum states, arXiv:quant-ph/9912017v2, p. 1, sentence before Eq. (2)

import Mathlib
import Definitions.Def_DuanEP_Pure_pairCoeff

namespace DuanEP.Pure

/-- The joint state `|Ψ⟩_{(AᵢBᵢ)}` of `m` two-mode squeezed pairs, "simply the product of all the
`|Ψ⟩_{AᵢBᵢ}`" (Duan, Giedke, Cirac, Zoller, *Entanglement purification of Gaussian continuous variable quantum states*, arXiv:quant-ph/9912017v2, before Eq. (2), p. 1), as a coefficient function on the Fock labels
`(a, b)` of the `A` side `A₁,…,A_m` and the `B` side `B₁,…,B_m`: `a i` is the occupation of `Aᵢ`
and `b i` that of `Bᵢ`.

**Formalization Note** The pair `(a, b) : (Fin m → ℕ) × (Fin m → ℕ)` encodes the bipartite cut
`A = A₁…A_m` versus `B = B₁…B_m` (the first component is Alice's, the second Bob's); the coefficient
is `∏ᵢ pairCoeff r (a i, b i)`. -/
noncomputable def jointCoeff (m : ℕ) (r : ℝ) : (Fin m → ℕ) × (Fin m → ℕ) → ℂ :=
  fun p => ∏ i, pairCoeff r (p.1 i, p.2 i)

end DuanEP.Pure


